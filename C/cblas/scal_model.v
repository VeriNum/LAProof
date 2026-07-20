(**  * LAProof.C.cblas.scal_model: functional model of GSL's [cblas_dscal]. *)
(** ** Corresponds to C program [C/cblas/src/dscal.c] (ported from GSL cblas). *)

(** This file provides two exact scaling models.  [scal_model] maps a scaling
    operation over an entire contiguous list; [scal_strided] models the general
    positive-stride [cblas_dscal] proof by updating the selected positions in
    the full input array.  Scaling is a deterministic *elementwise* update with
    no accumulation and needs no [feq] bridge.  GSL's kernel
    ([source_scal_r.h]) is
<<
      for (i = 0; i < N; i++) { X[ix] *= alpha; ix += incX; }
>>
    i.e., [X[ix] *= alpha] is [BMULT (X[ix]) alpha] (element-first).
    [scal_model] below captures the contiguous whole-list special case; the
    later [scal_strided] definition captures the kernel for arbitrary positive
    stride when the input array may contain unselected elements.

    LAProof's existing scale model [mv_mathcomp.scalemx] is alpha-first
    ([map_mx (BMULT a)]) and matrix-based; relating to it would need a [BMULT]
    commutativity lemma (not in LAProof) plus a vector/matrix reshape.  That is
    unnecessary here: the per-element accuracy (relative error <= unit roundoff)
    is exactly vcfloat's correctly-rounded-[BMULT] bound. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From LAProof.C Require Import floatlib.

Set Bullet Behavior "Strict Subproofs".

Definition scal_model (alpha: ftype Tdouble) (X: list (ftype Tdouble)) : list (ftype Tdouble) :=
  map (fun x => BMULT x alpha) X.

Lemma Zlength_scal_model: forall alpha X,
  Zlength (scal_model alpha X) = Zlength X.
Proof. intros. unfold scal_model. rewrite Zlength_map. reflexivity. Qed.

Lemma Znth_scal_model: forall alpha X k,
  0 <= k < Zlength X ->
  Znth k (scal_model alpha X) = BMULT (Znth k X) alpha.
Proof. intros. unfold scal_model. rewrite Znth_map by lia. reflexivity. Qed.

(** ** Strided-access helper used by [dscal] and [dasum]. *)

(** [strided incX N X] is the list of the [N] elements
    [[Znth 0 X; Znth incX X; ...; Znth ((N-1)*incX) X]] -- exactly the elements a
    GSL BLAS loop with stride [incX] touches in array [X].  It is a regular
    *strided* selection (step [incX]) from a *contiguous* array.  It is NOT a
    gather: a gather's addresses come from an index-vector *operand* (data) -- as
    in [verif_sparse]'s [Znth (Znth h col_ind) vval], where the [col_ind] array
    supplies the indices -- whereas here every index is derived from the single
    scalar [incX] as [i*incX].  (The distinction is the *source* of the indices,
    not their regularity: a gather's index vector could itself hold
    [0; incX; 2*incX; ...].)  It is also NOT a contiguous prefix/[sublist].  The
    lemma names follow VST's [Zlength_<f>]/[Znth_<f>] convention so
    [list_solve]/[autorewrite with sublist] discharge length and element
    side-goals automatically. *)
Definition strided {A} `{Inhabitant A} (incX N : Z) (X : list A) : list A :=
  map (fun i => Znth (i * incX) X) (upto (Z.to_nat N)).

Lemma Zlength_strided: forall {A} `{Inhabitant A} incX N (X: list A),
  0 <= N -> Zlength (strided incX N X) = N.
Proof.
  intros. unfold strided. rewrite Zlength_map, Zlength_upto, Z2Nat.id by lia. reflexivity.
Qed.

Lemma strided_snoc: forall {A} `{Inhabitant A} incX k (X: list A),
  0 <= k -> strided incX (k+1) X = strided incX k X ++ [Znth (k*incX) X].
Proof.
  intros A ? incX k X Hk. unfold strided.
  replace (Z.to_nat (k+1)) with (Z.to_nat k + 1)%nat by lia.
  rewrite upto_app, map_app. f_equal.
  cbn [upto map]. rewrite Z.add_0_r, Z2Nat.id by lia. reflexivity.
Qed.

(** ** Strided in-place scaling model (general positive stride [incX > 0]). *)

(** [scal_strided incX N alpha X] is [X] with the [N] strided positions
    [{i*incX : 0 <= i < N}] scaled by [alpha] and every other position unchanged
    -- exactly the array state left by GSL's [cblas_dscal] loop at stride [incX].
    It is a left fold of [upd_Znth] over the touched indices, so the loop
    invariant can carry it directly and each store step is [scal_strided_snoc].
    [src] holds the original values (the factor [BMULT (Znth (i*incX) src) alpha]
    reads the *original* entry); [acc] is the running array. *)
Definition scal_fold (incX: Z) (alpha: ftype Tdouble) (src: list (ftype Tdouble))
                     (l: list Z) (acc: list (ftype Tdouble)) : list (ftype Tdouble) :=
                     (* l is the list of iteration indices, not the data *)
  fold_left (fun a i => upd_Znth (i*incX) a (BMULT (Znth (i*incX) src) alpha)) l acc.

Definition scal_strided (incX N: Z) (alpha: ftype Tdouble) (X: list (ftype Tdouble))
  : list (ftype Tdouble) :=
  scal_fold incX alpha X (upto (Z.to_nat N)) X.

Lemma scal_strided_0: forall incX alpha X, scal_strided incX 0 alpha X = X.
Proof. reflexivity. Qed.

Lemma Zlength_scal_fold: forall incX alpha src l acc,
  (forall i, In i l -> 0 <= i*incX < Zlength acc) ->
  Zlength (scal_fold incX alpha src l acc) = Zlength acc.
Proof.
  intros incX alpha src. unfold scal_fold.
  induction l as [|a l IH]; intros acc Hin; [reflexivity|].
  cbn [fold_left].
  assert (Ha: 0 <= a*incX < Zlength acc) by (apply Hin; left; reflexivity).
  rewrite IH.
  - apply upd_Znth_Zlength; auto.
  - intros i Hi. rewrite upd_Znth_Zlength by exact Ha. apply Hin; right; exact Hi.
Qed.

Lemma Znth_scal_fold_notin: forall incX alpha src l acc p,
  0 <= p < Zlength acc ->
  (forall i, In i l -> 0 <= i*incX < Zlength acc) ->
  ~ In p (map (fun i => i*incX) l) ->
  Znth p (scal_fold incX alpha src l acc) = Znth p acc.
Proof.
  intros incX alpha src. unfold scal_fold.
  induction l as [|a l IH]; intros acc p Hp Hin Hnin; [reflexivity|].
  cbn [fold_left].
  assert (Ha: 0 <= a*incX < Zlength acc) by (apply Hin; left; reflexivity).
  assert (Hne: p <> a*incX) by (intro Heq; apply Hnin; cbn [map]; left; symmetry; exact Heq).
  set (acc' := upd_Znth (a*incX) acc (BMULT (Znth (a*incX) src) alpha)).
  assert (Hlen: Zlength acc' = Zlength acc) by (subst acc'; apply upd_Znth_Zlength; auto).
  transitivity (Znth p acc').
  - apply IH.
    + rewrite Hlen; exact Hp.
    + intros i Hi. rewrite Hlen. apply Hin; right; exact Hi.
    + intro Hc. apply Hnin; cbn [map]; right; exact Hc.
  - subst acc'. apply upd_Znth_diff; auto.
Qed.

Lemma scal_strided_snoc: forall incX k alpha X, 0 <= k ->
  scal_strided incX (k+1) alpha X
  = upd_Znth (k*incX) (scal_strided incX k alpha X) (BMULT (Znth (k*incX) X) alpha).
Proof.
  intros incX k alpha X Hk. unfold scal_strided, scal_fold.
  replace (Z.to_nat (k+1)) with (Z.to_nat k + 1)%nat by lia.
  rewrite upto_app, fold_left_app.
  cbn [upto map fold_left]. rewrite Z.add_0_r, Z2Nat.id by lia. reflexivity.
Qed.

Lemma Zlength_scal_strided: forall incX N alpha X,
  0 <= N -> 0 < incX -> (N-1)*incX < Zlength X ->
  Zlength (scal_strided incX N alpha X) = Zlength X.
Proof.
  intros incX N alpha X HN Hinc Hb. unfold scal_strided.
  apply Zlength_scal_fold.
  intros i Hi. rewrite In_upto, Z2Nat.id in Hi by lia. split; nia.
Qed.

(** The C kernel [X[ix] *= alpha] is a read-modify-write -- [X[ix] = X[ix] *
    alpha] -- reading the current contents of [X[ix]] before storing back.  At
    step [k] the slot [k*incX] is still untouched: prior writes hit [j*incX],
    [j < k], all below [k*incX] since [incX > 0].  So the value read equals the
    original [Znth (k*incX) X]. *)
Lemma Znth_scal_strided_self: forall incX k alpha X,
  0 <= k -> 0 < incX -> k*incX < Zlength X ->
  Znth (k*incX) (scal_strided incX k alpha X) = Znth (k*incX) X.
Proof.
  intros incX k alpha X Hk Hinc Hkb. unfold scal_strided.
  apply Znth_scal_fold_notin.
  - split; [ nia | exact Hkb ].
  - intros i Hi. rewrite In_upto, Z2Nat.id in Hi by lia. split; nia.
  - rewrite in_map_iff. intros [j [Hj Hjin]].
    rewrite In_upto, Z2Nat.id in Hjin by lia. nia.
Qed.
