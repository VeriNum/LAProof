(** * LAProof.C.matrix_model: Functional models of matrix operations *)

(** * Prologue: typical imports for MathComp floating-point matrix functional models *)

(* BEGIN This part copied from iterative_methods/cholesky/cholesky_model.v, 
   modified a bit, should really unify these libraries somehow *)

(** Don't import all of VST, since we have no separation-logic reasoning here;
  import only the part of VST for reasoning about functional models. *) 
Require Import VST.floyd.functional_base.

(** Other useful imported libraries. *)
Import ListNotations.
From Stdlib Require Import Permutation.
Require Import vcfloat.FPStdLib.
(*Require Import vcfloat.FPStdCompCert.*)
Require Import LAProof.accuracy_proofs.solve_model.

(** In contrast to certain other modules (e.g., [C.spec_densemat]
  where we [Require] mathcomp but carefully don't [Import] most of it), 
  here we intend to do lots of mathcomp reasoning, so we [Require Import]. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun bigop finset fingroup perm order.
From mathcomp Require Import div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.

(** Now we adjust all the settings that mathcomp has modified *)
(* begin show *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
(* end show *)

Definition neg_zero {t}: ftype t := Binary.B754_zero (fprec t) (femax t) true.


Lemma map_inj: forall [T1 T2] (f: T1 -> T2) (H: injective f) (al bl: list T1), map f al = map f bl -> al=bl.
Proof.
induction al; destruct bl; simpl; intros; inversion H0; clear H0; subst; auto.
f_equal; auto.
Qed.

Lemma enum_mem_ordinal: forall n, enum_mem (mem (ordinal n)) = ord_enum n.
Proof.
move => n. 
apply (@map_inj _ _ (@nat_of_ord n) (@ord_inj _)).
rewrite val_ord_enum val_enum_ord //.
Qed.


Definition widen_ik {n} (i: 'I_n) (k: 'I_i) : 'I_n := 
   widen_ord (ltnW (ltn_ord i)) k.

Lemma take_ord_enum: forall [n] (k: 'I_n), take k (ord_enum n) = map (@widen_ik _ _) (ord_enum k).
Proof.
intros.
  destruct k as [k H]; simpl in *.
  unfold widen_ik. simpl.
  set (H0 := ltnW _). clearbody H0.
  change (fun _ => _) with (@widen_ord k n H0).
  apply (@map_inj _ _ (@nat_of_ord n)). apply ord_inj.
  rewrite map_take val_ord_enum take_iota /minn H /ord_enum -map_comp pmap_filter.
  2: move => x; unfold insub; destruct idP; auto.
  clear.
  destruct k; auto.
  set (n := S k) in *.
  replace (fun x => isSome (insub x)) with (fun x => leq (S x) (addn O n)).
  2: extensionality m; unfold isSome, insub; destruct idP; auto.
  rewrite filter_iota_ltn; auto; lia.
  lia.
Qed.

(** When we have run the "Cholesky jik algorithm" only up to iteration (i,j),
   the matrix is only initialized above row i, and in row i up to column j, so we
  need this subrelation in our loop invariant. *)
Definition cholesky_jik_upto {NAN: FPCore.Nans}{t} [n] (imax: 'I_n) (jmax : 'I_n.+1) (A R : 'M[ftype t]_n) : Prop :=
  forall (i j: 'I_n),
      ((j<jmax)%N -> cholesky_jik_ij A R i j)
   /\ (nat_of_ord j = nat_of_ord jmax -> (i<imax)%N -> cholesky_jik_ij A R i j)
   /\ ((j>jmax)%N -> R i j = A i j)
   /\ (nat_of_ord j= nat_of_ord jmax -> (i>=imax)%N -> R i j = A i j).

(** The functional model above assumes that we compute every dot-product in left-to-right order.
  But the algorithm should work equally accurately no matter what the order, so we
 have this alternate presentation that permits any order of summation. *)

(* BEGIN adapted from iterative_methods/sparse/sparse_model.v *)
Inductive sum_any  {NAN: FPCore.Nans}{t}: forall (v: list (ftype t)) (s: ftype t), Prop :=
| Sum_Any_0: sum_any nil (Zconst t 0)
| Sum_Any_1: forall x y, feq x y -> sum_any [x] y
| Sum_Any_split: forall al bl a b c, sum_any al a -> sum_any bl b -> feq (BPLUS a b) c -> sum_any (al++bl) c
| Sum_Any_perm: forall al bl s, Permutation al bl -> sum_any al s -> sum_any bl s.
(* END copied form iterative_methods/sparse/sparse_model.v *)

Definition subtract_loop_any  {NAN: FPCore.Nans}{t} [n] (c: ftype t) (R: 'M[ftype t]_n) (i j k: 'I_n) : ftype t -> Prop :=
  sum_any (c :: map (fun k' => BOPP (BMULT (R k' i) (R k' j))) (take k (ord_enum n))).

Definition cholesky_jik_ij_any  {NAN: FPCore.Nans}{t} [n: nat] (A R: 'M[ftype t]_n) (i j: 'I_n) : Prop :=
     ((i < j)%N -> exists x, subtract_loop_any (A i j) R i j i x /\ R i j = BDIV x (R i i))
   /\ (i=j -> exists x, subtract_loop_any (A i j) R i j i x /\ R i j = BSQRT x).

Module AlternatePresentations.
(* This module discusses other possible presentations of the subtract loop. *)

Section WithNaN.

Context {NAN: FPCore.Nans} {t : type}.

Definition subtract_loop_ffuns' [n: nat] (c: ftype t) (a b: (ftype t)^n) : ftype t :=
   foldl BMINUS c (map (uncurry BMULT) (zip (image a 'I_n) (image b 'I_n))).

Definition subtract_loop_ffuns [n: nat] (c: ftype t) (a b: (ftype t)^n) : ftype t :=
   foldl BMINUS c (map (fun k => BMULT (a k) (b k)) (ord_enum n)).

Remark subtract_loop_ffuns_ffuns' [n] c a b:
       @subtract_loop_ffuns n c a b = subtract_loop_ffuns' c a b.
Proof.
rewrite /subtract_loop_ffuns /subtract_loop_ffuns' /image_mem enum_mem_ordinal zip_map -map_comp //.
Qed.

Definition subtract_loop_alt [n] (c: ftype t) (R: 'M[ftype t]_n) (i j k: 'I_n) : ftype t :=
   subtract_loop_ffuns c [ffun k': 'I_k => R (widen_ik k') i] [ffun k': 'I_k => R (widen_ik k') j].

Definition subtract_loop_listpairs (c: ftype t) (l: seq (ftype t * ftype t)) :=
  foldl BMINUS c (map (uncurry BMULT) l).

Definition subtract_loop_original [n] (c: ftype t) (R: 'M[ftype t]_n) (i j k: 'I_n) : ftype t :=
  foldl BMINUS c (map (fun k' => BMULT (R k' i) (R k' j)) (take k (ord_enum n))).

Remark subtract_loop_jik_original [n] c R i j k:
   @subtract_loop_jik _ _ n c R i j k = @subtract_loop_original n c R i j k.
Proof.
rewrite /subtract_loop_jik /subtract_loop /subtract_loop_listpairs -map_comp //.
Qed.

Remark subtract_loop_alt_original  [n] c R i j k:
    @subtract_loop_alt n c R i j k = @subtract_loop_original n c R i j k.
Proof.
rewrite /subtract_loop_alt /subtract_loop_original /subtract_loop_ffuns take_ord_enum -map_comp.
f_equal.
apply eq_in_map => x _.
rewrite /comp !ffunE //.
Qed.
End WithNaN.

End AlternatePresentations.

(** Supporting lemmas for proving steps of the Cholesky "jik" algorithm *)

(* duplicates floatlib.zerof, so at least keep it local *)
Local Instance zerof {t} : Inhabitant (ftype t) := (Zconst t 0).

(* BEGIN copied from iterative_methods/cholesky/verif_cholesky.v *)

Lemma update_i_lt_j_aux: forall [n] [i j: 'I_n], (i<j)%N -> (i.+1<n)%N.
Proof.
 intros.
 pose proof (ltn_ord j).
 lia.
Qed.


Lemma in_take_ord_enum: forall [n] (i x: 'I_n), x \in (take i (ord_enum n)) -> (x<i)%N.
Proof.
intros.
assert (nat_of_ord x \in map (@nat_of_ord n) (take i (ord_enum n))).
apply map_f; auto.
rewrite map_take in H0.
rewrite val_ord_enum in H0.
rewrite take_iota in H0.
rewrite mem_iota in H0. lia.
Qed.

Lemma eq_in_subrange: 
  forall n T (i: 'I_n) (f f': 'I_n -> T),
    (forall (a: 'I_n), (a<i)%N -> f a = f' a) ->
      map f (take i (ord_enum n)) = map f' (take i (ord_enum n)).
Proof.
intros.
apply eq_in_map.
intros ? ?; auto.
apply H.
apply in_take_ord_enum; auto.
Qed.

Definition lshift1 [n: nat] (k: ordinal n) : ordinal (S n) 
 := Ordinal (ltn_trans (ltn_ord k) (leqnn (S n))).


Lemma update_i_lt_j:
  forall  {NAN: FPCore.Nans} {t} n (i j: 'I_n) (A R: 'M[ftype t]_n)
   (Hij: (i < j)%N)
   (i1: 'I_n)
   (Hi1: nat_of_ord i1 = S i),
   cholesky_jik_upto i (lshift1 j) A R ->
   let rij := BDIV (subtract_loop_jik (A i j) R i j i) (R i i) in
    @cholesky_jik_upto _ t n i1 (lshift1 j) A (update_mx R i j rij).
Proof.
intros * Hij i1 Hi1 H1 rij i' j'.
subst rij.
simpl.
split; [ | split3]; intros * H2.
-
specialize (H1 i' j').
destruct H1 as [H1 _]. specialize (H1 H2).
split; intros * H4.
+
destruct H1 as [H1 _]. specialize (H1 H4). 
unfold update_mx.
rewrite !mxE.
destruct (Nat.eq_dec j j'); [lia |].
destruct (Nat.eq_dec _ _); simpl.
* destruct (Nat.eq_dec _ _); [ lia | simpl].
  apply ord_inj in e; subst i.
  rewrite H1. f_equal.
  unfold subtract_loop_jik.
  f_equal.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE; simpl. 
  destruct (Nat.eq_dec _ _); auto; lia.
  destruct (Nat.eq_dec _ _); auto; lia.
* rewrite H1. f_equal.
  unfold subtract_loop_jik.
  f_equal.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE.
  repeat destruct (Nat.eq_dec _ _); try lia; auto.
+ destruct H1 as [_ H1].
  unfold update_mx. subst i'.
  rewrite !mxE.
  destruct (Nat.eq_dec _ _); try lia.
  *
  destruct (Nat.eq_dec _ _); try lia.
  specialize (H1 (Logic.eq_refl _)).
  rewrite H1. simpl. f_equal.
  unfold subtract_loop_jik.
  f_equal.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE.
  f_equal; repeat (destruct (Nat.eq_dec _ _); try lia); auto.
  *
  specialize (H1 (Logic.eq_refl _)).
  rewrite H1. simpl. f_equal.
  unfold subtract_loop_jik.
  f_equal.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE. simpl in H2.
  f_equal; repeat (destruct (Nat.eq_dec _ _); try lia); auto.
- red in H1|-*.
  apply ord_inj in H2.
  subst j'.
  simpl in *.
  intro H3.
  split; intros; [ | subst; lia].
  unfold update_mx. 
  rewrite !mxE.
  destruct (Nat.eq_dec j j); [simpl; clear e | lia].
  destruct (Nat.eq_dec j i'); try lia. simpl.
   replace (if proj_sumbool (Nat.eq_dec i i') then R i' i' else R i' i') 
      with (R i' i') by (destruct (Nat.eq_dec _ _); auto).
   destruct (Nat.eq_dec _ _); simpl.
  * assert (i' = i) by (apply ord_inj; auto). subst i'. clear e.
    clear n0 H3.
    f_equal.
  match goal with |- _ = _ _ ?ff _ _ _ => set (f:=ff) end.
  unfold subtract_loop_jik.
  f_equal.
  apply eq_in_subrange; intros a H3; simpl.
  subst f. rewrite !mxE.
  destruct (Nat.eq_dec _ _); try lia; auto.
  destruct (Nat.eq_dec _ _); try lia; auto.
  * assert (i'<i)%N by lia.  clear n1 H3 n0.
   specialize (H1 i' j). destruct H1 as [_ [H1 _]].
   destruct H1 as [H1 _]; auto; try lia.
   rewrite H1; auto.
   f_equal.
  unfold subtract_loop_jik.
  f_equal.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE.
  f_equal;
  repeat (destruct (Nat.eq_dec _ _)); try lia; auto.
- unfold update_mx. rewrite !mxE.
  specialize (H1 i' j').
  destruct H1 as [_ [_ [H1 _]]].
  repeat (destruct (Nat.eq_dec _ _)); try lia; auto.
- intros.
  specialize (H1 i' j'). destruct H1 as [_ [_ [_ H1]]].
  assert (j'=j) by (apply ord_inj; auto).
  subst. clear H2.
  unfold update_mx. rewrite !mxE.  
  repeat (destruct (Nat.eq_dec _ _)); try lia; auto.
  simpl. apply H1; auto. lia.
Qed.

Lemma length_ord_enum: forall n, length (ord_enum n) = n.
Proof.
intros.
pose proof val_ord_enum n.
simpl in H.
transitivity (length (iota 0 n)).
transitivity (length (map (nat_of_ord (n:=n)) (ord_enum n))).
rewrite length_map; auto.
f_equal; auto.
apply size_iota.
Qed.

Lemma size_ord_enum: forall n, size (ord_enum n) = n.
Proof. exact length_ord_enum. Qed.

Lemma nth_ord_enum': forall n (d i: 'I_n), nth d (ord_enum n) i = i.
Proof.
intros.
pose proof (val_ord_enum n).
simpl in H.
apply ord_inj.
pose proof ltn_ord i.
rewrite <- nth_map with (x2:=nat_of_ord d).
rewrite H. rewrite nth_iota. lia. lia.
rewrite size_ord_enum.
auto.
Qed.

Lemma take_snoc: forall {T} (d: T) (k: nat) (al: seq T), 
       (k<size al)%N -> 
       take k.+1 al = take k al ++ [nth d al k].
Proof.
intros.
revert k H; induction al; destruct k; simpl; intros; try lia.
rewrite take0. auto.
f_equal; auto.
Qed.

Lemma subtract_another:
  forall  {NAN: FPCore.Nans} {t} n (i j k: 'I_n) (A R: 'M[ftype t]_n)
    (Hij: (i <= j)%N) 
    (Hkj: (k < j)%N)
    (k1: 'I_n)
    (Hk1: nat_of_ord k1 = S k),
    subtract_loop_jik (A i j) R i j k1 = 
     BMINUS (subtract_loop_jik (A i j) R i j k) (BMULT (R k i) (R k j)).
Proof.
intros.
assert (Datatypes.is_true (leq (S (S (nat_of_ord k))) n)).
  pose proof ltn_ord k1; lia.
assert (k1 = @Ordinal n (S k) H). apply ord_inj; auto.
subst k1.
unfold subtract_loop_jik at 1.
rewrite (take_snoc i).
  2: (rewrite  size_ord_enum; pose proof ltn_ord k;  lia).
rewrite /subtract_loop !map_cat /= foldl_cat /= nth_ord_enum' //.
Qed.

(* END copied from iterative_methods/cholesky/verif_cholesky.v *)

Lemma cholesky_jik_upto_zero:
  forall  {NAN: FPCore.Nans}  t n (A: 'M[ftype t]_n) (zero: 'I_n), nat_of_ord zero=O -> cholesky_jik_upto zero (lshift1 zero) A A.
Proof.
intros i j; split; [ | split3]; simpl; try lia; auto.
Qed.

Lemma cholesky_jik_upto_newrow:
 forall  {NAN: FPCore.Nans} t n (j: 'I_n) (A R: 'M[ftype t]_n),
  cholesky_jik_upto j (lshift1 j) A R ->
  cholesky_jik_upto (@Ordinal n 0 (leq_ltn_trans (leq0n j) (ltn_ord j)))
     (@Ordinal n.+1 (j.+1)%N (ltn_ord j)) A (update_mx R j j (BSQRT (subtract_loop_jik (A j j) R j j j))).
Proof.
pose proof I.
intros.
intros i' j'.
destruct (H0 i' j') as [? [? [? ?]]]; clear H0.
split; [ | split3]; intros; try split; hnf; intros; try lia.
-
 clear H4. simpl in H0.
 destruct (Nat.eq_dec j' j).
 + apply ord_inj in e. subst j'. clear H1 H3. specialize (H2 (Logic.eq_refl _) Hij).
   unfold update_mx at 1. rewrite mxE.
   destruct (Nat.eq_dec _ _); [lia  |]. simpl.
   destruct H2.
   rewrite H1; [ |apply Hij]. f_equal.
   * unfold subtract_loop_jik. f_equal.
     apply eq_in_subrange.
     intros. unfold update_mx. rewrite !mxE.
     repeat (destruct (Nat.eq_dec _ _)); try lia. auto.
   * unfold update_mx. rewrite !mxE.
     repeat (destruct (Nat.eq_dec _ _)); try lia. auto.
 + simpl in *. destruct (H1 ltac:(lia)); clear H1 H5. specialize (H4 ltac:(lia)). clear H2 H3.
   unfold update_mx at 1. rewrite mxE.
   repeat destruct (Nat.eq_dec _ _); try lia. simpl.
   rewrite H4. f_equal.
   * unfold subtract_loop_jik. f_equal.
     apply eq_in_subrange.
     intros. unfold update_mx. rewrite !mxE.
     repeat destruct (Nat.eq_dec _ _); try lia; auto.
   * unfold update_mx. rewrite mxE.
     repeat destruct (Nat.eq_dec _ _); try lia; auto.
- subst j'. simpl in *.
  destruct (Nat.eq_dec i' j).
 + apply ord_inj in e. subst. unfold update_mx. rewrite !mxE.
   repeat destruct (Nat.eq_dec _ _); try lia; auto. simpl.
   f_equal.
   unfold subtract_loop_jik. f_equal.
   apply eq_in_subrange.
   intros. rewrite !mxE.
   repeat destruct (Nat.eq_dec _ _); try lia; auto. 
 + unfold update_mx at 1. rewrite mxE.
   repeat destruct (Nat.eq_dec _ _); try lia; auto. 
   simpl.
   destruct (H1 ltac:(lia)). rewrite H6; auto.
   f_equal.
   unfold subtract_loop_jik. f_equal.
   apply eq_in_subrange.
   intros. unfold update_mx. rewrite !mxE.
   repeat destruct (Nat.eq_dec _ _); try lia; auto.
- simpl in *; lia. 
- simpl in *. lia.
- unfold update_mx. rewrite !mxE. simpl in *.
   repeat destruct (Nat.eq_dec _ _); try lia; auto.
- unfold update_mx. rewrite !mxE. simpl in *. clear H5.
  repeat destruct (Nat.eq_dec _ _); try lia; apply H3; lia.
Qed.

(** * Definitions for manipulating triangular matrices *)

(** [joinLU n L U]   produces a matrix whose upper-triangle (including diagonal) matches U,
         and whose lower_triangle (excluding diagonal) matches L *)
Definition joinLU {T} [n] (L U : 'M[T]_n) : 'M[T]_n :=
 \matrix_(i,j) if (i<=j)%N then U i j else L i j.

Definition mirror_UT {T} [n] (U: 'M[T]_n) : 'M[T]_n :=
  joinLU U^T U.
(*
Inductive block_cholesky {t: type}: forall (n: Z) (A R: Z -> Z -> ftype t), Prop :=
| Block_cholesky_1: forall A R, A 0 0 = BSQRT(R 0 0) -> block_cholesky 1 A R
| Block_cholesky_plus: forall n1 n2 A R,
   block_cholesky n1 A R ->
   blocksolve A n b c B
*)
