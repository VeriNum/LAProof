(**  * LAProof.C.cblas.verif_dscal: VST proof for GSL's [cblas_dscal]. *)
(** ** Corresponds to C program [C/cblas/src/dscal.c]. *)

(** [body_cblas_dscal] proves that after the compiled C [cblas_dscal] (unit
    stride) the array holds exactly [scal_model alpha X] (= [map (fun x => BMULT
    x alpha) X]).  This is an in-place routine: a writable array with a store in
    the loop, whose invariant is "scaled prefix ++ original suffix"; the per-step
    [upd_Znth]/[sublist] identity is discharged by [list_solve]. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From LAProof.C Require Import floatlib.
From LAProof.C.cblas Require Import dscal scal_model spec_dscal.

Set Bullet Behavior "Strict Subproofs".

Lemma body_cblas_dscal: semax_body Vprog Gprog f_cblas_dscal cblas_dscal_spec.
Proof.
start_function.
forward.                       (* ix = 0 *)
forward_if.
{ rep_lia. }                   (* dead: incX <= 0 contradicts incX = 1 *)
(* Invariant: the array holds a list [L] of length [Zlength X] whose first [k]
   entries are already scaled ([Znth j X * alpha]) and whose remaining entries
   are still the original [X].  Keeping the contents as [map Vfloat L] for a
   *plain* list [L] lets the load and store simplify; the pointwise [Znth]
   constraints make each step a simple [upd_Znth_same]/[upd_Znth_diff] case. *)
forward_for_simple_bound (Zlength X)
  (EX k:Z, EX L:list (ftype Tdouble),
    PROP (Zlength L = Zlength X;
          forall j, 0 <= j < k -> Znth j L = (Znth j X * alpha)%F64;
          forall j, k <= j < Zlength X -> Znth j L = Znth j X)
    LOCAL (temp _alpha (Vfloat alpha);
           temp _ix (Vint (Int.repr k));
           temp _N (Vint (Int.repr (Zlength X)));
           temp _incX (Vint (Int.repr 1));
           temp _X px)
    SEP (data_at sh (tarray tdouble (Zlength X)) (map Vfloat L) px))%assert.
- (* entry (k = 0): L := X *)
  Exists X. entailer!!.
- (* body: t = X[ix]; X[ix] = t * alpha; ix += incX *)
  Intros.
  (* Re-assert the invariant facts under explicit names so they survive the
     [forward]s (which clear the auto-named PROP hypotheses). *)
  assert (Hlen: Zlength L = Zlength X) by assumption.
  assert (Hpre: forall j, 0 <= j < i -> Znth j L = (Znth j X * alpha)%F64) by assumption.
  assert (Hsuf: forall j, i <= j < Zlength X -> Znth j L = Znth j X) by assumption.
  assert (Hi: 0 <= i < Zlength L) by lia.
  assert (HLX: Znth i L = Znth i X) by (apply Hsuf; lia).
  forward.                     (* t'1 = X[ix] *)
  forward.                     (* X[ix] = t'1 * alpha *)
  forward.                     (* ix += incX *)
  Exists (upd_Znth i L (BMULT (Znth i X) alpha)).
  entailer!!.
  2: { (* SEP: the stored value [X[i]*alpha] is the model element [BMULT .. alpha] *)
       apply derives_refl'. f_equal. rewrite <- upd_Znth_map. f_equal.
       rewrite ?Znth_map by lia.
       replace (@Znth float Inhabitant_float i L)
          with (@Znth float Inhabitant_float i X) by (symmetry; apply HLX).
       reflexivity. }
  (* the three pointwise list invariants for the updated list *)
  split3.
  { list_solve. }
  { intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
    { rewrite upd_Znth_same by lia. reflexivity. }
    { rewrite upd_Znth_diff by lia. apply Hpre; lia. } }
  { intros j Hj. rewrite upd_Znth_diff by lia. apply Hsuf; lia. }
- (* exit (k = Zlength X): the whole array now holds [scal_model alpha X] *)
  Intros L.
  assert (Hpre: forall j, 0 <= j < Zlength X -> Znth j L = (Znth j X * alpha)%F64)
    by assumption.
  assert (Hlen: Zlength L = Zlength X) by assumption.
  assert (L = scal_model alpha X). {
    apply Znth_eq_ext; [ rewrite Zlength_scal_model; lia | ].
    intros j Hj. rewrite Hlen in Hj.
    rewrite Znth_scal_model by lia. rewrite Hpre by lia. reflexivity. }
  subst L. entailer!!.
Qed.

(** Payoff: each element [BMULT (Znth k X) alpha] is the correctly-rounded
    product, so when that product is finite its relative error vs the exact
    product is bounded by the unit roundoff (vcfloat's [BMULT] accuracy lemma).
    A product can still overflow, but the finiteness (no-overflow) requirement is
    per element -- each [X[k]*alpha] independently -- rather than a single global
    hypothesis over an accumulation. *)
