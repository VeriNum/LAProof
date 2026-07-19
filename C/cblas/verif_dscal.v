(**  * LAProof.C.cblas.verif_dscal: VST proof for GSL's [cblas_dscal]. *)
(** ** Corresponds to C program [C/cblas/src/dscal.c]. *)

(** [body_cblas_dscal] proves that after the compiled C [cblas_dscal] (general
    positive stride [incX > 0]) the array holds exactly [scal_strided incX N
    alpha X].  The invariant tracks that model after [i] stores with
    [_ix = i*incX]; [Znth_scal_strided_self] shows that the next position still
    contains its original value. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From LAProof.C Require Import floatlib.
From LAProof.C.cblas Require Import dscal scal_model spec_dscal.

Set Bullet Behavior "Strict Subproofs".

Lemma body_cblas_dscal: semax_body Vprog Gprog f_cblas_dscal cblas_dscal_spec.
Proof.
start_function.
forward.
forward_if.
{ rep_lia. }
(* [L] contains the [k] completed updates and [_ix = k*incX]. *)
forward_for_simple_bound N
  (EX k:Z, EX L:list (ftype Tdouble),
    PROP (L = scal_strided incX k alpha X; Zlength L = n)
    LOCAL (temp _alpha (Vfloat alpha);
           temp _ix (Vint (Int.repr (k*incX)));
           temp _N (Vint (Int.repr N));
           temp _incX (Vint (Int.repr incX));
           temp _X px)
    SEP (data_at sh (tarray tdouble n) (map Vfloat L) px))%assert.
-
  Exists X. rewrite scal_strided_0. entailer!!.
-
  Intros.
  assert (HL: L = scal_strided incX i alpha X) by assumption.
  assert (Hlen: Zlength L = n) by assumption.
  assert (Hib: 0 <= i*incX < n) by nia.
  assert (Hself: Znth (i*incX) L = Znth (i*incX) X)
    by (rewrite HL; apply Znth_scal_strided_self; [ lia | lia | lia ]).
  forward.
  forward.
  (* Bound the signed addition used to advance [_ix]. *)
  assert (Hov: 0 <= i*incX + incX <= Int.max_signed) by nia.
  forward.
  Exists (upd_Znth (i*incX) L (BMULT (Znth (i*incX) L) alpha)).
  entailer!!.
  2: {
       assert (Hib': 0 <= i*incX < Zlength (scal_strided incX i alpha X))
         by (rewrite Hlen; exact Hib).
       apply derives_refl'. f_equal. rewrite <- upd_Znth_map. f_equal.
       rewrite Znth_map by exact Hib'. reflexivity. }
  split.
  +
    rewrite scal_strided_snoc by lia. f_equal. rewrite Hself. reflexivity.
  +
    split.
    * rewrite upd_Znth_Zlength by (rewrite Hlen; exact Hib). exact Hlen.
    * do 2 f_equal. ring.
-
  Intros L.
  assert (HL: L = scal_strided incX N alpha X) by assumption.
  subst L. entailer!!.
Qed.

(** Payoff: each element [BMULT (Znth k X) alpha] is the correctly-rounded
    product, so when that product is finite its relative error vs the exact
    product is bounded by the unit roundoff (vcfloat's [BMULT] accuracy lemma).
    A product can still overflow, but the finiteness (no-overflow) requirement is
    per element -- each [X[k]*alpha] independently -- rather than a single global
    hypothesis over an accumulation. *)
