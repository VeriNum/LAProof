(**  * LAProof.C.cblas.verif_dscal: VST proof for GSL's [cblas_dscal]. *)
(** ** Corresponds to C program [C/cblas/src/dscal.c]. *)

(** [body_cblas_dscal] proves that after the compiled C [cblas_dscal] (general
    positive stride [incX > 0]) the array holds exactly [scal_strided incX N
    alpha X].  This is an in-place routine: a writable array with a store in the
    loop.  The loop counter [_i] runs [0..N) while the address [_ix] advances by
    [incX] (so [_ix = i*incX]); the invariant carries [scal_strided incX i alpha
    X] directly, and each store step is one [scal_strided_snoc].  The value read
    at [X[ix]] is the *original* entry because position [i*incX] has not been
    written yet ([Znth_scal_strided_self]). *)

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
{ (* dead: the [incX <= 0] guard contradicts [0 < incX] *) rep_lia. }
(* Invariant: the array holds [scal_strided incX k alpha X] (the [k] strided
   positions already scaled, all others untouched).  The address [_ix] tracks
   [k*incX].  Carrying the model directly makes each store step exactly
   [scal_strided_snoc]. *)
forward_for_simple_bound N
  (EX k:Z, EX L:list (ftype Tdouble),
    PROP (L = scal_strided incX k alpha X; Zlength L = n)
    LOCAL (temp _alpha (Vfloat alpha);
           temp _ix (Vint (Int.repr (k*incX)));
           temp _N (Vint (Int.repr N));
           temp _incX (Vint (Int.repr incX));
           temp _X px)
    SEP (data_at sh (tarray tdouble n) (map Vfloat L) px))%assert.
- (* entry (k = 0): [L := X = scal_strided incX 0 alpha X], [_ix = 0*incX = 0] *)
  Exists X. rewrite scal_strided_0. entailer!!.
- (* body (counter [i], 0 <= i < N): t = X[ix]; X[ix] = t*alpha; ix += incX *)
  Intros.
  assert (HL: L = scal_strided incX i alpha X) by assumption.
  assert (Hlen: Zlength L = n) by assumption.
  assert (Hib: 0 <= i*incX < n) by nia.
  assert (Hself: Znth (i*incX) L = Znth (i*incX) X)
    by (rewrite HL; apply Znth_scal_strided_self; [ lia | lia | lia ]).
  forward.                     (* t'1 = X[ix] *)
  forward.                     (* X[ix] = t'1 * alpha *)
  (* [ix + incX] is signed [int] addition; supply the no-overflow bound
     [(i+1)*incX <= N*incX <= Int.max_signed] for [forward]'s tc solver. *)
  assert (Hov: 0 <= i*incX + incX <= Int.max_signed) by nia.
  forward.                     (* ix = ix + incX *)
  Exists (upd_Znth (i*incX) L (BMULT (Znth (i*incX) L) alpha)).
  entailer!!.
  2: { (* SEP: the stored value [X[ix]*alpha] is the model element [BMULT .. alpha] *)
       assert (Hib': 0 <= i*incX < Zlength (scal_strided incX i alpha X))
         by (rewrite Hlen; exact Hib).
       apply derives_refl'. f_equal. rewrite <- upd_Znth_map. f_equal.
       rewrite Znth_map by exact Hib'. reflexivity. }
  split.
  + (* the updated list is [scal_strided incX (i+1) alpha X] *)
    rewrite scal_strided_snoc by lia. f_equal. rewrite Hself. reflexivity.
  + (* Zlength preserved, and [_ix = (i+1)*incX = i*incX + incX] *)
    split.
    * rewrite upd_Znth_Zlength by (rewrite Hlen; exact Hib). exact Hlen.
    * do 2 f_equal. ring.
- (* exit (k = N): the whole array now holds [scal_strided incX N alpha X] *)
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
