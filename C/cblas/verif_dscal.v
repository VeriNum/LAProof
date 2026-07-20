(**  * LAProof.C.cblas.verif_dscal: VST proof for GSL's [cblas_dscal]. *)
(** ** Corresponds to C program [C/cblas/src/dscal.c]. *)

(** [body_cblas_dscal] proves the positive-stride updates described by
    [scal_strided] and the kernel's unchanged-array result for [incX <= 0]. *)

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
{ forward. entailer!!.
  destruct (Z.leb incX 0) eqn:Hle.
  - cancel.
  - apply Z.leb_gt in Hle; lia. }
{ assert (Hinc: 0 < incX) by rep_lia.
  assert (Hbounds: (N-1)*incX < n /\ N*incX <= Int.max_signed)
    by (destruct H3 as [Hnonpos | [_ Hbounds]]; [lia | exact Hbounds]).
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
  destruct (Z.leb incX 0) eqn:Hle.
  + apply Z.leb_le in Hle; lia.
  + cancel. }
Qed.

(** In the positive-stride branch, each updated element is a correctly rounded
    [BMULT].  Its relative-error bound requires that product to be finite; this
    is a per-element condition rather than a global accumulation hypothesis. *)
