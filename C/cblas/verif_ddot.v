(**  * LAProof.C.cblas.verif_ddot: VST proof for GSL's [cblas_ddot]. *)
(** ** Corresponds to C program [C/cblas/src/ddot.c]. *)

(** [body_cblas_ddot] proves the accumulation over the logical vectors selected
    by arbitrary signed strides, including zero.  The reduction models
    [ddot_model] and [dotprodF] are unchanged. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From LAProof.C Require Import floatlib.
From LAProof.C.cblas Require Import ddot stride_model ddot_model spec_ddot.
Require Import LAProof.accuracy_proofs.dotprod_model.

Set Bullet Behavior "Strict Subproofs".

Lemma body_cblas_ddot: semax_body Vprog Gprog f_cblas_ddot cblas_ddot_spec.
Proof.
start_function.
destruct H4 as (HincX & HnegX & HoffX & HidxX & HstepX).
destruct H5 as (HincY & HnegY & HoffY & HidxY & HstepY).
set (sx := blas_offset N incX).
set (sy := blas_offset N incY).
forward.
forward_if (PROP ()
  LOCAL (temp _t'1 (Vint (Int.repr sx));
         temp _r (Vfloat (Float.of_bits (Int64.repr 0)));
         temp _N (Vint (Int.repr N)); temp _X px;
         temp _incX (Vint (Int.repr incX)); temp _Y py;
         temp _incY (Vint (Int.repr incY)))
  SEP (data_at shX (tarray tdouble nX) (map Vfloat X) px;
       data_at shY (tarray tdouble nY) (map Vfloat Y) py)).
{ forward. entailer!!.
  subst sx. unfold blas_offset.
  destruct (0 <? incX) eqn:Hlt; [reflexivity |].
  apply Z.ltb_ge in Hlt; lia. }
{ assert (Hincmin: Int.min_signed < incX) by (apply HnegX; lia).
  assert (Hminus: Int.min_signed <= -incX <= Int.max_signed) by rep_lia.
  assert (Hprod: Int.min_signed <= (N-1)*(-incX) <= Int.max_signed).
  { subst sx. unfold blas_offset in HoffX.
    destruct (0 <? incX) eqn:Hlt.
    - apply Z.ltb_lt in Hlt; lia.
    - exact HoffX. }
  forward. entailer!!.
  subst sx. unfold blas_offset.
  destruct (0 <? incX) eqn:Hlt.
  - apply Z.ltb_lt in Hlt; lia.
  - reflexivity. }
forward.
forward_if (PROP ()
  LOCAL (temp _t'2 (Vint (Int.repr sy));
         temp _ix (Vint (Int.repr sx));
         temp _r (Vfloat (Float.of_bits (Int64.repr 0)));
         temp _N (Vint (Int.repr N)); temp _X px;
         temp _incX (Vint (Int.repr incX)); temp _Y py;
         temp _incY (Vint (Int.repr incY)))
  SEP (data_at shX (tarray tdouble nX) (map Vfloat X) px;
       data_at shY (tarray tdouble nY) (map Vfloat Y) py)).
{ forward. entailer!!.
  subst sy. unfold blas_offset.
  destruct (0 <? incY) eqn:Hlt; [reflexivity |].
  apply Z.ltb_ge in Hlt; lia. }
{ assert (Hincmin: Int.min_signed < incY) by (apply HnegY; lia).
  assert (Hminus: Int.min_signed <= -incY <= Int.max_signed) by rep_lia.
  assert (Hprod: Int.min_signed <= (N-1)*(-incY) <= Int.max_signed).
  { subst sy. unfold blas_offset in HoffY.
    destruct (0 <? incY) eqn:Hlt.
    - apply Z.ltb_lt in Hlt; lia.
    - exact HoffY. }
  forward. entailer!!.
  subst sy. unfold blas_offset.
  destruct (0 <? incY) eqn:Hlt.
  - apply Z.ltb_lt in Hlt; lia.
  - reflexivity. }
forward.
(* [_r] models the first [k] selected pairs. *)
forward_for_simple_bound N
  (EX k:Z,
    PROP ()
    LOCAL (temp _r (Vfloat
             (ddot_model (strided_from sx incX k X)
                         (strided_from sy incY k Y)));
           temp _ix (Vint (Int.repr (sx + k*incX)));
           temp _iy (Vint (Int.repr (sy + k*incY)));
           temp _N (Vint (Int.repr N));
           temp _incX (Vint (Int.repr incX));
           temp _incY (Vint (Int.repr incY));
           temp _X px; temp _Y py)
    SEP (data_at shX (tarray tdouble nX) (map Vfloat X) px;
         data_at shY (tarray tdouble nY) (map Vfloat Y) py))%assert.
-
  entailer!!.
-
  assert (Hix: 0 <= sx + i*incX < nX)
    by (subst sx; apply HidxX; lia).
  assert (Hiy: 0 <= sy + i*incY < nY)
    by (subst sy; apply HidxY; lia).
  forward.
  forward.
  forward.
  assert (Hsx: Int.min_signed <= sx + i*incX + incX <= Int.max_signed)
    by (subst sx; apply HstepX; lia).
  assert (Hsy: Int.min_signed <= sy + i*incY + incY <= Int.max_signed)
    by (subst sy; apply HstepY; lia).
  forward.
  forward.
  entailer!.
  rewrite !strided_from_snoc by lia.
  rewrite ddot_model_snoc.
  + repeat split; do 2 f_equal; ring.
  + apply Nat2Z.inj. rewrite <- !Zlength_correct.
    rewrite !Zlength_strided_from by lia. reflexivity.
-
  forward.
  Exists (ddot_model (strided_from sx incX N X) (strided_from sy incY N Y)).
  entailer!.
  unfold blas_strided. fold sx sy.
  apply ddot_model_feq_dotprodF.
  rewrite !Zlength_strided_from by lia. reflexivity.
Qed.

(** Conditional accuracy payoff: the result is [feq]-equal to [dotprodF]
    applied to the two logical strided vectors.  After additionally establishing
    that this model result is finite, one can transfer
    [LAProof.accuracy_proofs.dot_acc.dotprod_forward_error] to the value computed
    by the compiled C [cblas_ddot].  That composition is not stated as a checked
    theorem here. *)
