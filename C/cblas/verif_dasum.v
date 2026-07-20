(**  * LAProof.C.cblas.verif_dasum: VST proof for GSL's [cblas_dasum]. *)
(** ** Corresponds to C program [C/cblas/src/dasum.c]. *)

(** [body_cblas_dasum] proves the positive-stride accumulation over
    [strided incX N X] and the kernel's early return for [incX <= 0].  The
    reduction models [asum_model] and [sumF] are unchanged. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math.
From LAProof.C Require Import floatlib.
From LAProof.C.cblas Require Import dasum scal_model asum_model spec_dasum.
Require Import LAProof.accuracy_proofs.sum_model.

Set Bullet Behavior "Strict Subproofs".

Lemma body_cblas_dasum: semax_body Vprog Gprog f_cblas_dasum cblas_dasum_spec.
Proof.
start_function.
forward.
forward.
forward_if.
{ forward.
  Exists (Zconst Tdouble 0).
  entailer!!.
  destruct (Z.leb incX 0) eqn:Hle; [reflexivity |].
  apply Z.leb_gt in Hle; lia. }
{ assert (Hinc: 0 < incX) by rep_lia.
  assert (Hbounds: (N-1)*incX < n /\ N*incX <= Int.max_signed)
    by (destruct H3 as [Hnonpos | [_ Hbounds]]; [lia | exact Hbounds]).
  (* [_r] models the first [k] selected elements and [_ix = k*incX]. *)
  forward_for_simple_bound N
  (EX k:Z,
    PROP ()
    LOCAL (temp _r (Vfloat (asum_model (strided incX k X)));
           temp _ix (Vint (Int.repr (k*incX)));
           temp _N (Vint (Int.repr N));
           temp _incX (Vint (Int.repr incX));
           temp _X px)
    SEP (data_at shX (tarray tdouble n) (map Vfloat X) px))%assert.
-
  entailer!!.
-
  assert (Hib: 0 <= i*incX < n) by nia.
  forward.
  forward_call (Znth (i*incX) X).
  + entailer!!.
  + forward.
    assert (Hov: 0 <= i*incX + incX <= Int.max_signed) by nia.
    forward.
    entailer!!.
    rewrite strided_snoc by lia.
    rewrite asum_loop_snoc.
    split.
    * reflexivity.
    * do 2 f_equal. ring.
-
  forward.
  Exists (asum_model (strided incX N X)).
  entailer!!.
  destruct (Z.leb incX 0) eqn:Hle.
  + apply Z.leb_le in Hle; lia.
  + apply asum_model_feq_sumF. }
Qed.

(** For [incX > 0], the conditional accuracy payoff applies [fSUM] to
    [map BABS (strided incX N X)] after establishing that its sum is finite.
    The composition is not stated as a checked theorem here. *)
