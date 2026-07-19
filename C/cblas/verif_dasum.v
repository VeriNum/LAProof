(**  * LAProof.C.cblas.verif_dasum: VST proof for GSL's [cblas_dasum]. *)
(** ** Corresponds to C program [C/cblas/src/dasum.c]. *)

(** [body_cblas_dasum] proves that the compiled C [cblas_dasum] (unit stride)
    returns a value [feq]-equal to [sumF (map BABS X)].  Its invariant uses
    [asum_model] on the length-[k] prefix; supporting lemmas are in
    [LAProof.C.cblas.asum_model]. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math.
From LAProof.C Require Import floatlib.
From LAProof.C.cblas Require Import dasum asum_model spec_dasum.
Require Import LAProof.accuracy_proofs.sum_model.

Set Bullet Behavior "Strict Subproofs".

Lemma body_cblas_dasum: semax_body Vprog Gprog f_cblas_dasum cblas_dasum_spec.
Proof.
start_function.
forward.
forward.
forward_if.
{ rep_lia. }
(* [_r] models the first [k] elements; unit stride makes [_ix = k]. *)
forward_for_simple_bound (Zlength X)
  (EX k:Z,
    PROP ()
    LOCAL (temp _r (Vfloat (asum_model (sublist 0 k X)));
           temp _ix (Vint (Int.repr k));
           temp _N (Vint (Int.repr (Zlength X)));
           temp _incX (Vint (Int.repr 1));
           temp _X px)
    SEP (data_at shX (tarray tdouble (Zlength X)) (map Vfloat X) px))%assert.
-
  entailer!!.
-
  forward.
  forward_call (Znth i X).
  forward.
  forward.
  entailer!!.
  rewrite (asum_model_step X i) by list_solve.
  reflexivity.
-
  forward.
  Exists (asum_model (sublist 0 (Zlength X) X)).
  entailer!!.
  rewrite sublist_same by lia.
  apply asum_model_feq_sumF.
Qed.

(** Conditional accuracy payoff: the result is [feq]-equal to
    [sumF (map BABS X)].  After additionally establishing that this model result
    is finite (the accuracy theorem's [Hfin] hypothesis), one can transfer
    [LAProof.accuracy_proofs.sum_acc.fSUM], applied to [map BABS X], to the value
    computed by the compiled C [cblas_dasum].  That composition is not stated as
    a checked theorem here; see [C/cblas/README.md]. *)
