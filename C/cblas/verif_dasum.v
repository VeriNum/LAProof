(**  * LAProof.C.cblas.verif_dasum: VST proof for GSL's [cblas_dasum]. *)
(** ** Corresponds to C program [C/cblas/src/dasum.c]. *)

(** [body_cblas_dasum] proves that the compiled C [cblas_dasum] (unit stride)
    refines LAProof's summation model: its result is [feq]-equal to
    [sumF (map BABS X)].  Sibling of [verif_ddot]; the loop invariant carries the
    partial accumulation [asum_model (sublist 0 k X)], with the per-step / start /
    bridge reasoning in [LAProof.C.cblas.asum_model].  The only structural
    additions over [ddot] are an [fabs] [forward_call] in the loop body and the
    dead [if (incX<=0) return 0;] guard (unreachable since [incX = 1]). *)

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
forward.                       (* r = 0.0 *)
forward.                       (* ix = 0 *)
(* if (incX <= 0) return 0;  -- dead, incX = 1 *)
forward_if.
{ rep_lia. }                   (* then-branch: incX <= 0 contradicts incX = 1 *)
(* accumulation loop *)
forward_for_simple_bound (Zlength X)
  (EX k:Z,
    PROP ()
    LOCAL (temp _r (Vfloat (asum_model (sublist 0 k X)));
           temp _ix (Vint (Int.repr k));
           temp _N (Vint (Int.repr (Zlength X)));
           temp _incX (Vint (Int.repr 1));
           temp _X px)
    SEP (data_at shX (tarray tdouble (Zlength X)) (map Vfloat X) px))%assert.
- (* entry (k = 0): asum_model nil = +0.0 *)
  entailer!!.
- (* body: t = X[ix]; r += fabs(t); ix += incX *)
  forward.                     (* t'2 = X[ix] *)
  forward_call (Znth i X).     (* t'1 = fabs(X[i]) = BABS (Znth i X) *)
  forward.                     (* r = r + t'1 *)
  forward.                     (* ix = ix + incX *)
  entailer!!.
  rewrite (asum_model_step X i) by list_solve.
  reflexivity.
- (* exit (k = Zlength X): return r = asum_model X *)
  forward.                     (* return r *)
  Exists (asum_model (sublist 0 (Zlength X) X)).
  entailer!!.
  rewrite sublist_same by lia.
  apply asum_model_feq_sumF.
Qed.

(** Payoff (stub): because the result is [feq]-equal to [sumF (map BABS X)], the
    forward-error bound [LAProof.accuracy_proofs.sum_acc.fSUM] (applied to the
    list [map BABS X]) bounds the C result's error whenever that result is finite
    (the no-overflow hypothesis [Hfin]; see [C/cblas/README.md]). *)
