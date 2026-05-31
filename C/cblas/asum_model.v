(**  * LAProof.C.cblas.asum_model: functional model of GSL's [cblas_dasum]. *)
(** ** Corresponds to C program [C/cblas/src/dasum.c] (ported from GSL cblas). *)

(** This file provides [asum_model], the partial accumulation that the
    [cblas_dasum] loop invariant tracks, with the *step* lemma (how one loop
    iteration extends the accumulation) and the *end* lemma (the result of the
    accumulation once the loop finishes).  GSL's kernel ([source_asum_r.h]) is
<<
      double r = 0.0;
      for (i = 0; i < N; i++) { r += fabs(X[ix]); ix += incX; }
      return r;
>>
    i.e., it adds [|X[i]|] left to right into the accumulator ([BPLUS acc |x|]),
    starting from [+0.0].  The C [fabs] computes [BABS] (the result of VSTlib's
    [fabs_spec], whose [ff_func] is [BABS]), so the model uses [BABS].

    The matching LAProof accuracy model is [sum_model.sumF] applied to
    [map BABS X] (the absolute values); over it [sum_acc.fSUM] proves the
    forward-error bound.  The C's operand order ([BPLUS acc x]
    vs [sumF]'s [BPLUS x acc]) and initial accumulator ([+0.0] = [Zconst Tdouble 0]
    vs [sumF]'s [neg_zero]) differ, so the end/bridge lemma relates the two by
    [feq] (IEEE-equality identifying [±0]/NaN). *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPStdCompCert.
From vcfloat Require Import FPStdLib.
From LAProof.C Require Import floatlib.
(* [sum_model] only [Require Import]s (not [Export]s) the mathcomp preamble, so
   this does not pollute the VST namespace with ssreflect notations.  We do NOT
   [Import common] (it would re-scope [<=]/[<] over [R]); [common.BPLUS_comm] /
   [common.neg_zero] are used qualified.  [BPLUS_mor], [BABS], the [feq]
   [Equivalence] come from vcfloat. *)
Require Import LAProof.accuracy_proofs.sum_model.

Set Bullet Behavior "Strict Subproofs".

(** [asum_model X] is the value the C loop *literally* computes: a left fold with
    the accumulator as the first [BPLUS] operand, separate abs-then-add, starting
    from [+0.0].  This mirrors the Clight AST in [dasum.v] exactly. *)
Definition asum_loop (l: list (ftype Tdouble)) : ftype Tdouble :=
  fold_left (fun acc x => BPLUS acc (BABS x)) l (Zconst Tdouble 0).

Definition asum_model (X: list (ftype Tdouble)) : ftype Tdouble := asum_loop X.

(** ** Model lemmas (the [partial_row_*] triple, specialised to a dense asum). *)

Lemma asum_loop_snoc: forall l x,
  asum_loop (l ++ [x]) = BPLUS (asum_loop l) (BABS x).
Proof. intros. unfold asum_loop. rewrite fold_left_app. reflexivity. Qed.

(** *step*: extending the length-[k] prefix [X[0..k-1]] with the element [X[k]]
    adds one [BABS] term, with the accumulator as the first [BPLUS] operand --
    exactly the Clight statement [r = r + fabs(X[k])]. *)
Lemma asum_model_step: forall (X: list (ftype Tdouble)) k,
  0 <= k < Zlength X ->
  asum_model (sublist 0 (k+1) X)
  = BPLUS (asum_model (sublist 0 k X)) (BABS (Znth k X)).
Proof.
  intros X k Hk. unfold asum_model.
  rewrite (sublist_last_1 0 k X) by lia.
  rewrite asum_loop_snoc. reflexivity.
Qed.

(** *end*/bridge: the finished accumulation equals LAProof's summation model
    [sumF (map BABS X)] up to [feq].  Generalized-accumulator induction using
    [common.BPLUS_comm] and [BPLUS_mor], with the [feq (+0.0) (-0.0)] base case
    ([sumF] starts at [neg_zero]). *)
Lemma asum_model_feq_sumF: forall (X: list (ftype Tdouble)),
  feq (asum_model X) (sumF (map BABS X)).
Proof.
  intros X. unfold asum_model, asum_loop, sumF.
  assert (Hs: feq (Zconst Tdouble 0) (@common.neg_zero Tdouble)) by reflexivity.
  revert Hs.
  generalize (Zconst Tdouble 0).
  generalize (@common.neg_zero Tdouble).
  induction X as [|x X IH]; intros g f Hs.
  - (* X = nil: both folds are the (feq-linked) initial accumulators. *)
    simpl. exact Hs.
  - simpl. apply IH.
    unfold Basics.flip.
    etransitivity; [ apply common.BPLUS_comm | apply BPLUS_mor; [ reflexivity | exact Hs ] ].
Qed.
