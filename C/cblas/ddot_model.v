(**  * LAProof.C.cblas.ddot_model: functional model of GSL's [cblas_ddot]. *)
(** ** Corresponds to C program [C/cblas/src/ddot.c] (ported from GSL cblas). *)

(** This file plays the same role for [cblas_ddot] that [LAProof.C.sparse_model]
    plays for the sparse routines: it defines the partial-accumulation *model
    function* the loop invariant tracks, together with the *start* / *step* /
    *end* lemmas about it (cf. [partial_row]/[partial_row_start]/
    [partial_row_next]/[partial_row_end]).  No VST [funspec]s or Clight ASTs
    appear here -- those live in [spec_ddot] and [verif_ddot].

    GSL's loop (after macro expansion of [source_dot_r.h]) is
<<
      double r = 0.0;
      for (i = 0; i < N; i++) { r += X[ix] * Y[iy]; ix += incX; iy += incY; }
      return r;
>>
    i.e. a forward, left-to-right accumulation using *separate* multiply-then-add
    (not fused multiply-add), starting from +0.0.  That is exactly the [dotprodF]
    model of [LAProof.accuracy_proofs.dotprod_model]
    ([dotprodF = dotprod BMULT BPLUS pos_zero]), over which the forward-error
    theorem [dot_acc.dotprod_forward_error] is proved -- *not* the FMA-based
    [floatlib.dotprod].

    Note on operand order: the C statement [r += X*Y] computes [BPLUS acc prod]
    (accumulator first), whereas [dotprodF]'s fold step is [BPLUS prod acc]
    (product first).  IEEE addition is commutative *up to [feq]*, hence the
    end/bridge lemma below relates the two by [feq]. *)

Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPStdCompCert.
From vcfloat Require Import FPStdLib.
From LAProof.C Require Import floatlib.
(* [dotprod_model] only [Require Import]s (not [Export]s) the mathcomp preamble,
   so this does not pollute the VST namespace with ssreflect notations.  We do
   NOT [Import common]: that would bring mathcomp's order/ring notations into
   scope (making [<=]/[<] parse over [R] and breaking [ddot_model_step]).
   Instead [common.BPLUS_comm] / [common.pos_zero] are used qualified below;
   [BPLUS_mor] and the [feq] [Equivalence] come from vcfloat. *)
Require Import LAProof.accuracy_proofs.dotprod_model.

Set Bullet Behavior "Strict Subproofs".

(** [ddot_model X Y] is the value the C loop *literally* computes: a left fold
    with the accumulator as the first [BPLUS] operand, separate multiply then
    add, starting from [+0.0].  This mirrors the Clight AST in [ddot.v] exactly,
    which makes it the natural value to carry in the loop invariant. *)
Definition ddot_loop (xy: list (ftype Tdouble * ftype Tdouble)) : ftype Tdouble :=
  fold_left (fun acc p => BPLUS acc (BMULT (fst p) (snd p))) xy (Zconst Tdouble 0).

Definition ddot_model (X Y: list (ftype Tdouble)) : ftype Tdouble :=
  ddot_loop (combine X Y).

(** ** Model lemmas (the [partial_row_*] triple, specialised to a dense ddot). *)

Lemma combine_app_eqlen {A B} (l1 l1': list A) (l2 l2': list B):
  length l1 = length l2 ->
  combine (l1 ++ l1') (l2 ++ l2') = combine l1 l2 ++ combine l1' l2'.
Proof.
  revert l2; induction l1; destruct l2; simpl; intros; try discriminate; auto.
  f_equal; auto.
Qed.

Lemma ddot_loop_snoc: forall xy p,
  ddot_loop (xy ++ [p]) = BPLUS (ddot_loop xy) (BMULT (fst p) (snd p)).
Proof. intros. unfold ddot_loop. rewrite fold_left_app. reflexivity. Qed.

(** *step*: extending both length-[k] prefixes by their [k]-th element adds one
    [BMULT] term, with the accumulator as the first [BPLUS] operand -- exactly
    the Clight statement [r = r + X[k]*Y[k]]. (cf. [partial_row_next]) *)
Lemma ddot_model_step: forall (X Y: list (ftype Tdouble)) k,
  Zlength X = Zlength Y -> 0 <= k < Zlength X ->
  ddot_model (sublist 0 (k+1) X) (sublist 0 (k+1) Y)
  = BPLUS (ddot_model (sublist 0 k X) (sublist 0 k Y))
          (BMULT (Znth k X) (Znth k Y)).
Proof.
  intros X Y k Hlen Hk. unfold ddot_model.
  rewrite (sublist_last_1 0 k X) by lia.
  rewrite (sublist_last_1 0 k Y) by lia.
  rewrite combine_app_eqlen
    by (apply Nat2Z.inj; rewrite <- !Zlength_correct, !Zlength_sublist by lia; lia).
  cbn [combine].   (* combine [Znth k X] [Znth k Y] = [(Znth k X, Znth k Y)] *)
  rewrite ddot_loop_snoc. reflexivity.
Qed.

(** *end*/bridge: the finished accumulation equals LAProof's accuracy model
    [dotprodF] up to [feq].  They differ only by the [BPLUS] operand order
    ([BPLUS acc prod] here vs [BPLUS prod acc] in [dotprodF]'s fold step), so the
    proof is a generalized-accumulator induction using [common.BPLUS_comm]
    (feq (BPLUS x y) (BPLUS y x)) and the [BPLUS_mor] feq-congruence, plus the
    fact that [List.combine = seq.zip] on equal-length lists and that the two
    initial zeros ([Zconst Tdouble 0] vs [pos_zero]) are [feq].  This is the one
    remaining model obligation; once discharged, [dot_acc.dotprod_forward_error]
    transfers to the C result. *)
Lemma ddot_model_feq_dotprodF:
  forall (X Y: list (ftype Tdouble)),
    Zlength X = Zlength Y ->
    Forall finite X -> Forall finite Y ->
    feq (ddot_model X Y) (dotprodF X Y).
Proof.
  intros X Y Hlen _ _.
  assert (Hl: length X = length Y)
    by (apply Nat2Z.inj; rewrite <- !Zlength_correct; exact Hlen).
  clear Hlen.
  unfold ddot_model, ddot_loop, dotprodF, dotprod.
  (* The two folds differ only by the initial accumulator ([Zconst Tdouble 0] vs
     [pos_zero], which are [feq]) and the [BPLUS] operand order at each step.
     Generalize both accumulators, keeping them [feq]-linked, and induct. *)
  assert (Hs: feq (Zconst Tdouble 0) (@common.pos_zero Tdouble)) by reflexivity.
  revert Y Hl Hs.
  generalize (Zconst Tdouble 0).
  generalize (@common.pos_zero Tdouble).
  induction X as [|x X IH]; intros g f Y Hl Hs.
  - (* X = nil (so Y = nil): both folds are the (feq-linked) initial accs. *)
    destruct Y as [|y Y']; [ | simpl in Hl; discriminate ].
    simpl. exact Hs.
  - destruct Y as [|y Y']; simpl in Hl; [ discriminate | ].
    simpl.
    apply IH.
    + congruence.
    + (* one accumulation step: [BPLUS f prod] vs [flip BPLUS g prod = BPLUS prod g] *)
      simpl. unfold Basics.flip.
      etransitivity; [ apply common.BPLUS_comm | apply BPLUS_mor; [ reflexivity | exact Hs ] ].
Qed.
