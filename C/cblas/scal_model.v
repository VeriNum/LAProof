(**  * LAProof.C.cblas.scal_model: functional model of GSL's [cblas_dscal]. *)
(** ** Corresponds to C program [C/cblas/src/dscal.c] (ported from GSL cblas). *)

(** Unlike the reduction routines ([ddot]/[dasum]), scaling is a deterministic
    *elementwise* update with no accumulation, so the C computes the model
    exactly (no [feq] needed).  GSL's kernel ([source_scal_r.h]) is
<<
      for (i = 0; i < N; i++) { X[ix] *= alpha; ix += incX; }
>>
    and [X[ix] *= alpha] is [BMULT (X[ix]) alpha] (element-first), so the model
    is the C-faithful list map below.

    LAProof's existing scale model [mv_mathcomp.scalemx] is alpha-first
    ([map_mx (BMULT a)]) and matrix-based; relating to it would need a [BMULT]
    commutativity lemma (not in LAProof) plus a vector/matrix reshape.  That is
    unnecessary here: the per-element accuracy (relative error <= unit roundoff)
    is exactly vcfloat's correctly-rounded-[BMULT] bound. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From LAProof.C Require Import floatlib.

Set Bullet Behavior "Strict Subproofs".

Definition scal_model (alpha: ftype Tdouble) (X: list (ftype Tdouble)) : list (ftype Tdouble) :=
  map (fun x => BMULT x alpha) X.

Lemma Zlength_scal_model: forall alpha X,
  Zlength (scal_model alpha X) = Zlength X.
Proof. intros. unfold scal_model. rewrite Zlength_map. reflexivity. Qed.

Lemma Znth_scal_model: forall alpha X k,
  0 <= k < Zlength X ->
  Znth k (scal_model alpha X) = BMULT (Znth k X) alpha.
Proof. intros. unfold scal_model. rewrite Znth_map by lia. reflexivity. Qed.
