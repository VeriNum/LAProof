(**  * LAProof.C.VSU_densemat: Packaging the [densematVSU], the Verified Software Unit  *)
(** ** Corresponds to C program [densemat.c] *)

(** * Prologue. 

 For explanation see the prologue of [LAProof.C.spec_densemat] *)
From VST.floyd Require Import proofauto VSU.
From LAProof.C Require Import densemat spec_alloc spec_densemat floatlib matrix_model.
From vcfloat Require Import FPStdCompCert FPStdLib.
Require Import VSTlib.spec_math VSTlib.spec_malloc.
Require Import Coq.Classes.RelationClasses.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
Import fintype matrix.

From LAProof.C Require Import  densemat_lemmas verif_densemat verif_densemat_mult verif_densemat_cholesky.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition densematVSU: @VSU NullExtension.Espec
         densemat_E densemat_imported_specs 
         ltac:(QPprog prog) densematASI (fun _ => TT).
  Proof.
    mkVSU prog densemat_internal_specs.
    - solve_SF_internal body_densemat_malloc.
    - solve_SF_internal body_densemat_free.
    - solve_SF_internal body_densematn_clear.
    - solve_SF_internal body_densemat_clear.
    - solve_SF_internal body_densemat_get.
    - solve_SF_internal body_densematn_get.
    - solve_SF_internal body_densemat_set.
    - solve_SF_internal body_densematn_set.
    - solve_SF_internal body_densemat_addto.
    - solve_SF_internal body_densematn_addto.
    - solve_SF_internal body_data_norm.
    - solve_SF_internal body_data_norm2.
    - solve_SF_internal body_densemat_norm.
    - solve_SF_internal body_densemat_norm2.
    - solve_SF_internal body_densemat_print.
    - solve_SF_internal body_densematn_print.
    - solve_SF_internal body_densemat_csolve.
    - solve_SF_internal body_densematn_csolve.
    - solve_SF_internal body_densemat_cfactor.
    - solve_SF_internal body_densematn_cfactor.
    - solve_SF_internal body_densematn_cfactor_and_solve.
    - solve_SF_internal body_densematn_dotprod.
    - solve_SF_internal body_densemat_dotprod.
    - solve_SF_internal body_densematn_mult.
    - solve_SF_internal body_densemat_mult.
  Qed.

