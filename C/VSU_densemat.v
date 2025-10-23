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

(* BEGIN workaround for VST issue #814, until we can install VST 2.16 which fixes it. *)
Ltac new_simpl_fst_snd :=
  match goal with |- context[@fst ident funspec ?A] =>
     let j := eval hnf in A in 
     match j with (?x,?y) => 
      try change (fst A) with x;
      try change (snd A) with y
     end
    end.

Ltac SF_vacuous ::=
 try new_simpl_fst_snd;
 match goal with |- SF _ _ _ (vacuous_funspec _) => idtac end;
 match goal with H: @eq compspecs _ _ |- _ => rewrite <- H end;
red; red; repeat simple apply conj;
[ reflexivity (* id_in_list ... *)
| repeat apply Forall_cons; (* Forall complete_type fn_vars *)
  try apply Forall_nil; reflexivity
| repeat constructor; simpl; rep_lia (* var_sizes_ok *)
| reflexivity (* fn_callconv ... *)
| split3; [reflexivity | reflexivity | intros; apply semax_vacuous] (* semax_body *)
| eexists; split; compute; reflexivity (* genv_find_func *)
].
(* END workaround for VST issue #814 *)

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
    - solve_SF_internal body_densemat_csolve.
    - solve_SF_internal body_densematn_csolve.
    - solve_SF_internal body_densemat_cfactor.
    - solve_SF_internal body_densematn_cfactor.
    - solve_SF_internal body_densematn_dotprod.
    - solve_SF_internal body_densemat_dotprod.
    - solve_SF_internal body_densematn_mult.
    - solve_SF_internal body_densemat_mult.
  Qed.

