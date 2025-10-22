(**  * LAProof.C.verif_densemat_mult: VST proofs dense matrix multiply functions *)
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

Require Import LAProof.C.densemat_lemmas.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope logic.


Lemma body_densematn_mult: semax_body Vprog Gprog f_densematn_mult densematn_mult_spec.
Proof.
start_function.
Admitted.

Lemma body_densemat_mult: semax_body Vprog Gprog f_densemat_mult densemat_mult_spec.
Proof.
start_function.
Admitted.

Lemma body_densematn_dotprod: semax_body Vprog Gprog f_densematn_dotprod densematn_dotprod_spec.
Proof.
start_function.
Admitted.

Lemma body_densemat_dotprod: semax_body Vprog Gprog f_densemat_dotprod densemat_dotprod_spec.
Proof.
start_function.
Admitted.
