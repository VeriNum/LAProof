From VST.floyd Require Import proofauto VSU.
From LAProof.C Require Import alloc spec_alloc.
(* From vcfloat Require Import vcfloat.FPStdCompCert vcfloat.FPStdLib. *)
Require Import VSTlib.spec_math VSTlib.spec_malloc.
Require Import Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Require VST.floyd.library.

Parameter body_exit:
 forall {Espec: OracleKind},
  VST.floyd.library.body_lemma_of_funspec
    (EF_external "exit" (mksignature [Xint] Xvoid cc_default))
    (snd (exit_spec)).

Definition alloc_E : funspecs := [exit_spec].
Definition alloc_imported_specs : funspecs := MallocASI.
Definition alloc_internal_specs : funspecs := allocASI.
Definition Gprog := alloc_imported_specs ++ alloc_internal_specs.

Lemma body_surely_malloc: semax_body Vprog Gprog f_surely_malloc surely_malloc_spec'.
Proof.
start_function.
  forward_call. (* p = malloc(n); *)
  Intros p.
  forward_if
  (PROP ( )
   LOCAL (temp _p p)
   SEP (mem_mgr gv; malloc_token' Ews n p * memory_block Ews n p)).
*
  if_tac.
    subst p. entailer!.
    entailer!.
*
    forward_call (Int.repr 1).
    contradiction.
*
    if_tac.
    + forward. subst p. congruence.
    + Intros. forward. entailer!.
*
(* temporarily: *) forward_if True. contradiction. forward. entailer!.
  forward. Exists p; entailer!.
Qed.

Lemma body_double_calloc: semax_body Vprog Gprog f_double_calloc double_calloc_spec.
Proof.
start_function.
forward_call (surely_malloc_spec_sub (tarray tdouble n)) gv.
entailer!. simpl. do 3 f_equal. rep_lia.
simpl. rep_lia.
Intros p.
forward_call (p, n, Ews).
forward.
Exists p.
entailer!.
Qed.


Lemma body_int_calloc: semax_body Vprog Gprog f_int_calloc int_calloc_spec.
Proof.
start_function.
forward_call (surely_malloc_spec_sub (tarray tint n)) gv.
entailer!. simpl. do 3 f_equal. rep_lia.
simpl. rep_lia.
Intros p.
freeze FR1 := - (data_at_ _ _ _).
forward_for_simple_bound n (EX i: Z, PROP() LOCAL(temp _p p; temp _n (Vint (Int.repr n)))
             SEP (FRZL FR1; 
              data_at Ews (tarray tint n) 
                 (Zrepeat (Vint Int.zero) i ++ Zrepeat Vundef (n-i)) p)).
- entailer!. simpl. cancel.
- forward. entailer!. apply derives_refl'. f_equal. list_solve.
- thaw FR1. forward. Exists p. entailer!.
  apply derives_refl'.  f_equal. list_solve.
Qed.

Lemma body_double_clear: semax_body Vprog Gprog f_double_clear double_clear_spec.
Proof.
start_function.
forward_for_simple_bound n (EX i: Z, PROP() LOCAL(temp _p p; temp _n (Vint (Int.repr n)))
             SEP (data_at sh (tarray tdouble n) 
                 (Zrepeat (Vfloat Float.zero) i ++ Zrepeat Vundef (n-i)) p)).
- entailer!. cancel.
- forward. entailer!. apply derives_refl'. f_equal. list_solve.
- entailer!. apply derives_refl'. f_equal. list_solve.
Qed.

Definition allocVSU: @VSU NullExtension.Espec
         alloc_E alloc_imported_specs ltac:(QPprog prog) allocASI (fun gv => emp).
  Proof.
    mkVSU prog alloc_internal_specs.
    - solve_SF_external (@body_exit NullExtension.Espec).
    - solve_SF_internal body_surely_malloc.
    - solve_SF_internal body_double_calloc.
    - solve_SF_internal body_int_calloc.
    - solve_SF_internal body_double_clear.
Qed.



