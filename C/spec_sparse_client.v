Require Import VST.floyd.proofauto.
From LAProof.C Require Import floatlib sparse sparse_model distinct spec_alloc build_csr2 partial_csrg sparse_client.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import VSTlib.spec_math VSTlib.spec_malloc.
Require Import Coq.Classes.RelationClasses.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

#[export] Declare Instance M: MallocAPD.

(* Zconst *)
Check Zconst.

Definition float1 := Vfloat (Float.of_bits (Int64.repr 4607182418800017408)).
Definition float2 := Vfloat (Float.of_bits (Int64.repr 4611686018427387904)).
Definition float3 := Vfloat (Float.of_bits (Int64.repr 4613937818241073152)).

(* define the entire list of coog *)
Definition coog := [(r, c) *4]
(* two lists of values *)

(* delta_mx *)

Definition test_spec :=
  DECLARE _test 
  WITH sh:share, p1 : val, p2 : val, gv : globals
  PRE [ tptr (tdouble), tptr (tdouble) ]
    PROP (writable_share sh)
    PARAMS (p1; p2) 
    GLOBALS (gv)
    SEP (data_at_ sh (tarray tdouble 3) p1; 
      data_at_ sh (tarray tdouble 3) p2;
      mem_mgr gv)
  POST [ tvoid ]
    PROP ()
    RETURN () 
    SEP (data_at sh (tarray tdouble 3) [float2; float1; float1] p1; 
      data_at sh (tarray tdouble 3) [float2; float3; float1] p2;
      mem_mgr gv).

Definition Sparse_Client_ASI : funspecs := [test_spec].