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

Definition intval := fun x => Vint (Int.repr x).

Definition test_spec :=
  DECLARE _test 
  WITH sh:share, p1 : val, p2 : val
  PRE [ tptr (tdouble), tptr (tdouble) ]
    PROP (writable_share sh)
    PARAMS (p1; p2) 
    SEP (data_at_ sh (tarray tdouble 3) p1; data_at_ sh (tarray tdouble 3) p2)
  POST [ tvoid ]
    PROP ()
    RETURN () 
    SEP (data_at sh (tarray tdouble 3) (map intval [2; 1; 1]) p1; 
      data_at sh (tarray tdouble 3) (map intval [2; 3; 1]) p2).