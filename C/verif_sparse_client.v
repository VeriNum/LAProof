Require Import VST.floyd.proofauto.
From LAProof.C Require Import floatlib build_csr2 sparse_model spec_sparse spec_build_csr2 distinct partial_csrg sparse_client spec_sparse_client.
Require Import VSTlib.spec_math.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog: funspecs := Sparse_Client_ASI ++ Build_CSR2_ASI ++ SparseASI ++ MathASI.

Lemma body_test : semax_body Vprog Gprog f_test test_spec.
Proof.
  start_function.
  forward. forward. forward.
  fold float1.
  forward_call (3, gv).
  { entailer!!. rewrite sepcon_comm.
    

    ([data_at Tsh (tarray tdouble 3)
  (upd_Znth 2 (upd_Znth 1 (upd_Znth 0 (default_val (tarray tdouble 3)) float1) float1) float1) v_v; 
data_at_ sh (tarray tdouble 3) p1; data_at_ sh (tarray tdouble 3) p2]).