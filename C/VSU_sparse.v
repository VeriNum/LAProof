Require Import VST.floyd.proofauto VST.floyd.VSU.
Require Import LAProof.floatlib.
From LAProof.C Require Import sparse sparse_model spec_sparse.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPStdCompCert.
Require Import VSTlib.spec_math.
From LAProof.C Require Import verif_sparse verif_sparse_byrows.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

#[local] Existing Instance NullExtension.Espec.  (* FIXME *)

Definition sparseImports : funspecs := [fma_spec]. (* Ideally , 
   the VSU system would let us say MathASI instead of [fma_spec] *)

Definition SparseVSU {NAN : FPStdLib.Nans}: VSU nil sparseImports ltac:(QPprog prog) SparseASI emp.
  Proof. 
    mkVSU prog SparseASI.
- solve_SF_internal body_crs_matrix_rows.
- solve_SF_internal body_crs_row_vector_multiply.
- solve_SF_internal body_crs_matrix_vector_multiply_byrows.
- solve_SF_internal body_crs_matrix_vector_multiply.
Qed.

