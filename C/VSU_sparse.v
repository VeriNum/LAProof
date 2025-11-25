Require Import VST.floyd.proofauto VST.floyd.VSU.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPStdCompCert.
Require Import VSTlib.spec_math.
From LAProof.C Require Import sparse sparse_model spec_sparse
                            floatlib verif_sparse verif_sparse_byrows verif_build_csr.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

#[local] Existing Instance NullExtension.Espec.  (* FIXME *)


Definition SparseVSU {NAN : FPCore.Nans}: VSU nil sparse_imports ltac:(QPprog prog) SparseASI emp.
  Proof. 
    mkVSU prog SparseASI.
- solve_SF_internal body_csr_matrix_rows.
- solve_SF_internal body_csr_row_vector_multiply.
- solve_SF_internal body_csr_matrix_vector_multiply_byrows.
- solve_SF_internal body_csr_matrix_vector_multiply.
- solve_SF_internal body_coo_count.
- admit. (* solve_SF_internal body_swap. *)
- admit. (* solve_SF_internal body_coo_quicksort. *)
- admit. (* solve_SF_internal body_add_to_coo_matrix. *)
- solve_SF_internal body_coo_to_csr_matrix.
- admit. (* solve_SF_internal body_coo_less. *)
- admit. (* solve_SF_internal body_create_coo_matrix. *)
all: fail.
Admitted.


