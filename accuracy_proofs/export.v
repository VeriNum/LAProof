(** Don't export the preamble!  It sets some settings that perhaps the client doesn't want. *)
From LAProof.accuracy_proofs Require Export  
       common dotprod_model sum_model dot_acc float_acc_lems 
       mv_mathcomp gemv_acc vec_op_acc gemm_acc.

