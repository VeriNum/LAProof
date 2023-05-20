# LAProof: a library of formal proofs of accuracy and correctness for linear algebra programs

LAProof is a modular, portable proof layer between
the verification of application software and the verification
of programs implementing operations defined by the basic linear algebra subprograms (BLAS) specification.

LAProof provides formal machine-checked proofs of the accuracy of basic linear algebra operations:
inner product using conventional multiply and add, inner product
using fused multiply-add, scaled matrix-vector and matrix-matrix
multiplication, and scaled vector and matrix addition. LAProof error bounds are give as backward error
bounds and mixed backward-forward error bounds that account
for underflow, proved subject to no assumptions except a low-
level formal model of IEEE-754 arithmetic. We treat low-order
error terms concretely, not approximating as $O(u^2)$.

The LAProof repository contains a machine-checked correctness proof of a C function
implementing compressed-row-storage (CRS) sparse matrix-
vector multiplication as an example of connecting LAProof functions to concrete programs.
