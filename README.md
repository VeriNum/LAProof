# LAProof: a library of formal proofs of accuracy and correctness for linear algebra programs

LAProof is a modular, portable proof layer between
the verification of application software and the verification
of programs implementing operations defined by the basic linear algebra subprograms (BLAS) specification.

_See:_  [the paper in _30th IEEE International Symposium on Computer Arithmetic (ARITH '23)_](https://doi.org/10.1109/ARITH58626.2023.00021) or [non-paywall version](https://www.cs.princeton.edu/~appel/papers/LAProof.pdf)

LAProof provides formal machine-checked proofs of the accuracy of basic linear algebra operations:
inner product using conventional multiply and add, inner product
using fused multiply-add, scaled matrix-vector and matrix-matrix
multiplication, and scaled vector and matrix addition. LAProof error bounds are backward error
bounds and mixed backward-forward error bounds that account
for underflow, proved subject to no assumptions except a low-
level formal model of IEEE-754 arithmetic. We treat low-order
error terms concretely, not approximating as $O(u^2)$.

The LAProof repository contains a machine-checked correctness proof of a C function
implementing compressed sparse row matrix-
vector multiplication as an example of connecting LAProof to concrete programs.

## DOCUMENTATION

LAProof 2.0beta1 is based more directly on MathComp; that is, matrix and vector operations use definitions in mathcomp.algebra.matrix.

Most of the definitions and lemmas listed here are parameterized by a floating-point format not shown in this summary: that is, `{_: FPCore.Nans}{t: FPStdLib.type}`.

- `F.sum [n] ('I_n -> ftype t) : ftype t`
- `F.dotprod [n]  (x: 'rV[ftype t]_n) (y: 'cV[ftype t]_n) : ftype t`
- `F.mulmx [m n p] (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,p))`
- `F.scalemx [m n] (a: ftype t) (M: 'M[ftype t]_(m,n)`
- `F.addmx [m n] (A B: 'M[ftype t]_(m,n)) : 'M[ftype t]_(m,n)`
- `Fsum_backward_error [n] (x: 'I_n -> ftype t) ...`
- `Fsum_forward_error [n] (x: 'I_n -> ftype t) ...`
- `Faddmx_mixed_error [m n] (A B: 'M[ftype t]_(m,n)) ...`
- `Fscalemx_mixed_error [m n] (a: ftype t) (v: 'M[ftype t]_(m,n)) ...`
- `vec_vec_mul_mixed_error [n] (A: 'rV[ftype t]_n) (B: 'cV[ftype t]_n) ...`
- `mat_vec_mul_mixed_error [m n] (A 'M[ftype t](m,n)) (B: 'cV[ftype t]_n) ...`
- `mat_vec_mul_forward_error [m n]  (A 'M[ftype t](m,n)) (B: 'cV[ftype t]_n) ...`
- `mat_sum_error [m n] (A B: 'M[ftype t]_(m,n)) ...`
- `mat_axpby_error  [m n] (A B: 'M[ftype t]_(m,n)) (x y: ftype t) ...` (xA+yB)
- `GEMM_error [m n p] (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,p)) (Y: 'M[ftype t]_(m,p)) (s1 s2: ftype t) ...` (s1*A*B+s2*Y)

