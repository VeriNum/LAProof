(**  * LAProof.C.cblas.spec_ddot: VST specification of GSL's [cblas_ddot]. *)
(** ** Corresponds to C program [C/cblas/src/ddot.c] (ported from GSL cblas). *)

(** This file connects a real-world BLAS implementation -- GSL's double-precision
    dot product [cblas_ddot] -- to LAProof's functional dot-product model.

    GSL's loop (after macro expansion of [source_dot_r.h]) is
<<
      double r = 0.0;
      for (i = 0; i < N; i++) { r += X[ix] * Y[iy]; ix += incX; iy += incY; }
      return r;
>>
    i.e. a forward, left-to-right accumulation using *separate* multiply-then-add
    (not fused multiply-add), starting from +0.0.  That is exactly the
    [dotprodF] model of [LAProof.accuracy_proofs.dotprod_model]
    ([dotprodF = dotprod BMULT BPLUS pos_zero]), over which the forward-error
    theorem [dot_acc.dotprod_forward_error] is proved -- *not* the FMA-based
    [floatlib.dotprod].

    Note on operand order: the C statement [r += X*Y] computes [BPLUS acc prod]
    (accumulator first), whereas [dotprodF]'s fold step is [BPLUS prod acc]
    (product first).  IEEE addition is commutative *up to [feq]*, so we state the
    postcondition with [feq] -- the same convention used by
    [LAProof.C.spec_sparse] for [csr_row_vector_multiply_spec]. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From LAProof.C Require Import floatlib.
From LAProof.C.cblas Require Import ddot ddot_model.
(* [dotprod_model] only [Require Import]s (not [Export]s) the mathcomp preamble,
   so this does not pollute the VST namespace with ssreflect notations.  We need
   it here for [dotprodF], which the postcondition is stated against. *)
Require Import LAProof.accuracy_proofs.dotprod_model.

Set Bullet Behavior "Strict Subproofs".

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** The partial-accumulation model [ddot_model] and its start/step/end lemmas
    live in [LAProof.C.cblas.ddot_model] (mirroring the [sparse_model] /
    [spec_sparse] split).  This file states only the VST [funspec]. *)

(** ** Funspec for [cblas_ddot] (unit-stride case [incX = incY = 1]). *)
(** Unit stride is a deliberate first milestone, not a fundamental limit. *)
Definition cblas_ddot_spec :=
 DECLARE _cblas_ddot
 WITH shX: share, shY: share, n: Z,
      X: list (ftype Tdouble), Y: list (ftype Tdouble),
      px: val, py: val
 PRE [ tint, tptr tdouble, tint, tptr tdouble, tint ]
   PROP (readable_share shX; readable_share shY;
         Zlength X = n; Zlength Y = n; 0 <= n <= Int.max_signed)
   PARAMS (Vint (Int.repr n); px; Vint (Int.repr 1); py; Vint (Int.repr 1))
   SEP (data_at shX (tarray tdouble n) (map Vfloat X) px;
        data_at shY (tarray tdouble n) (map Vfloat Y) py)
 POST [ tdouble ]
   EX s: ftype Tdouble,
   PROP (feq s (dotprodF X Y))
   RETURN (Vfloat s)
   SEP (data_at shX (tarray tdouble n) (map Vfloat X) px;
        data_at shY (tarray tdouble n) (map Vfloat Y) py).

Definition DdotASI : funspecs := [ cblas_ddot_spec ].
Definition ddot_imports : funspecs := [].   (* no external calls: the loop is self-contained *)
Definition Gprog : funspecs := ddot_imports ++ DdotASI.
