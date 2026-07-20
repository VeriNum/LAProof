(**  * LAProof.C.cblas.spec_dasum: VST specification of GSL's [cblas_dasum]. *)
(** ** Corresponds to C program [C/cblas/src/dasum.c] (ported from GSL cblas). *)

(** Sibling of [LAProof.C.cblas.spec_ddot].  [cblas_dasum] computes the sum of
    absolute values of a strided vector; the postcondition relates its result
    (up to [feq]) to LAProof's unchanged summation model [sumF], applied to the
    logical vector selected from the input array by [incX]. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math.
From LAProof.C Require Import floatlib.
From LAProof.C.cblas Require Import dasum scal_model asum_model.
(* for [sumF]; [Require Import] (not [Export]) keeps ssreflect out of scope. *)
Require Import LAProof.accuracy_proofs.sum_model.

Set Bullet Behavior "Strict Subproofs".

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** ** Funspec for [cblas_dasum] at general stride. *)
(** For [incX > 0], the kernel reads [N] elements at positions [i*incX] in
    the length-[n] input array.  The bounds cover those reads and the final
    signed-[int] update of [ix].  For [incX <= 0], it returns [+0.0] without
    accessing the array. *)
Definition cblas_dasum_spec :=
 DECLARE _cblas_dasum
 WITH shX: share, n: Z, N: Z, incX: Z,
      X: list (ftype Tdouble), px: val
 PRE [ tint, tptr tdouble, tint ]
   PROP (readable_share shX; Zlength X = n; 0 <= n <= Int.max_signed;
         0 <= N <= Int.max_signed;
         Int.min_signed <= incX <= Int.max_signed;
         incX <= 0 \/
           (0 < incX /\ (N-1)*incX < n /\ N*incX <= Int.max_signed))
   PARAMS (Vint (Int.repr N); px; Vint (Int.repr incX))
   SEP (data_at shX (tarray tdouble n) (map Vfloat X) px)
 POST [ tdouble ]
   EX s: ftype Tdouble,
   PROP (feq s
     (if Z.leb incX 0
      then Zconst Tdouble 0
      else sumF (map BABS (strided incX N X))))
   RETURN (Vfloat s)
   SEP (data_at shX (tarray tdouble n) (map Vfloat X) px).

Definition DasumASI : funspecs := [ cblas_dasum_spec ].
Definition dasum_imports : funspecs := [ fabs_spec ].   (* fabs is the one external call *)
Definition Gprog : funspecs := dasum_imports ++ DasumASI.
