(**  * LAProof.C.cblas.spec_dasum: VST specification of GSL's [cblas_dasum]. *)
(** ** Corresponds to C program [C/cblas/src/dasum.c] (ported from GSL cblas). *)

(** Sibling of [LAProof.C.cblas.spec_ddot].  [cblas_dasum] computes the sum of
    absolute values of a vector; the postcondition relates its result (up to
    [feq]) to LAProof's summation model [sumF] applied to [map BABS X], over
    which [sum_acc.fSUM] proves the forward-error bound. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math.
From LAProof.C Require Import floatlib.
From LAProof.C.cblas Require Import dasum asum_model.
(* for [sumF]; [Require Import] (not [Export]) keeps ssreflect out of scope. *)
Require Import LAProof.accuracy_proofs.sum_model.

Set Bullet Behavior "Strict Subproofs".

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** ** Funspec for [cblas_dasum] (unit-stride case [incX = 1]). *)
Definition cblas_dasum_spec :=
 DECLARE _cblas_dasum
 WITH shX: share, n: Z, X: list (ftype Tdouble), px: val
 PRE [ tint, tptr tdouble, tint ]
   PROP (readable_share shX; Zlength X = n; 0 <= n <= Int.max_signed;
         Forall finite X)
   PARAMS (Vint (Int.repr n); px; Vint (Int.repr 1))
   SEP (data_at shX (tarray tdouble n) (map Vfloat X) px)
 POST [ tdouble ]
   EX s: ftype Tdouble,
   PROP (feq s (sumF (map BABS X)))
   RETURN (Vfloat s)
   SEP (data_at shX (tarray tdouble n) (map Vfloat X) px).

Definition DasumASI : funspecs := [ cblas_dasum_spec ].
Definition dasum_imports : funspecs := [ fabs_spec ].   (* fabs is the one external call *)
Definition Gprog : funspecs := dasum_imports ++ DasumASI.
