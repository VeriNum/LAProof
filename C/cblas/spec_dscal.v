(**  * LAProof.C.cblas.spec_dscal: VST specification of GSL's [cblas_dscal]. *)
(** ** Corresponds to C program [C/cblas/src/dscal.c] (ported from GSL cblas). *)

(** [cblas_dscal] scales a vector in place by [alpha].  Because scaling is
    deterministic elementwise, the postcondition is stated as an *exact* equality
    (the array is left holding [scal_model alpha X]); no [feq]/[EX] is needed,
    unlike the reduction routines [ddot]/[dasum]. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From LAProof.C Require Import floatlib.
From LAProof.C.cblas Require Import dscal scal_model.

Set Bullet Behavior "Strict Subproofs".

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** ** Funspec for [cblas_dscal] (unit-stride case [incX = 1]). *)
(** Unit stride is a first milestone, not a fundamental limit.*)
Definition cblas_dscal_spec :=
 DECLARE _cblas_dscal
 WITH sh: share, n: Z, alpha: ftype Tdouble, X: list (ftype Tdouble), px: val
 PRE [ tint, tdouble, tptr tdouble, tint ]
   PROP (writable_share sh; Zlength X = n; 0 <= n <= Int.max_signed)
   PARAMS (Vint (Int.repr n); Vfloat alpha; px; Vint (Int.repr 1))
   SEP (data_at sh (tarray tdouble n) (map Vfloat X) px)
 POST [ tvoid ]
   PROP ()
   RETURN ()
   SEP (data_at sh (tarray tdouble n) (map Vfloat (scal_model alpha X)) px).

Definition DscalASI : funspecs := [ cblas_dscal_spec ].
Definition dscal_imports : funspecs := [].   (* no external calls *)
Definition Gprog : funspecs := dscal_imports ++ DscalASI.
