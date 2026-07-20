(**  * LAProof.C.cblas.spec_dscal: VST specification of GSL's [cblas_dscal]. *)
(** ** Corresponds to C program [C/cblas/src/dscal.c] (ported from GSL cblas). *)

(** [cblas_dscal] scales a vector in place by [alpha].  Because scaling is
    deterministic elementwise, the postcondition is stated as an *exact* equality
    (the array is left holding [scal_strided incX N alpha X]); no [feq]/[EX] is
    needed, unlike the reduction routines [ddot]/[dasum]. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From LAProof.C Require Import floatlib.
From LAProof.C.cblas Require Import dscal scal_model.

Set Bullet Behavior "Strict Subproofs".

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** ** Funspec for [cblas_dscal] at general stride. *)
(** [X] represents the entire input array ([Zlength X = n]); [N] is the
    element count the loop scales, touching positions
    [{i*incX : 0 <= i < N}].  Memory safety
    needs the last touched index in range ([(N-1)*incX < n]); [N*incX <=
    Int.max_signed] keeps the final [ix += incX] from overflowing [int].  For
    [incX <= 0], the GSL kernel returns without modifying the array. *)
Definition cblas_dscal_spec :=
 DECLARE _cblas_dscal
 WITH sh: share, n: Z, N: Z, incX: Z, alpha: ftype Tdouble,
      X: list (ftype Tdouble), px: val
 PRE [ tint, tdouble, tptr tdouble, tint ]
   PROP (writable_share sh; Zlength X = n; 0 <= n <= Int.max_signed;
         0 <= N <= Int.max_signed;
         Int.min_signed <= incX <= Int.max_signed;
         incX <= 0 \/
           (0 < incX /\ (N-1)*incX < n /\ N*incX <= Int.max_signed))
   PARAMS (Vint (Int.repr N); Vfloat alpha; px; Vint (Int.repr incX))
   SEP (data_at sh (tarray tdouble n) (map Vfloat X) px)
 POST [ tvoid ]
   PROP ()
   RETURN ()
   SEP (data_at sh (tarray tdouble n)
          (map Vfloat
            (if Z.leb incX 0 then X else scal_strided incX N alpha X)) px).

Definition DscalASI : funspecs := [ cblas_dscal_spec ].
Definition dscal_imports : funspecs := [].   (* no external calls *)
Definition Gprog : funspecs := dscal_imports ++ DscalASI.
