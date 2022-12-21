Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
From Iterative.sparse Require Import sparse sparse_model.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition t_crs := Tstruct _crs_matrix noattr.

Definition crs_rep (sh: share) (mval: matrix Tdouble) (p: val) : mpred :=
  EX v: val, EX ci: val, EX rp: val, 
  EX cols, EX vals: list (ftype Tdouble), EX col_ind: list Z, EX row_ptr: list Z,
  !! crs_rep_aux mval cols vals col_ind row_ptr &&
  data_at sh t_crs (v,(ci,(rp,(Vint (Int.repr (matrix_rows mval)), Vint (Int.repr cols))))) p *
  data_at sh (tarray tdouble (Zlength col_ind)) (map Vfloat vals) v * 
  data_at sh (tarray tuint (Zlength col_ind)) (map Vint (map Int.repr col_ind)) ci *
  data_at sh (tarray tuint (matrix_rows mval + 1)) (map Vint (map Int.repr row_ptr)) rp.

Definition crs_row_vector_multiply_spec :=
 DECLARE _crs_row_vector_multiply
 WITH sh1: share, sh2: share, sh3: share,
      m: val, mval: matrix Tdouble, v: val, vval: vector Tdouble, i: Z
 PRE [ tptr t_crs, tptr tdouble, tuint ]
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             matrix_cols mval (Zlength vval);
             matrix_rows mval < Int.max_unsigned;
             Zlength vval < Int.max_unsigned;
             0 <= i < matrix_rows mval;
             Forall finite vval;
             Forall (Forall finite) mval)
    PARAMS(m; v; Vint (Int.repr i))
    SEP (crs_rep sh1 mval m;
         data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v)
 POST [ tdouble ]
   EX s: ftype Tdouble,
    PROP(float_eqv s (dotprod (Znth i mval) vval)) 
    RETURN(Vfloat s)
    SEP (crs_rep sh1 mval m;
          data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v).

Definition crs_matrix_vector_multiply_byrows_spec :=
 DECLARE _crs_matrix_vector_multiply_byrows
 WITH sh1: share, sh2: share, sh3: share,
      m: val, mval: matrix Tdouble, v: val, vval: vector Tdouble, p: val
 PRE [ tptr t_crs, tptr tdouble, tptr tdouble ]
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             matrix_cols mval (Zlength vval);
             matrix_rows mval < Int.max_unsigned;
             Zlength vval < Int.max_unsigned;
             Forall finite vval;
             Forall (Forall finite) mval)
    PARAMS(m; v; p)
    SEP (crs_rep sh1 mval m;
         data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
         data_at_ sh3 (tarray tdouble (matrix_rows mval)) p)
 POST [ tvoid ]
   EX result: vector Tdouble,
    PROP(floatlist_eqv result (matrix_vector_mult mval vval)) 
    RETURN()
    SEP (crs_rep sh1 mval m;
          data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
          data_at sh3 (tarray tdouble (matrix_rows mval)) 
             (map Vfloat result) p).

Definition crs_matrix_vector_multiply_spec :=
 DECLARE _crs_matrix_vector_multiply
 WITH sh1: share, sh2: share, sh3: share,
      m: val, mval: matrix Tdouble, v: val, vval: vector Tdouble, p: val
 PRE [ tptr t_crs, tptr tdouble, tptr tdouble ]
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             matrix_cols mval (Zlength vval);
             matrix_rows mval < Int.max_unsigned;
             Zlength vval < Int.max_unsigned;
             Forall finite vval;
             Forall (Forall finite) mval)
    PARAMS(m; v; p)
    SEP (crs_rep sh1 mval m;
         data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
         data_at_ sh3 (tarray tdouble (matrix_rows mval)) p)
 POST [ tvoid ]
   EX result: vector Tdouble,
    PROP(floatlist_eqv result (matrix_vector_mult mval vval)) 
    RETURN()
    SEP (crs_rep sh1 mval m;
          data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
          data_at sh3 (tarray tdouble (matrix_rows mval)) 
             (map Vfloat result) p).

Definition SparseASI : funspecs := [ 
   crs_row_vector_multiply_spec;
   crs_matrix_vector_multiply_byrows_spec;
   crs_matrix_vector_multiply_spec ].
