Require Import VST.floyd.proofauto.
From VSTlib Require Import spec_malloc.
From LAProof.C Require Import floatlib sparse sparse_model distinct spec_alloc.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import VSTlib.spec_math.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition t_csr := Tstruct _csr_matrix noattr.
Definition t_coo := Tstruct _coo_matrix noattr.

Definition csr_rep' sh (csr: csr_matrix Tdouble) (v: val) (ci: val) (rp: val) (p: val) :=
  data_at sh t_csr (v,(ci,(rp,(Vint (Int.repr (csr_rows csr)), Vint (Int.repr (csr_cols csr)))))) p *
  data_at sh (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) v * 
  data_at sh (tarray tuint (Zlength (csr_col_ind csr))) (map Vint (map Int.repr (csr_col_ind csr))) ci *
  data_at sh (tarray tuint (csr_rows csr + 1)) (map Vint (map Int.repr (csr_row_ptr csr))) rp.

Definition csr_rep (sh: share) (csr: csr_matrix Tdouble) (p: val) : mpred :=
  EX v: val, EX ci: val, EX rp: val,
  csr_rep' sh csr v ci rp p.

Definition csr_token' (csr: csr_matrix Tdouble) (p: val) : mpred :=
 EX v: val, EX ci: val, EX rp: val,
    csr_rep' Ews csr v ci rp p -*
    (csr_rep' Ews csr v ci rp p
     * (spec_malloc.malloc_token Ews t_csr p *
        spec_malloc.malloc_token Ews (tarray tdouble (Zlength (csr_vals csr))) v *
        spec_malloc.malloc_token Ews (tarray tuint (Zlength (csr_vals csr))) ci *
        spec_malloc.malloc_token Ews (tarray tuint (csr_rows csr + 1)) rp)).

Definition csr_token (m: matrix Tdouble) (p: val) : mpred :=
 EX (csr: csr_matrix Tdouble) (H: csr_to_matrix csr m), csr_token' csr p.

Definition coo_rep (sh: share) (coo: coo_matrix Tdouble) (p: val) : mpred :=
 EX (maxn: Z) (rp cp vp : val), 
 !! (0 <= Zlength (coo_entries coo) <= maxn /\ maxn <= Int.max_signed 
     /\ 0 <= coo_rows coo < Int.max_signed 
     /\ 0 <= coo_cols coo < Int.max_signed /\ coo_matrix_wellformed coo) &&
  data_at sh t_coo (rp, (cp, (vp, (Vint (Int.repr (Zlength (coo_entries coo))), (Vint (Int.repr maxn), 
                     (Vint (Int.repr (coo_rows coo)), 
                     (Vint (Int.repr (coo_cols coo))))))))) p *
  data_at sh (tarray tuint maxn)
    (map (fun e => Vint (Int.repr (fst (fst e)))) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-(Zlength (coo_entries coo)))) rp *
  data_at sh (tarray tuint maxn)
    (map (fun e => Vint (Int.repr (snd (fst e)))) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-(Zlength (coo_entries coo)))) cp *
  data_at sh (tarray tdouble maxn)
    (map (fun e => Vfloat (snd e)) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-(Zlength (coo_entries coo)))) vp.

Definition coo_to_csr_matrix_spec :=
 DECLARE _coo_to_csr_matrix
 WITH sh: share, coo: coo_matrix Tdouble, p: val, gv: globals
 PRE [ tptr t_coo ]
    PROP(writable_share sh;
         coo_matrix_wellformed coo)
    PARAMS( p )
    GLOBALS (gv)
    SEP (coo_rep sh coo p; mem_mgr gv)
 POST [ tptr t_csr ]
   EX coo': coo_matrix Tdouble, EX csr: csr_matrix Tdouble, EX m: matrix Tdouble, EX q: val,
    PROP(coo_matrix_equiv coo coo'; coo_to_matrix coo m; csr_to_matrix csr m)
    RETURN( q )
    SEP (coo_rep sh coo' p; csr_rep Ews csr q; csr_token m q; mem_mgr gv).

Definition csr_matrix_rows_spec :=
 DECLARE _csr_matrix_rows
 WITH sh: share, m: val, mval: matrix Tdouble, csr: csr_matrix Tdouble
 PRE [ tptr t_csr ]
    PROP (readable_share sh; matrix_rows mval < Int.max_unsigned; csr_to_matrix csr mval)
    PARAMS (m)
    SEP (csr_rep sh csr m)
 POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (matrix_rows mval)))
    SEP (csr_rep sh csr m).

Definition csr_row_vector_multiply_spec :=
 DECLARE _csr_row_vector_multiply
 WITH sh1: share, sh2: share, sh3: share,
      m: val, mval: matrix Tdouble, csr: csr_matrix Tdouble, 
      v: val, vval: vector Tdouble, i: Z
 PRE [ tptr t_csr, tptr tdouble, tuint ]
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             csr_to_matrix csr mval;
             matrix_cols mval (Zlength vval);
             matrix_rows mval < Int.max_unsigned;
             Zlength vval < Int.max_unsigned;
             0 <= i < matrix_rows mval;
             Forall finite vval;
             Forall (Forall finite) mval)
    PARAMS(m; v; Vint (Int.repr i))
    SEP (csr_rep sh1 csr m;
         data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v)
 POST [ tdouble ]
   EX s: ftype Tdouble,
    PROP(feq s (dotprod (Znth i mval) vval)) 
    RETURN(Vfloat s)
    SEP (csr_rep sh1 csr m;
          data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v).

Definition csr_matrix_vector_multiply_byrows_spec :=
 DECLARE _csr_matrix_vector_multiply_byrows
 WITH sh1: share, sh2: share, sh3: share,
      m: val, mval: matrix Tdouble, csr: csr_matrix Tdouble, 
      v: val, vval: vector Tdouble, p: val
 PRE [ tptr t_csr, tptr tdouble, tptr tdouble ]
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             csr_to_matrix csr mval;
             matrix_cols mval (Zlength vval);
             matrix_rows mval < Int.max_unsigned;
             Zlength vval < Int.max_unsigned;
             Forall finite vval;
             Forall (Forall finite) mval)
    PARAMS(m; v; p)
    SEP (csr_rep sh1 csr m;
         data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
         data_at_ sh3 (tarray tdouble (matrix_rows mval)) p)
 POST [ tvoid ]
   EX result: vector Tdouble,
    PROP(Forall2 feq result (matrix_vector_mult mval vval)) 
    RETURN()
    SEP (csr_rep sh1 csr m;
          data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
          data_at sh3 (tarray tdouble (matrix_rows mval)) 
             (map Vfloat result) p).

Definition csr_matrix_vector_multiply_spec :=
 DECLARE _csr_matrix_vector_multiply
 WITH sh1: share, sh2: share, sh3: share,
      m: val, mval: matrix Tdouble, csr: csr_matrix Tdouble, 
      v: val, vval: vector Tdouble, p: val
 PRE [ tptr t_csr, tptr tdouble, tptr tdouble ]
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             csr_to_matrix csr mval;
             matrix_cols mval (Zlength vval);
             matrix_rows mval < Int.max_unsigned;
             Zlength vval < Int.max_unsigned;
             Forall finite vval;
             Forall (Forall finite) mval)
    PARAMS(m; v; p)
    SEP (csr_rep sh1 csr m;
         data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
         data_at_ sh3 (tarray tdouble (matrix_rows mval)) p)
 POST [ tvoid ]
   EX result: vector Tdouble,
    PROP(Forall2 feq result (matrix_vector_mult mval vval)) 
    RETURN()
    SEP (csr_rep sh1 csr m;
          data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
          data_at sh3 (tarray tdouble (matrix_rows mval)) 
             (map Vfloat result) p).

Definition add_to_coo {t} (coo: coo_matrix t) (i j: Z) (v: ftype t): coo_matrix t :=
 {| coo_rows := coo_rows coo ;
    coo_cols := coo_cols coo ;
    coo_entries := coo_entries coo ++ [(i,j,v)]
  |}.

Definition add_to_coo_matrix_spec :=
 DECLARE _add_to_coo_matrix
 WITH sh: share, p : val, i: Z, j: Z, x: ftype Tdouble, coo: coo_matrix Tdouble
 PRE [ tptr t_coo, tuint, tuint, tdouble ]
   PROP (writable_share sh; 0 <= i < Int.max_unsigned; 0 <= j < Int.max_unsigned) 
   PARAMS ( p; Vint (Int.repr i); Vint (Int.repr j); Vfloat x) 
   SEP (coo_rep sh coo p)
 POST [ tvoid ]
   PROP ()
   RETURN ()
   SEP (coo_rep sh (add_to_coo coo i j x) p).

Definition swap_spec :=
 DECLARE _swap
 WITH sh: share, coo: coo_matrix Tdouble, p: val, a: Z, b: Z
 PRE [ tptr t_coo, tuint, tuint ]
    PROP(writable_share sh;
         coo_matrix_wellformed coo;
         0 <= a < Zlength (coo_entries coo);
         0 <= b < Zlength (coo_entries coo))
    PARAMS( p; Vint (Int.repr a); Vint (Int.repr b))
    SEP (coo_rep sh coo p)
 POST [ tvoid ]
   EX coo': coo_matrix Tdouble,
    PROP(coo_rows coo' = coo_rows coo; 
         coo_cols coo' = coo_cols coo;
         coo_entries coo' = 
          upd_Znth a (upd_Znth b (coo_entries coo) 
                        (Znth a (coo_entries coo))) 
                 (Znth b (coo_entries coo)))
    RETURN( )
    SEP (coo_rep sh coo' p).

Definition coo_quicksort_spec :=
 DECLARE _coo_quicksort
 WITH sh: share, coo: coo_matrix Tdouble, p: val, base: Z, n: Z
 PRE [ tptr t_coo, tuint, tuint ]
    PROP(writable_share sh;
         coo_matrix_wellformed coo;
         0 <= base; base <= base+n <= Zlength (coo_entries coo))
    PARAMS( p; Vint (Int.repr base); Vint (Int.repr n))
    SEP (coo_rep sh coo p)
 POST [ tvoid ]
   EX coo': coo_matrix Tdouble,
    PROP(coo_matrix_equiv coo coo'; 
         sorted coord_le (sublist base (base+n) (coo_entries coo')))
    RETURN( )
    SEP (coo_rep sh coo' p).

Definition coo_count_spec :=
 DECLARE _coo_count
 WITH sh: share, coo: coo_matrix Tdouble, p: val
 PRE [ tptr t_coo ]
    PROP(writable_share sh;
         coo_matrix_wellformed coo;
         sorted coord_le (coo_entries coo))
    PARAMS( p )
    SEP (coo_rep sh coo p)
 POST [ tuint ]
    PROP()
    RETURN( Vint (Int.repr (count_distinct (coo_entries coo))) )
    SEP (coo_rep sh coo p).


Definition coo_less_spec : ident*funspec := 
 (_coo_less, vacuous_funspec (Internal f_coo_less)).
Definition create_coo_matrix_spec : ident*funspec := 
 (_create_coo_matrix, vacuous_funspec (Internal f_create_coo_matrix)).

Definition SparseASI : funspecs := [ 
   csr_matrix_rows_spec;
   csr_row_vector_multiply_spec;
   csr_matrix_vector_multiply_byrows_spec;
   csr_matrix_vector_multiply_spec;
   coo_count_spec; swap_spec; coo_quicksort_spec; 
   add_to_coo_matrix_spec; coo_to_csr_matrix_spec;
   coo_less_spec; create_coo_matrix_spec
 ].


Definition sparse_imports := [fma_spec] ++ [spec_alloc.surely_malloc_spec'].

Definition Gprog: funspecs := sparse_imports ++ SparseASI.

Lemma BFMA_eq:
   forall H H0 x y z,
  Binary.Bfma (fprec Tdouble) (femax Tdouble) H H0
    (@FPCompCert.FMA_NAN.fma_nan_pl 
          (FPCore.fprec FPCore.Tdouble) 
          (FPCore.femax FPCore.Tdouble) (FPCore.fprec_gt_one _)) 
     BinarySingleNaN.mode_NE x y z = 
  BFMA x y z.
Proof.
intros.
 unfold BFMA.
 f_equal; try apply proof_irr.
 simpl. f_equal. apply proof_irr.
Qed.

