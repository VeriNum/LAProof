Require Import VST.floyd.proofauto.
(* Require Import Iterative.floatlib. *)
From LAProof.C Require Import floatlib sparse sparse_model distinct spec_alloc build_csr2 partial_csrg spec_sparse.
(* From Iterative.sparse Require Import sparse_model build_csr2 distinct partial_csrg. *)
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import VSTlib.spec_math VSTlib.spec_malloc.
Require Import Coq.Classes.RelationClasses.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

#[export] Declare Instance M: MallocAPD.


Definition intpair_to_valpair (a : int * int) : val * val :=
  match a with 
  | (x, y) => (Vint x, Vint y)
  end.

Definition intpair_to_Zpair (a : int * int) : Z * Z :=
  match a with 
  | (x, y) => (Int.intval x, Int.intval y)
  end.

Definition Zpair_to_valpair (a : Z * Z) : val * val :=
  match a with 
  | (x, y) => (Vint (Int.repr x), Vint (Int.repr y))
  end.

Definition rowcol_range (rowcol : Z * Z) :=
  match rowcol with 
  | (r, c) => 0 <= r < Int.max_unsigned /\ 0 <= c < Int.max_unsigned
  end.

Definition swap_rc_spec :=
 DECLARE _swap_rc
 WITH sh: share, coog: list (Z * Z), p: val, a: Z, b: Z
 PRE [ tptr (Tstruct _rowcol noattr), tuint, tuint ]
    PROP(writable_share sh;
         Zlength coog < Int.max_unsigned;
         Forall rowcol_range coog;
         0 <= a < Zlength coog;
         0 <= b < Zlength coog)
    PARAMS( p; Vint (Int.repr a); Vint (Int.repr b))
    SEP (data_at sh (Tarray (Tstruct  _rowcol noattr) (Zlength coog) noattr) (map Zpair_to_valpair coog) p)
 POST [ tvoid ]
    PROP ()
    RETURN( )
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog) noattr) (map Zpair_to_valpair (upd_Znth a (upd_Znth b coog (Znth a coog)) (Znth b coog))) p).

(* compare with the one in the repo that's verified *)
Definition coog_quicksort_spec :=
 DECLARE _coog_quicksort
 WITH sh: share, coog: list (Z * Z), p: val, base: Z, n: Z
 PRE [ tptr (Tstruct _rowcol noattr), tuint, tuint ]
    PROP(writable_share sh;
         (* coo_matrix_wellformed coo; *)
         Zlength coog <= Int.max_unsigned;
         0 <= base; base <= base+n <= Zlength coog)
    PARAMS( p; Vint (Int.repr base); Vint (Int.repr n))
    SEP (data_at sh (Tarray (Tstruct  _rowcol noattr) (Zlength coog) noattr) (map Zpair_to_valpair coog) p)
 POST [ tvoid ]
   EX coog': list (Z * Z),
    PROP(Permutation coog coog'; 
         sorted coord2_le ((sublist base (base+n) coog')))
    RETURN( )
    SEP (data_at sh (Tarray (Tstruct  _rowcol noattr) (Zlength coog) noattr) (map Zpair_to_valpair coog') p).

Definition coog_count_spec :=
 DECLARE _coog_count
 WITH sh: share, coog: list (Z * Z), p: val
 PRE [ tuint, tptr (Tstruct _rowcol noattr) ]
    PROP(writable_share sh;
         0 <= Zlength coog <= Int.max_unsigned;
         Forall rowcol_range coog;
         sorted coord2_le coog)
    PARAMS(Vint (Int.repr (Zlength coog)); p)
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog) noattr) (map Zpair_to_valpair coog) p)
 POST [ tuint ]
    PROP()
    RETURN( Vint (Int.repr (count_distinct  coog)) )
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog) noattr) (map Zpair_to_valpair coog) p).

Definition start_coog_spec :=
  DECLARE _start_coog
  WITH n : Z, gv : globals
  PRE [tuint]
    PROP (0 <= n <= Int.max_unsigned)
    PARAMS (Vint (Int.repr n))
    GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [tptr (Tstruct _rowcol noattr)]
    EX p : val,
    PROP ()
    RETURN (p)
    SEP (mem_mgr gv; 
      malloc_token Ews (Tarray (Tstruct _rowcol noattr) n noattr) p;
      data_at_ Ews (Tarray (Tstruct _rowcol noattr) n noattr) p)
    .

Definition add_to_coog_spec :=
  DECLARE _add_to_coog
  WITH sh : share, coog : list (Z * Z), p : val, r : Z, c : Z, maxn : Z
  PRE [tptr (Tstruct _rowcol noattr), tuint, tuint, tuint]
    PROP (0 <= Zlength coog < maxn;
      0 <= maxn <= Int.max_unsigned;
      Forall rowcol_range coog;
      writable_share sh)
    PARAMS (p; Vint (Int.repr (Zlength coog)); Vint (Int.repr r); Vint (Int.repr c))
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) maxn noattr) (map Zpair_to_valpair coog ++ Zrepeat (Vundef, Vundef) (maxn - Zlength coog)) p)
  POST [tvoid]
    PROP ()
    RETURN ()
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) maxn noattr) 
    (map Zpair_to_valpair coog ++ [Zpair_to_valpair (r, c)] ++ (Zrepeat (Vundef, Vundef) (maxn - Zlength coog - 1))) p ).


Definition t_csr := Tstruct _csr_matrix noattr.

Definition csrg_rep' sh (csr: csr_matrix Tdouble) (v: val) (ci: val) (rp: val) (p: val) :=
  data_at sh t_csr (v,(ci,(rp,(Vint (Int.repr (csr_rows csr)), Vint (Int.repr (csr_cols csr)))))) p *
  data_at_ sh (tarray tdouble (Zlength (csr_col_ind csr))) v * 
  data_at sh (tarray tuint (Zlength (csr_col_ind csr))) (map Vint (map Int.repr (csr_col_ind csr))) ci *
  data_at sh (tarray tuint (csr_rows csr + 1)) (map Vint (map Int.repr (csr_row_ptr csr))) rp.

Definition csrg_rep (sh: share) (csr: csr_matrix Tdouble) (p: val) : mpred :=
  EX v: val, EX ci: val, EX rp: val,
  csrg_rep' sh csr v ci rp p.

Definition csrg_token (csr: csr_matrix Tdouble) (p: val) : mpred :=
 EX v: val, EX ci: val, EX rp: val,
    csrg_rep' Ews csr v ci rp p -*
    (csrg_rep' Ews csr v ci rp p
     * (spec_malloc.malloc_token Ews t_csr p *
        spec_malloc.malloc_token Ews (tarray tdouble (Zlength (csr_vals csr))) v *
        spec_malloc.malloc_token Ews (tarray tuint (Zlength (csr_vals csr))) ci *
        spec_malloc.malloc_token Ews (tarray tuint (csr_rows csr + 1)) rp)).

Definition csr_rep' sh (csr: csr_matrix Tdouble) (v: val) (ci: val) (rp: val) (p: val) :=
  data_at sh t_csr (v,(ci,(rp,(Vint (Int.repr (csr_rows csr)), Vint (Int.repr (csr_cols csr)))))) p *
  data_at sh (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) v * 
  data_at sh (tarray tuint (Zlength (csr_col_ind csr))) (map Vint (map Int.repr (csr_col_ind csr))) ci *
  data_at sh (tarray tuint (csr_rows csr + 1)) (map Vint (map Int.repr (csr_row_ptr csr))) rp.

Definition csr_rep (sh: share) (csr: csr_matrix Tdouble) (p: val) : mpred :=
  EX v: val, EX ci: val, EX rp: val,
  csr_rep' sh csr v ci rp p.


Definition coog_to_csrg_aux_spec := 
  DECLARE _coog_to_csrg_aux
  WITH sh1 : share, sh2 : share, coog : coog_matrix, p : val, pc : val, pr : val, gv : globals
  PRE [tptr (Tstruct _rowcol noattr), tuint, tuint, tptr tuint, tptr tuint]
    PROP ( writable_share sh1; readable_share sh2;
      coog_matrix_wellformed coog;
      coog_rows coog < Int.max_unsigned; 
      coog_cols coog < Int.max_unsigned;
      Zlength (coog_entries coog) < Int.max_unsigned;
      sorted coord2_le (coog_entries coog))
    PARAMS (p; Vint (Int.repr (Zlength (coog_entries coog))); Vint (Int.repr (coog_rows coog)); pc; pr)
    GLOBALS (gv)
    SEP (data_at sh2 (Tarray (Tstruct _rowcol noattr) (Zlength (coog_entries coog)) noattr) (map Zpair_to_valpair (coog_entries coog)) p;
         data_at_ sh1 (Tarray tuint (count_distinct (coog_entries coog)) noattr) pc;
         data_at_ sh1 (Tarray tuint ((coog_rows coog) + 1) noattr) pr; 
         mem_mgr gv (* this is not really needed *) )
  POST [Tvoid]
    EX rowptr : list val,
    EX colind : list val,
    PROP (partial_CSRG (Zlength (coog_entries coog)) (coog_rows coog) coog rowptr colind)
    RETURN ()
    SEP (data_at sh2 (Tarray (Tstruct _rowcol noattr) (Zlength (coog_entries coog)) noattr) (map Zpair_to_valpair (coog_entries coog)) p;
         data_at sh1 (Tarray tuint (count_distinct (coog_entries coog)) noattr) colind pc;
         data_at sh1 (Tarray tuint (coog_rows coog + 1) noattr) rowptr pr;
         mem_mgr gv).

Definition coog_to_csrg_spec :=
  DECLARE _coog_to_csrg 
  WITH sh : share, coog : list (Z * Z), p : val, rows : Z, cols : Z, gv : globals
  PRE [tptr (Tstruct _rowcol noattr), tuint, tuint, tuint]
    PROP ( writable_share sh; 
      coog_matrix_wellformed (Build_coog_matrix rows cols coog);
      rows < Int.max_unsigned;
      cols < Int.max_unsigned;
      Zlength coog < Int.max_unsigned)
    PARAMS (p; Vint (Int.repr (Zlength coog)); Vint (Int.repr rows); Vint (Int.repr cols))
    GLOBALS (gv)
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog) noattr) (map Zpair_to_valpair coog) p; mem_mgr gv)
  POST [tptr (Tstruct _csr_matrix noattr)]
    EX coog' : list (Z * Z),
    EX csrg : csr_matrix Tdouble,
    EX q : val,
    PROP (Permutation coog coog';
      coog_csr (Build_coog_matrix rows cols coog') csrg)
    RETURN (q)
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog') noattr) (map Zpair_to_valpair coog') p; 
      csrg_rep Ews csrg q; 
      csrg_token csrg q;
      mem_mgr gv).

(* Ews: extern write share (for newly malloced object) *)


Definition csr_same_graph {t : type} (csr1 csr2 : csr_matrix t) :=
  csr_cols csr1 = csr_cols csr2 /\
  csr_col_ind csr1 = csr_col_ind csr2 /\
  csr_row_ptr csr1 = csr_row_ptr csr2.


From LAProof.accuracy_proofs Require Import mv_mathcomp.
From mathcomp Require ssreflect.
Import fintype matrix.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Definition reset_csr_spec := 
  DECLARE _reset_csr
  WITH sh : share, csr : csr_matrix Tdouble, q : val, gv : globals
  PRE [tptr (Tstruct _csr_matrix noattr)]
    PROP (writable_share sh)
    PARAMS (q)
    SEP (csrg_rep sh csr q; csrg_token csr q; mem_mgr gv)
  POST [Tvoid]    
    EX csr' : csr_matrix Tdouble,
    EX X : {mn : nat * nat & 'M[ftype Tdouble]_(fst mn, snd mn)}%type,
    let '(existT _ (rows, cols) m) := X in 
    PROP (csr_same_graph csr csr'; csr_to_M csr' m;
          forall i j, m i j = Zconst Tdouble 0)
    RETURN ()
    SEP (csr_rep sh csr' q; csrg_token csr' q; mem_mgr gv).


Definition rc_in_csrg {t} (r c : Z) (csrg : csr_matrix t) : Prop :=
  0 <= r < csr_rows csrg /\
  0 <= c < csr_cols csrg /\
  In c (sublist (Znth r (csr_row_ptr csrg)) (Znth (r+1) (csr_row_ptr csrg)) (csr_col_ind csrg)).  

Fixpoint find_index (c : Z) (l : list Z) : Z :=
  match l with
  | nil => 0
  | h :: t => if Z.eqb h c then 0 else 1 + find_index c t
  end.

(* predicate only using csr *)
Definition add_rcx_to_csr_rel' {t} (r c : Z) (x : ftype t) 
  (csr csr' : csr_matrix t) : Prop := 
  rc_in_csrg r c csr /\
  csr_same_graph csr csr' /\
  let vi := Znth r (csr_row_ptr csr) + 
    find_index c (sublist (Znth r (csr_row_ptr csr)) (Znth (r+1) (csr_row_ptr csr)) (csr_col_ind csr)) in 
  feq (BPLUS (Znth vi (csr_vals csr)) x) (Znth vi (csr_vals csr')) /\
  forall i, 0 <= i < Zlength (csr_vals csr) -> i <> vi -> (Znth i (csr_vals csr)) = (Znth i (csr_vals csr')).

Definition add_rcx_to_csr_rel {t : type} {rows cols : nat} (r c : Z) (x : ftype t) 
  (m m' : 'M[ftype t]_(rows, cols)) : Prop :=
  exists csr csr', 
  csr_to_M csr m /\ csr_to_M csr' m' /\
  add_rcx_to_csr_rel' r c x csr csr'.

Definition add_to_csr_spec :=
  DECLARE _add_to_csr
  WITH sh : share, 
    csr : csr_matrix Tdouble, csr' : csr_matrix Tdouble, r : Z, c : Z, 
    x : ftype Tdouble, q : val, gv : globals,
    X : {mn : nat * nat & 'M[ftype Tdouble]_(fst mn, snd mn) * 'M[ftype Tdouble]_(fst mn, snd mn)}%type
  PRE [tptr (Tstruct _csr_matrix noattr), tuint, tuint, tdouble]
    let '(existT _ (rows, cols) (m, m')) := X in 
    PROP (writable_share sh; rc_in_csrg r c csr; csr_to_M csr m)
    PARAMS (q; Vint (Int.repr r); Vint (Int.repr c); Vfloat x)
    SEP (csr_rep sh csr q; csrg_token csr q; mem_mgr gv)
  POST [Tvoid]
    EX csr' : csr_matrix Tdouble,
    let '(existT _ (rows, cols) (m, m')) := X in 
    PROP (writable_share sh; add_rcx_to_csr_rel r c x m m'; csr_to_M csr' m')
    RETURN ()
    SEP (csr_rep sh csr' q; csrg_token csr' q; mem_mgr gv). 

(* m' cannot be existentially quantified in the post-condition *)
(* since otherwise the size of m' will be represented with different variables *)
(* and add_rcs_to_csr_rel will not type check *)

Definition surely_malloc_spec :=
  DECLARE _surely_malloc
   WITH t:Ctypes.type, gv: globals
   PRE [ size_t ]
       PROP (0 <= sizeof t <= Ptrofs.max_unsigned;
                complete_legal_cosu_type t = true;
                natural_aligned natural_alignment t = true)
       PARAMS (Vptrofs (Ptrofs.repr (sizeof t))) GLOBALS (gv)
       SEP (mem_mgr gv)
    POST [ tptr tvoid ] EX p:_,
       PROP ()
       LOCAL (temp ret_temp p)
       SEP (mem_mgr gv; malloc_token Ews t p * data_at_ Ews t p).

Definition Build_CSR2_ASI : funspecs := [
  surely_malloc_spec; swap_rc_spec; coog_quicksort_spec; 
  coog_count_spec; start_coog_spec; add_to_coog_spec;
  coog_to_csrg_aux_spec; coog_to_csrg_spec
].