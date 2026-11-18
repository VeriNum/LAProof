(**  * LAProof.C.spec_sparsemat: VST specifications of functions on two-phase sparse matrices. *)
(** ** Corresponds to C program [sparsemat.h] and [sparsemat.c] *)
Require Import VST.floyd.proofauto.
From VSTlib Require Import spec_malloc.
From LAProof.C Require Import sparsemat floatlib sparse_model spec_alloc spec_sparse.
From vcfloat Require Import FPStdCompCert FPStdLib.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

(** [coo_rep'] is the body of [spec_sparse.coo_rep] with the capacity and array
  pointers exposed, so that [coo_tokens] can refer to them.
  It is stated before this file's [CompSpecs] instance, so it uses [spec_sparse.CompSpecs]
  and [coo_rep_eq] holds by [reflexivity]. *)
Definition coo_rep' (sh: share) (coo: coo_matrix Tdouble) (maxn: Z) (rp cp vp: val) (p: val) : mpred :=
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

Lemma coo_rep_eq: forall sh coo p,
  coo_rep sh coo p = EX (maxn: Z) (rp cp vp: val), coo_rep' sh coo maxn rp cp vp p.
Proof. reflexivity. Qed.

(** The malloc tokens of a COO matrix depend only on its capacity, not its contents,
  so they survive [add_to_coo_matrix] and sorting. *)
Definition coo_tokens (sh: share) (maxn: Z) (rp cp vp: val) (p: val) : mpred :=
  malloc_token sh t_coo p *
  malloc_token sh (tarray tuint maxn) rp *
  malloc_token sh (tarray tuint maxn) cp *
  malloc_token sh (tarray tdouble maxn) vp.

(** Likewise, the malloc tokens of a CSR matrix depend only on its shape
  (number of stored entries and rows), unlike [spec_sparse.csr_token],
  so they survive changes to the stored values.
  The array types match those in [spec_sparse.csr_rep']. *)
Definition csr_tokens (sh: share) (csr: csr_matrix Tdouble) (v ci rp: val) (p: val) : mpred :=
  malloc_token sh t_csr p *
  malloc_token sh (tarray tdouble (Zlength (csr_col_ind csr))) v *
  malloc_token sh (tarray tuint (Zlength (csr_col_ind csr))) ci *
  malloc_token sh (tarray tuint (csr_rows csr + 1)) rp.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_sparsemat := Tstruct _sparsemat_t noattr.

(** ** The COO phase (graph not yet fixed) *)

(** [sparsemat_coo sh coo p]: [p] is a [sparsemat_t] whose graph is not yet fixed,
  holding the triples of [coo].  The value at [(i,j)] is any sum ([sum_any]) of the
  triples at [(i,j)], and the graph is the set of their positions.
  The capacity is hidden, as in [spec_sparse.coo_rep]; [add_to_coo_matrix]
  exits when it is exceeded. *)
Definition sparsemat_coo (sh: share) (coo: coo_matrix Tdouble) (p: val) : mpred :=
  EX (q: val) (maxn: Z) (rp cp vp: val),
    field_at sh t_sparsemat (DOT _graph_fixed) (Vint (Int.repr 0)) p *
    field_at sh t_sparsemat (UnionField _coo :: DOT _u)%gfield q p *
    malloc_token sh t_sparsemat p *
    coo_rep' sh coo maxn rp cp vp q *
    coo_tokens sh maxn rp cp vp q.

(** ** The CSR phase (graph fixed) *)

(** [sparsemat_csr sh csr p]: [p] is a [sparsemat_t] whose graph is fixed,
  holding the CSR matrix [csr].  The graph is the set of positions
  [(i, Znth k (csr_col_ind csr))] for [k] in row [i]; [csr_matrix_wellformed]
  makes the column indices in each row strictly increasing, as [csr_find] needs. *)
Definition sparsemat_csr (sh: share) (csr: csr_matrix Tdouble) (p: val) : mpred :=
  EX (q: val) (v ci rp: val),
    !! csr_matrix_wellformed csr &&
    field_at sh t_sparsemat (DOT _graph_fixed) (Vint (Int.repr 1)) p *
    field_at sh t_sparsemat (UnionField _csr :: DOT _u)%gfield q p *
    malloc_token sh t_sparsemat p *
    csr_rep' sh csr v ci rp q *
    csr_tokens sh csr v ci rp q.

(** ** Either phase *)

(** A [sparsemat] is [inl coo] before the graph is fixed, [inr csr] after. *)
Definition sparsemat := (coo_matrix Tdouble + csr_matrix Tdouble)%type.

Definition sparsemat_rep (sh: share) (s: sparsemat) (p: val) : mpred :=
  match s with
  | inl coo => sparsemat_coo sh coo p
  | inr csr => sparsemat_csr sh csr p
  end.

(** ** Memory management *)

Definition sparsemat_malloc_spec :=
  DECLARE _sparsemat_malloc
  WITH m: Z, n: Z, maxn: Z, gv: globals
  PRE [ tint, tint, tint ]
    PROP(0 <= m < Int.max_signed;
         0 <= n < Int.max_signed;
         0 <= maxn <= Int.max_signed)
    PARAMS (Vint (Int.repr m); Vint (Int.repr n); Vint (Int.repr maxn)) GLOBALS (gv)
    SEP( mem_mgr gv )
  POST [ tptr t_sparsemat ]
   EX p: val,
    PROP ()
    RETURN (p)
    SEP(sparsemat_coo Ews (Build_coo_matrix _ m n nil) p; mem_mgr gv).

(** [sparsemat_free] works in either phase. *)
Definition sparsemat_free_spec :=
  DECLARE _sparsemat_free
  WITH s: sparsemat, p: val, gv: globals
  PRE [ tptr t_sparsemat ]
    PROP ()
    PARAMS (p) GLOBALS (gv)
    SEP(sparsemat_rep Ews s p; mem_mgr gv)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP(mem_mgr gv).
