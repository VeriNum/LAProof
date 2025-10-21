(**  * LAProof.C.spec_densemat: VST specifications of functions on dense matrices. *)
(** ** Corresponds to C program [densemat.h] and [densemat.c] *)
(** Among other things, this .v file serves as a demonstration of how to write VST specifications
  of functions with respect to a functional model expressed using the MathComp matrix library.
  To do that, we start by importing the usual things that one would import into a VST funspecs
 file, including in this case [densemat.v] which is the result of using [clightgen] to translate
 [densemat.c] into a Clight abstract syntax tree.
*)
Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math spec_malloc.
From LAProof.C Require Import densemat spec_alloc floatlib matrix_model.
Require Import Coq.Classes.RelationClasses.

(** We [Require] the [mathcomp] files, but without [Import] because we don't want
   to use [ssreflect] tactics in VST proofs, and we don't want the namespace polluted with
   all that mathcomp stuff.
*) 
From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
(** Among all the mathcomp stuff, these are the files that we *do* want to Import: *)
Import fintype matrix.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(** The next lines are usual in VST specification files *)
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

(** In a typical VST proof, many variables and operators have type [Z] and few have type [nat],
  so there are not many coercions between [Z] and [nat].  In a MathComp proof, there are many
  uses of ordinals ['I_n], which coerce naturally to [nat]; but the VST operators still prefer [Z].
  So there is more motivation (than usual in VST) to implicitly coerce [nat] to [Z]. 
*) 
Coercion Z.of_nat : nat >-> Z.

(** ** Abstracting the floating-point precision *)
(** C programs may use single precision or double precision.
  This chart covers different wa7ys to talk about these types.
<<
Ctypes.floatsize      F64        F32
Ctypes.type           tdouble    tsingle   (= Tfloat Fxx noattr, where Fxx=F64 or F32)
CompCert Type         float      float32
Values.val            Vfloat     Vsingle
vcfloat.FPStdLib.type Tdouble    Tsingle
>>
[ftype Tdouble] is convertible to [float], and [ftype Tsingle] is convertible to [float32].
*)

(** To make our specifications (mostly) portable to C programs that use F64 or F32,
  we define [the_ctype] as either [tdouble] or [tsingle], depending on what type
  the program uses for the [data] field of dense matrices.  The [nested_field_type]
  computation in the definition of [the_ctype] goes looking for that. *) 

Definition densemat_t := Tstruct _densemat_t noattr.

Definition the_ctype := ltac:(
    let d := constr:(nested_field_type densemat_t (DOT _data SUB 0))
     in let d := eval compute in d 
     in first [ unify d tdouble; exact tdouble
              | unify d tfloat; exact tfloat
              ]).

(** Corresponding to [the_ctype] is [the_type], which is the description of that
 type's exponent size and mantissa size, per VCFloat. *)

Definition the_type := 
  ltac:(first [ unify the_ctype tdouble; exact Tdouble
              | unify the_ctype tsingle; exact Tsingle
              ]).

(** There is a correspondence between a [Ctypes.type] and a [vcfloat.FPStdLib.type] *)

Definition ctype_of_type (t: type) : Ctypes.type :=
 if type_eq_dec t Tdouble then tdouble
 else if type_eq_dec t Tsingle then tfloat
 else tvoid.


Local Remark about_the_ctype: the_ctype=tdouble \/ the_ctype=tfloat.
Proof. auto. Qed.

Local Remark ctype_of_the_type: ctype_of_type the_type = the_ctype.
Proof. reflexivity. Qed.

(** ** Conversions between floats, float-options, and [val] *)
(* We use [ftype t] as the type of floating-point values in format [t].
  However, some arrays and matrices may be partially initialized, so we also
 need [option (ftype t)] as the type of maybe-intialized floats.

  CompCert's [val] type allows injecting double- and single-precision floats, and has
  a separate constructor for uninitialized values of any type:
<<
Inductive val : Type :=
    Vundef : val
  | Vint : int -> val
  | Vlong : int64 -> val
  | Vfloat : float -> val     (*  recall that   float = ftype Tdouble *)
  | Vsingle : float32 -> val   (* recall that float32 = ftype Tsingle *)
  | Vptr : block -> ptrofs -> val.
>>
So therefore we need several functions that can convert between [ftype t], [option (ftype t)], and [val]
*)

Definition val_of_float {t} (f: ftype t) : val :=
match type_eq_dec t Tdouble with
     | left e =>
          eq_rect_r (fun t0 : type => ftype t0 -> val)
            (fun f1 : ftype Tdouble => Vfloat f1) e f
     | right _ =>
          match type_eq_dec t Tsingle with
          | left e =>
               eq_rect_r (fun t0 : type => ftype t0 -> val)
                 (fun f1 : ftype Tsingle => Vsingle f1) e f
          | right _ => Vundef
          end
     end.

Definition val_of_optfloat {t} (x: option (ftype t)) : val :=
match x with
| Some f => val_of_float f
| None => Vundef
end.

(** An arbitrary NaN value with the least informative payload *)
Lemma nan_pl_1: forall t, eq (Binary.nan_pl (fprec t) 1) true.
Proof.
intros.
unfold Binary.nan_pl, fprec.
simpl.
pose proof fprecp_not_one t.
lia.
Qed.

Definition nan1 (t: type) := Binary.B754_nan (fprec t) (femax t) false _ (nan_pl_1 t).

Definition optfloat_to_float {t: type} (x: option (ftype t)) := 
  match x with
  | Some y => y
  | None => nan1 t
  end.

(** [reptype_ftype] is a convertible (transparent) coercion, useful in [data_at] *) 
Definition reptype_ftype {t: type} (n: Z): list val -> reptype (tarray (ctype_of_type t) n).
intro vl.
unfold ctype_of_type.
repeat if_tac.
apply vl.
apply vl.
apply (Zrepeat tt n).
Defined.

(** Here's a proof that it really is a convertible equality *)
Local Remark about_reptype_ftype: forall vl, @reptype_ftype the_type (Zlength vl) vl = vl.
Proof. reflexivity. Qed.


(** ** Representation predicates for dense matrices *)
(** Let [A: 'M_(m,n)] be a matrix of floats, and [p: val] be an address.
  We want a _Verifiable C_ representation predicate [densemat] saying that [A] is
  represented in memory at address [p] using the C type [densemat_t],
  in column-major order, perhaps only partially initialized, with access permission [sh].

  Furthermore, for those functions whose name begins with [densematn], which
  don't pass the address of the [struct densemat_t] but pass only the address of
  an array (such as the [data] field of a [densemat_t], we want a representation
  predicate [densematn].

  This section develops these predicates, step by step.
*)

Definition densemat_data_offset := 
  ltac:(let x := constr:(nested_field_offset densemat_t (DOT _data))
        in let y := eval compute in x in exact y).

Local Remark check_densemat_layout:
  forall sh m n (x: list val) p, 
    data_at sh (Tstruct _densemat_t noattr) (Vint m,(Vint n,x)) p 
  |-- field_at sh (Tstruct _densemat_t noattr) (DOT _m) (Vint m) p *
    field_at sh (Tstruct _densemat_t noattr) (DOT _n) (Vint n) p.
(** This lemma could fail if there's padding between the fields. *)
Proof.
intros.
unfold_data_at (data_at _ _ _ _).
cancel.
entailer!.
rewrite value_fits_eq in H0. simpl in H0. destruct H0 as [? _].
change (unfold_reptype _) with x in H0.
destruct x; [ | list_solve].
unfold field_at. simpl.
entailer!!.
unfold data_at_rec. simpl.
unfold at_offset.
change (unfold_reptype _) with (@nil val).
rewrite array_pred_len_0; auto.
Qed.

Definition column_major {T} [rows cols: nat] (f: 'M[T]_(rows,cols)) :=
 concat (map (fun j => map (fun i => f i j) (ord_enum rows)) (ord_enum cols)).

(** Spatial predicate (mpred) to represent the [data] field of a [struct densemat_t] *)
Definition densematn {t: type} (sh: share) [m n] (M: 'M[option (ftype t)]_(m,n)) (p: val) : mpred :=
 !! (0 < m <= Int.max_signed /\ 0 < n <= Int.max_signed /\ m * n <= Int.max_signed)
 && data_at sh (tarray (ctype_of_type t) (m*n))
      (reptype_ftype (m*n) (map (@val_of_optfloat t) (column_major M)))
      p.

(** Spatial predicate (mpred) to represent an entire [struct densemat_t] *)
Definition densemat (sh: share) [m n] (M: 'M[option (ftype the_type)]_(m,n))
     (p: val) : mpred :=
     field_at sh (Tstruct _densemat_t noattr) (DOT _m) (Vint (Int.repr m)) p
   * field_at sh (Tstruct _densemat_t noattr) (DOT _n) (Vint (Int.repr n)) p
   * densematn sh M (offset_val densemat_data_offset p)
   * malloc_token' sh (densemat_data_offset + sizeof (tarray the_ctype (Z.of_nat m * Z.of_nat n))) p.

(** As usual with new spatial predicates, populate the Hint databases [saturate_local] and [valid_pointer] *)
Definition densematn_local_facts: forall {t} sh m n M p,
  @densematn t sh m n M p |-- 
      !! (0 < m <= Int.max_signed 
          /\ 0 < n <= Int.max_signed
          /\ m*n <= Int.max_signed
          /\ field_compatible (tarray (ctype_of_type t) (m*n)) [] p).
Proof.
intros.
unfold densematn.
entailer!.
Qed.

Definition densemat_local_facts: forall sh m n M p,
  @densemat sh m n M p |-- 
      !! (0 < m <= Int.max_signed 
          /\ 0 < n <= Int.max_signed
          /\ m*n <= Int.max_signed
          /\ malloc_compatible (densemat_data_offset + sizeof (tarray the_ctype (m*n))) p).
Proof.
intros.
unfold densemat, densematn.
entailer!.
Qed.

#[export] Hint Resolve densematn_local_facts densemat_local_facts : saturate_local.

Lemma densematn_valid_pointer:
  forall t sh m n M p,
   sepalg.nonidentity sh ->
   @densematn t sh m n M p |-- valid_pointer p.
Proof.
 intros.
 unfold densematn.
 Intros.
 apply data_at_valid_ptr; auto.
 unfold ctype_of_type.
 repeat if_tac; simpl; lia.
Qed.

Lemma densemat_valid_pointer:
  forall sh m n M p,
   @densemat sh m n M p |-- valid_pointer p.
Proof.
 intros.
 unfold densemat. entailer!.
Qed.

#[export] Hint Resolve densematn_valid_pointer densemat_valid_pointer : valid_pointer.

(** * Function specifications (funspecs) *)
(** Compare these to the function headers in [densemat.h] *)

(** [densemat_malloc] takes [m] and [n] such that [m*n] is representable as a signed integer, 
    and returns an uninitialized [m*n] matrix. *)
Definition densemat_malloc_spec :=
  DECLARE _densemat_malloc
  WITH m: nat, n: nat, gv: globals
  PRE [ tint, tint ]
    PROP(0 < m <= Int.max_signed;
         0 < n <= Int.max_signed;
         m*n <= Int.max_signed)
    PARAMS (Vint (Int.repr m); Vint (Int.repr n) ) GLOBALS (gv)
    SEP( mem_mgr gv )
  POST [ tptr densemat_t ]
   EX p: val,
    PROP () 
    RETURN (p) 
    SEP(densemat Ews (@const_mx (option(ftype the_type)) m n None) p; mem_mgr gv).

(** [densemat_free] takes an m*n matrix and returns nothing.

    This funspec illustrates how we must handle dependently typed WITH clauses.
    That is, the bound variables of this specification include a dimension (m,n) and
    a matrix of type ['M_(m,n)].  Because VST's [WITH] clauses cannot handle dependent
    typing among the separate bound variables, we package this up as a [sigT] named [X].
    Then, to extract the bounds from [X] part we use [projT1], and to extract the matrix
    we use [projT2]. *)
Definition densemat_free_spec :=
  DECLARE _densemat_free
  WITH X: {mn & 'M[option (ftype the_type)]_(fst mn, snd mn)}, p: val, gv: globals
  PRE [ tptr densemat_t ]
    PROP() 
    PARAMS ( p ) GLOBALS (gv)
    SEP(densemat Ews (projT2 X) p; mem_mgr gv)
  POST [ tvoid ]
    PROP () 
    RETURN () 
    SEP( mem_mgr gv ).

(** [densematn_clear] takes just the [data] part of an m*n matrix and 
   sets all its elements to floating-point zero.  Therefore, as with all [densematn] operations,
   we need to pass bounds information as function parameters.   

   The [let '(existT _ ...)] unpacks the components of [X].  Due to a limitation in VST's notation system,
  We have to repeat this unpacking separately in the PRE and POST clauses. *)
Definition densematn_clear_spec :=
  DECLARE _densematn_clear
  WITH X: {mn & 'M[option (ftype the_type)]_(fst mn, snd mn)}, p: val, sh: share
  PRE [ tptr the_ctype, tint, tint ] let '(existT _ (m,n) M) := X in
    PROP(writable_share sh) 
    PARAMS (p; Vint (Int.repr m); Vint (Int.repr n))
    SEP(densematn sh M p)
  POST [ tvoid ] let '(existT _ (m,n) M) := X in
    PROP () 
    RETURN () 
    SEP(densematn sh (@const_mx _ m n (Some (Zconst the_type 0))) p).

(** [densemat_clear] takes just the struct (with bounds information) of an m*n matrix and 
   sets all its elements to floating-point zero. *)
Definition densemat_clear_spec :=
  DECLARE _densemat_clear
  WITH X: {mn & 'M[option (ftype the_type)]_(fst mn, snd mn)}, p: val, sh: share
  PRE [ tptr densemat_t ] let '(existT _ (m,n) M) := X in 
    (PROP(writable_share sh) 
    PARAMS (p)
    SEP(densemat sh M p))
   POST [ tvoid ] let '(existT _ (m,n) M) := X in 
    PROP () 
    RETURN () 
    SEP(densemat sh (@const_mx _ m n (Some (Zconst the_type 0))) p).

(** [densematn_get] fetches the (i,j) component of a matrix.  Since the matrix is in column-major
    order, we must also pass the number of rows [m].  Since this function does not do bounds-checking,
    there is no need to also pass the number of columns [n].  In principle, since we are proving the 
   program correct, there's no need for dynamic bounds checking.  

  The precondition of the function enforces that [0 <= i < m] and [0 <= j < n].  It does so by construction
   of the dependently typed value [X], where the last component is a pair [(i: 'I_[m], j: 'I[n]).
    *)
Definition densematn_get_spec :=
  DECLARE _densematn_get
  WITH X: {mn : nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)) }%type,
        p: val, sh: share, x: ftype the_type
  PRE [ tptr the_ctype , tint, tint, tint ] let '(existT _ (m,n) (M,(i,j))) := X in
    PROP(readable_share sh; M i j = Some x)
    PARAMS (p ; Vint (Int.repr m); Vint (Int.repr i); Vint (Int.repr j))
    SEP(densematn sh M p)
  POST [ the_ctype ] let '(existT _ (m,n) (M,(i,j))) := X in
    PROP () 
    RETURN (val_of_float x) 
    SEP(densematn sh M p).

Definition densemat_get_spec :=
  DECLARE _densemat_get
  WITH X: {mn : nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)) }%type,
        p: val, sh: share, x: ftype the_type
  PRE [ tptr densemat_t , tint, tint ] let '(existT _ (m,n) (M,(i,j))) := X in
    PROP(readable_share sh; M i j = Some x)
    PARAMS (p ; Vint (Int.repr i); Vint (Int.repr j))
    SEP(densemat sh M p)
  POST [ the_ctype ]  let '(existT _ (m,n) (M,(i,j))) := X in
    PROP () 
    RETURN (val_of_float x) 
    SEP(densemat sh M p).

Definition densematn_set_spec :=
  DECLARE _densematn_set
  WITH X: {mn : nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)) }%type,
       p: val, sh: share, x: ftype the_type
  PRE [ tptr the_ctype, tint, tint, tint, the_ctype ] let '(existT _ (m,n) (M,(i,j))) := X in
    PROP(writable_share sh) 
    PARAMS (p ; Vint (Int.repr m); Vint (Int.repr i); Vint (Int.repr j); val_of_float x)
    SEP(densematn sh M p)
  POST [ tvoid ] let '(existT _ (m,n) (M,(i,j))) := X in
    PROP () 
    RETURN () 
    SEP(densematn sh (update_mx M i j (Some x)) p).

Definition densemat_set_spec :=
  DECLARE _densemat_set
  WITH X: {mn : nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)) }%type,
       p: val, sh: share, x: ftype the_type
  PRE [ tptr densemat_t, tint, tint, the_ctype ] let '(existT _ (m,n) (M,(i,j))) := X in
    PROP(writable_share sh) 
    PARAMS (p ; Vint (Int.repr i); Vint (Int.repr j); val_of_float x)
    SEP(densemat sh M p)
  POST [ tvoid ] let '(existT _ (m,n) (M,(i,j))) := X in
    PROP () 
    RETURN () 
    SEP(densemat sh (update_mx M i j (Some x)) p).

Definition densematn_addto_spec :=
  DECLARE _densematn_addto
  WITH X: {mn : nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)) }%type,
       p: val, sh: share, y: ftype the_type, x: ftype the_type
  PRE [ tptr the_ctype, tint, tint, tint, the_ctype ] let '(existT _ (m,n) (M,(i,j))) := X in
    PROP(writable_share sh; M i j = Some y) 
    PARAMS (p ; Vint (Int.repr m); Vint (Int.repr i); Vint (Int.repr j); val_of_float x)
    SEP(densematn sh M p)
  POST [ tvoid ] let '(existT _ (m,n) (M,(i,j))) := X in
    PROP () 
    RETURN () 
    SEP(densematn sh (update_mx M i j (Some (BPLUS y x))) p).

Definition densemat_addto_spec :=
  DECLARE _densemat_addto
  WITH X: {mn : nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)) }%type,
       p: val, sh: share, y: ftype the_type, x: ftype the_type
  PRE [ tptr densemat_t, tint, tint, the_ctype ] let '(existT _ (m,n) (M,(i,j))) := X in
    PROP(writable_share sh; M i j = Some y) 
    PARAMS (p ; Vint (Int.repr i); Vint (Int.repr j);
            val_of_float x)
    SEP(densemat sh M p)
  POST [ tvoid ] let '(existT _ (m,n) (M,(i,j))) := X in
    PROP () 
    RETURN () 
    SEP(densemat sh (update_mx M i j (Some (BPLUS y x))) p).

Definition data_norm2_spec :=
  DECLARE _data_norm2
  WITH sh: share, v: list (ftype the_type), p: val
  PRE [ tptr the_ctype, tint ]
    PROP (readable_share sh; Zlength v <= Int.max_signed)
    PARAMS (p; Vint (Int.repr (Zlength v)))
    SEP(data_at sh (tarray the_ctype (Zlength v)) (map val_of_float v) p)
  POST [ the_ctype ]
    PROP() RETURN (val_of_float (norm2 v)) 
    SEP(data_at sh (tarray the_ctype (Zlength v)) (map val_of_float v) p).

Definition data_norm_spec :=
  DECLARE _data_norm
  WITH sh: share, v: list (ftype the_type), p: val
  PRE [ tptr the_ctype, tint ]
    PROP (readable_share sh; Zlength v <= Int.max_signed)
    PARAMS (p; Vint (Int.repr (Zlength v)))
    SEP(data_at sh (tarray the_ctype (Zlength v)) (map val_of_float v) p)
  POST [ the_ctype ]
    PROP() RETURN (Vfloat (FPStdLib.BSQRT(norm2 v))) 
    SEP(data_at sh (tarray the_ctype (Zlength v)) (map val_of_float v) p).

Definition frobenius_norm2 {t: type} [m n: nat] (M: matrix.matrix (ftype t) m n) :=
  norm2 (column_major M).

Definition frobenius_norm {t: type} [m n: nat] (M: matrix.matrix (ftype t) m n)  :=
  BSQRT (frobenius_norm2 M).

Definition densemat_norm2_spec :=
  DECLARE _densemat_norm2
  WITH sh: share, X: {mn & 'M[ftype the_type]_(fst mn, snd mn)}, p: val
  PRE [ tptr densemat_t ] let '(existT _ (m,n) M) := X in
    PROP (readable_share sh)
    PARAMS (p)
    SEP(densemat sh (map_mx Some M) p)
  POST [ the_ctype ] let '(existT _ (m,n) M) := X in
    PROP() RETURN (val_of_float (frobenius_norm2 M))
    SEP(densemat sh (map_mx Some M) p).

Definition densemat_norm_spec :=
  DECLARE _densemat_norm
  WITH sh: share, X: {mn & 'M[ftype the_type]_(fst mn, snd mn)}, p: val
  PRE [ tptr densemat_t ] let '(existT _ (m,n) M) := X in
    PROP (readable_share sh)
    PARAMS (p)
    SEP(densemat sh (map_mx Some M) p)
  POST [ the_ctype ] let '(existT _ (m,n) M) := X in
    PROP() RETURN (val_of_float (frobenius_norm M))
    SEP(densemat sh (map_mx Some M) p).

Definition densematn_cfactor_spec :=
 DECLARE _densematn_cfactor
 WITH sh: share, X: {n & 'M[option (ftype the_type)]_n}, p: val
 PRE [ tptr the_ctype, tint ] let '(existT _ n M) := X in
    PROP (writable_share sh;
          forall i j, isSome (mirror_UT M i j))
    PARAMS (p; Vint (Int.repr n))
    SEP (densematn sh M p)
 POST [ tvoid ] let '(existT _ n M) := X in
   EX R: 'M_n,
    PROP (cholesky_jik_spec (map_mx optfloat_to_float (mirror_UT M)) R)
    RETURN ()
    SEP (densematn sh (joinLU M (map_mx Some R)) p).

Definition densemat_cfactor_spec :=
 DECLARE _densemat_cfactor
 WITH sh: share, X: {n & 'M[option (ftype the_type)]_n}, p: val
 PRE [ tptr densemat_t ] let '(existT _ n M) := X in
    PROP (writable_share sh;
          forall i j, isSome (mirror_UT M i j))
    PARAMS (p)
    SEP (densemat sh M p)
 POST [ tvoid ] let '(existT _ n M) := X in
   EX R: 'M_n,
    PROP (cholesky_jik_spec (map_mx optfloat_to_float (mirror_UT M)) R)
    RETURN ()
    SEP (densemat sh (joinLU M (map_mx Some R)) p).

Definition densematn_csolve_spec :=
 DECLARE _densematn_csolve
 WITH rsh: share, sh: share, X: {n & 'M[option (ftype the_type)]_n * 'cV[ftype the_type]_n}%type,
      p: val, xp: val
 PRE [ tptr the_ctype, tptr the_ctype, tint ] let '(existT _ n (M,x)) := X in
    PROP (readable_share rsh; writable_share sh;
          forall i j, isSome (mirror_UT M i j))
    PARAMS (p; xp; Vint (Int.repr n))
    SEP (densematn rsh M p; densematn sh (map_mx Some x) xp)
 POST [ tvoid ] let '(existT _ n (M,x)) := X in
    PROP ()
    RETURN ()
    SEP (densematn rsh M p;
         densematn sh (map_mx Some 
                       (backward_subst (map_mx optfloat_to_float M)
                          (forward_subst (trmx (map_mx optfloat_to_float M)) x)))
           xp).

Definition densemat_csolve_spec :=
 DECLARE _densemat_csolve
 WITH rsh: share, sh: share, X: {n & 'M[option (ftype the_type)]_n * 'cV[ftype the_type]_n}%type,
      p: val, xp: val
 PRE [ tptr densemat_t, tptr the_ctype ] let '(existT _ n (M,x)) := X in
    PROP (readable_share rsh; writable_share sh;
          forall i j, isSome (mirror_UT M i j))
    PARAMS (p; xp)
    SEP (densemat rsh M p; densematn sh (map_mx Some x) xp)
 POST [ tvoid ] let '(existT _ n (M,x)) := X in
    PROP ()
    RETURN ()
    SEP (densemat rsh M p;
         densematn sh (map_mx Some 
                       (backward_subst (map_mx optfloat_to_float M)
                          (forward_subst (trmx (map_mx optfloat_to_float M)) x)))
           xp).

(** * Not-yet-specified functions *)

Definition densemat_lujac_spec : ident*funspec := 
 (_densemat_lujac, vacuous_funspec (Internal f_densemat_lujac)).
Definition densematn_lujac_spec : ident*funspec := 
 (_densematn_lujac, vacuous_funspec (Internal f_densematn_lujac)).
Definition densematn_print_spec : ident*funspec := 
 (_densematn_print, vacuous_funspec (Internal f_densematn_print)).
Definition densemat_print_spec : ident*funspec := 
 (_densemat_print, vacuous_funspec (Internal f_densemat_print)).
Definition densemat_lusolve_spec : ident*funspec := 
 (_densemat_lusolve, vacuous_funspec (Internal f_densemat_lusolve)).
Definition densematn_lusolve_spec : ident*funspec := 
 (_densematn_lusolve, vacuous_funspec (Internal f_densematn_lusolve)).
Definition densemat_lufactor_spec : ident*funspec := 
 (_densemat_lufactor, vacuous_funspec (Internal f_densemat_lufactor)).
Definition densematn_lufactor_spec : ident*funspec := 
 (_densematn_lufactor, vacuous_funspec (Internal f_densematn_lufactor)).
Definition densematn_lusolveT_spec : ident*funspec := 
 (_densematn_lusolveT, vacuous_funspec (Internal f_densematn_lusolveT)).
Definition densemat_lusolveT_spec : ident*funspec := 
 (_densemat_lusolveT, vacuous_funspec (Internal f_densemat_lusolveT)).
Definition blocksolve_spec : ident*funspec := 
 (_blocksolve, vacuous_funspec (Internal f_blocksolve)).
Definition subtractoff_spec : ident*funspec := 
 (_subtractoff, vacuous_funspec (Internal f_subtractoff)).
Definition densematn_cfactor_block_spec : ident*funspec := 
 (_densematn_cfactor_block, vacuous_funspec (Internal f_densematn_cfactor_block)).
Definition densematn_cfactor_outer_spec : ident*funspec := 
 (_densematn_cfactor_outer, vacuous_funspec (Internal f_densematn_cfactor_outer)).

(** * Building the "Abstract Specification Interface", the list of funspecs for this module *)

Definition densematASI : funspecs := [ 
   densemat_malloc_spec; densemat_free_spec; densematn_clear_spec; densemat_clear_spec;
   densemat_get_spec; densematn_get_spec;
   densemat_set_spec; densematn_set_spec;
   densemat_addto_spec; densematn_addto_spec;
   data_norm_spec; data_norm2_spec;
   densemat_norm_spec; densemat_norm2_spec;
   densemat_lujac_spec; densematn_lujac_spec;
   densemat_print_spec; densematn_print_spec;
   densemat_lusolve_spec; densematn_lusolve_spec;
   densemat_lufactor_spec; densematn_lufactor_spec;
   densemat_csolve_spec; densematn_csolve_spec;
   densemat_cfactor_spec; densematn_cfactor_spec;
   densemat_lusolveT_spec; densematn_lusolveT_spec;
   blocksolve_spec; subtractoff_spec; densematn_cfactor_block_spec; densematn_cfactor_outer_spec
    ].


