(**  * LAProof.C.spec_bandmat: VST specifications of functions on banded matrices. *)
(** ** Corresponds to C program [bandmat.h] and [bandmat.c] *)
Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math spec_malloc.
From LAProof.accuracy_proofs Require Import solve_model.
From LAProof.C Require Import bandmat spec_alloc floatlib matrix_model.
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

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

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
  the program uses for the [data] field of banded matrices.  The [nested_field_type]
  computation in the definition of [the_ctype] goes looking for that. *) 

Definition bandmat_t := Tstruct _bandmat_t noattr.

Definition the_ctype := ltac:(
    let d := constr:(nested_field_type bandmat_t (DOT _data SUB 0))
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

(*** (almost) copied from spec_densemat until here ***)
(*****************************************************)
Definition bandmat_data_offset := 
  ltac:(let x := constr:(nested_field_offset bandmat_t (DOT _data))
        in let y := eval compute in x in exact y).

(* Old version not being used anymore *)
(* TODO: replace option (ftype t) with T *)
(* Remark: might need None instead of Some (Zconst t 0), given that dense_to_band doesn't initialize them *)
(* Remark: we use (S m) for the size otherwise (@inord m (j+i)) creates issues *)
Definition banded_repr' (*{T}*) {t: type} [m: nat] (b: nat) (f: 'M[(*T*)option (ftype t)]_(S m,S m)) :=
 concat (map (fun j => (map (fun i => (*default*)Some (Zconst t 0)) (ord_enum (nat_of_ord j))) ++ (* repeat 0, j times *)
                         (* we put default's but technically it could be anything *)
                       (map (fun i => f i (@inord m (j+i))) (sublist 0 (S m-j) (ord_enum (S m)))))
             (ord_enum (S b))).

(* An attempt to have the matrix size m*m instead (S m) * (S m) by using auxiliary definitions. *)
Definition inord_add {m n : nat} (j : 'I_n) (i : 'I_(m-j)) : 'I_m.
apply (@Ordinal m (i+j)).
pose proof (ltn_ord i). lia.
Defined.

Definition inord_inj {m j : nat} (i : 'I_(m-j)) : 'I_m.
apply (@Ordinal m i). 
pose proof (ltn_ord i). lia.
Defined.

Definition banded_repr (*{T}*) {t: type} [m: nat] (b: nat) (f: 'M[(*T*)option (ftype t)]_(m,m)) :=
 concat (map (fun j => (map (fun i => (*default*)Some (Zconst t 0)) (ord_enum (nat_of_ord j))) ++
                       (map (fun (i : 'I_(m-j)) => f (@inord_inj m j i) (@inord_add m (S b) j i)) (ord_enum (m-j))))
             (ord_enum (S b))).

(** Spatial predicate (mpred) to represent the [data] field of a [struct bandmat_t] *)
Definition bandmatn {t: type} (sh: share) [m] (b: nat) (M: 'M[option (ftype t)]_(m,m)) (p: val) : mpred :=
 !! (0 < m <= Int.max_signed /\ m * S b <= Int.max_signed /\ trmx M = M /\ 
     forall (i j : 'I_m), j>i+b -> M i j = Some (Zconst t 0)) (* might need to be None instead *)
 && data_at sh (tarray (ctype_of_type t) (m * S b))
      (reptype_ftype (m * S b) (map (@val_of_optfloat t) (banded_repr b M)))
      p.

(** Spatial predicate (mpred) to represent an entire [struct bandmat_t] *)
Definition bandmat (sh: share) [m] (b: nat) (M: 'M[option (ftype the_type)]_(m, m))
     (p: val) : mpred :=
     field_at sh (Tstruct _bandmat_t noattr) (DOT _m) (Vint (Int.repr m)) p
   * field_at sh (Tstruct _bandmat_t noattr) (DOT _b) (Vint (Int.repr b)) p
   * bandmatn sh b M (offset_val bandmat_data_offset p)
   * malloc_token' sh (bandmat_data_offset + sizeof (tarray the_ctype (Z.of_nat m * Z.of_nat (S b)))) p.

(** As usual with new spatial predicates, populate the Hint databases [saturate_local] and [valid_pointer] *)
Definition bandmatn_local_facts: forall {t} sh m b M p,
  @bandmatn t sh m b M p |-- 
      !! (0 < m <= Int.max_signed
          /\ m * S b <= Int.max_signed
          /\ trmx M = M 
          /\ forall (i j : 'I_(m)), j>i+b -> M i j = Some (Zconst t 0)
          /\ field_compatible (tarray (ctype_of_type t) (m * S b)) [] p).
Proof.
intros.
unfold bandmatn.
entailer!.
Qed.

Definition bandmat_local_facts: forall sh m b M p,
  @bandmat sh m b M p |-- 
      !! (0 < m <= Int.max_signed
          /\ m * S b <= Int.max_signed
          /\ trmx M = M 
          /\ forall (i j : 'I_m), j>i+b -> M i j = Some (Zconst the_type 0)
          /\ malloc_compatible (bandmat_data_offset + sizeof (tarray the_ctype (m * S b))) p).
Proof.
intros.
unfold bandmat, bandmatn.
entailer!.
Qed.

#[export] Hint Resolve bandmatn_local_facts bandmat_local_facts : saturate_local.

Lemma bandmatn_valid_pointer:
  forall t sh m b M p,
   sepalg.nonidentity sh ->
   @bandmatn t sh m b M p |-- valid_pointer p.
Proof.
 intros.
 unfold bandmatn.
 Intros.
 apply data_at_valid_ptr; auto.
 unfold ctype_of_type.
 repeat if_tac; simpl; lia.
Qed.

Lemma bandmat_valid_pointer:
  forall sh m b M p,
   @bandmat sh m b M p |-- valid_pointer p.
Proof.
 intros.
 unfold bandmat. entailer!.
Qed.

#[export] Hint Resolve bandmatn_valid_pointer bandmat_valid_pointer : valid_pointer.

(** * Function specifications (funspecs) *)
(** Compare these to the function headers in [bandmat.h] *)

(** [bandmat_malloc] takes [m] and [b] such that [m * S b] is representable as a signed integer, 
    and returns a banded uninitialized [m * m] matrix. *)
(* Note: the argument in C code is n instead of m, might want to change it for clarity *)
Definition bandmat_malloc_spec :=
  DECLARE _bandmat_malloc
  WITH m: nat, b: nat, gv: globals
  PRE [ tint, tint ]
    PROP(0 < m <= Int.max_signed;
         0 <= b <= Int.max_signed;
         m * S b <= Int.max_signed)
    PARAMS (Vint (Int.repr m); Vint (Int.repr b) ) GLOBALS (gv)
    SEP( mem_mgr gv )
  POST [ tptr bandmat_t ]
   EX p: val,
    PROP () 
    RETURN (p) 
    SEP(bandmat Ews b (@const_mx (option(ftype the_type)) m m None) p; mem_mgr gv).
    (* alternative: build the matrix with zeros in the corners and None on the bands *)

(** [bandmat_free] takes an m * m banded matrix and returns nothing. *)
Definition bandmat_free_spec :=
  DECLARE _bandmat_free
  WITH X: {m & 'M[option (ftype the_type)]_(m, m)}, b : nat, p: val, gv: globals
  PRE [ tptr bandmat_t ]
    PROP() 
    PARAMS ( p ) GLOBALS (gv)
    SEP(bandmat Ews b (projT2 X) p; mem_mgr gv)
  POST [ tvoid ]
    PROP () 
    RETURN () 
    SEP( mem_mgr gv ).

(** [bandmatn_clear] takes just the [data] part of an m*n matrix and 
   sets all its elements to floating-point zero.  Therefore, as with all [bandmatn] operations,
   we need to pass bounds information as function parameters.   

   The [let '(existT _ ...)] unpacks the components of [X].  Due to a limitation in VST's notation system,
  We have to repeat this unpacking separately in the PRE and POST clauses. *)
Definition bandmatn_clear_spec :=
  DECLARE _bandmatn_clear
  WITH X: {m & 'M[option (ftype the_type)]_(m, m)}, b: nat, p: val, sh: share
  PRE [ tptr the_ctype, tint, tint ] let '(existT _ m M) := X in
    PROP(writable_share sh) 
    PARAMS (p; Vint (Int.repr m); Vint (Int.repr b))
    SEP(bandmatn sh b M p)
  POST [ tvoid ] let '(existT _ m M) := X in
    PROP () 
    RETURN () 
    SEP(bandmatn sh b (@const_mx _ m m (Some (Zconst the_type 0))) p).
  (* For this function it has to enforce zero's, not None, in the corners *)

(** [bandmat_clear] takes just the struct (with bounds information) of an m*n matrix and 
   sets all its elements to floating-point zero. *)
Definition bandmat_clear_spec :=
  DECLARE _bandmat_clear
  WITH X: {m & 'M[option (ftype the_type)]_(m, m)}, b: nat, p: val, sh: share
  PRE [ tptr bandmat_t ] let '(existT _ m M) := X in 
    (PROP(writable_share sh) 
    PARAMS (p)
    SEP(bandmat sh b M p))
   POST [ tvoid ] let '(existT _ m M) := X in 
    PROP () 
    RETURN () 
    SEP(bandmat sh b (@const_mx _ m m (Some (Zconst the_type 0))) p).
