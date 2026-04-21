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

(* An attempt to have the matrix size m*m instead (S m) * (S m) by using auxiliary definitions. *)
Definition inord_add {m n : nat} (j : 'I_n) (i : 'I_(m-j)) : 'I_m.
apply (@Ordinal m (i+j)).
pose proof (ltn_ord i). lia.
Defined.

Definition inord_inj {m j : nat} (i : 'I_(m-j)) : 'I_m.
apply (@Ordinal m i). 
pose proof (ltn_ord i). lia.
Defined.

Definition banded_repr {T: Type} {InhT: Inhabitant T} [m: nat] (b: nat) (f: 'M[T]_(m,m)) :=
 concat (map (fun j => (repeat InhT (nat_of_ord j)) ++
                       (map (fun (i : 'I_(m-j)) => f (@inord_inj m j i) (@inord_add m (S b) j i)) (ord_enum (m-j))))
             (ord_enum (S b))).

(* Could define a predicate Banded *)

(** Spatial predicate (mpred) to represent the [data] field of a [struct bandmat_t] *)
Definition bandmatn {t: type} (sh: share) [m] (b: nat) (M: 'M[option (ftype t)]_(m,m)) (p: val) : mpred :=
 !! (0 < m <= Int.max_signed /\ m * S b <= Int.max_signed /\ trmx M = M /\ 
     forall (i j : 'I_m), j>i+b -> M i j = Some (Zconst t 0))
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
    and returns a b-banded uninitialized [m * m] matrix. *)
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

(** [bandmat_free] takes a b-banded m * m banded matrix and returns nothing. *)
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

(** [bandmatn_clear] takes just the [data] part of a b-banded m*m matrix and 
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

(** [bandmat_clear] takes just the struct (with bounds information) of a b-banded m*m matrix and 
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


(** [bandmatn_get] fetches the (i,j) component of a matrix.  Since the matrix is in banded form
    order, we must also pass the size [m] and the number of bands [b].

   The precondition of the function enforces that [0 <= i < m] and [0 <= d < m].  It does so by construction
   of the dependently typed value [X], where the last component is a pair [(i: 'I_[m], d: 'I[m])].

   Note that d = j-i is the diagonal number
    *)
(* The code uses i+d*rows = i+(j-i)*rows, assuming j>=i; This is the same as the more general formula
   max(i,j)+rows*abs(i-j) = max(i,d)+rows*abs(i-d), where d=abs(i-j) and m=rows. *)
Definition bandmatn_get_spec :=
  DECLARE _bandmatn_get
  WITH X: {m & 'M[option (ftype the_type)]_(m, m) * ('I_(m) * 'I_(m)) }%type,
       b:nat, p: val, sh: share, x: ftype the_type
  PRE [ tptr the_ctype, tint, tint, tint ] let '(existT _ m (M,(i,j))) := X in let 'd := j-i in
    PROP(readable_share sh; M i j = Some x; 0 <= d <= b)
    PARAMS (p ; Vint (Int.repr m); Vint (Int.repr i); Vint (Int.repr d))
    SEP (bandmatn sh b M p)
  POST [ the_ctype ] let '(existT _ m (M,(i,j))) := X in
    PROP () 
    RETURN (val_of_float x) 
    SEP(bandmatn sh b M p).

Definition bandmat_get_spec :=
  DECLARE _bandmat_get
  WITH X: {m & 'M[option (ftype the_type)]_(m, m) * ('I_(m) * 'I_(m)) }%type,
       b:nat, p: val, sh: share, x: ftype the_type
  PRE [ tptr bandmat_t , tint, tint ] let '(existT _ m (M,(i,j))) := X in let 'd := j-i in
    PROP(readable_share sh; M i j = Some x; 0 <= d <= b)
    PARAMS (p ; Vint (Int.repr i); Vint (Int.repr d))
    SEP(bandmat sh b M p)
  POST [ the_ctype ]  let '(existT _ m (M,(i,j))) := X in
    PROP () 
    RETURN (val_of_float x) 
    SEP(bandmat sh b M p).

Definition bandmatn_set_spec :=
  DECLARE _bandmatn_set
  WITH X: {m & 'M[option (ftype the_type)]_(m, m) * ('I_(m) * 'I_(m)) }%type,
       b:nat, p: val, sh: share, x: ftype the_type
  PRE [ tptr the_ctype, tint, tint, tint, the_ctype ] 
    let '(existT _ m (M,(i,j))) := X in let 'd := j-i in
    PROP(writable_share sh; 0 <= d <= b) 
    PARAMS (p ; Vint (Int.repr m); Vint (Int.repr i); Vint (Int.repr d); val_of_float x)
    SEP(bandmatn sh b M p)
  POST [ tvoid ] let '(existT _ m (M,(i,j))) := X in
    PROP () 
    RETURN () 
    SEP(bandmatn sh b (update_mx M i j (Some x)) p).

Definition bandmat_set_spec :=
  DECLARE _bandmat_set
  WITH X: {m & 'M[option (ftype the_type)]_(m, m) * ('I_(m) * 'I_(m)) }%type,
       b:nat, p: val, sh: share, x: ftype the_type
  PRE [ tptr bandmat_t, tint, tint, the_ctype ] 
    let '(existT _ m (M,(i,j))) := X in let 'd := j-i in
    PROP(writable_share sh; 0 <= d <= b) 
    PARAMS (p ; Vint (Int.repr i); Vint (Int.repr d); val_of_float x)
    SEP(bandmat sh b M p)
  POST [ tvoid ] let '(existT _ m (M,(i,j))) := X in
    PROP () 
    RETURN () 
    SEP(bandmat sh b (update_mx M i j (Some x)) p).

Definition bandmatn_addto_spec :=
  DECLARE _bandmatn_addto
  WITH X: {m & 'M[option (ftype the_type)]_(m, m) * ('I_(m) * 'I_(m)) }%type,
       b:nat, p: val, sh: share, y: ftype the_type, x: ftype the_type
  PRE [ tptr the_ctype, tint, tint, tint, the_ctype ] 
    let '(existT _ m (M,(i,j))) := X in let 'd := j-i in
    PROP(writable_share sh; M i j = Some y; 0 <= d <= b) 
    PARAMS (p ; Vint (Int.repr m); Vint (Int.repr i); Vint (Int.repr d); val_of_float x)
    SEP(bandmatn sh b M p)
  POST [ tvoid ] let '(existT _ m (M,(i,j))) := X in
    PROP () 
    RETURN () 
    SEP(bandmatn sh b (update_mx M i j (Some (BPLUS y x))) p).

Definition bandmat_addto_spec :=
  DECLARE _bandmat_addto
  WITH X: {m & 'M[option (ftype the_type)]_(m, m) * ('I_(m) * 'I_(m)) }%type,
       b:nat, p: val, sh: share, y: ftype the_type, x: ftype the_type
  PRE [ tptr bandmat_t, tint, tint, the_ctype ] 
    let '(existT _ m (M,(i,j))) := X in let 'd := j-i in
    PROP(writable_share sh; M i j = Some y; 0 <= d <= b) 
    PARAMS (p ; Vint (Int.repr i); Vint (Int.repr d);
            val_of_float x)
    SEP(bandmat sh b M p)
  POST [ tvoid ] let '(existT _ m (M,(i,j))) := X in
    PROP () 
    RETURN () 
    SEP(bandmat sh b (update_mx M i j (Some (BPLUS y x))) p).

(* Importing for now, should probably refactor eventually *)
From LAProof.C Require Import spec_densemat.

(* problem here is that the symmetric elements are not repeated *)
Definition banded_repr_nopadding_aux {T: Type} [m: nat] (b: nat) (f: 'M[T]_(m,m)) :=
 concat (map (fun (j:'I_(S b)) => map (fun (i : 'I_(m-j)) => f (@inord_inj m j i) (@inord_add m (S b) j i)) (ord_enum (m-j)))
             (ord_enum (S b))).

(* with repeated elements, in order abcd,efghi,efghi for a 4x4 2-banded matrix *)
Definition banded_repr_nopadding {T: Type} [m: nat] (b: nat) (f: 'M[T]_(m,m)) :=
  let l := banded_repr_nopadding_aux b f in
  l ++ (sublist m (length l) l).

Fixpoint duplicate {A:Type} (l: list A) : list A :=
  match l with
  nil => nil
| h :: t => cons h (cons h (duplicate t))
end.

(* with repeated elements, in order abcd,eeffgg,hhii for a 4x4 2-banded matrix *)
Definition banded_repr_nopadding' {T: Type} [m: nat] (b: nat) (f: 'M[T]_(m,m)) :=
  let l := banded_repr_nopadding_aux b f in
  let s := sublist m (length l) l in
  (sublist 0 m l) ++ (duplicate s).

Definition repeat {A:Type} (l: list A) : list A := l ++ l.

Definition banded_repr_nopadding_aux'' {T: Type} [m: nat] (b: nat) (f: 'M[T]_(m,m)) :=
 concat (map (fun (j:'I_(S b)) => repeat (map (fun (i : 'I_(m-j)) => f (@inord_inj m j i) (@inord_add m (S b) j i)) (ord_enum (m-j))))
             (ord_enum (S b))).

(* with repeated elements, in order abcd,efgefg,hihi for a 4x4 2-banded matrix *)
Definition banded_repr_nopadding'' {T: Type} [m: nat] (b: nat) (f: 'M[T]_(m,m)) :=
  let l := banded_repr_nopadding_aux'' b f in
  sublist m (length l) l.

(* THERE ARE KNOWN PROBLEMS IN THIS SPEC, SEE BELOW *)
Definition bandmat_norm2_spec :=
  DECLARE _bandmat_norm2
  WITH sh: share, b:nat, X: {m & 'M[ftype the_type]_(m, m)}, p: val
  (* No option forces M to be fully initialized *)
  PRE [ tptr bandmat_t ] let '(existT _ m M) := X in
    PROP (readable_share sh)
    PARAMS (p)
    SEP(bandmat sh b (map_mx Some M) p)
  POST [ the_ctype ] let '(existT _ m M) := X in
    PROP() RETURN (val_of_float (norm2 (banded_repr_nopadding b M)))
    (* (frobenius_norm2 M) would not work because the order of addition is different *)
    (* technically (banded_repr b M) might work, but only because the default float is 0 *)
    SEP(bandmat sh b (map_mx Some M) p).
(* It is a little odd that M doesn't have type 'M[option (ftype the_type)]_(m, m).
   But what would you return if it's completely uninitialized? *)
(* ISSUE 1: The current code is incorrect: if some of the leading zeros in the bands are uninitialized, 
   since they're added up but not initialized (hence could be anything), that could create issues.
   This is because the code takes the norm2 of the whole array, including the leading zeros in the bands.
   Solution 1: Change the spec of bandmat_norm2_spec to use `norm2 (banded_repr b M)`,
               instead of `(norm2 (banded_repr_nopadding b M))`. Feels like cheating + very fragile.
               Also what happens to the None?
               But no issue thanks to type: because M does not contain options, the leading elements
               of the bands are initialized to the default ftype, which is 0.
               This would not work with an M of type 'M[option (ftype the_type)]_(m, m).
               But then to verify you would need to asume the leading zeros are actually zero, 
               which dense_to_band doesn't enforce in the code.
   Solution 2: Change the code of bandmat_norm2 to not add up the leading potentially uninitialized zeros/
               Probably the best option.
   Solution 3: Enforce that the leading zeros are actually 0 (instead of None), but that doesn't 
               match the code of dense_to_band.
               In bandmatn_clear this is done. But not in dense_to_band.
               There might be a bug if one does dense_to_band followed by bandmat_norm2. *)
(* ISSUE 2: bandmat_norm2 (and also bandmat_norm, densemat_norm2, densemat_norm) appear to be 
            computing the Frobenius norm, not the 2-norm of the matrix. At a minimum we should rename. *)
(* ISSUE 3: densemat_norm2 and densemat_norm are only adding up the bands once, but they should
            appear twice in the Frobenius sum since the matrix is symmetric *)

Definition bandmat_norm_spec :=
  DECLARE _bandmat_norm
  WITH sh: share, b:nat, X: {m & 'M[ftype the_type]_(m, m)}, p: val
  PRE [ tptr bandmat_t ] let '(existT _ m M) := X in
    PROP (readable_share sh)
    PARAMS (p)
    SEP(bandmat sh b (map_mx Some M) p)
  POST [ the_ctype ] let '(existT _ m M) := X in
    PROP() RETURN (val_of_float (BSQRT (norm2 (banded_repr_nopadding b M))))
    SEP(bandmat sh b (map_mx Some M) p).

(* Note: the densematn_print_spec is Admitted *)
(* Note: there is no bandmatn_print in bandmat.h or bandmat.c *)
(* Doesn't say anything about the output *)
Definition bandmat_print_spec :=
  DECLARE _bandmat_print
  WITH b:nat, X: {m & 'M[ftype the_type]_(m, m)}, p: val, sh: share
  PRE [ tptr bandmat_t ] let '(existT _ m M) := X in 
    (PROP(readable_share sh) 
    PARAMS (p)
    SEP(bandmat sh b (map_mx Some M)  p))
   POST [ tvoid ] let '(existT _ m M) := X in 
    PROP () 
    RETURN () 
    SEP(bandmat sh b (map_mx Some M) p).

Definition dense_to_band_spec :=
  DECLARE _dense_to_band
  WITH X: {m & 'M[option (ftype the_type)]_(m, m)}, p: val, sh: share, bw: nat, gv:globals
  PRE [ tptr densemat_t, tint ] let '(existT _ m M) := X in
    (* enforcing that M is banded with band width bw *)
    (PROP(readable_share sh ; 0 < m <= Int.max_signed ; m * S bw <= Int.max_signed ;
          trmx M = M ; forall (i j : 'I_m), j>i+bw -> M i j = Some (Zconst the_type 0) )
    PARAMS (p ; Vint (Int.repr bw)) GLOBALS (gv)
    SEP(densemat sh M p))
  POST [ tptr bandmat_t ] let '(existT _ m M) := X in
   EX q: val,
    PROP () 
    RETURN (q) 
    SEP(bandmat Ews bw M q; mem_mgr gv).

Definition bandmat_factor_spec :=
 DECLARE _bandmat_factor
 WITH sh: share, X: {n & 'M[option (ftype the_type)]_n}, p: val, b: nat
 PRE [ tptr bandmat_t ] let '(existT _ m M) := X in
    PROP (writable_share sh;
          forall i j, isSome (mirror_UT M i j))
    PARAMS (p)
    SEP (bandmat sh b M p)
 POST [ tint ] let '(existT _ m M) := X in
   EX R: 'M_m,
    PROP (cholesky_jik_spec (map_mx optfloat_to_float (mirror_UT M)) R)
    RETURN (Vint (Int.repr (Zcholesky_return (cholesky_return R))))
    SEP (bandmat sh b (joinLU M (map_mx Some R)) p).

Definition bandmat_solve_spec :=
 DECLARE _bandmat_solve
 WITH rsh: share, sh: share, X: {m & 'M[option (ftype the_type)]_m * 'cV[ftype the_type]_m}%type,
      b: nat, p: val, xp: val
 PRE [ tptr bandmat_t, tptr the_ctype ] let '(existT _ m (M,x)) := X in
    PROP (readable_share rsh; writable_share sh;
          forall i j, isSome (mirror_UT M i j))
    PARAMS (p; xp)
    SEP (bandmat rsh b M p; densematn sh (map_mx Some x) xp)
 POST [ tvoid ] let '(existT _ m (M,x)) := X in
    PROP ()
    RETURN ()
    SEP (bandmat rsh b M p;
         densematn sh (map_mx Some 
                      (backward_subst (map_mx optfloat_to_float M)
                          (forward_subst (trmx (map_mx optfloat_to_float M)) x)))
           xp).

