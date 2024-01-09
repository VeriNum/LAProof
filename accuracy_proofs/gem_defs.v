(** This file contains the low level list 
  definitions of matrices and vectors, along with 
  useful lemmas about these definitions 

  Copyright Ariel Kellison, 2023 *)

Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.

From LAProof.accuracy_proofs Require Import common 
                                            op_defs 
                                            dotprod_model 
                                            sum_model
                                            float_acc_lems 
                                            list_lemmas
                                            float_tactics.


(* General list matrix and vector definitions *)
Section MVGenDefs. 

Definition matrix {A : Type} := list (list A).

Definition vector {A : Type} := list A.

Fixpoint zero_vector {A: Type} (m : nat) (zero : A) : vector := 
  match m with 
  | S n => zero :: zero_vector n zero
  | _ => []
  end. 

Fixpoint zero_matrix {A: Type} (m n: nat) (zero : A) : matrix := 
  match m,n with 
  | S m', S n' => zero_vector n zero :: zero_matrix m' n zero
  | _, _ => []
  end. 

Definition is_finite_vec {t : type} {STD: is_standard t} (v: vector) : Prop := 
  Forall (fun (x : ftype t) => is_finite x = true) v.

Definition is_finite_mat {t : type} {STD : is_standard t} (A: matrix) : Prop := 
  Forall (fun x => is_finite_vec x) A.

Definition is_zero_vector {A: Type} v (zero : A) : Prop := forall x, In x v -> x = zero.

Definition map_mat {A B: Type} (f : A -> B) (M : matrix) : matrix :=
  map (map f) M.  

Definition map2 {A B C: Type} (f: A -> B -> C) al bl :=
  map (uncurry f) (List.combine al bl).

Fixpoint zero_map_vec {A B : Type} (zero : B) (v : @vector A) : @vector B :=
  match v with 
  | [] => []
  | h :: t => zero :: zero_map_vec zero t
end. 

Fixpoint zero_map_mat {A B : Type} (zero : B) (M : @matrix A) : @matrix B :=
  match M with 
  | [] => []
  | hM :: tM => zero_map_vec zero hM :: zero_map_mat zero tM
end. 

Definition in_matrix {T : Type} (A : list (list T)) (a : T) := 
  let A' := flat_map (fun x => x) A in In a A'.

Definition matrix_index {A} (m: matrix) (i j: nat) (zero: A) : A :=
 nth j (nth i m nil) zero.

Definition eq_size {T1 T2} 
  (A : list (list T1)) (B : list (list T2)) := length A = length B /\
  forall x y, In x A -> In y B -> length x = length y.

End MVGenDefs.

Section MVOpDefs.

(* generic vector sum *)
Definition vec_sum {A: Type} (sum : A -> A -> A) : 
  vector -> vector -> vector := map2 sum.

(* sum vectors of reals *)
Definition vec_sumR :=  vec_sum Rplus.

(* sum vectors of floats *)
Definition vec_sumF 
  {NAN : Nans} {t : type} {STD : is_standard t} :=  vec_sum BPLUS.

(* generic matrix sum *)
Definition mat_sum {T: Type} (sum : T -> T -> T):= 
  map2 (map2 sum).

(* sum matrices of reals *)
Definition mat_sumR :=  mat_sum Rplus .

(* sum matrices of floats *)
Definition mat_sumF {NAN : Nans} {t: type} {STD: is_standard t} := mat_sum BPLUS.

(* generic matrix vector multiplication *)
Definition MV {A: Type} (DOT : @vector A -> @vector A -> A) 
      (m: matrix) (v: vector) : vector :=
      map (fun row => DOT row v) m.

(* floating-point matrix vector multiplication *)
Definition mvF {NAN : Nans} {t: type} {STD: is_standard t}: matrix -> vector -> vector  :=
      MV dotprodF.

(* real valued matrix vector multiplication *)
Definition mvR  : matrix -> vector -> vector  := MV dotprodR.

(* helper for generic matrix-matrix multiplication *)
Definition mul' {A: Type} (d : A) (mult: A -> A -> A) (m : @matrix A) (v : @vector A) := 
  map (fun a => map (mult a) v) (map (hd d) m).


(* transpose of matrix B of size ( m x p) *) 
Fixpoint trans {A: Type} d p (B : matrix) : matrix :=
  match p with
   | S p' => (map (hd d) B) :: trans d p'(map (@tl A) B)
   | 0%nat => []
  end.

Goal trans 0%R 3 [[1;1;2];[1;1;2];[1;1;2]] = [[]].
unfold trans. simpl.
Abort.
Notation "A ^T" := (trans A) (at level 40).

(* perform p dot products between row and the p columns of m2 of size (m x p) *) 
Fixpoint DOT {A: Type} (dotprod : @vector A -> @vector A -> A) 
   row (m2 : matrix) :=
  match m2 with
   | col :: m2' => dotprod row col :: DOT dotprod row m2'
   | _ => []
  end.

(* generic matrix-matrix multiplication on row major order matrices of size (m x n);
   assumes m2 is transposed *)
Fixpoint MMT {A: Type} (d : A) (dotprod : @vector A -> @vector A -> A) 
      (m1 m2: @matrix A) : @matrix A :=
  match m1 with
    | row :: m1' =>
         DOT dotprod row m2 :: MMT d dotprod m1' m2 
    | _  => []
  end.

Example checkMMT : let A:= trans 0%R 2 [[1;1];[1;1]] in
  MMT 0%R dotprodR [[1;2];[3;4]] A = [[3;3];[7;7]].
simpl. unfold dotprodR. simpl. repeat f_equal ;field_simplify; nra. Qed.

(* floating-point matrix matrix multiplication. *)
Definition MMTF {NAN : Nans}  {t: type} {STD : is_standard t}: matrix -> matrix -> matrix  := 
  MMT (Zconst t 0) dotprodF.

(* real valued matrix matrix multiplication *)
Definition MMTR : matrix -> matrix -> matrix  := 
  MMT 0%R dotprodR.


(* perform p dot products between row a and the p columns of B *) 
Fixpoint dot' {A: Type} (d : A) (dotprod : @vector A -> @vector A -> A) 
      p a (B : matrix) :=
  match p with
   | S p' => dotprod a (map (hd d) B) :: dot' d dotprod  p' a (map (@tl A) B)
   | 0%nat => []
  end.

(* generic matrix-matrix multiplication on row major order matrices of size (m x n) *)
Fixpoint MM' {A: Type} (d : A) (dotprod : @vector A -> @vector A -> A) 
      (m1 m2: @matrix A) : @matrix A :=
  match m1,m2  with
    | row :: m1', b :: m2'  =>
        dot' d dotprod (length b) row m2 :: MM' d dotprod m1' m2 
    | _ ,_ => []
  end.

(* floating-point matrix matrix multiplication. *)
Definition MMF' {NAN : Nans}  {t: type} {STD : is_standard t} : 
    matrix -> matrix -> matrix  :=   MM' (Zconst t 0) dotprodF.

(* real valued matrix matrix multiplication *)
Definition MMR' : matrix -> matrix -> matrix  := 
  MM' 0%R dotprodR.

(* scale vector v by constant a *)
Definition scaleV {T} (mul: T -> T -> T) (a : T) (v : vector) : vector := 
  map (mul a) v.

Definition scaleVR := @scaleV R Rmult.
Definition scaleVF {NAN : Nans} {t : type} {STD : is_standard t} := @scaleV (ftype t) BMULT.

(* multiply row a of size m by matrix B of size (m x p)*)
Fixpoint rowM {T} (d: T) (sum : @vector T -> @vector T -> @vector T) 
  (mul: T -> T -> T) (m : nat) a B : vector := 
  match a,B with
    | a0 :: a', b :: B' => sum (scaleV mul a0 b) (rowM d sum mul m a' B')
    | _, _ => zero_vector m d  
  end. 

Fixpoint MM {T} (d: T) (sum : @vector T -> @vector T -> @vector T) 
  (mul: T -> T -> T) A B : matrix := 
  match A,B with
  | a :: A', b1 :: b2 => let m:= length b1 in 
        rowM d sum mul m a B :: MM d sum mul A' B
  | _, _ => []
end.

(* floating-point matrix matrix multiplication. *)
Definition MMF {NAN : Nans} {t: type} {STD : is_standard t} 
    : matrix -> matrix -> matrix  :=  MM (Zconst t 0) vec_sumF BMULT.

(* real valued matrix matrix multiplication *)
Definition MMR : matrix -> matrix -> matrix  := 
  MM 0%R vec_sumR Rmult.

Goal MMR [[1;2;3] ;[1;2;3]; [1;2;3]] [[1;0;0]; [0;1;0]; [0;0;1]] = 
  [[1;2;3] ;[1;2;3]; [1;2;3]].
repeat (unfold MMR, MM, vec_sumR, vec_sum, map2; simpl; auto).
repeat f_equal;  field_simplify; nra. Qed.

Definition MMC {T} (dot : vector -> vector -> T) A B : matrix := 
  map (fun b => MV dot A b) B.

Example checkMMC: let A:= trans 0%R 2 [[1;1];[1;1]] in
  MMC dotprodR [[1;2];[3;4]] A = trans 0%R 2 [[3;3];[7;7]].
simpl. unfold dotprodR. simpl. repeat f_equal ;field_simplify; nra. Qed. 

Definition MMCR := MMC dotprodR.
Definition MMCF {NAN : Nans} {t : type} {STD : is_standard t} := MMC dotprodF.

Definition scaleM {T} (mul : T -> T -> T) a M :=  map_mat (mul a) M.

Definition scaleMR := scaleM Rmult.
Definition scaleMF {NAN : Nans} {t: type} {STD : is_standard t} := scaleM BMULT.


Definition GEMM {T} (dot : vector -> vector -> T) 
  (sum mul : T -> T -> T) (A B C: matrix) (a b : T) := 
  mat_sum sum (scaleM mul a (MMC dot A B)) (scaleM mul b C).

Definition GEMMR := GEMM dotprodR Rplus Rmult.
Definition GEMMF {NAN : Nans} {t: type} := 
                      GEMM dotprodF BPLUS BMULT.
  
End MVOpDefs.


Notation "A *f v" := (mvF A v) (at level 40).
Notation "A *r v"  := (mvR A v) (at level 40).
Notation "A *fr v" := (map FT2R (mvF A v)) (at level 40).

Notation "u -v v" := (vec_sum Rminus u v) (at level 40).
Notation "u +v v" := (vec_sumR u v) (at level 40).

Notation "A -m B" := (mat_sumR A (map_mat Ropp B)) (at level 40).
Notation "A +m B" := (mat_sumR A B) (at level 40).

Notation "E _( i , j )"  :=
  (matrix_index E i j 0%R) (at level 15).

Section MVLems.

Lemma dotprod_diff u1 u2 v:
length u1 = length u2 ->
dotprodR u1 v - dotprodR u2 v = dotprodR (u1 -v u2) v.
Proof.  revert  u1 u2.
induction v. intros. rewrite !dotprodR_nil_r. nra.
intros.
destruct u1. 
 simpl in H. symmetry in H. apply length_zero_iff_nil in H. subst.
 rewrite !dotprodR_nil_l. nra.
destruct u2; try discriminate. 
unfold dotprodR. simpl.
rewrite !fold_left_Rplus_Rplus.
fold (@dotprodR u1 v).
fold (@dotprodR u2 v).
field_simplify.
replace (r * a - a * r0 + dotprodR u1 v - dotprodR u2 v) with
  (r * a - a * r0 + (dotprodR u1 v - dotprodR u2 v)) by nra.
apply Rplus_eq_compat_l.
rewrite IHv; auto.
Qed.

Lemma map2_length {A B C: Type} (f: A -> B -> C) al bl : 
  length al = length bl -> 
  length (map2 f al bl) = length al.
Proof. intros; unfold map2; rewrite map_length, combine_length, H, Nat.min_id; auto. Qed.

Lemma map_mat_length {A B: Type} :
  forall (f : A -> B) (M : @matrix A) ,
  length (map_mat f M) = length M.
Proof. intros; induction M; [simpl; auto | simpl; rewrite IHM; auto]. Qed. 

Lemma zero_matrix_length {A: Type} (m n: nat) (zero : A) :
  forall (Hn : (0 < n)%nat),
  length (zero_matrix m n zero) = m .
Proof. revert n. induction m.
unfold zero_matrix. auto. intros.
specialize (IHm n Hn). simpl. destruct n. lia.
simpl. lia.
Qed. 

Lemma mvF_len {NAN : Nans} m v:
  length (mvF m v)  = length m.
Proof. induction m; simpl; auto. Qed.

Lemma dotprodF_nil {NAN : Nans} {t: type} {STD : is_standard t} row :
  dotprodF row [] = (Zconst t 0). 
Proof. destruct row; simpl; auto. Qed. 

Lemma mvF_nil {NAN : Nans} {t: type} {STD : is_standard t} 
  : forall m, mvF m [] = @zero_vector (ftype t) (length m) (Zconst t 0).
Proof. 
intros; unfold mvF, MV.
set (f:= (fun row : vector => dotprodF row [])).
replace (map f m) with  (map (fun _ => Zconst t 0) m).
induction m; simpl; auto.
{ rewrite IHm; auto. }
apply map_ext_in; intros.
subst f; simpl. rewrite dotprodF_nil; auto.
Qed.

Lemma mvR_nil : forall m, mvR m [] = zero_vector (length m) 0%R. 
Proof.
intros; unfold mvR, MV.
set (f:= (fun row : vector => dotprodR row [])).
replace (map f m) with  (map (fun _ => 0%R) m).
induction m; simpl; auto.
{ rewrite IHm; auto. }
apply map_ext_in; intros.
subst f; simpl. rewrite dotprodR_nil_r; auto.
Qed.

Lemma mat_sum_length {T: Type} (sum: T -> T -> T) :  
  forall (A B: matrix),
  forall (Hlen : length A = length B),
  length (mat_sum sum A B) = length A.
Proof. intros. unfold mat_sum; rewrite map2_length; auto. Qed.

Lemma zero_vector_length {A : Type} (m : nat) (zero : A) :
  length (zero_vector m zero) =  m.
Proof. induction m; simpl; auto. Qed.

Lemma nth_zero_vector m i:
  nth i (zero_vector m 0%R) 0%R = 0%R.
Proof. revert i. induction m ; simpl; auto; destruct i; simpl ;auto. Qed.


Lemma vec_sum_cons {T} (sum : T -> T -> T):
forall (u v : @vector T) u0 v0,
vec_sum sum (u0 :: u) (v0 :: v)  = sum u0 v0 :: vec_sum sum u v.
Proof. 
induction u; destruct v; 
(intros; unfold vec_sum, map2; simpl; auto). 
Qed.

(* TODO: REMOVE *)
Lemma vec_sumR_cons : 
forall (u v : vector) u0 v0,
vec_sum Rplus (u0 :: u) (v0 :: v)  = (u0 + v0) :: vec_sum Rplus  u v.
Proof. 
apply vec_sum_cons.
Qed.

Lemma vec_sum_zero {T} (sum : T -> T -> T) d:
  forall (v : vector) (Hsum : forall a, sum a d = a),
  vec_sum sum v (zero_vector (length v) d)  = v.
Proof.
intros; induction v; simpl; auto.
rewrite vec_sum_cons, IHv. 
rewrite Hsum; auto.
Qed.

Lemma vec_sum_zeroF {NAN : Nans} {t : type} {STD : is_standard t}:
  forall (v : vector),
  map FT2R (vec_sumF v (zero_vector (length v) (Zconst t 0)))  
          = map FT2R v.
Proof.
intros; induction v; auto.
unfold vec_sumF.
set (z := (zero_vector (length (a::v)) (Zconst t 0))).
 replace z with ((Zconst t 0) :: zero_vector (length v) (Zconst t 0))
  by (simpl; auto).
rewrite vec_sum_cons.
simpl. unfold vec_sumF in IHv.
 rewrite IHv. f_equal.
Search Binary.B2R FT2R. 
rewrite <-!B2R_float_of_ftype;
  unfold BPLUS, BINOP.
rewrite float_of_ftype_of_float.
replace (float_of_ftype (Zconst t 0))
  with  (Binary.B754_zero (fprec t) (femax t) false).
destruct (float_of_ftype a); simpl; auto;
destruct s; simpl; auto.
cbv [float_of_ftype]. 
destruct t; destruct nonstd; easy.
Qed.

Lemma vec_sum_zeroR :
  forall (v : vector),
  vec_sumR v (zero_vector (length v) 0%R)  = v.
Proof.
intros.
rewrite (vec_sum_zero Rplus); auto. 
intros; nra.
Qed.


Lemma map_nil {A B: Type} (f : A -> B) : map f [] = []. 
Proof. simpl; auto. Qed.


Lemma mat_sumR_cons:  
  forall (A B: matrix) av bv,
  forall (Hlen : length A = length B),
  mat_sumR (av :: A) (bv :: B) = vec_sumR av bv :: mat_sumR A B.
Proof. induction A; destruct B; (intros; unfold mat_sum, vec_sum, map2; simpl; auto). Qed.

Lemma mat_sumR_zero:
  forall (B : matrix) (n : nat)
  (Hn : (0<n)%nat)
  (Hin : forall row, In row B -> length row  = n), 
  mat_sum Rplus B (zero_matrix (length B) n 0%R) = B.
Proof.
intros ? ? ? ?.
 induction B; auto.
fold (mat_sumR (a :: B) (zero_matrix (length (a :: B)) n 0)).
fold (mat_sumR B (zero_matrix (length B) n 0)) in IHB.
simpl. destruct n. lia. 
rewrite mat_sumR_cons.
rewrite <- IHB; [ f_equal | intros; apply Hin; simpl; auto].
rewrite <- vec_sum_zeroR; unfold vec_sumR; repeat f_equal.
symmetry; apply Hin; simpl; auto.
repeat f_equal; apply IHB; intros; apply Hin; simpl; auto.
rewrite zero_matrix_length; auto.
Qed.

Lemma mat_sum_nil {A : Type} M (f: A -> A -> A) :
  mat_sum f M [] = [].
Proof. destruct M; auto. Qed.

Lemma zero_map_mat_length {A B: Type} :
  forall (M : @matrix A) (z : B), length (zero_map_mat z M) = length M. 
Proof.
intros; induction M; [simpl; auto | simpl; rewrite IHM; auto ].
Qed. 

Lemma vec_sumR_bounds a b a' b':
a' + b' :: vec_sumR a b =  vec_sumR (a' :: a) (b' :: b).
Proof. unfold vec_sumR; simpl; auto. Qed.

Lemma vec_sumR_opp :
forall u v, 
length u = length v -> 
vec_sum Rminus u v = vec_sum Rplus u (map Ropp v).
Proof.
intros ?.
induction u.
{ intros; simpl; auto. }
intros; destruct v; simpl; auto.
rewrite vec_sumR_cons.
rewrite <- IHu; auto.
Qed.

Lemma vec_sumR_comm :
forall u v , 
length u = length v ->
vec_sumR u v = vec_sumR v u.
Proof.
intros ?.
induction u.
{ intros. simpl in H; symmetry in H; apply length_zero_iff_nil in H; subst;
simpl; auto. }
intros; destruct v; auto. 
unfold vec_sumR; rewrite !vec_sumR_cons.
fold (vec_sumR v u);
fold (vec_sumR u v).
rewrite <- IHu. rewrite Rplus_comm; auto.
simpl in H; auto.
Qed.

Lemma vec_sumR_assoc :
forall u v w, 
length u = length v ->
length w = length v ->
vec_sumR (vec_sumR u v) w = vec_sumR u (vec_sumR v w).
Proof.
intros ?.
induction u.
{ intros. simpl in H; symmetry in H; apply length_zero_iff_nil in H; subst;
simpl; auto. }
intros; destruct v; simpl; auto.
destruct w; unfold vec_sumR; simpl; auto.
unfold vec_sumR; rewrite !vec_sumR_cons.
fold (vec_sumR v w). 
fold (vec_sumR u v). 
simpl in H, H0.
fold (vec_sumR (vec_sumR u v) w); 
rewrite IHu; [rewrite Rplus_assoc; auto  | lia | lia ].
Qed.

Lemma vec_sumR_minus :
forall u , 
vec_sumR (map Ropp u) u = (zero_vector (length u) 0%R).
Proof.
intros; induction u.
{ simpl; auto. }
unfold vec_sumR; simpl; rewrite !vec_sumR_cons.
fold (vec_sumR (map Ropp u) u).
rewrite IHu; f_equal; nra.
Qed. 

Lemma vec_sum_length {A : Type} :
forall u v (f : A -> A -> A) , 
length u = length v -> 
length u = length (vec_sum f u v ).
Proof.
intros ?; induction u.
{ simpl; auto. }
intros; destruct v; simpl; auto.
specialize (IHu v f); rewrite IHu.
unfold vec_sum; auto.
simpl in H; auto.
Qed. 

Lemma vec_sum_length2  {A B: Type} (f : B -> B-> B) :
forall (u : list A) v w, 
length u = length v -> 
length v = length w -> 
length u = length (vec_sum f v w ).
Proof.
intros ?;
induction u.
{ intros. simpl in H; symmetry in H; apply length_zero_iff_nil in H; subst;
simpl; auto. }
intros; destruct v; simpl; auto.
destruct w. { simpl in H0;  discriminate. }
simpl; auto.
specialize (IHu v w); rewrite IHu.
unfold vec_sum; auto.
simpl in H; auto.
simpl in H; auto.
Qed. 

Lemma nth_app_0 {T : Type} :
forall (l0 l : list T),
l0 <> [] ->
nth 0 (l0 ++ l) = nth 0 l0.
Proof.
intros.
induction l0; auto.
simpl. assert False by auto; contradiction.
Qed.

Lemma matrix_index_nil {A} (i j: nat) (zero: A) : 
   matrix_index [] i j zero = zero.
Proof. unfold matrix_index. destruct i; destruct j; simpl; auto. Qed.

Lemma vec_sumR_nth :
forall j u a
(Hlen: length a = length u), 
nth j u 0%R - nth j a 0%R = nth j (vec_sum Rminus u a) 0%R.
Proof.
induction j; destruct u; intros.
{ simpl; apply length_zero_iff_nil in Hlen; subst; simpl; nra. }
{ destruct a; try discriminate; auto. } 
{ destruct a; simpl; [nra | try discriminate; auto]. } 
destruct a; try discriminate; auto.
assert (length a = length u) by (simpl in Hlen; lia);
specialize (IHj u a H);
simpl; auto.
Qed.

Lemma nth_cons_vec_sumR a l r u2 : forall i,
  nth i ((l) +v (u2)) 0 = nth i (l) 0 + nth i ( u2) 0 ->
  nth (S i) ((a :: l) +v (r :: u2)) 0 = nth (S i) (a :: l) 0 + nth (S i) (r :: u2) 0.
Proof. intros; simpl; auto. Qed.

Lemma nth_cons_mvR b B u : forall i,
  nth (S i) ( (b::B) *r u) = nth i (B *r u).
Proof. intros; simpl; auto. Qed.

Lemma length_mvR_mvF {NANS : Nans} {t : type} : 
  forall (m : matrix) (v : vector), 
  length ((map_mat FT2R m) *r (map FT2R v)) = length (m *fr v).
Proof.
  intros. 
  unfold mvR, mvF, MV, map_mat.
rewrite !map_length; auto.
Qed.

Lemma nth_vec_sum op : forall u1 u2 
  (Hlen: length u2 = length u1) i
  (Hop : op 0 0 = 0),
  nth i (vec_sum op u1 u2) 0 = op (nth i u1 0) (nth i u2 0).
Proof.
induction u1. intros.
rewrite length_zero_iff_nil in Hlen.
subst. simpl. destruct i; auto.
destruct u2; try discriminate. intros.
simpl; destruct i; auto.
rewrite <- IHu1; auto.
Qed.

Lemma vec_sum_nth_plus : forall u1 u2 
(Hlen: length u2 = length u1) i,
nth i (u1 +v u2) 0 = nth i u1 0 + nth i u2 0.
Proof.
induction u1. intros. 
rewrite length_zero_iff_nil in Hlen.
subst. destruct i; simpl; ring.
destruct u2; intros.
destruct i; try discriminate.
destruct i; simpl; try ring.
apply IHu1. simpl in Hlen; lia.
Qed.

End MVLems.


From mathcomp Require Import all_ssreflect all_algebra ssrnum.
Require Import VST.floyd.functional_base.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with R.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Section SIZEDEFS.

Definition size_col {T} (A : list (list T)) m n :=
  length A = n /\
  forall a, In a A -> length a = m.

Definition size_row {T} (A : list (list T)) m n :=
  length A = m /\
  forall a, In a A -> length a = n.

Lemma eq_size_cons {T1 T2} (a: list T1) (b: list T2) A B: 
eq_size (a :: A) (b :: B) ->
eq_size A B /\ length a = length b.
Proof.
rewrite /eq_size => /=; intros.
destruct H; repeat split; try lia.
intros; apply H0; by right. 
intros; apply H0; by  left.
Qed.

Lemma eq_size_scaleM {T} mul (x : T) A n :
  (forall a, In a A -> length a = n) -> 
  forall y, In y (scaleM mul x A) -> length y = n.
Proof.
elim : A => //.
intros; destruct H1. 
rewrite -H1 -(H0 a). by rewrite !map_length.
simpl; by left.
apply H => //. 
intros; apply H0; simpl; by right.
Qed.

Lemma eq_size_trans {T1 T2 T3} (A : list (list T1))
  (B : list (list T2)) (C : list (list T3)) : 
  eq_size A B -> eq_size B C -> eq_size A C.
Proof.
revert A B.
elim: C. 
{ rewrite /eq_size/=; intros; split; 
[lia|]; intros => //. } 
move => c C IH A.
case: A. 
{ rewrite /eq_size/=; intros; split; 
[lia|]; intros => //. } 
move => a A B.
case: B. 
{ rewrite /eq_size/=; intros; split; 
[lia|]. destruct H0 => //. } 
move => b B.
intros.
have H1 : eq_size A C.
destruct (eq_size_cons a b A B) => //.
destruct (eq_size_cons b c B C) => //.
by apply (IH A B). 
move: H H0.
rewrite /eq_size; intros; split;
destruct H; destruct H0.
by rewrite H -H0 .
move => x y [|]Hx [|]Hy.
{ rewrite -Hx -Hy.
rewrite (H2 a b) => /=; try left => //. 
rewrite -(H3 b c) => //=; by left. } 
{ rewrite -Hx. 
rewrite (H2 a b) => /=; try left => //.
rewrite -(H3 b y) => //=; [by left| by right]. }
rewrite -Hy. 
rewrite -(H3 b c) => /=; try left => //.
rewrite -(H2 x b) => //=; [by right| by left].
destruct H1. apply H4 => //. 
Qed.

Lemma eq_size_symm {T1 T2} (A : list (list T1))
  (B : list (list T2)) : 
  eq_size A B -> eq_size B A.
Proof.
rewrite /eq_size. intros; destruct H; split => //.
intros. by rewrite -(H0 y x).
Qed.


End SIZEDEFS.

Section MxLems.


Lemma mat_sum_nil_l :
forall (A : Type) (M : gem_defs.matrix) (f : A -> A -> A),
       mat_sum f [::] M = [::].
Proof. by []. Qed.

Lemma in_zero_matrix_length m n a: 
In a (zero_matrix m n 0%R) -> length a = n.
Proof. move : a . elim: m => //=.
move => m IH a. destruct n => //= . move => [H|H].
rewrite -H //=. by rewrite zero_vector_length.
by apply IH.
Qed.

Lemma dotprodR_dist a b v : 
length a = length b -> 
dotprodR (a +v b) v = (dotprodR a v + dotprodR b v)%R.
Proof.
move: a b.
elim : v => //=.
{ intros.
rewrite! dotprodR_nil_r; nra. } 
move => v0 v IH a. 
case : a => //=.
{ intros. 
symmetry in H.
rewrite length_zero_iff_nil in H.
rewrite H. rewrite !dotprodR_nil_l; nra. } 
move => a0 a b. case b => //=.
intros. 
rewrite /dotprodR. simpl. 
rewrite !fold_left_Rplus_Rplus.
specialize (IH a l).
rewrite /dotprodR/vec_sumR/vec_sum/map2 in IH.
rewrite IH; [|lia].  nra.
Qed.

Lemma MVR_dist A B v : 
forall (Hlen : forall a b, In a A -> In b B -> 
  length a = length b),  
(A +m B) *r v = (A *r v) +v (B *r v).
Proof.
move : A v.
elim: B => //=.
{intros; rewrite /vec_sumR/vec_sum/map2/= 
  combine_nil map_nil /mat_sumR mat_sum_nil
  /mvR/MV//=. } 
move => b B IH A.
case : A => //=.
move => a A v H.
rewrite IH. clear IH.
rewrite /vec_sumR vec_sum_cons. 
f_equal.
set (y:= vec_sumR a b).
fold (vec_sum Rplus a b).
fold (vec_sumR a b).
apply dotprodR_dist.
apply H; by left.
move => a0 b0 H1 H2.
apply H; by right.
Qed.

Lemma GEMM_nilC {T} (dot : vector -> vector -> T) 
  (sum mul : T -> T -> T) (A B : @gem_defs.matrix T) (x y : T) : 
  GEMM dot sum mul A B [] x y = [].
Proof. by rewrite /GEMM/scaleM mat_sum_nil. Qed.

Lemma GEMM_nilB {T} (dot : vector -> vector -> T) 
  (sum mul : T -> T -> T) (A C : @gem_defs.matrix T) (x y : T) : 
  GEMM dot sum mul A [] C x y = [].
Proof. by rewrite /GEMM/scaleM/MMC/=mat_sum_nil_l. Qed.

Lemma GEMM_cons {T} (dot : vector -> vector -> T) 
  (sum mul : T -> T -> T) 
  (A B C : @gem_defs.matrix T) b c (x y : T) :
let hd := vec_sum sum (scaleV mul x (MV dot A b)) (scaleV mul y c) in
GEMM dot sum mul A (b :: B) (c :: C) x y =  
  hd :: GEMM dot sum mul A B C x y.
Proof. rewrite /GEMM/mat_sum -(vec_sum_cons) /vec_sum /scaleM//=. Qed.

Lemma scaleMR_cons y d D :
scaleMR y (d :: D) = ((scaleVR y d) :: scaleMR y D).
Proof. by []. Qed.

Lemma scaleVR_dist : forall a u v,
scaleVR a (u +v v) = scaleVR a u +v (scaleVR a v).
Proof.
rewrite /scaleVR/scaleV/vec_sumR/vec_sum/map2/=. 
intros. rewrite map_map/=.
rewrite (combine_map' R R (Rmult a)
  (fun x : R * R => (a * (uncurry Rplus x))%R)) => //.
intros; simpl; nra.
Qed.

Lemma scaleMR_dist x A B: 
length A = length B -> 
scaleMR x (A +m B) = scaleMR x A +m scaleMR x B.
Proof. 
revert A x. 
elim: B => //.
{ intros. by rewrite /mat_sumR !mat_sum_nil /=. }
move =>  b B IH A.
case: A => //. 
move => a A /=. intros.
rewrite IH; try lia. 
rewrite mat_sumR_cons.
rewrite -scaleVR_dist => //.
rewrite !map_length; lia.
Qed.

Lemma mat_sumR_assoc A B C: 
eq_size A B -> eq_size B C -> 
(A +m B) +m C = A +m (B +m C).
Proof. 
revert A B. 
elim: C => //.
{ intros. by rewrite /mat_sumR !mat_sum_nil /=. }
move =>  c C IH A.
case: A => //. 
move => a A B /=.
case: B => //. move => b B. intros.
have HA : length A = length B;  
   destruct H; simpl in H. lia.
have HC : length B = length C;  
   destruct H0; simpl in H0. lia.
rewrite !mat_sumR_cons => //.
rewrite IH. rewrite vec_sumR_assoc => //.
destruct H;
rewrite (H1 a b) => //=; by left.
symmetry;
rewrite (H2 b c) => //=; by left.
by apply (eq_size_cons a b A B).
by apply (eq_size_cons b c B C).
by rewrite mat_sum_length.
rewrite mat_sum_length => //. lia.
Qed.

Lemma mat_sumR_comm A B : 
eq_size A B ->  
(A +m B)= (B +m A).
Proof. 
revert B. 
elim: A => //.
{ intros. by rewrite /mat_sumR !mat_sum_nil /=. }
move => a A IH B.
case: B => //. 
move => b B /=. intros.
have HA : length A = length B;  
   destruct H; simpl in H. lia.
have HB : eq_size A B 
by apply (eq_size_cons a b A B).
rewrite !mat_sumR_cons => //.
rewrite IH => //. rewrite vec_sumR_comm => //.
apply (H0 a b) => //=; by left.
Qed.

Lemma GEMMR_distC  (A B C D: gem_defs.matrix ) (x y : R) :
(forall c, In c C -> length c = length A) -> 
length C = length B ->
eq_size C D -> 
GEMMR A B (C +m D) x y = (GEMMR A B C x y) +m (scaleMR y D).
Proof.
move : A B C.
elim: D.
{ intros. rewrite /scaleMR/scaleM/=.
by rewrite /mat_sumR !mat_sum_nil/GEMMR GEMM_nilC. } 
move => d D IH A B C. 
case: C => //. 
{ intros. destruct H1 => //. }  
move => c C. 
case: B => //.
move => b B. intros. 
simpl in H0. 
rewrite mat_sumR_cons => //; try lia.
rewrite /GEMMR !GEMM_cons.
fold GEMMR vec_sumR scaleVR.
rewrite IH; try lia. rewrite scaleMR_cons mat_sumR_cons. 
rewrite !(vec_sumR_assoc). 
f_equal. f_equal. 
by rewrite -scaleVR_dist.
rewrite !map_length;
symmetry. by apply H; left. 
rewrite !map_length. 
destruct H1;
by symmetry ;apply H2 => /=; left.
rewrite !map_length combine_length !map_length.
have HB : length B = length C by lia.
have HC : length C = length D .
destruct H1; simpl in H1. lia.
rewrite HB HC. apply Nat.min_id.
intros; apply H => /=; by right.
destruct H1. simpl in H1.
rewrite /eq_size; split; try lia.
intros; apply H2 => /=; by right.
destruct H1; simpl in H1; lia.
Qed.

Lemma mat_sumR_scale_opp A n: 
  (0 < n) %nat -> 
  (forall a, In a A -> length a = n) -> 
  A -m A = zero_matrix (length A) n 0%R.
Proof.
elim : A . 
{ intros.  by rewrite /mat_sumR mat_sum_nil. } 
intros. rewrite mat_sumR_cons. rewrite H => //.
rewrite {1}vec_sumR_comm.
rewrite vec_sumR_minus.
suff Ha : length a = n%nat.
rewrite Ha => //=.
destruct n => //=.
apply H1 => /=. by left.
by rewrite !map_length.
intros; apply H1 => /=; by right.
by rewrite !map_length.
Qed.


End MxLems.

Section MMLems.

Lemma nth_mul' : forall (A : list (list R)) b i j
( Hj : (j < length b)%nat),
(nth 0 (nth i A []) 0%R * nth j b 0%R =
nth j (nth i (map (fun a0 : R => map (Rmult a0) b) (map (hd 0%R) A)) []) 0%R)%R.
Proof.
move =>  A. elim: A => [b i j H| a A IH b i j Hj] /=.
destruct i; destruct j => /=; ring.   
destruct i => /= //.
rewrite hd_nth => /=. 
rewrite (nth_map' (Rmult (nth 0 a 0%R)) 0%R 0%R j b) => //=.
apply /ssrnat.ltP => //.
specialize (IH b i j Hj). rewrite -IH => //.
Qed.

Lemma rowM_nil_r {T: Type} sum mul (a : list T) d: 
 rowM d sum mul 0 a [] = [].
Proof.  elim: a => //. Qed.

Lemma rowM_nil_r0 {T: Type} sum mul (a :  list T) d m: 
 rowM d (vec_sum sum) mul m a [] = (zero_vector m d).
Proof.  elim: a => //=. Qed.

(* The length of the vector and the matrix passed
  to rowM should be of equal length. This is enforced
  in theorem statements, not the definition *)
Lemma rowM_nil_l {T: Type} sum mul (B : list (list T)) d : 
 rowM d (vec_sum sum) mul 0 [] B = [].
Proof.  elim: B => //=. Qed.

Lemma rowM_nil_l0 {T: Type} sum mul (B : list (list T)) d m: 
 rowM d (vec_sum sum) mul m [] B = (zero_vector m d).
Proof.  elim: B => //=. Qed.

Lemma MM_nil_l {T : Type} (B: list (list T))
  sum mult d : 
  (@MM T d sum mult [::] B) = [::].
Proof. by []. Qed.

Lemma MM_nil_r {T : Type} (A: list (list T))
  sum mult d :  MM d sum mult A [::] = [].
Proof. case: A => //. Qed.

Lemma MM_length {T : Type} (A B: list (list T)) 
  sum mul d:
A <> [] -> B <> [] -> 
length A = length (MM d sum mul A B).
Proof.
move: B.
elim: A => //. move => a A H B.
case: B => //= [b B H1 H2]. 
assert (A = [] \/ A <> []). clear H1 H.
  case: A. by left. move => a0 l. by right.
destruct H0.
rewrite H0 MM_nil_l //.
rewrite (@H (b :: B)) //.
Qed.

Lemma rowM_length {T : Type} v (B: list (list T)) 
  sum mul d m:
  (forall b, In b B -> length b = m) -> 
  length (rowM d (vec_sum sum) mul m v B) = m.
Proof.
move:  v. 
elim: B. intros.
by case: v => //=; rewrite zero_vector_length.
move => b B IH v H.
case: v => //=[|a l]. 
by rewrite zero_vector_length.
specialize (IH l). 
remember (rowM d (vec_sum sum) mul m l B) as u.
rewrite /vec_sum/scaleV map_length combine_length map_length.
rewrite H/=; [ | by left].
rewrite IH; [lia | ]. 
move => b0 Hb0. apply H => /=. by right.
Qed.

Lemma scaleM_length {T} (x : T) A n mul :
(forall a, In a A -> length a  = n) -> 
forall a', In a' (scaleM mul x A) -> length a' = n.
Proof.
elim: A => //.
move => a A. intros.
destruct H1. 
rewrite -H1 !map_length.
apply H0 => /=; by left.
apply H => //. 
intros; apply H0 =>/=; by right.
Qed.


Lemma in_mul'_length : forall (A : list (list R)) b a0,
(length A = length b) ->
In a0 (mul' 0%R Rmult A b) -> length a0 = length b.
Proof.
move =>  A b. move: A. 
elim: b => /= [A a0 | ]. 
rewrite /mul' /=. move => HA H.
apply in_map_iff in H. elim H => x H1.
  elim H1 => H2 H3. rewrite -H2 //.
move => b0 b IH A a HA.
rewrite /mul' /=. move => H.
apply in_map_iff in H. elim H => x H1.
  elim H1 => /= H2 H3. rewrite -H2 /=.
rewrite map_length //.
Qed.

Lemma in_MM_length {T : Type} (A B: list (list T)) 
 sum mul d m:
(forall b, In b B -> length b = m) ->
forall v, In v (MM d (vec_sum sum) mul A B) -> length v = m.
Proof. 
move: B m. 
elim: A => // [a A IH B ].
case: B => // [b B m H1 v H2].
move: H2 =>  /=. move => [H2 | H2].
have Hb : (length b = m).
  apply H1 => /=. by left.
by rewrite -H2 Hb /= rowM_length.
by apply (IH (b::B) m).
Qed.

Lemma in_MMC_length {T : Type} (A B: list (list T)) 
 sum mul m d:
length A = m -> 
forall v, In v (MMC (dotprod mul sum d) A B) -> length v = m.
Proof. 
move: A m . 
elim: B => // . 
move => b B IH A m H2 v/= [|]Hv.
rewrite -Hv !map_length => //. 
apply (IH A m) => //. 
Qed.

 

Lemma  in_MM {T : Type} (A B: list (list T)) 
 a sum mul d x:
In x (MM d (vec_sum sum) mul A B) ->
In x (MM d (vec_sum sum) mul (a :: A) B).
Proof.
move: x a B. case: A => //. 
move => a0 A x a B. case : B => //.
move => b B /= [H1|H1]. 
by right; left.
by right; right.
Qed.


Lemma in_MM2 {T : Type} (A B: list (list T)) 
 a sum mul d x:
In x (MM d (vec_sum sum) mul A B) ->
In x (MM d (vec_sum sum) mul (a :: A) B) \/ x = a.
Proof.
case: A => //=.
case: B => //= a0 l a1 l1 [H | H].
by left; right; left.
by left; right; right.
Qed.

Lemma is_finite_mat_cons {NAN : Nans} {t : type} {STD : is_standard t}  a A:
@is_finite_mat t STD (a :: A) -> 
  (@is_finite_mat t STD A /\ is_finite_vec a).
Proof.
rewrite /is_finite_mat !Forall_forall /=.
move => H1. split.
{ move => x Hx. apply H1. by right. }
apply H1. by left.
Qed.

Lemma is_finite_mat_cons2 {NAN : Nans} {t : type} {STD : is_standard t} a A:
@is_finite_mat t STD A -> is_finite_vec a -> @is_finite_mat t STD (a :: A). 
Proof.
rewrite /is_finite_mat !Forall_forall /=.
move => Hx Ha [ H| x0 x [H|H]] //=.
by rewrite -H.
by apply Hx.
Qed.

Lemma in_zero_vec {NAN : Nans} {t : type} {STD : is_standard t} m x:
In x (zero_vector m (Zconst t 0)) -> x = (Zconst t 0).
Proof.
elim: m => //=;
move => [_ [|]| [_ [|]| _ _ [|] ] ] //=. 
Qed.

Lemma is_finite_vec_cons {NAN : Nans} {t : type} {STD : is_standard t} v0 v : 
  @is_finite_vec t STD (v0 :: v) -> 
  is_finite_vec v /\ is_finite v0.
Proof.
rewrite /is_finite_vec 
  !Forall_forall/=; intros; split; intros;
apply H. by right. by left.
Qed.

Lemma is_finite_vec_sum {NAN : Nans} {t : type} {STD : is_standard t} u v : 
length u = length v ->
@is_finite_vec t STD (vec_sumF u v) -> 
  @is_finite_vec t STD u /\ @is_finite_vec t STD v.
Proof.
move: v. elim: u => //=.
{ move => v H. symmetry in H.
rewrite length_zero_iff_nil in H. by rewrite H. }  
move => u0 u IH v.
case: v => //. 
rewrite /vec_sumF/vec_sum/map2/=.
move => v0 v H H1.
apply is_finite_vec_cons in H1.
elim: H1.
fold (map2 BPLUS u v).
fold (vec_sum BPLUS).
fold (@vec_sumF NAN t).
move => H1 H2. 
rewrite /is_finite_vec 
  !Forall_forall/=; intros; split.
{ move => x [|] Hx; subst.
  have FIN : (is_finite (BPLUS x v0) = true) => //.
  by move : FIN; subexpr_finite.
  have : is_finite_vec u by apply (IH v) => //; lia.
  rewrite /is_finite_vec !Forall_forall; move => H3.
  by apply H3. } 
move => x [|] Hx; subst.
have FIN : (is_finite (BPLUS u0 x) = true) => //.
by move : FIN; subexpr_finite.
have : is_finite_vec v by apply (IH v) => //; lia.
rewrite /is_finite_vec !Forall_forall; move => H3.
by apply H3.   
Qed.

Lemma is_finite_scaleV {NAN : Nans} {t : type} {STD : is_standard t} a0 a : 
is_finite_vec (scaleV BMULT a0 a) ->
  @is_finite_vec t STD a .
Proof.
rewrite /is_finite_vec !Forall_forall /scaleV //.
intros. pose proof in_map (BMULT a0) a x H0.
specialize (H (BMULT a0 x) H1).
  by move : H; subexpr_finite.
Qed.

Lemma is_finite_scaleV' {NAN : Nans} {t : type} {STD : is_standard t} a0 a : 
a <> [] -> 
@is_finite_vec t STD (scaleV BMULT a0 a) ->
  is_finite a0.
Proof.
move: a0. case: a => //. 
move => a0 a a1 H. 
rewrite /is_finite_vec !Forall_forall //=.
intros.
have : is_finite (BMULT a1 a0) = true.
apply (H0 (BMULT a1 a0)). by left.
by subexpr_finite.
Qed.


Lemma is_finite_rowM {NAN : Nans} {t : type} {STD : is_standard t} a B m
   (Hm: (0 < m)%nat) (Hb :forall b, In b B -> length b = m) 
  (Hlen: length a = length B) : 
  is_finite_vec (rowM (Zconst t 0) vec_sumF BMULT
          m a B) -> is_finite_vec a.
Proof.
move : B Hb Hlen.
elim: a => //.
{ intros; rewrite /is_finite_vec Forall_forall //=. }
move => a l IH B. move: a l IH.
case: B => //. move => b B a0 a IH  H1 H2 H3.
have Hb:  b <> []. 
  rewrite /not. intros.   
  apply length_zero_iff_nil in H.
  specialize (H1 b) => //=. rewrite H1 in H.
  rewrite H in Hm => //. simpl. by left.
simpl in H3.
apply is_finite_vec_sum in H3.
 elim: H3. move => H3 H4. 
rewrite /is_finite_vec Forall_forall //=.
move => x [Hx | Hx]. rewrite -Hx.
apply (is_finite_scaleV' a0 b) in H3 => //.
have Hlen: ((Datatypes.length a) = (Datatypes.length B)).
  simpl in H2. lia.
suff : is_finite_vec a.
rewrite /is_finite_vec Forall_forall //=.
 move => Ha. by apply Ha.
intros; apply (IH B) => //.
move => b0 Hb0. apply H1 => /=. by right. 
rewrite map_length rowM_length.
apply H1 => /=. by left.
move => b0 Hb0. apply H1 => /=. by right.
Qed.


Lemma in_MMF_finite' {NAN : Nans} {t : type} {STD : is_standard t} 
(A B : seq.seq (seq.seq (ftype t))) (m : nat)
(HB : B <> [])
(Hm : (0 < m)%nat)
(Hb :forall b, In b B -> length b = m)
(Hlen : forall x, In x A -> length x = length B):
@is_finite_mat t STD (MMF A B) -> @is_finite_mat t STD A.
Proof.
move: B HB Hb Hlen.
elim: A => //.  
move => a A IH B. 
case: B => //=. move => b B. intros.
rewrite /MMF/= in H.
apply is_finite_mat_cons in H.
elim: H; move=> H1 H2.
have Hb' : length b = m by apply Hb; left.
rewrite Hb' in H2.
apply is_finite_rowM in H2 => //.
apply is_finite_mat_cons2 => //.
apply (IH (b ::B)) => //.
move => x Hx. apply Hlen. by right.
apply is_finite_rowM in H2 => //.
all: simpl; auto.
Qed.


Lemma in_MMF_finite {NAN : Nans} {t : type} {STD : is_standard t} A B m
(HB : B <> [])
(Hm : (0 < m)%nat)
(Hb :forall b, In b B -> length b = m)
(Hlen : forall x, In x A -> length x = length B):
(forall x : vector, In x (MMF A B) ->  
  is_finite_vec x) -> 
  forall a0, In a0 A -> @is_finite_vec t STD a0.
Proof.
move: A Hlen HB Hb.
case: B => //.  
move => b B A. move: B b. 
elim : A => //. 
rewrite /MMF/=. intros.
elim: H1; intros.
have Hb' : length b = m by apply Hb; left.
rewrite -H1.
remember (rowM (Zconst t 0) vec_sumF BMULT 
  (Datatypes.length b) a (b :: B)) as u.
have Hu : is_finite_vec u.
by apply H0; left.
apply (is_finite_rowM a (b::B)
  (length b)). 
by rewrite Hb'.
move => b0 /=. move => Hb0. 
by rewrite Hb'; apply Hb.
by apply Hlen; left.
by apply H0; left.
apply (H B b) => //. 
move => x Hx.
by apply Hlen; right.
move => x Hx.
by apply H0; right.
Qed.

Lemma is_finite_vec_cons2 {NAN : Nans} {t} {STD : is_standard t} a0 (a : list (ftype t)) : 
  is_finite a0 = true -> 
  is_finite_vec a -> is_finite_vec (a0 :: a).
Proof.
rewrite /is_finite_vec !Forall_forall; intros. 
destruct H1; subst => //.
by apply H0. Qed.

Lemma is_finite_vec_mapBPLUS {NAN : Nans} {t} {STD : is_standard t}  (a : list (ftype t)) b : 
length a = length b -> 
is_finite_vec (map (uncurry BPLUS) (combine a b)) -> 
is_finite_vec a /\ is_finite_vec b.
Proof.
move : a. elim: b => //.
{ intros.
rewrite length_zero_iff_nil in H; subst => //. } 
move =>  b0 b IH a. case : a => //. intros. simpl in H.
simpl in H0. apply is_finite_vec_cons in H0. 
destruct H0.
have H2: is_finite (BPLUS a b0) = true => //.
move: H2. subexpr_finite.
intros; split; apply is_finite_vec_cons2 => //.
apply IH => //; lia.
apply (IH l) => //; lia.
Qed.


Lemma is_finite_scaleM {NAN : Nans} {t : type} {STD : is_standard t} x A : 
  @is_finite_mat t STD (scaleM BMULT x A) ->
  @is_finite_mat t STD A .
Proof.
rewrite /is_finite_mat !Forall_forall /scaleM //.
intros. pose proof in_map ( map (BMULT x) ) A x0 H0. 
specialize (H (map (BMULT x) x0) H1).
destruct A; destruct x0 => //.
simpl in H; apply is_finite_vec_cons in H; destruct H.
have H3: is_finite (BMULT x f) = true => //. move : H3.
subexpr_finite.
apply is_finite_vec_cons2 => //.
by apply (is_finite_scaleV x).
Qed.

Lemma is_finite_mat_sum {NAN : Nans} {t} {STD : is_standard t}
(A B : @gem_defs.matrix (ftype t)) : 
eq_size A B -> 
@is_finite_mat t STD (mat_sumF A B) -> is_finite_mat A /\ is_finite_mat B.
Proof.
move : A. elim: B.
{ move => A. 
rewrite /mat_sumF mat_sum_nil.
move => H. destruct H => //.
rewrite length_zero_iff_nil in H; subst => //. } 
move => b B IH A.  case: A => //.
{ intros. destruct H => //. }
rewrite /mat_sumF/mat_sum/map2/=.
move => a A. intros.
apply eq_size_cons in H; destruct H.
pose proof (IH A H).
apply is_finite_mat_cons in H0.
destruct H0. 
have HA: is_finite_mat A. apply H2 => //.
have HB: is_finite_mat B. apply H2 => //.
split.
all: (apply is_finite_mat_cons2 => //;
apply is_finite_vec_mapBPLUS in H3; destruct H3 => //).
Qed.

Lemma eq_size_scale {T} (x : T) A mul n: 
 (forall a, In a A -> length a = n) -> 
 eq_size (scaleM mul x A) A.
Proof.
rewrite /eq_size; split.
by rewrite !map_length.
intros. apply (eq_size_scaleM mul x A) => //.
intros. rewrite H => //.
symmetry; by apply H.
Qed.

End MMLems.

Section GenLems.

Lemma in_FT2R_map  {t}  (A : list (list (ftype t))) x m: 
  (forall y, In y A -> length y = m) -> 
  In x (map_mat FT2R A) -> length x = m.
Proof.
move => Ha Hin. 
apply in_map_iff in Hin.
destruct Hin. destruct H.
rewrite -H  map_length.
by apply Ha.
Qed.

End GenLems. 
 