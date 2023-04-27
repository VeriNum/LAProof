(** This file contains the low level list 
  definitions of matrices and vectors, along with 
  useful lemmas about these definitions 

  Copyright Ariel Kellison, 2023 *)

Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.

Require Import common op_defs dotprod_model sum_model.
Require Import float_acc_lems list_lemmas.

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

Definition is_finite_vec {t : type} (v: vector) : Prop := 
  Forall (fun x => Binary.is_finite (fprec t) (femax t) x = true) v.

Definition is_finite_mat {t : type} (A: matrix) : Prop := 
  Forall (fun x => @is_finite_vec t x) A.

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
Definition vec_sumF {NAN : Nans} {t : type} :=  vec_sum (@BPLUS NAN t).

(* generic matrix sum *)
Definition mat_sum {T: Type} (sum : T -> T -> T):= 
  map2 (map2 sum).

(* sum matrices of reals *)
Definition mat_sumR :=  mat_sum Rplus .

(* sum matrices of floats *)
Definition mat_sumF {NAN : Nans} {t: type} := mat_sum (@BPLUS NAN t).

(* generic matrix vector multiplication *)
Definition MV {A: Type} (DOT : @vector A -> @vector A -> A) 
      (m: matrix) (v: vector) : vector :=
      map (fun row => DOT row v) m.

(* floating-point matrix vector multiplication *)
Definition mvF {NAN : Nans}  {t: type} : matrix -> vector -> vector  :=
      MV (@dotprodF NAN t).

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
Definition MMTF {NAN : Nans}  {t: type} : matrix -> matrix -> matrix  := 
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
Definition MMF' {NAN : Nans}  {t: type} : matrix -> matrix -> matrix  := 
  MM' (Zconst t 0) dotprodF.

(* real valued matrix matrix multiplication *)
Definition MMR' : matrix -> matrix -> matrix  := 
  MM' 0%R dotprodR.

(* scale vector v by constant a *)
Definition scaleV {T} (mul: T -> T -> T) (a : T) (v : vector) : vector := 
  map (mul a) v.

Definition scaleVR := @scaleV R Rmult.
Definition scaleVF {NAN : Nans} {t : type} := @scaleV (ftype t) (@BMULT NAN t).

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
Definition MMF {NAN : Nans}  {t: type} : matrix -> matrix -> matrix  := 
  MM (Zconst t 0) (@vec_sumF NAN t) (@BMULT NAN t).

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
Definition MMCF {NAN : Nans} {t: type}  := MMC (@dotprodF NAN t).

Definition scaleM {T} (mul : T -> T -> T) a M := map_mat (mul a) M.

Definition scaleMR := scaleM Rmult.
Definition scaleMF {NAN : Nans} {t: type} := scaleM (@BMULT NAN t).

Definition GEMM {T} (dot : vector -> vector -> T) 
  (sum mul : T -> T -> T) (A B C: matrix) (a b : T) := 
  mat_sum sum (scaleM mul a (MMC dot A B)) (scaleM mul b C).

Definition GEMMR := GEMM dotprodR Rplus Rmult.
Definition GEMMF {NAN : Nans} {t: type} := 
                      GEMM dotprodF (@BPLUS NAN t) (@BMULT NAN t).
  
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

Lemma mvF_len {NAN : Nans} t m v:
  length (@mvF NAN t m v)  = length m.
Proof. induction m; simpl; auto. Qed.

Lemma dotprodF_nil {NAN : Nans} {t: type} row :
dotprodF row [] = (Zconst t 0). 
Proof. destruct row; simpl; auto. Qed. 

Lemma mvF_nil {NAN : Nans} {t: type} : forall m, @mvF NAN t m [] = zero_vector (length m) (Zconst t 0).
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

Lemma vec_sum_zeroF {NAN : Nans} {t : type}:
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
destruct a; simpl; auto.
destruct s; simpl; auto.
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

Lemma length_mvR_mvF {NANS : Nans} {t : type} : forall (m : @matrix (ftype t)) v, 
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

Lemma is_finite_mat_cons {NAN : Nans} {t : type} a A:
is_finite_mat (a :: A) -> 
  (@is_finite_mat t A /\ is_finite_vec a).
Proof.
rewrite /is_finite_mat !Forall_forall /=.
move => H1. split.
{ move => x Hx. apply H1. by right. }
apply H1. by left.
Qed.

Lemma is_finite_mat_cons2 {NAN : Nans} {t : type} a A:
@is_finite_mat t A -> is_finite_vec a -> is_finite_mat (a :: A). 
Proof.
rewrite /is_finite_mat !Forall_forall /=.
move => Hx Ha [ H| x0 x [H|H]] //=.
by rewrite -H.
by apply Hx.
Qed.

Lemma in_zero_vec {NAN : Nans} {t : type} m x:
In x (zero_vector m (Zconst t 0)) -> x = (Zconst t 0).
Proof.
elim: m => //=;
move => [_ [|]| [_ [|]| _ _ [|] ] ] //=. 
Qed.

Lemma is_finite_vec_cons {NAN : Nans} {t : type} v0 v : 
  @is_finite_vec t (v0 :: v) -> 
  is_finite_vec v /\ Binary.is_finite _ _ v0.
Proof.
rewrite /is_finite_vec 
  !Forall_forall/=; intros; split; intros;
apply H. by right. by left.
Qed.

Lemma is_finite_vec_sum {NAN : Nans} {t : type} u v : 
length u = length v ->
@is_finite_vec t (vec_sumF u v) -> 
  @is_finite_vec t u /\ @is_finite_vec t v.
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
fold (map2 (@BPLUS NAN t) u v).
fold (vec_sum (@BPLUS NAN t)).
fold (@vec_sumF NAN t).
move => H1 H2. 
rewrite /is_finite_vec 
  !Forall_forall/=; intros; split.
{ move => x [|] Hx.
  have : (Binary.is_finite _ _ (BPLUS u0 v0)) = true.
  apply H2; left => //. rewrite -Hx. 
  destruct u0; destruct v0; 
  destruct s; destruct s0 => //=.
  have : is_finite_vec u. apply (IH v) => //. lia.
  rewrite /is_finite_vec !Forall_forall/=; intros.
  apply H0 => //. } 
{ move => x [|] Hx.
  have : (Binary.is_finite _ _ (BPLUS u0 v0)) = true.
  apply H2; left => //. rewrite -Hx. 
  destruct u0; destruct v0; 
  destruct s; destruct s0 => //=.
  have : is_finite_vec v. apply (IH v) => //. lia.
  rewrite /is_finite_vec !Forall_forall/=; intros.
  apply H0 => //. } 
Qed.

Lemma is_finite_scaleV {NAN : Nans} {t : type} a0 a : 
is_finite_vec (scaleV BMULT a0 a) ->
  @is_finite_vec t a .
Proof.
rewrite /is_finite_vec !Forall_forall /scaleV //.
intros. pose proof in_map (@BMULT NAN t a0) a x H0.
specialize (H (BMULT a0 x) H1).
destruct x; destruct a0 => //. 
Qed.

Lemma is_finite_scaleV' {NAN : Nans} {t : type} a0 a : 
a <> [] -> 
@is_finite_vec t (scaleV BMULT a0 a) ->
  Binary.is_finite _ _ a0.
Proof.
move: a0. case: a => //. 
move => a0 a a1 H. 
rewrite /is_finite_vec !Forall_forall //=.
intros.
have : @Binary.is_finite _ _ (BMULT a1 a0) = true.
apply (H0 (BMULT a1 a0)). by left.
intros. destruct a0; destruct a1 => //.
Qed.


Lemma is_finite_rowM {NAN : Nans} {t : type} a B m
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
apply (IH B) => //.
move => b0 Hb0. apply H1 => /=. by right. 
rewrite map_length rowM_length.
apply H1 => /=. by left.
move => b0 Hb0. apply H1 => /=. by right.
Qed.



Lemma in_MMF_finite' {NAN : Nans} {t : type} A B m
(HB : B <> [])
(Hm : (0 < m)%nat)
(Hb :forall b, In b B -> length b = m)
(Hlen : forall x, In x A -> length x = length B):
is_finite_mat (MMF A B) -> @is_finite_mat t A.
Proof.
move: B HB Hb Hlen.
elim: A => //.  
move => a A IH B. 
case: B => //=. move => b B. intros.
rewrite /MMF/= in H.
apply is_finite_mat_cons in H.
elim: H; move=> H1 H2.
have Hb' : length b = m by apply Hb; left.
apply is_finite_rowM in H2 => //.
apply is_finite_mat_cons2 => //.
apply (IH (b ::B)) => //.
move => x Hx. apply Hlen. by right.
apply is_finite_rowM in H2 => //.
by rewrite Hb'. 
by rewrite Hb'.
move => b0 /=. move => Hb0. 
by rewrite Hb'; apply Hb.
by apply Hlen; left.
move => b0 /=. move => Hb0. 
by rewrite Hb'; apply Hb.
by apply Hlen; left.
Qed.


Lemma in_MMF_finite {NAN : Nans} {t : type} A B m
(HB : B <> [])
(Hm : (0 < m)%nat)
(Hb :forall b, In b B -> length b = m)
(Hlen : forall x, In x A -> length x = length B):
(forall x : vector, In x (MMF A B) ->  
  is_finite_vec x) -> 
  forall a0, In a0 A -> @is_finite_vec t a0.
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

Lemma scaleVR_dist : forall a u v,
scaleVR a (u +v v) = scaleVR a u +v (scaleVR a v).
Proof.
rewrite /scaleVR/scaleV/vec_sumR/vec_sum/map2/=. 
intros. rewrite map_map/=.
rewrite (combine_map' R R (Rmult a)
  (fun x : R * R => (a * (uncurry Rplus x))%R)) => //.
intros; simpl; nra.
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
 