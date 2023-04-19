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
Definition vec_sum {A: Type} (u v : vector) (sum : A -> A -> A)  : @vector A := 
  map2 sum u v.

(* sum vectors of reals *)
Definition vec_sumR u v :=  vec_sum u v Rplus.

(* generic matrix sum *)
Definition mat_sum {T: Type} (A B : matrix) (sum : T -> T -> T) : @matrix T := 
  map2 (map2 sum) A B.

(* sum matrices of reals *)
Definition mat_sumR A B :=  mat_sum A B Rplus.

(* sum matrices of floats *)
Definition mat_sumF {NAN : Nans} {t: type} A B := mat_sum A B (@BPLUS NAN t).

(* generic matrix vector multiplication *)
Definition MV {A: Type} (DOT : @vector A -> @vector A -> A) (m: matrix) (v: vector) : vector :=
      map (fun row => DOT row v) m.

(* floating-point matrix vector multiplication *)
Definition mvF {NAN : Nans}  {t: type} : matrix -> vector -> vector  :=
      MV (@dotprodF NAN t).

(* real valued matrix vector multiplication *)
Definition mvR  : matrix -> vector -> vector  := MV dotprodR.

(* helper for generic matrix-matrix multiplication *)
Definition mul' {A: Type} (d : A) (mult: A -> A -> A) (m : @matrix A) (v : @vector A) := 
  map (fun a => map (mult a) v) (map (hd d) m).

(* generic matrix-matrix multiplication on row major order matrices of size (m x n) *)
Fixpoint MM {A: Type} (d : A) (mat_sum : @matrix A -> @matrix A -> @matrix A) (mult: A -> A -> A)
 (m : nat) (m1 m2: @matrix A) : @matrix A :=
  match m2 with
    | row :: b => mat_sum (mul' d mult m1 row) (MM d mat_sum mult m (map (@tl A) m1) b)
    | nil => zero_matrix m m d
  end.

(* floating-point matrix matrix multiplication. *)
Definition MMF {NAN : Nans}  {t: type} (m : nat) : matrix -> matrix -> matrix  := 
  MM (Zconst t 0) (@mat_sumF NAN t) (@BMULT NAN t) m.

(* real valued matrix matrix multiplication *)
Definition MMR (m : nat) : matrix -> matrix -> matrix  := MM 0%R mat_sumR Rmult m.

End MVOpDefs.


Notation "A *f v" := (mvF A v) (at level 40).
Notation "A *r v"  := (mvR A v) (at level 40).
Notation "A *fr v" := (map FT2R (mvF A v)) (at level 40).

Notation "u -v v" := (vec_sum u v Rminus) (at level 40).
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
  length (mat_sum A B sum) = length A.
Proof. intros. unfold mat_sum; rewrite map2_length; auto. Qed.

Lemma zero_vector_length {A : Type} (m : nat) (zero : A) :
  length (zero_vector m zero) =  m.
Proof. induction m; simpl; auto. Qed.

Lemma nth_zero_vector m i:
  nth i (zero_vector m 0%R) 0%R = 0%R.
Proof. revert i. induction m ; simpl; auto; destruct i; simpl ;auto. Qed.

Lemma vec_sumR_cons : 
forall (u v : vector) u0 v0,
vec_sum (u0 :: u) (v0 :: v) Rplus = (u0 + v0) :: vec_sum u v Rplus.
Proof. induction u; destruct v; (intros; unfold vec_sum, map2; simpl; auto). Qed.

Lemma vec_sum_zeroR:
  forall (v : vector),
  vec_sum v (zero_vector (length v) 0%R) Rplus = v.
Proof.
intros; induction v; simpl; auto.
rewrite vec_sumR_cons, IHv, Rplus_0_r; auto.
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
  mat_sum B (zero_matrix (length B) n 0%R) Rplus = B.
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
  mat_sum M [] f = [].
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
vec_sum u v Rminus = vec_sum u (map Ropp v) Rplus.
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
length u = length (vec_sum u v f).
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
length u = length (vec_sum v w f).
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
nth j u 0%R - nth j a 0%R = nth j (vec_sum u a Rminus) 0%R.
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
  nth i (vec_sum u1 u2 op) 0 = op (nth i u1 0) (nth i u2 0).
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
       mat_sum [::] M f = [::].
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

Lemma MM_nil_r {T : Type} (A : list (list T))
  sum mult d m: 
(@MM T d sum mult m A [::]) = zero_matrix m m d.
Proof.  by []. Qed.

Lemma MMR_nil_r A m: 
(MMR m A [::]) = zero_matrix m m 0%R.
Proof.  by []. Qed.

Lemma MMR_nil_l B m : 
B <> nil ->
MMR m [::] B = [::].
Proof. destruct B => //. Qed.

Lemma MMF_nil_l {NAN: Nans} {t : type}  B m : 
B <> nil ->
@MMF NAN t m [::] B = [::].
Proof. destruct B => //. Qed.

Lemma MMR_length A B (m : nat) : 
length A = m -> 
length A = length (MMR m A B).
Proof.
move : B m .
case : A => // [B| a A].
  case : B  => /= [ m H1 | a A m H1] //.
  rewrite MMR_nil_r. by rewrite -H1. 
move => B. move: a A .  
elim : B => //= [a A m H1 |b B IH a A m H1].
   rewrite MMR_nil_r zero_matrix_length //. lia.
rewrite mat_sum_length.
by rewrite !map_length.
rewrite -IH /=.
rewrite !map_length //.
rewrite !map_length //.
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

Lemma in_MMR_length A B (m : nat) : 
length A = m -> 
(forall b, In b B -> length b = m) ->
forall v, In v (MMR m A B) -> length v = m.
Proof. 
move: A m. 
elim: B => /= [A m Hlen1 Hlen2 v| b B IH A m H1 H2 v].
rewrite MMR_nil_r //.
apply in_zero_matrix_length.
rewrite /MMR/MM . move => H.
apply in_map_iff in H. 
elim H => x H3. clear H.
move: H3. elim: x => /=. move => x1 x2 H.
elim H => H3 H4.  clear H.
rewrite -H3 /map2/= map_length. clear H3.
rewrite combine_length.
fold (@MM R 0%R mat_sumR Rmult) in H4.
fold (@MMR m (map (tl (A:=R)) A) B) in H4.
have Hm : (Datatypes.length (map (tl (A:=R)) A)) = m.
  by rewrite map_length.
have Hm2 : 
(forall b : seq.seq R, (In b B) -> (Datatypes.length b) = m).
  move => b0 Hb. apply H2. by right.
rewrite (IH (map (tl (A:=R)) A) m Hm Hm2 x2). 
have Hx1 : length x1 = m.
  rewrite (in_mul'_length A b x1).
apply H2. by left.
rewrite H1. symmetry. apply H2. by left.
by apply in_combine_l in H4.
rewrite Hx1 => //. lia. 
by apply in_combine_r in H4.
Qed.
 

End MMLems. 