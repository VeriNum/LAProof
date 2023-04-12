Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.

Require Import common op_defs dotprod_model sum_model.
Require Import float_acc_lems list_lemmas.

Section MVGenDefs. 

Definition matrix {A : Type} := list (list A).

Definition vector {A : Type} := list A.

Fixpoint zero_vector {A: Type} (m : nat) (zero : A) : vector := 
  match m with 
  | S n => zero :: zero_vector n zero
  | _ => []
  end. 

Fixpoint zero_matrix {A: Type} (m n: nat) (zero : A) : matrix := 
  match m with 
  | S m' => zero_vector n zero :: zero_matrix m' n zero
  | _ => []
  end. 

Definition is_finite_vec {t : type} (v: vector) : Prop := 
  forall x, In x v -> Binary.is_finite (fprec t) (femax t) x = true.

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

(* floating-point matrix vector multiplication *)
Definition mvF {NAN : Nans}  {t: type} (m: matrix ) (v: vector ) : vector  :=
      map (fun row => @dotprodF NAN t row v) m.

(* real valued matrix vector multiplication *)
Definition mvR  (m: matrix) (v: vector) : vector :=
      map (fun row => dotprodR row v) m.

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
  length (zero_matrix m n zero) = m .
Proof. induction m; unfold zero_matrix; simpl; auto. Qed. 

Lemma mvF_len {NAN : Nans} t m v:
  length (@mvF NAN t m v)  = length m.
Proof. induction m; simpl; auto. Qed.

Lemma dotprodF_nil {NAN : Nans} {t: type} row :
dotprodF row [] = (Zconst t 0). 
Proof. destruct row; simpl; auto. Qed. 

Lemma mvF_nil {NAN : Nans} {t: type} : forall m, @mvF NAN t m [] = zero_vector (length m) (Zconst t 0).
Proof. 
intros; unfold mvF.
set (f:= (fun row : list (ftype t) => dotprodF row [])).
replace (map f m) with  (map (fun _ => Zconst t 0) m).
induction m; simpl; auto.
{ rewrite IHm; auto. }
apply map_ext_in; intros.
subst f; simpl. rewrite dotprodF_nil; auto.
Qed.

Lemma mvR_nil : forall m, mvR m [] = zero_vector (length m) 0%R. 
Proof.
intros; unfold mvR.
set (f:= (fun row : list R => dotprodR row [])).
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
  (Hin : forall row, In row B -> length row  = n), 
  mat_sum B (zero_matrix (length B) n 0%R) Rplus = B.
Proof.
intros ? ? ?. induction B; auto.
fold (mat_sumR (a :: B) (zero_matrix (length (a :: B)) n 0)).
fold (mat_sumR B (zero_matrix (length B) n 0)) in IHB.
simpl; rewrite mat_sumR_cons.
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
  unfold mvR, mvF, map_mat.
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