(* This file contains theorems connecting MathComp operations on 
  matrices and vectors to operations on lists. *)

Require Import vcfloat.VCFloat.
Require Import List Reals.
Require Import common op_defs dotprod_model sum_model.
Require Import dot_acc float_acc_lems list_lemmas gem_defs.
Import ListNotations.
Require Import  FEC.Common.CommonSSR.

From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.
From Coquelicot Require Import Coquelicot.
From mathcomp.analysis Require Import Rstruct.
From mathcomp Require Import matrix all_ssreflect all_algebra ssralg ssrnum bigop.
Require Import mc_extra2.

Set Bullet Behavior "Strict Subproofs". 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import VST.floyd.functional_base.


Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import List ListNotations.

From mathcomp.algebra_tactics Require Import ring.

Section MVtoMC_Defs.

Definition getv  (l:  (list R)) i  :=
   (nth i l 0%R).

Definition getm  (l: list (list R)) i j :=
   (nth j (nth i l []) 0%R).

Definition vector_to_vc (m' : nat) (v: @vector R) : 'cV[R]_m' := 
  let m := Z.of_nat m' in 
\matrix_(i < m', j < 1) 
  (getv v  (fintype.nat_of_ord i)).

Definition matrix_to_mx (m' n': nat) (mx: @gem_defs.matrix R) : 'M[R]_(m',n') := 
  let m := Z.of_nat m' in 
  let n := Z.of_nat n' in 
\matrix_(i < m', j < n') 
  (getm mx (fintype.nat_of_ord i) (fintype.nat_of_ord j)).

End MVtoMC_Defs.

Section MVtoMC_Lems.

Lemma matrix_to_mx_nil n': 
matrix_to_mx 0 n' [] = 0.
Proof.
by rewrite /matrix_to_mx/getm// /=;
apply/matrixP =>  k i /[!mxE];
destruct k. 
Qed.

Lemma vector_to_vc_nil : 
vector_to_vc 0 [] = 0.
Proof. 
by rewrite /vector_to_vc/getv // /=;
apply/matrixP =>  k i /[!mxE] /=;
destruct k. 
Qed.

Lemma vec_sum_nth_plus : forall u1 u2 
  (Hlen: length u2 = length u1) i,
nth i (u1 +v u2) 0 = nth i u1 0 + nth i u2 0.
Proof. by apply gem_defs.vec_sum_nth_plus. Qed.

Lemma matrix_to_mx_plus : forall A E 
  (Hlen1: length A = length E)
  (Hlen2: forall a e, In a A -> In e E -> length a = length e),
  matrix_to_mx (length A) (length E)
  (A +m E) = matrix_to_mx (length A) (length E) A + matrix_to_mx(length A) (length E) E.
Proof.
move => A E Hlen1 Hlen2.
rewrite /matrix_to_mx/getm => /=.
apply /matrixP => i j; do ![rewrite mxE | ].
rewrite  -(vec_sum_nth_plus).
f_equal. clear j. revert Hlen1 Hlen2 i. revert E.
elim :A  => [| a l IH E Hlen1 Hin i].
  destruct i => //.
destruct E => //. destruct i; destruct m => /= //.
have Hlen3 : length l = length E. simpl in Hlen1 . lia.
have Hin1 : (forall a e : seq.seq R,
     In a l ->
     In e E -> Datatypes.length a = Datatypes.length e) by
  (move => a0 e Ha He; apply Hin; simpl; right => //).
have Hn : (m < length E)%nat. simpl in i. rewrite -Hlen3. lia. 
rewrite -Hlen3 in Hn.
have Hnord : (nat_of_ord (Ordinal Hn) = m) => //.
specialize (IH E Hlen3 Hin1 (Ordinal Hn)). rewrite Hnord in IH. 
rewrite -IH. f_equal.
by symmetry; apply Hlen2; apply nth_In => //; destruct i => /= ; lia.
Qed.

Lemma matrix_to_mx_plus' : forall A E m
  (Hlen1: length A = length E)
  (Hlen2: forall a e, In a A -> In e E -> length a =  m 
    /\ length e = m),
  matrix_to_mx (length A) m (A +m E) = 
  matrix_to_mx (length A) m A + matrix_to_mx (length A) m E.
Proof.
move => A E m Hlen1 Hlen2.
rewrite /matrix_to_mx/getm => /=.
apply /matrixP => i j; do ![rewrite mxE | ].
rewrite -(vec_sum_nth_plus).
f_equal. clear j. revert Hlen1 Hlen2 i. revert E.
elim :A  => [  |  a l IH E Hlen1 Hin i].
by destruct i.
destruct E => //. 
destruct i; destruct m0 => /= //.
have Hlen3 : length l = length E. simpl in Hlen1 . lia.
have Hin1 : (forall a e : seq.seq R,
     In a l ->
     In e E -> length a = m /\ length e = m).
  move => a0 e Ha He. 
specialize (Hin a0 e). apply Hin; simpl; auto.
have Hm0 : (m0 < length E)%nat. simpl in i. 
rewrite -Hlen3. lia. rewrite -Hlen3 in Hm0.
have Hnord : (nat_of_ord (Ordinal Hm0) = m0) => //.
specialize (IH E Hlen3 Hin1 (Ordinal Hm0)). rewrite Hnord in IH. 
rewrite -IH. f_equal. symmetry.
have Hlen3 : (length (nth i A []) = m /\ length (nth i E []) = m).
apply (Hlen2  (nth i A []) (nth i E [])); apply nth_In;
destruct i => /= ; lia.
by destruct Hlen3; etransitivity; [apply H | ].
Qed.

Lemma matrix_to_mx_plus_m : forall A E m n
  (Hm   : m = length A)
  (Hlen1: length A = length E)
  (Hlen2: forall a e, In a A -> In e E -> length a =  n 
    /\ length e = n),
  matrix_to_mx m n (A +m E) = 
  matrix_to_mx m n A + matrix_to_mx m n E.
Proof.
move => A E m n Hm Hlen1 Hlen2.
rewrite /matrix_to_mx/getm => /=.
apply /matrixP => i j; do ![rewrite mxE | ].
rewrite -(vec_sum_nth_plus).
f_equal. clear j. revert Hlen1 Hlen2 Hm i. revert m. revert E.
elim : A  => [ |  a l IH E m Hlen1 Hin Hm i]. 
by (destruct m => //; destruct i).
destruct E => //. 
(destruct m => //; destruct i).
destruct m0 => /= //.
have Hlen3 : length l = length E. simpl in Hlen1 . lia.
have Hin1 : (forall a e : seq.seq R,
     In a l ->
     In e E -> length a = n /\ length e = n).
  move => a0 e Ha He. 
specialize (Hin a0 e). apply Hin; simpl; auto.
have Hm0 : (m0 < length E)%nat. simpl in i. 
rewrite -Hlen3. simpl in Hm. lia. rewrite -Hlen3 in Hm0.
have Hm' : m = Datatypes.length l by (simpl in Hm; lia).
rewrite -Hm' in Hm0.
have Hnord : (nat_of_ord (Ordinal Hm0) = m0) => //.
specialize (IH E m Hlen3 Hin1 Hm'(Ordinal Hm0)). 
rewrite -IH. f_equal. symmetry.
have Hlen3 : (length (nth i A []) = n /\ length (nth i E []) = n).
apply (Hlen2  (nth i A []) (nth i E [])); apply nth_In;
destruct i => /= ; lia.
by destruct Hlen3; etransitivity; [apply H | ].
Qed.

Lemma vector_to_vc_plus u1 u2
  (Hlen: length u1 = length u2) : 
  vector_to_vc (length u2) (u1 +v u2) = 
      (vector_to_vc (length u2) u1) + (vector_to_vc (length u2) u2).
Proof.
rewrite /vector_to_vc/getv => /=.
apply /matrixP => i j; do ![rewrite mxE | ].
by destruct i; apply vec_sum_nth_plus.
Qed.

Lemma vector_to_vc_plus' u1 u2 m 
  (Hm: m = length u2) 
  (Hlen: length u1 = length u2) : 
  vector_to_vc m (u1 +v u2) = 
      (vector_to_vc m u1) + (vector_to_vc m u2).
Proof.
rewrite /vector_to_vc/getv => /=.
apply /matrixP => i j; do ![rewrite mxE | ].
by destruct i; apply vec_sum_nth_plus.
Qed.


Lemma vector_to_vc_mulmx' B u2 i:
nth i (B *r u2) 0%R = dotprodR (nth i B []) u2.
Proof.
by rewrite /mvR (map_nth (dotprodR^~ u2) B []).
Qed.

Lemma  vec_to_vc_dotproR v1 v2 i j: 
dotprodR v1 v2 = (vector_to_vc 1 (dotprodR v1 v2 :: [])) i j.
Proof.
by rewrite !mxE /getv; destruct i; destruct m.
Qed.

Lemma vector_to_vc_mulmxp: forall v1 v2,
  length v1 = length v2 -> 
  vector_to_vc 1 (dotprodR v1 v2 :: []) = 
  (vector_to_vc (length v1) v1)^T *m  (vector_to_vc (length v1) v2).
Proof.
move => v1 /=; elim : v1 => /= [ | a l IH ]. 
{ rewrite vector_to_vc_nil /vector_to_vc trmx0 => v2 H. 
rewrite mul0mx dotprodR_nil_l /getv. 
apply /matrixP => i j; do ![rewrite mxE /getv];
  destruct i; destruct m => /= //. }
destruct v2 => /= // Hlen'.
have : ( (length l = 0)%nat \/ ( 0 <> length l)%nat ) by lia. 
  move => [Hl | Hl].
{ rewrite Hl. rewrite Hl in Hlen'.  
apply length_zero_iff_nil in Hl; rewrite Hl.
have Hv2 : (length v2 = 0)%nat by lia.
apply length_zero_iff_nil in Hv2. 
  rewrite Hv2 /vector_to_vc /getv /dotprodR.
apply /matrixP => i j; do ![rewrite mxE /getv].
rewrite (@big_nth R _ Rplus _ i) ordinal_enum_size index_ord_enum
  (@big_nat_recl R 0 Rplus) => //. 
  rewrite ((@CommonSSR.nth_ord_enum 1) 0).
destruct i; destruct m => /= //.
rewrite Rplus_comm !mxE /=. 
f_equal => //.
rewrite big_nat_cond. 
rewrite big_pred0 => //. }
rewrite /dotprodR => /=.
rewrite fold_left_Rplus_Rplus.
apply /matrixP => i j; do ![rewrite mxE /getv].
assert ((fold_left Rplus (map (uncurry Rmult) (combine l v2)) 0) =
  ((vector_to_vc 1 (dotprodR l v2 :: [])) i j)).
apply vec_to_vc_dotproR. 
rewrite H. clear H.
rewrite IH. clear IH.
rewrite /vector_to_vc.
have Hord: ( 0 < (Datatypes.length l).+1)%nat by lia.
rewrite (@big_nth _ 0 Rplus _ (Ordinal Hord))
  (@big_ltn R 0 Rplus) /index_enum  ordinal_enum_size. 
rewrite (@big_addn R 0 Rplus 0).
replace (nat_of_ord i) with 0%nat  => /= .
rewrite  !mxE. f_equal => /= //.
rewrite (@ordinal_enum (Datatypes.length l).+1
  (Ordinal Hord)) /= /getv /= //.
assert (((Datatypes.length l).+1 - 1)%nat =
  Datatypes.length l) by lia. 
rewrite H. clear H. 
have Hord1: ( 0 < (Datatypes.length l))%nat by lia.
rewrite big_nat_cond. 
rewrite (@big_nth R _ Rplus _ (Ordinal Hord1) )
  /= /index_enum /=  ordinal_enum_size.
rewrite big_nat_cond. 
apply: eq_big => k //.
move => Hk'.
have Hk : (k < Datatypes.length l)%nat by lia.
have Hkp : (k + 1 < (Datatypes.length l).+1)%nat by lia.
rewrite (@ordinal_enum (Datatypes.length l).+1 (Ordinal Hkp)  (Ordinal Hord)).
rewrite (@ordinal_enum (Datatypes.length l)    (Ordinal Hk)   (Ordinal Hord1)).
rewrite /getv /= !mxE.
destruct k => /= // ; repeat f_equal => /= //; lia.
destruct i; destruct m => /= //.
all: lia.
Qed.

Lemma vector_to_vc_mulmx : forall B u2
  (Hlen: forall x, In x B -> length x = length u2),
  vector_to_vc (length B) (B *r u2) = 
  matrix_to_mx (length B) (length u2) B *m  (vector_to_vc (length u2) u2).
Proof.
move => B u2 Hin.
apply /matrixP => i j; do ![rewrite mxE /getv].
rewrite vector_to_vc_mulmx' => //.
pose proof vec_to_vc_dotproR (@nth (seq.seq R) i B []) u2 j j.
rewrite H ; clear H.
pose proof @vector_to_vc_mulmxp (@nth (seq.seq R) i B []) u2.
have Hlen': (@Datatypes.length R (@nth (seq.seq R) i B []) = 
 length u2). 
{ apply Hin.  apply nth_In. destruct i.  
have Hord : (nat_of_ord (Ordinal i) = m) => //.
rewrite Hord; lia. }
rewrite H => //.
rewrite mxE /getv/matrix_to_mx/vector_to_vc/getm/getv /= .
rewrite Hlen'.
apply: eq_bigr => k _; rewrite !mxE => //.
Qed.

Lemma vector_to_vc_mulmx_m : forall B u2 m n
  (Hm : m = length B)
  (Hn : n = length u2)
  (Hlen: forall x, In x B -> length x = n),
  vector_to_vc m (B *r u2) = 
  matrix_to_mx m n B *m  (vector_to_vc n u2).
Proof.
move => B u2 m n Hm Hn Hin.
apply /matrixP => i j; do ![rewrite mxE /getv].
rewrite vector_to_vc_mulmx' => //.
pose proof vec_to_vc_dotproR (@nth (seq.seq R) i B []) u2 j j.
rewrite H ; clear H.
pose proof @vector_to_vc_mulmxp (@nth (seq.seq R) i B []) u2.
have Hlen': (@Datatypes.length R (@nth (seq.seq R) i B []) = 
 length u2).  
{ rewrite Hin => //.  apply nth_In. destruct i.  
have Hord : (nat_of_ord (Ordinal i) = m0) => //. 
rewrite Hord; lia. }
rewrite H => //.
rewrite mxE /getv/matrix_to_mx/vector_to_vc/getm/getv /= .
rewrite Hlen'. subst n.
apply: eq_bigr => k _; rewrite !mxE => //.
Qed.

Notation " i ' " := (Ordinal i) (at level 40).

Lemma matrix_sum_preserves_length' B E m0:
(forall x, In x E -> length x = m0 ) -> 
(forall x, In x B -> length x = m0 ) -> 
forall x, In x (B +m E) -> length x = m0.
Proof. 
intros. unfold mat_sumR, mat_sum in H1.
unfold map2 at 1 in H1.
apply list_in_map_inv in H1.
destruct H1 as (x0 & H1 & H2).
destruct x0. rewrite H1.
pose proof in_combine_r _ _ _ _ H2. 
pose proof in_combine_l _ _ _ _ H2.
specialize (H l0 H3). specialize (H0 l H4).
simpl. unfold map2. 
rewrite map_length combine_length; lia.
Qed.

Lemma matrix_to_mx_index E (i j m0 n0: nat)
(Hi: (i < m0)%nat) (Hj: (j < n0)%nat) :
matrix_index E i j 0 = matrix_to_mx m0 n0 E (Hi ') (Hj ').
Proof.
by rewrite !mxE; rewrite /getm/matrix_index.
Qed.

Lemma vector_to_vc_index u (j n0: nat) (Hj: (j < n0)%nat):
vector_to_vc n0 u  (Hj ') 0 = nth j u 0%R.
Proof.
by rewrite !mxE; rewrite /getv/matrix_index.
Qed.

End MVtoMC_Lems.

Section Norms.

Definition sum_abs {m} (A: 'M[R]_m) i : R:= \sum_j (Rabs (A i j)).
Definition normv   {m} (v: 'cV[R]_m)  : R:= \big[maxr/0]_(i < m) Rabs (v i 0).
Definition normM   {m} (A: 'M[R]_m)   : R:= \big[maxr/0]_i (sum_abs A i).

(* generally useful lemmmas for max operator *)
Lemma maxrC : @commutative R R maxr. 
  Proof. rewrite /commutative => x y.
  rewrite -!RmaxE. apply Rmax_comm. Qed.

Lemma maxrA : @associative R  maxr. 
  Proof. rewrite /associative => x y z.
  rewrite -!RmaxE. apply Rmax_assoc. Qed. 

Lemma big_mul {n:nat} (F : ordinal (n.+1) -> R) op a:
(forall i b, op (F i) b * a = op (F i * a) (b * a)) -> 
0 <= a -> \big[op/0]_(i0 < n.+1) (F i0) * a = \big[op/0]_(i0 < n.+1) (F i0 * a).
Proof. 
revert F a. elim: n => /= // [F a Hc Ha| n0 IH F a Hc Ha].
rewrite !big_ord_recl !big_ord0/= //.
rewrite (Hc ord0 0) mul0r //. 
rewrite big_ord_recl => /= //. 
etransitivity.
2 : rewrite big_ord_recl => /= //.
rewrite Hc.
rewrite IH => //.
Qed.

Lemma big_max_mul {n:nat} (F : ordinal (n.+1) -> R) a:
0 <= a -> \big[maxr/0]_(i0 < n.+1) (F i0) * a = \big[maxr/0]_(i0 < n.+1) (F i0 * a).
Proof. 
move => Ha.
apply big_mul => //.
move => i  b.
rewrite maxr_pmull // mul0r //.
Qed.

(* Lemmas about norm defs *)

Lemma normv_pos {m} (v: 'cV[R]_m.+1) : 0 <= normv v.
Proof.
rewrite /normr/normv. 
elim/big_ind: _ => //[x y Hx Hy| i _].
rewrite  -RmaxE. eapply le_trans; [apply Hy|].
apply /RleP; apply Rmax_r.
apply /RleP; apply Rabs_pos.
Qed.

Lemma normM_pos {m} (A: 'M[R]_m.+1) : 0 <= normM A.
Proof.
rewrite /normr/normM . 
elim/big_ind: _ => //[x y Hx Hy| i _].
rewrite  -RmaxE/Rmax. destruct Rle_dec => //.
rewrite /sum_abs. 
elim/big_ind: _ => //[x y Hx Hy| j _].
apply addr_ge0 => //.
apply /RleP; apply Rabs_pos.
Qed.

Lemma Rabs_sum (n:nat) : forall (F : ordinal (n.+1) -> R),
Rabs (\sum_j F j) <= \sum_j Rabs (F j).
Proof.
elim : n => [F | n IH F]. 
rewrite !big_ord_recr!big_ord0/=. 
  eapply le_trans ; [apply Rleb_norm_add| rewrite Rabs_R0; apply ler_add => /= //].
eapply le_trans.
1, 2: rewrite big_ord_recr /=. apply Rleb_norm_add.
apply ler_add => /= //.
Qed.


Lemma subMultNorm m (A: 'M[R]_m.+1)  (u : 'cV_m.+1) : 
  normv ( A *m u ) <= normM A * normv u.
Proof.
remember (normv u) as umax.
rewrite /normr /normM /normv /sum_abs /= big_max_mul.
apply le_bigmax2 => i0 _. 
rewrite mxE => /=.
eapply le_trans.
apply Rabs_sum .
elim/big_rec2: _ =>  // [ |i1 y1 y2 _ Hy].
apply mulr_ge0 => //. 
rewrite Hequmax; apply normv_pos.
rewrite mulrDl.
apply ler_add => //.
rewrite Rabs_mult.
apply ler_pmul => //.
1,2: apply /RleP; apply Rabs_pos.
rewrite Hequmax/normv.
by apply /le_bigmax.
rewrite Hequmax; apply normv_pos.
Qed.

Lemma normv_triang m  (u v: 'cV_m.+1) : 
  normv ( u + v ) <= normv u + normv v.
Proof.
rewrite {1}/normv.
apply: bigmax_le => [ | i _]. 
apply addr_ge0; apply normv_pos.
rewrite mxE => /=.
eapply le_trans.
apply Rleb_norm_add. apply ler_add;
apply: le_bigmax => [ | i _]. 
Qed.


End Norms. 
