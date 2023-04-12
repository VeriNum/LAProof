(* This file contains basic lemmas about lists for this project. *)

Require Import List Arith.
Import List ListNotations.


Lemma combine_map (A B : Type) (f : A -> B) g (v1 v2 : list A) :
(forall a a0, (f a, f a0) = g (a, a0)) -> 
combine (map f v1) (map f v2) = (map g (combine v1 v2)).
Proof. intros.
revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto.
Qed.

Lemma combine_map' (A B : Type) (f : A -> B) (g : A * A -> B) h (v1 v2 : list A) :
(forall a a0, h (f a, f a0) = g (a, a0)) -> 
map h (combine (map f v1) (map f v2)) = (map g (combine v1 v2)).
Proof. intros.
revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto.
Qed.

Lemma rev_empty (A: Type) : @rev A [] = []. simpl; auto. Qed.

Lemma combine_nil_r (A : Type) (l1 l2: list A) :
  length l1 = length l2 -> 
  combine l1 [] = combine l1 l2 -> l2 = [].
Proof. intros. 
rewrite combine_nil in H0. symmetry in H0.      
apply length_zero_iff_nil in H0.
      rewrite combine_length in H0.
  rewrite H in H0; clear H. rewrite Nat.min_id in H0. 
apply length_zero_iff_nil; auto.
Qed.

Lemma combine_nil_l (A : Type) (l1 l2: list A) :
  length l1 = length l2 -> 
  combine l1 [] = combine l1 l2 -> l1 = [].
Proof. intros. 
rewrite combine_nil in H0. symmetry in H0.      
apply length_zero_iff_nil in H0.
      rewrite combine_length in H0. symmetry in H.
  rewrite H in H0; clear H. rewrite Nat.min_id in H0. 
apply length_zero_iff_nil; auto.
Qed.

Lemma combine_app (A : Type) a1 a2 : forall (l1 l2 : list A),
  length l1 = length l2 -> combine l1 l2 ++ [(a1,a2)] = combine (l1 ++ [a1]) (l2 ++ [a2]).
Proof.
induction l1. 
{ intros. pose proof combine_nil_r A [] l2 H eq_refl; subst; simpl; auto. }
intros. destruct l2. 
{ pose proof combine_nil_l A (a :: l1) [] H eq_refl as H0; inversion H0. }
assert (Hlen: length l1 = length l2) by auto.
specialize (IHl1 l2 Hlen).
simpl; rewrite IHl1; simpl; auto.
Qed.

Lemma combine_rev (A : Type) (l1 l2: list A) :
length l1 = length l2 ->
combine (rev l1) (rev l2) = rev (combine l1 l2).
Proof.
revert l1.
induction l2.
{ intros. rewrite !combine_nil; simpl; auto. }
intros. destruct l1.
{ simpl. auto. }
assert (Hlen : length l1 = length l2) by (simpl; auto).
specialize (IHl2 l1 Hlen).
simpl. rewrite <- IHl2.
simpl.
rewrite <- combine_app; auto.
rewrite !rev_length; auto.
Qed.

Lemma combine_single A v1 v2 (a : A * A) : 
  length v1 = length v2 -> 
  combine v1 v2 = [a] -> v1 = [fst a] /\ v2 = [snd a].
Proof.
intros. pose proof combine_split v1 v2 H.
rewrite H0 in H1. destruct a. 
simpl in H1. inversion H1; simpl; split; auto.
Qed.

Lemma combine_single' A u (a u0 d : A) :
 combine (u0 :: u) [a] = [(u0, a)].
Proof. simpl; rewrite combine_nil; auto. Qed.

From Coq Require Import ZArith Reals Psatz.
From Coquelicot Require Import Coquelicot.

Lemma length_not_empty {A} l :
l <> [] -> 
(1 <= @length A l)%nat.
Proof.
intros.
destruct l; simpl; 
 try simpl (length (a :: l)); try lia.
destruct H; auto.
Qed.

Lemma length_not_empty' {A} l :
l <> [] -> 
(1 <= INR (@length A l))%R.
Proof.
intros.
replace 1%R with (INR 1) by (simpl; auto).
eapply le_INR.
apply length_not_empty; auto.
Qed.

Lemma length_not_empty_nat {A} l :
l <> [] -> 
(1 <= (@length A l))%nat.
Proof.
intros.
apply INR_le.
apply length_not_empty';auto.
Qed.

Lemma length_not_empty_lt {A} l :
l <> [] -> 
(0 < INR (@length A l))%R.
Proof.
intros.
destruct l.
destruct H; auto.
simpl (length (a:: l)).
rewrite <- Nat.add_1_r.
rewrite plus_INR.
apply Rcomplements.Rlt_minus_l.
field_simplify.
simpl.
eapply Rlt_le_trans with 0;  try nra.
apply pos_INR.
Qed.

Lemma length_not_empty_nat' {A} l :
l <> [] -> 
(0 <= (@length A l))%nat.
Proof.
intros.
apply INR_le.
apply Rlt_le.
apply length_not_empty_lt;auto.
Qed.

Lemma fold_left_Rplus_Rplus:
 forall al b c, fold_left Rplus al (b+c) = c + fold_left Rplus al b.
Proof.
intros.
rewrite ! fold_symmetric by (intros; lra).
induction al; simpl; intros; lra.
Qed.

Lemma fold_left_Rplus_0:
 forall al b , fold_left Rplus al b = b + fold_left Rplus al 0.
Proof.
intros.
rewrite ! fold_symmetric by (intros; lra).
induction al; simpl; intros; lra.
Qed.
