(* This file contains floating point functional models for the summation of
  two lists, as well as theorems regarding their equivalence. *)

From LAProof.accuracy_proofs Require Import 
        preamble common float_acc_lems.
                                          (*  float_tactics.*)
Import ListNotations.
Require Import Sorting Permutation.
Require Import Reals.
Open Scope R.


Definition sum {A: Type} (sum_op : A -> A -> A) (a b : A) : A := sum_op a b.

Inductive sum_rel {A : Type} (default: A) (sum_op : A -> A -> A) : list A -> A -> Prop :=
| sum_rel_nil  : sum_rel default sum_op [] default
| sum_rel_cons : forall l a s,
    sum_rel default sum_op l s ->
    sum_rel default sum_op (a::l) (sum sum_op a s).

Definition sum_rel_R := @sum_rel R 0%R Rplus.

Inductive sum_rel_any {A : Type} (default: A) (sum_op : A -> A -> A) : list A -> A -> Prop :=
| sum_rel_0  : sum_rel_any default sum_op [] default
| sum_rel_1 : forall a, sum_rel_any default sum_op (a::nil) a
| sum_rel_app: forall a1 a2 s1 s2,
     sum_rel_any default sum_op a1 s1 ->
     sum_rel_any default sum_op a2 s2 ->
     sum_rel_any default sum_op (a1++a2) (sum sum_op s1 s2).

Lemma sum_rel_R_abs :
forall l s1 s2,
sum_rel_R l s1 -> sum_rel_R (map Rabs l) s2 -> s1 <= s2.
Proof.
induction l.
-
intros.
inversion H.
inversion H0.
nra.
-
intros.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
unfold sum.
eapply Rplus_le_compat.
apply Rle_abs.
fold sum_rel_R in H4.
fold sum_rel_R in H3.
apply IHl;
auto.
Qed.

Lemma sum_rel_R_Rabs_pos : 
forall l s,
sum_rel_R (map Rabs l) s -> 0 <= s.
Proof.
induction  l.
-
intros.
inversion H; nra.
-
intros.
inversion H; subst; clear H.
unfold sum.
fold sum_rel_R in H3.
specialize (IHl s0 H3).
apply Rplus_le_le_0_compat; auto;
  try apply Rabs_pos.
Qed.

Lemma sum_rel_R_Rabs_eq :
forall l s,
sum_rel_R (map Rabs l) s -> Rabs s = s.
Proof.
induction  l.
-
intros.
inversion H.
rewrite Rabs_R0.
nra.
-
intros.
inversion H; subst; clear H.
unfold sum.
replace (Rabs(Rabs a + s0)) with 
  (Rabs a  + s0); try nra.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rabs_pos.
eapply Rle_trans with (Rabs s0).
apply Rabs_pos.
eapply Req_le.
apply IHl.
fold sum_rel_R in H3.
auto.
Qed.


Lemma sum_rel_R_Rabs :
forall l s1 s2,
sum_rel_R l s1 -> sum_rel_R (map Rabs l) s2 -> Rabs s1 <= Rabs s2.
Proof.
induction l.
-
intros.
inversion H.
inversion H0.
nra.
-
intros.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
fold sum_rel_R in H4.
fold sum_rel_R in H3.
unfold sum.
eapply Rle_trans.
apply Rabs_triang.
replace (Rabs(Rabs a + s0)) with 
  (Rabs a  + s0).
eapply Rplus_le_compat; try nra.
eapply Rle_trans with (Rabs s0).
fold sum_rel_R in H4.
fold sum_rel_R in H3.
apply IHl; auto.
apply Req_le.
eapply sum_rel_R_Rabs_eq; apply H3.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rabs_pos.
eapply Rle_trans with (Rabs s0).
apply Rabs_pos.
apply Req_le.
eapply sum_rel_R_Rabs_eq; apply H3.
Qed.


Lemma sum_rel_R_single :
forall (a : R) (fs : R), sum_rel_R [a] fs -> fs = a.
Proof.
intros.
inversion H; auto.
inversion H3. subst.
unfold sum; nra.
Qed.

Lemma sum_rel_R_single' :
forall (a : R) , sum_rel_R [a] a.
Proof.
intros.
unfold sum_rel_R.
replace a with (a + 0) at 2 by nra. 
apply sum_rel_cons. apply sum_rel_nil.
Qed. 

Lemma sum_rel_R_app_cons :
forall l' l'' a s,
sum_rel_R (l' ++  l'') s ->
sum_rel_R (l' ++ a :: l'') (a + s).
Proof.
induction l'; simpl.  
{ intros; apply sum_rel_cons; auto. }
intros. 
inversion H; subst; clear H.
specialize (IHl' l'' a0 s0 H3).
unfold sum.
replace (a0 + (a + s0)) with (a + (a0 + s0)) by nra.
apply sum_rel_cons; auto.
Qed.

Lemma sum_rel_bound  :
  forall (l : list R) (rs a: R)
  (Hrs : sum_rel_R l rs)
  (Hin : forall x, In x l -> Rabs x <= a),
  Rabs rs <= INR (length l) * a.
Proof.
induction l; intros.
{ inversion Hrs; subst; simpl; rewrite Rabs_R0; nra. }
  inversion Hrs; subst. 
  unfold sum; eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat;
  [apply Hin; simpl; auto| apply IHl; 
                        [ apply H2 | intros; apply Hin; simpl; auto ] ] | ].
  apply Req_le. replace (length (a :: l)) with (length l + 1)%nat by (simpl; lia).
  rewrite plus_INR; simpl; nra.
Qed.
  
Lemma sum_rel_R_permute :
  forall (l l0: list R)
  (Hper: Permutation l l0) (rs: R)
  (Hrs: sum_rel_R l rs),
  sum_rel_R l0 rs.
Proof.
intros ?.
induction l.
{ intros; inversion Hrs; subst.
apply Permutation_nil in Hper; subst; simpl; auto. }
intros.
apply Permutation_sym in Hper.
pose proof Permutation_vs_cons_inv Hper as H.
destruct H as (l' & l'' & H); subst.
apply Permutation_sym in Hper.
pose proof (@Permutation_cons_app_inv R l l' l'' a Hper).
inversion Hrs; subst. fold sum_rel_R in H3.
specialize (IHl (l' ++ l'') H s H3).
unfold sum; clear Hrs.
apply sum_rel_R_app_cons; auto.
Qed.

Lemma sum_rel_R_permute_t :
  forall (t: type) (l l0: list (ftype t))
  (Hper: Permutation l l0) (rs: R)
  (Hrs: sum_rel_R (map FT2R l) rs),
  sum_rel_R (map FT2R l0) rs.
Proof.
intros;
apply sum_rel_R_permute with (map FT2R l); auto.
apply Permutation_map; auto.
Qed.

Definition sumR := fold_right Rplus 0.

Lemma sumRabs_pos x :
0 <= sumR (map Rabs x).
Proof.
induction x; simpl; try nra.
apply Rplus_le_le_0_compat; [apply Rabs_pos | nra].
Qed.

Lemma sumRabs_Rabs x :
Rabs (sumR (map Rabs x)) = sumR (map Rabs x).
Proof. rewrite Rabs_pos_eq; auto. apply sumRabs_pos. Qed.

Lemma sumR_mult x a :
sumR x * a = sumR (map (Rmult a) x).
Proof. induction x; simpl; nra. Qed.

Lemma sumR_le_sumRabs x :
Rabs (sumR x) <= Rabs (sumR (map Rabs x)).
Proof.
induction x; simpl; [nra | ].
rewrite sumRabs_Rabs in IHx.
eapply Rle_trans.
2: rewrite Rabs_pos_eq.
apply Rabs_triang.
apply Rplus_le_compat_l; auto.
apply Rplus_le_le_0_compat; 
[apply Rabs_pos|  apply sumRabs_pos].
Qed.

Lemma sumR_app_cons l' l'' a: 
a + sumR (l' ++ l'') = sumR (l' ++ a :: l'').
Proof. induction l'; simpl; [nra | rewrite <- IHl'; nra]. Qed.

Lemma sumR_permute :
  forall x x0 (Hper: Permutation x x0) ,
  sumR x = sumR x0.
Proof.
intros ?.
induction x; intros.
{ apply Permutation_nil in Hper; subst; simpl; auto. }
apply Permutation_sym in Hper.
pose proof Permutation_vs_cons_inv Hper as H.
destruct H as (l' & l'' & H); subst.
apply Permutation_sym in Hper.
pose proof (@Permutation_cons_app_inv R x l' l'' a Hper).
specialize (IHx (l' ++ l'') H ).
simpl. rewrite IHx sumR_app_cons; auto.
Qed.

Lemma sum_rel_bound'  :
  forall (t : type) (l : list (ftype t)) (rs a: R)
  (Hrs : sum_rel_R (map FT2R l) rs)
  (Hin : forall x, In x l -> Rabs (FT2R x) <= a),
  Rabs rs <= INR (length l) * a.
Proof.
induction l; intros.
{ inversion Hrs; subst; simpl; rewrite Rabs_R0; nra. }
  inversion Hrs; subst. 
  unfold sum; eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat;
  [apply Hin; simpl; auto| apply IHl; 
                        [ apply H2 | intros; apply Hin; simpl; auto ] ] | ].
  apply Req_le. replace (length (a :: l)) with (length l + 1)%nat by (simpl; lia).
  rewrite plus_INR; simpl; nra.
Qed.

Lemma sum_rel_bound''  :
  forall (t : type) (l : list (ftype t)) (rs_abs a: R)
  (Hrs : sum_rel_R (map Rabs (map FT2R l)) rs_abs)
  (Hin : forall x, In x l -> Rabs (FT2R x) <= a),
  rs_abs <= INR (length l) * a.
Proof.
induction l; intros.
{ inversion Hrs; subst; simpl; nra. }
  inversion Hrs; subst.
  unfold sum. fold sum_rel_R in H2.
  eapply Rle_trans; [apply Rplus_le_compat;
  [apply Hin; simpl; auto| apply IHl; 
                        [ apply H2 | intros; apply Hin; simpl; auto ] ] | ].
  apply Req_le. replace (length (a :: l)) with (length l + 1)%nat by (simpl; lia).
  rewrite plus_INR; simpl; nra.
Qed. 


Lemma sum_rel_R_fold : forall l rs, 
   sum_rel_R l rs -> rs = sumR l.
Proof. 
induction l.
intros; inversion H; simpl; auto.
intros; inversion H. 
fold sum_rel_R in H3.
specialize (IHl s H3).
subst; simpl.
unfold sum; auto.
Qed.

Lemma sum_map_Rmult (l : list R) (s a: R):
sum_rel_R l s -> 
sum_rel_R (map (Rmult a) l) (a * s). 
Proof. 
revert l s a. induction l.
{ intros. simpl. inversion H; subst; rewrite Rmult_0_r; auto. }
intros. inversion H. destruct l.
{ simpl; unfold sum. inversion H3; subst. rewrite Rplus_0_r.
  apply sum_rel_R_single'. }
fold sum_rel_R in H3. specialize (IHl s0 a0 H3).
unfold sum; simpl. rewrite Rmult_plus_distr_l; apply sum_rel_cons.
fold sum_rel_R. simpl in IHl; auto.
Qed.

Section WithSTD.
Context {NAN: FPCore.Nans} {t : type}.

Definition sum_rel_Ft := @sum_rel (ftype t) neg_zero (BPLUS ).

Lemma sum_rel_Ft_single fs a:
Binary.is_finite fs = true ->
sum_rel_Ft [a] fs -> fs = a.
Proof.
move => FIN Hs.
move: FIN.
inversion Hs; subst.
inversion H2; subst.
rewrite /sum/BPLUS/BINOP
  /neg_zero.
move => FIN.
destruct a; 
  try discriminate FIN => //;
destruct s => //.
Qed.

Lemma sum_rel_R_exists :
  forall (l : list (ftype t)) (fs : ftype t)
  (Hfs : sum_rel_Ft l fs),
  exists rs, sum_rel_R (map FT2R l) rs.
Proof.
intros ?. induction l.
{ simpl; exists 0. apply sum_rel_nil. }
intros. inversion Hfs; subst. 
fold sum_rel_Ft in H2.
destruct (IHl s H2) as (rs & Hrs); clear IHl.
exists (FT2R a + rs); simpl. 
apply sum_rel_cons; auto.
Qed.

Lemma sum_rel_R_abs_exists:
  forall (l : list (ftype t)) (fs : ftype t)
  (Hfs : sum_rel_Ft l fs),
  exists rs, sum_rel_R (map Rabs (map FT2R l)) rs.
Proof.
intros ?. induction l.
{ simpl; exists 0. apply sum_rel_nil. }
intros. inversion Hfs; subst. 
fold sum_rel_Ft in H2.
destruct (IHl s H2) as (rs & Hrs); clear IHl.
exists (Rabs (FT2R a) + rs); simpl. 
apply sum_rel_cons; auto.
Qed.
 
Lemma is_finite_in :
  forall (l : list (ftype t)) fs,
  sum_rel_Ft l fs ->
  let e  := @default_abs t in
  let d  := @default_rel t in 
  let ov := powerRZ 2 (femax t) in
  Binary.is_finite fs = true ->
  forall a, In a l -> Binary.is_finite a = true.
Proof.
induction l => //=.
move => fs H0 H1 s [Hs|Hs]; subst.
inversion H0; subst.
move : H1; rewrite /sum => H1. 
destruct (BPLUS_correct _ _ H1) as [[? ?] ?]; auto.
inversion H0; clear H0; subst.
fold sum_rel_Ft in H4.
eapply IHl; try eassumption.
destruct (BPLUS_correct _ _  H1) as [[? ?] ?]; auto.
Qed.

Definition sumF := fold_right (@BPLUS _ t) neg_zero.

Lemma sum_rel_Ft_fold : forall l fs, 
   sum_rel_Ft l fs -> fs = sumF l.
Proof. 
induction l.
intros; inversion H; simpl; auto.
intros; inversion H. 
fold sum_rel_Ft  in H3.
specialize (IHl s H3).
subst; simpl.
unfold sum; auto.
Qed.


End WithSTD.