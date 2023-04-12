(* This file contains floating point functional models for the summation of
  two lists, as well as theorems regarding their equivalence. *)

Require Import vcfloat.VCFloat.
Require Import List.
Import List ListNotations.

Require Import Sorting Permutation.

Require Import common.

Require Import Reals.
Open Scope R.


Definition sum {A: Type} (sum_op : A -> A -> A) (a b : A) : A := sum_op a b.

Inductive sum_rel {A : Type} (default: A) (sum_op : A -> A -> A) : list A -> A -> Prop :=
| sum_rel_nil  : sum_rel default sum_op [] default
| sum_rel_cons : forall l a s,
    sum_rel default sum_op l s ->
    sum_rel default sum_op (a::l) (sum sum_op a s).

Definition sum_rel_R := @sum_rel R 0%R Rplus.


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
simpl. rewrite IHx, sumR_app_cons; auto.
Qed.

Section NAN.


From vcfloat Require Import IEEE754_extra.

Lemma plus_zero {NAN: Nans}  a:
Binary.is_finite _ _ a = true -> 
(a + -0)%F32 = a.
Proof.
destruct a; simpl; auto;
intros; try discriminate; auto;
destruct s;
cbv; auto.
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


Definition sum_rel_Ft {NAN: Nans} (t: type) := @sum_rel (ftype t) neg_zero (BPLUS ).

Lemma sum_rel_Ft_single {NAN: Nans} t fs a:
Binary.is_finite _ _ fs = true ->
sum_rel_Ft t [a] fs -> fs = a.
Proof.
intros.
inversion H0.
inversion H4; subst.
unfold sum, BPLUS; destruct a; try discriminate; 
  simpl; auto.
destruct s; simpl; auto.
Qed.

Lemma sum_rel_R_exists {NAN: Nans}:
  forall (t : type) (l : list (ftype t)) (fs : ftype t)
  (Hfs : sum_rel_Ft t l fs),
  exists rs, sum_rel_R (map FT2R l) rs.
Proof.
intros ?. induction l.
{ simpl; exists 0. apply sum_rel_nil. }
intros. inversion Hfs; subst. 
fold (@sum_rel_Ft NAN t) in H2.
destruct (IHl s H2) as (rs & Hrs); clear IHl.
exists (FT2R a + rs); simpl. 
apply sum_rel_cons; auto.
Qed.

Lemma sum_rel_R_abs_exists {NAN: Nans}:
  forall (t : type) (l : list (ftype t)) (fs : ftype t)
  (Hfs : sum_rel_Ft t l fs),
  exists rs, sum_rel_R (map Rabs (map FT2R l)) rs.
Proof.
intros ?. induction l.
{ simpl; exists 0. apply sum_rel_nil. }
intros. inversion Hfs; subst. 
fold (@sum_rel_Ft NAN t) in H2.
destruct (IHl s H2) as (rs & Hrs); clear IHl.
exists (Rabs (FT2R a) + rs); simpl. 
apply sum_rel_cons; auto.
Qed.
 
Lemma is_finite_in {NAN: Nans} (t : type) :
  forall (l : list (ftype t)) fs,
  sum_rel_Ft t l fs ->
  let e  := @default_abs t in
  let d  := @default_rel t in 
  let ov := powerRZ 2 (femax t) in
  Binary.is_finite (fprec t) (femax t) fs = true ->
  forall a, In a l -> Binary.is_finite (fprec t) (femax t) a = true.
Proof.
induction l.
simpl; intros; auto.
intros. 
destruct H1; subst.
inversion H.
rewrite <- H2 in H0. clear H2.
unfold sum in H0.
destruct a0, s; auto.
destruct s, s0; simpl in H0; try discriminate.
inversion H.
fold (@sum_rel_Ft NAN t) in H5.
assert (Binary.is_finite (fprec t) (femax t) s = true).
unfold sum in H3.
rewrite <- H3 in H0. clear H3.
destruct a, s; auto.
destruct s, s0; simpl in H0; try discriminate.
specialize (IHl s H5 H6).
apply IHl; auto.
Qed.

Definition sumF {NAN: Nans} {t: type} := fold_right (@BPLUS NAN t) neg_zero.

Lemma sum_rel_Ft_fold {NAN: Nans} : forall t l fs, 
   sum_rel_Ft t l fs -> fs = sumF l.
Proof. 
induction l.
intros; inversion H; simpl; auto.
intros; inversion H. 
fold (@sum_rel_Ft NAN t) in H3.
specialize (IHl s H3).
subst; simpl.
unfold sum; auto.
Qed.




End NAN.