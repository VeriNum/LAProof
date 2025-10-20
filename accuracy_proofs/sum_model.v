(* This file contains floating point functional models for the summation of
     lists, as well as theorems regarding their equivalence. *)

From LAProof.accuracy_proofs Require Import  preamble common.

Require Import Permutation.

Inductive sum_rel {A : Type} (default: A) (sum_op : A -> A -> A) : list A -> A -> Prop :=
| sum_rel_nil  : sum_rel default sum_op [] default
| sum_rel_cons : forall l a s,
    sum_rel default sum_op l s ->
    sum_rel default sum_op (a::l) (sum_op a s).

Definition sum_rel_R := @sum_rel R 0%R Rplus.

Inductive sum_any' {NAN: FPCore.Nans} {t}: forall (h: nat) (v: list (ftype t)) (s: ftype t), Prop :=
| Sum_Any_1: forall x, sum_any' O [x] x
| Sum_Any_split: forall n1 n2 al bl a b, 
      sum_any' n1 al a -> sum_any' n2 bl b -> sum_any' (S (Nat.max n1 n2)) (al++bl) (BPLUS a b)
| Sum_Any_perm: forall n al bl s, Permutation al bl -> sum_any' n al s -> sum_any' n bl s.

Inductive sum_any {NAN: FPCore.Nans} {t:type}: forall (h: nat) (v: list (ftype t)) (s: ftype t), Prop :=
| Sum_Any_None: sum_any O nil pos_zero
| Sum_Any_Some: forall n v s, sum_any' n v s -> sum_any n v s.

Lemma sum_rel_sum_any: forall {NAN: FPCore.Nans} {t} z (v: list (ftype t)) s (Hz: iszero z),
  sum_rel z BPLUS v s -> 
  exists s', feq s s' /\ sum_any (Nat.pred (size v)) v s'.
Proof.
destruct v; intros.
-
destruct z; try discriminate; clear Hz;
inversion H; clear H; subst; (eexists; split; [ | constructor]; reflexivity).
-
revert f s z Hz H; induction v; simpl; intros.
+
inversion H; clear H; subst.
inversion H3; clear H3; subst.
destruct s0; try discriminate.
destruct s;
(eexists; split; [ | constructor; constructor];
destruct f; try reflexivity;
destruct s; reflexivity).
+
inversion H; clear H; subst.
specialize (IHv a s0 z Hz H3).
change (cons f (cons a v)) with ([f] ++ cons a v).
replace (S (size v)) with (S (Nat.max O (size v))) by lia.
destruct IHv as [s1 [? ?]].
eexists.
inversion H0; clear H0; subst.
simpl in H1.
split.
2:{ constructor 2.
eapply Sum_Any_split; auto.
apply Sum_Any_1.
eassumption.
}
clear z Hz H3 H1.
rewrite H; auto.
Qed.

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
inversion H; compute; nra.
-
intros.
inversion H; subst; clear H.
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
apply Rabs_R0.
-
intros.
inversion H; subst; clear H.
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
apply Rplus_0_r.
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
replace (a0 + (a + s0)) with (a + (a0 + s0)) by nra.
apply sum_rel_cons; auto.
Qed.

Lemma sum_rel_bound  :
  forall (l : list R) (rs a: R)
  (Hrs : sum_rel_R l rs)
  (Hin : forall x, In x l -> Rabs x <= a),
  Rabs rs <= INR (size l) * a.
Proof.
induction l; intros.
{ inversion Hrs; subst; simpl; rewrite Rabs_R0; nra. }
  inversion Hrs; subst. 
  eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat;
  [apply Hin; simpl; auto| apply IHl; 
                        [ apply H2 | intros; apply Hin; simpl; auto ] ] | ].
  apply Req_le. replace (size (a :: l)) with (size l + 1)%nat by (simpl; lia).
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
clear Hrs.
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

Definition sumR := foldr Rplus 0.

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

Lemma sumR_rev: forall l, sumR (rev l) = sumR l.
Proof.
move => l.
apply sumR_permute.
rewrite rev_list_rev.
apply Permutation_sym.
apply Permutation_rev.
Qed.

Lemma sum_rel_bound'  :
  forall (t : type) (l : list (ftype t)) (rs a: R)
  (Hrs : sum_rel_R (map FT2R l) rs)
  (Hin : forall x, In x l -> Rabs (FT2R x) <= a),
  Rabs rs <= INR (size l) * a.
Proof.
induction l; intros.
{ inversion Hrs; subst; simpl; rewrite Rabs_R0; nra. }
  inversion Hrs; subst. 
  eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat;
  [apply Hin; simpl; auto| apply IHl; 
                        [ apply H2 | intros; apply Hin; simpl; auto ] ] | ].
  apply Req_le. replace (size (a :: l)) with (size l + 1)%nat by (simpl; lia).
  rewrite plus_INR; simpl; nra.
Qed.

Lemma sum_rel_bound''  :
  forall (t : type) (l : list (ftype t)) (rs_abs a: R)
  (Hrs : sum_rel_R (map Rabs (map FT2R l)) rs_abs)
  (Hin : forall x, In x l -> Rabs (FT2R x) <= a),
  rs_abs <= INR (size l) * a.
Proof.
induction l; intros.
{ inversion Hrs; subst; simpl. compute. nra. }
  inversion Hrs; subst.
   fold sum_rel_R in H2.
  eapply Rle_trans; [apply Rplus_le_compat;
  [apply Hin; simpl; auto| apply IHl; 
                        [ apply H2 | intros; apply Hin; simpl; auto ] ] | ].
  apply Req_le. replace (size (a :: l)) with (size l + 1)%nat by (simpl; lia).
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
auto.
Qed.

Lemma sum_map_Rmult (l : list R) (s a: R):
sum_rel_R l s -> 
sum_rel_R (map (Rmult a) l) (a * s). 
Proof. 
revert l s a. induction l.
{ intros. simpl. inversion H; subst; rewrite Rmult_0_r; auto. }
intros. inversion H. destruct l.
{ simpl. inversion H3; subst. rewrite Rplus_0_r.
  apply sum_rel_R_single'. }
fold sum_rel_R in H3. specialize (IHl s0 a0 H3).
simpl. rewrite Rmult_plus_distr_l; apply sum_rel_cons.
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
clear - H1; destruct s,s0; try destruct s; try destruct s0; try discriminate H1; reflexivity.
inversion H0; clear H0; subst.
fold sum_rel_Ft in H4.
eapply IHl; try eassumption.
clear - H1; destruct a,s0; try destruct s; try destruct s0; try discriminate H1; reflexivity.
Qed.

Definition sumF := foldl(Basics.flip (@BPLUS _ t)) neg_zero.

Lemma sum_rel_Ft_fold : forall l fs, 
   sum_rel_Ft (rev l) fs -> fs = sumF l.
Proof.
intros.
rewrite /sumF -(revK l) foldl_rev.
move :fs H.
induction (rev l).
intros; inversion H; simpl; auto.
intros; inversion H. 
fold sum_rel_Ft  in H3.
specialize (IHl0 s H3).
subst; simpl.
auto.
Qed.

(** subtract_loop is a variant on summation used in some implementations of Cholesky decomposition,
  among other things.  We should be able to prove an equivalence, of sorts, with sum_rel,
  so that the accuracy theorem for sum_rel can apply here as well. *)
Definition subtract_loop: forall (c: ftype t) (al: list (ftype t)), ftype t := foldl BMINUS.

Lemma BMINUS_neg_zero: forall (c: ftype t), feq (BMINUS neg_zero (BOPP c)) c.
Proof. destruct c; try destruct s; reflexivity. Qed.

Lemma subtract_loop_congr1: forall  (u v: ftype t) al, 
  feq u v -> feq (subtract_loop u al) (subtract_loop v al).
Proof.
intros.
revert u v H; induction al; simpl; intros; auto.
apply IHal. rewrite H; auto.
Qed.

(* Don't seem to need this yet.  . . .
Definition loose_feq (x y: ftype t) : Prop :=
 match x,y with
 | Binary.B754_zero _ _ _, Binary.B754_zero _ _ _ => true
 | Binary.B754_zero _ _ _, _ => false
 | _, Binary.B754_zero _ _ _ => false
 | Binary.B754_finite _ _ b1 m1 e1 _, Binary.B754_finite _ _ b2 m2 e2 _ => 
      and (eq b1 b2) (and (eq m1 m2) (eq e1 e2))
 | Binary.B754_finite _ _ _ _ _ _, _ => false
 | _, Binary.B754_finite _ _ _ _ _ _ => false
 | _, _ => true
 end.  

Lemma loose_feq_refl : Relation_Definitions.reflexive _ loose_feq.
Proof.
intro x; destruct x; simpl; auto.
Qed.

Lemma loose_feq_sym : Relation_Definitions.symmetric (ftype t) loose_feq.
Proof.
intros x y; destruct x,y; simpl; auto.
intros [? [? ?]].
subst. auto.
Qed.

Lemma loose_feq_trans: Relation_Definitions.transitive (ftype t) loose_feq.
Proof.
intros x y z.
destruct x,y,z; simpl; intros; auto; try contradiction; try discriminate.
destruct H as [? [? ?]]; destruct H0 as [? [? ?]]; subst; auto.
Qed.

Add Parametric Relation : (ftype t) loose_feq
  reflexivity proved by loose_feq_refl
  symmetry proved by loose_feq_sym
  transitivity proved by loose_feq_trans
   as loose_feq_rel.

Add Parametric Morphism: (@BPLUS NAN t)
 with signature loose_feq ==> loose_feq ==> loose_feq
 as loose_BPLUS_mor.
Proof.
intros.
destruct x,y; inversion H; clear H; subst; destruct x0,y0; inversion H0; clear H0; subst; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
subst;
repeat proof_irr; 
try constructor; auto; try reflexivity.
Qed.

Lemma feq_loose_feq: forall x y, feq x y -> loose_feq x y.
Proof.
intros.
destruct x, y; try destruct s; try destruct s0; simpl in *; auto.
Qed.

*)

Lemma BPLUS_neg_zero: forall (c: ftype t), feq (BPLUS c neg_zero) c.
Proof. destruct c; try destruct s; reflexivity. Qed.

Lemma BPLUS_comm: forall (x y: ftype t),  feq (BPLUS x y) (BPLUS y x).
Proof.
destruct x, y; try destruct s; try destruct s0; try reflexivity;
unfold BPLUS, BINOP, feq, Binary.Bplus, Binary.BSN2B, BinarySingleNaN.SF2B; simpl;
rewrite (Z.min_comm e1 e);
rewrite ?(Pos.add_comm (fst (SpecFloat.shl_align m0 e1 (Z.min e e1)))).
1,4: destruct (BinarySingleNaN.SF2B _ _); simpl; auto.
1,2: destruct (BinarySingleNaN.binary_normalize _ _ _ _ _ _ _ _); simpl; auto.
Qed.

Lemma MINUS_PLUS_BOPP: forall x y: ftype t, feq (BMINUS x y) (BPLUS x (BOPP y)).
Proof.
destruct x, y; try destruct s; try destruct s0; try reflexivity;
unfold BMINUS, BPLUS, BINOP, BOPP, UNOP, feq, Binary.Bplus, Binary.Bminus, 
   Binary.BSN2B, BinarySingleNaN.SF2B, Binary.build_nan; simpl.
1,4: destruct (BinarySingleNaN.binary_normalize _ _ _ _ _ _ _ _); auto.
1,2: destruct (BinarySingleNaN.SF2B _ _); auto.
Qed.

Lemma subtract_loop_sumR: forall (c: ftype t) (al: list (ftype t)),
  feq (subtract_loop c al) (sumF (c :: map BOPP al)).
Proof.
intros.
revert c; induction al; simpl; intros.
destruct c; try destruct s; reflexivity.
rewrite {}IHal /sumF -/(ftype t).
simpl.
set x := Basics.flip BPLUS neg_zero (BMINUS c a).
set y := Basics.flip BPLUS  (Basics.flip BPLUS neg_zero c)  (BOPP a).
assert (feq x y) by rewrite  /x /y /Basics.flip !BPLUS_neg_zero BPLUS_comm MINUS_PLUS_BOPP //.
clearbody x; clearbody y.
revert x y H; induction al; simpl; intros; auto.
apply IHal; auto.
apply BPLUS_mor; auto.
Qed.

Lemma sum_rel_Ft_exists: forall (l: list (ftype t)), exists s, sum_rel_Ft l s.
Proof.
unfold sum_rel_Ft.
induction l; simpl.
eexists; constructor.
destruct IHl as [s ?].
eexists; constructor; eauto.
Qed.

Lemma subtract_loop_sum_any:  forall  (c: ftype t) (al: list (ftype t)),
   exists s, feq (subtract_loop c al) s /\ sum_any (size al) (rev (c::map BOPP al)) s.
Proof.
intros.
assert (exists s: ftype t, sum_rel neg_zero BPLUS (rev (c::map BOPP al)) s /\ feq (subtract_loop c al) s).
-
destruct (sum_rel_Ft_exists (rev (cons c (map BOPP al)))) as [s ?].
exists s; split; auto.
apply sum_rel_Ft_fold in H.
subst s.
apply subtract_loop_sumR.
-
destruct H as [s [? ?]].
apply sum_rel_sum_any in H; [ | reflexivity].
destruct H as [s' [? ?]].
exists s'.
split. rewrite <- H; auto.
simpl in H1.
rewrite size_rev /= size_map in H1.
auto.
Qed.

End WithSTD.