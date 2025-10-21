(*This file contains two theorems: forward and backward error bounds for 
  the sum of two floating point lists; the functional model for
  the summation is defined in sum_model.v.*)

From LAProof.accuracy_proofs Require Import preamble common
                                            sum_model
                                            float_acc_lems .
Require LAProof.accuracy_proofs.mv_mathcomp.

Require Import Permutation.

Section WithNan . 
Context {NAN: FPCore.Nans} {t: type}.
Notation g := (@g t).

Notation D := (@default_rel t).

Notation neg_zero := (@common.neg_zero t). 

Theorem bSUM :
  forall (x: list (ftype t)) (Hfin: Binary.is_finite (sumF x)),
    exists (x': list R), 
    size x' = size x /\
    FT2R (sumF x) = sumR x' /\
    (forall n, (n < size x')%nat -> exists delta, 
        nth 0 x' n = FT2R (nth neg_zero x n) * (1 + delta) /\ Rabs delta <= g (size x' - 1)).
Proof.
move => x.
rewrite /sumF -(revK x) foldl_rev size_rev.
induction (rev x) as [ | a l] => Hfin; clear x.
-
exists []; repeat split; auto => //=.
- (* case a::l *)
have Hl: l = [] \/ l <> []. {
 destruct l; auto. right; congruence.
}
destruct Hl.
+ (* case empty l *)
  subst; simpl in *;
  destruct (BPLUS_finite_e _ _ Hfin).
  exists [FT2R a]; split; [ simpl; auto | split ; 
  [rewrite Bplus_0R|] ] => //.
  unfold sumR; simpl; nra.  
  intros. exists 0; simpl in H1; split.
 rewrite Rplus_0_r Rmult_1_r. 
  have H3: ((n = 1)%nat \/ (n = 0)%nat) by lia.
 destruct H3; subst; auto.
  rewrite Rabs_R0 /g /=. lra.
+ (* case non-empty l *)
simpl in *.
destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
(* IHl *)
pose proof (size_not_empty_nat l H) as Hlen1.
specialize (IHl B).
destruct IHl as (l' & Hlen' & Hsum & Hdel); auto.
rewrite {1}/Basics.flip in Hfin.
(* construct l'0 *)
pose proof (BPLUS_accurate' _ _ Hfin) as Hplus.
destruct Hplus as (d' & Hd'& Hplus).
rewrite /Basics.flip in Hsum,B,Hplus|-*.
change (fun x z => @BPLUS NAN t x z) with (@BPLUS _ t)  in Hsum,B,Hplus |- *.
exists (map (Rmult (1+d')) l' ++ [:: FT2R a * (1+d')]); repeat split.
* rewrite size_cat size_map /= Hlen' addnC //. 
* rewrite {}Hplus Hsum Rmult_plus_distr_r -sumR_app_cons cats0 sumR_mult //.
* move => n H1.
  rewrite nth_cat.
  rewrite size_cat size_map in H1|-*. simpl size in H1.
  destruct (n < size l')%N eqn:Hn.
 -- rewrite (nth_map R0); [ | lia].
   specialize (Hdel n Hn).
    destruct Hdel as (d & Hd1 & Hd2).
   exists ( (1+d') * (1+d) -1).
   rewrite {}Hd1. split.
  ++ fold (ftype t).
     rewrite rev_cons nth_rcons size_rev.
     destruct (n < size l)%N eqn:Hn'; [ | lia]. nra.
  ++ field_simplify_Rabs. 
  eapply Rle_trans; [apply Rabs_triang | eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang | ]  ].
rewrite Rabs_mult.
replace (Rabs d' * Rabs d + Rabs d' + Rabs d ) with
  ((1 + Rabs d') * Rabs d + Rabs d' ) by nra.
eapply Rle_trans; [apply Rplus_le_compat | ].
apply Rmult_le_compat; try apply Rabs_pos.
apply Fourier_util.Rle_zero_pos_plus1; try apply Rabs_pos.
apply Rplus_le_compat_l; apply Hd'.
apply Hd2. apply Hd'.
replace ((1 + D) * g (size l' - 1) + D) with
((1 + D) * g (size l' - 1) * 1 + D * 1) by nra.
rewrite one_plus_d_mul_g; apply Req_le; rewrite Rmult_1_r /=. f_equal; lia.
 --
 fold (ftype t).
 assert (n = size l') by lia. subst n.
 rewrite nth_rev /= ; [ | lia].
 rewrite -Hlen'. do 2 replace (_ - _)%N with O by lia. simpl.
 exists d'; split; auto.
 eapply Rle_trans; [ apply Hd' | ].
 apply d_le_g_1. lia.
Qed.

Theorem Fsum_backward_error :
  forall [n] (x: 'I_n -> ftype t) (Hfin: Binary.is_finite (mv_mathcomp.F.sum x)),
    exists (x': 'I_n -> R), 
    FT2R (mv_mathcomp.F.sum x) = \sum_i x' i /\
    (forall i: 'I_n, exists delta, 
        x' i = FT2R (x i) * (1 + delta) /\ Rabs delta <= g (n-1)).
Proof.
intros.
have :(Binary.is_finite (sumF (map x (ord_enum n)))).
rewrite -mv_mathcomp.F.sum_sumF //.
move  => Hfin'.
destruct (bSUM _ Hfin') as [x' [H [H0 H1]]].
rewrite size_map mv_mathcomp.size_ord_enum in H. subst n.
exists (nth R0 x').
split.
rewrite mv_mathcomp.F.sum_sumF. rewrite H0 mv_mathcomp.sumR_sum //.
move => i.
destruct (H1 i) as [delta [H2 H3]].
destruct i; simpl; lia.
exists delta.
rewrite {}H2.
change GRing.mul with Rmult.
change GRing.add with Rplus.
change (GRing.one _) with 1%Re.
split; auto.
clear H3.
f_equal.
f_equal.
clear.
destruct (size x'); clear x'.
simpl.
destruct i; lia.
rewrite (nth_map (@ord0 n) common.neg_zero).
rewrite mv_mathcomp.nth_ord_enum' //.
rewrite mv_mathcomp.size_ord_enum.
pose proof ltn_ord i. lia.
Qed.

Theorem fSUM :
    forall (x: list (ftype t))  (Hfin: Binary.is_finite (sumF x)),
    Rabs ((sumR (map FT2R x)) - FT2R (sumF x)) <=  g (size x) * (sumR (map Rabs (map FT2R x))).
Proof.
move => x.
rewrite -(revK x).
induction (rev x); clear x => Hfin.
- unfold g; subst; simpl. rewrite Rminus_0_r Rabs_R0; nra. 
- (* case a::l *)
assert (Hl: l = [] \/ l <> []).
destruct l; auto; right; congruence. 
destruct Hl.
+ (* case empty l *)
subst. unfold g; simpl; subst.
destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
rewrite Bplus_0R; auto.
field_simplify_Rabs; field_simplify; rewrite Rabs_R0. 
apply Rmult_le_pos; auto with commonDB; apply Rabs_pos.
+ (* case non-empty l *)
rewrite /sumF foldl_rev /= in Hfin.
change (fun x z : ftype t => Basics.flip BPLUS z x) with (@BPLUS _ t) in Hfin.
destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
(* IHl *)
rewrite -foldl_rev in B.
specialize (IHl B).
(* accuracy rewrites *)
destruct (BPLUS_accurate'  _ _ Hfin) as (d' & Hd'& Hplus).
move :IHl.
rewrite /sumF.
rewrite !foldl_rev.
change (fun x z : ftype t => Basics.flip BPLUS z x) with (@BPLUS _ t).
rewrite !map_rev !sumR_rev !size_rev => IHl.
simpl.
rewrite {}Hplus.
(* algebra *)
field_simplify_Rabs.
set s0 := sumR (map FT2R l).
 set (s :=  foldr _ _ l).
replace (- FT2R a * d' + s0 - FT2R s * d' - FT2R s) with
  ((s0 - FT2R s) - d' * (FT2R s + FT2R a)) by nra.
eapply Rle_trans; 
  [ apply Rabs_triang | eapply Rle_trans; [ apply Rplus_le_compat_r
    | rewrite !Rabs_Ropp] ].
apply IHl.
eapply Rle_trans; 
  [apply Rplus_le_compat_l | ].
  rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos.
  apply Hd'.
  eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat_r].
  rewrite Rabs_minus_sym in IHl; apply Rabs_le_minus in IHl. apply IHl.
rewrite !Rmult_plus_distr_l; rewrite <- !Rplus_assoc.
set (s1 := sumR (map Rabs (map FT2R l))).
replace (g (size l ) * s1 + D * (g (size l ) * s1)) with
  ((1+ D) * g (size l) * s1) by nra.
eapply Rle_trans; [apply Rplus_le_compat_r; 
  apply Rplus_le_compat_l; apply Rmult_le_compat_l; try apply Rabs_pos|].
apply default_rel_ge_0.
apply sumR_le_sumRabs.
rewrite sumRabs_Rabs.
rewrite one_plus_d_mul_g. 
rewrite Rplus_comm.
apply size_not_empty_nat in H.
apply Rplus_le_compat.
apply Rmult_le_compat; try apply Rabs_pos; 
  try apply default_rel_ge_0; try nra.
apply d_le_g_1; lia. 
apply Req_le; f_equal.
f_equal. lia. 
Qed.

Lemma Fsum_forward_error: 
    forall [n] (x: 'I_n -> ftype t)  (Hfin: Binary.is_finite (mv_mathcomp.F.sum x)),
    Rabs (\sum_i (FT2R (x i)) - FT2R (mv_mathcomp.F.sum x)) <= g n * (\sum_i (Rabs (FT2R (x i)))).
Proof.
intros.
have :(Binary.is_finite (sumF (map x (ord_enum n)))).
rewrite -mv_mathcomp.F.sum_sumF //.
move  => Hfin'.
move :(fSUM _ Hfin') => H.
rewrite !mv_mathcomp.sumR_sum !size_map !mv_mathcomp.size_ord_enum -map_comp in H.
rewrite mv_mathcomp.F.sum_sumF.
match goal with H: Rle (Rabs (Rminus ?A _)) (Rmult _ ?B) |- Rle (Rabs (Rminus ?A' _)) (Rmult _ ?B') =>
   replace A' with A; [replace B' with B | ]; auto; clear
end.
-
apply eq_bigr => i _.
destruct n. destruct i; lia.
rewrite -map_comp.
rewrite (nth_map (@ord0 n) R0).
rewrite  mv_mathcomp.nth_ord_enum' //.
rewrite mv_mathcomp.size_ord_enum //.
-
apply eq_bigr => i _.
destruct n. destruct i; lia.
rewrite (nth_map (@ord0 n) R0).
rewrite  mv_mathcomp.nth_ord_enum' //.
rewrite mv_mathcomp.size_ord_enum //.
Qed.

Lemma sum_forward_error_permute' :
   forall (x x0: list (ftype t))
    (Hfin: Binary.is_finite (sumF x))
    (Hfin0: Binary.is_finite (sumF x0))
    (Hper: Permutation x x0),   
    Rabs ((sumR (map FT2R x0)) - FT2R (sumF x0)) <=  g (size x) * (sumR (map Rabs (map FT2R x0))).
Proof.
intros.
eapply Rle_trans.
apply (fSUM x0 Hfin0).
apply Req_le; f_equal.
change @size with @length. 
rewrite (Permutation_length Hper); auto.
Qed.

Theorem sum_forward_error_permute :
   forall (x x0: list (ftype t))
    (Hfin: Binary.is_finite (sumF x))
    (Hfin0: Binary.is_finite (sumF x0))
    (Hper: Permutation x x0),   
    Rabs ((sumR (map FT2R x)) - FT2R (sumF x0)) <=  g (size x) * (sumR (map Rabs (map FT2R x))).
Proof.
intros.
rewrite (sumR_permute (map FT2R x) (map FT2R x0)); [|apply Permutation_map; auto].
eapply Rle_trans.
apply sum_forward_error_permute'; eauto.
apply Req_le; f_equal; symmetry.
f_equal. apply Permutation_length; auto. 
apply sumR_permute.
repeat apply Permutation_map; auto.
Qed.

End WithNan.
