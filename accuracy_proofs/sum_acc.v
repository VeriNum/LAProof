(*This file contains two theorems: forward and backward error bounds for 
  the sum of two floating point lists; the functional model for
  the summation is defined in sum_model.v.*)

Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common sum_model float_acc_lems op_defs list_lemmas.

Require Import Reals.
Open Scope R.

Require Import Sorting Permutation.

Section BackwardError. 
Variable (NAN: Nans) (t: type).
Notation g := (@g t).
Notation D := (@default_rel t).

Variable (x : list (ftype t)).
Notation xR := (map FT2R x).
Hypothesis (Hfin: Binary.is_finite (fprec t) (femax t) (sumF x) = true).

Theorem bSUM :
    exists (x': list R), 
    length x' = length x /\
    FT2R (sumF x) = sumR x' /\
    (forall n, (n < length x')%nat -> exists delta, 
        nth n x' 0 = FT2R (nth n x neg_zero) * (1 + delta) /\ Rabs delta <= g (length x' - 1)).
Proof.
induction x.
{ intros; exists []; repeat split; auto. intros. 
  intros. simpl in H; assert (n = 0)%nat by lia; subst.
  exists 0; split; [simpl; nra| unfold g; rewrite Rabs_R0; simpl; nra].
}
(* case a::l *)
intros.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* case empty l *)
{ subst; simpl in *;
  destruct (BPLUS_finite_e _ _ Hfin).
  exists [FT2R a]; split; [ simpl; auto | split ; 
  [unfold sum; rewrite BPLUS_neg_zero|] ].
  unfold sumR; simpl; nra. auto.  
  intros. exists 0; simpl in H1; split; 
  [assert ((n = 1)%nat \/ (n = 0)%nat) by lia; destruct H2; subst; simpl; nra|].
  rewrite Rabs_R0; simpl; unfold g; nra.
}
(* case non-empty l *)
simpl in *.
destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
(* IHl *)
pose proof (length_not_empty_nat l H) as Hlen1.
specialize (IHl B).
destruct IHl as (l' & Hlen' & Hsum & Hdel); auto.
(* construct l'0 *)
pose proof (BPLUS_accurate' a (sumF l) Hfin) as Hplus.
destruct Hplus as (d' & Hd'& Hplus).
exists (FT2R a * (1+d') :: map (Rmult (1+d')) l'); repeat split.
{ simpl; auto. rewrite map_length; auto. }
{ simpl; rewrite Hplus, Rmult_plus_distr_r, Hsum, <- sumR_mult; auto. } 
intros. destruct n. 
{ simpl. exists d'; split; auto.
  eapply Rle_trans; [apply Hd'| ]. apply d_le_g_1. rewrite map_length; auto.
  rewrite Hlen'. lia. }
simpl in H0; rewrite map_length in H0; rewrite Hlen' in H0.
assert (Hlen2: (n < length l')%nat) by lia.
specialize (Hdel n Hlen2).
destruct Hdel as (d & Hd1 & Hd2).
exists ( (1+d') * (1+d) -1). simpl; split.
{ replace 0 with (Rmult (1 + d') 0) by nra. rewrite map_nth; rewrite Hd1; nra. }
rewrite map_length. field_simplify_Rabs. 
  eapply Rle_trans; [apply Rabs_triang | eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang | ]  ].
rewrite Rabs_mult.
replace (Rabs d' * Rabs d + Rabs d' + Rabs d ) with
  ((1 + Rabs d') * Rabs d + Rabs d' ) by nra.
eapply Rle_trans; [apply Rplus_le_compat | ].
apply Rmult_le_compat; try apply Rabs_pos.
apply Fourier_util.Rle_zero_pos_plus1; try apply Rabs_pos.
apply Rplus_le_compat_l; apply Hd'.
apply Hd2. apply Hd'.
replace ((1 + D) * g (length l' - 1) + D) with
((1 + D) * g (length l' - 1) * 1 + D * 1) by nra.
rewrite one_plus_d_mul_g; apply Req_le; rewrite Rmult_1_r. f_equal; lia.
Qed.

End BackwardError. 

Section ForwardError.

Variable (NAN: Nans) (t: type).
Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).

Variable (x : list (ftype t)).
Notation xR := (map FT2R x). 
Notation n := (length x).

Hypothesis (Hfin: Binary.is_finite (fprec t) (femax t) (sumF x) = true).

Theorem fSUM :
    Rabs ((sumR xR) - FT2R (sumF x)) <=  g n * (sumR (map Rabs xR)).
Proof.
induction x.
{ intros; unfold g; subst; simpl;
  rewrite Rminus_0_r, Rabs_R0; nra.  } 
(* case a::l *)
intros.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* case empty l *)
{ subst. unfold g; simpl; subst.
destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
rewrite BPLUS_neg_zero; auto.
field_simplify_Rabs; field_simplify; rewrite Rabs_R0. 
apply Rmult_le_pos; auto with commonDB; apply Rabs_pos. }
(* case non-empty l *)
simpl in *.
destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
(* IHl *)
specialize (IHl B).
(* accuracy rewrites *)
destruct (BPLUS_accurate'  a (sumF l) Hfin) as (d' & Hd'& Hplus).
rewrite Hplus. 
(* algebra *)
field_simplify_Rabs.
set (s0 := sumR (map FT2R l)). 
set (s :=  (sumF l)).
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
replace (g (length l ) * s1 + D * (g (length l ) * s1)) with
  ((1+ D) * g (length l) * s1) by nra.
eapply Rle_trans; [apply Rplus_le_compat_r; 
  apply Rplus_le_compat_l; apply Rmult_le_compat_l; try apply Rabs_pos|].
apply default_rel_ge_0.
apply sumR_le_sumRabs.
rewrite sumRabs_Rabs.
rewrite one_plus_d_mul_g. 
rewrite Rplus_comm.
apply length_not_empty in H; auto.
apply Rplus_le_compat.
apply Rmult_le_compat; try apply Rabs_pos; 
  try apply default_rel_ge_0; try nra.
apply d_le_g_1; lia. 
apply Req_le; f_equal.
f_equal. lia. 
Qed.

End ForwardError.

Section SumPermute.

Variable (NAN: Nans) (t: type).
Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).

Variable (x x0: list (ftype t)).
Notation xR := (map FT2R x). 
Notation xR0 := (map FT2R x0). 
Notation n := (length x).

Hypothesis (Hfin: Binary.is_finite (fprec t) (femax t) (sumF x) = true).
Hypothesis (Hfin0: Binary.is_finite (fprec t) (femax t) (sumF x0) = true).
Hypothesis (Hper: Permutation x x0).

Lemma sum_forward_error_permute' :
    Rabs ((sumR xR0) - FT2R (sumF x0)) <=  g n * (sumR (map Rabs xR0)).
Proof.
eapply Rle_trans.
apply (fSUM _ _ x0 Hfin0).
apply Req_le; f_equal. rewrite (Permutation_length Hper); auto.
Qed.

Theorem sum_forward_error_permute :
    Rabs ((sumR xR) - FT2R (sumF x0)) <=  g n * (sumR (map Rabs xR)).
Proof.
rewrite (sumR_permute xR xR0); [|apply Permutation_map; auto].
eapply Rle_trans.
apply sum_forward_error_permute'.
apply Req_le; f_equal. 
rewrite (sumR_permute (map Rabs xR) (map Rabs xR0)); auto.
repeat (apply Permutation_map); auto.
Qed.

End SumPermute.
