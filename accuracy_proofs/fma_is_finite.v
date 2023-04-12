Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common op_defs dotprod_model sum_model.
Require Import float_acc_lems list_lemmas.
Require Import dot_acc_lemmas sum_acc.

Require Import Reals.
Open Scope R.

Section NAN.
Variable NAN: Nans.

Definition fmax (t: type) := bpow Zaux.radix2 (femax t).

Lemma is_finite_fma_no_overflow' (t : type) :
  forall x y z
  (Hfinx: Binary.is_finite (fprec t) (femax t) x = true)
  (Hfiny: Binary.is_finite (fprec t) (femax t) y = true)
  (Hfinz: Binary.is_finite (fprec t) (femax t) z = true)
  (Hov : @fma_no_overflow t (FT2R x) (FT2R y) (FT2R z)),
 Binary.is_finite (fprec t) (femax t) (BFMA x y z) = true.
Proof.
intros.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t)
                      BinarySingleNaN.mode_NE x y z Hfinx Hfiny Hfinz).
unfold fma_no_overflow, FT2R, rounded in Hov;
apply Rlt_bool_true in Hov.
cbv zeta in H.
rewrite Hov in H; simpl in H; destruct H as (_ & B & _); simpl; auto.
Qed.

Definition fun_bnd (t : type) (n : nat) :=
let x := (fmax t - @default_abs t) / (1 + @default_rel t) - @g1 t n (n-1) in
let y := 1 / (1 + INR n * (@g t (n - 1) + 1)) in x * y.

Lemma rdiv_lt (a b: R) :
  0 < b -> 0 < a -> b < a -> / a < / b. 
Proof. 
intros.
replace (/b) with (1/b) by nra.
apply Rdiv_lt_right; auto.
rewrite Rmult_comm.
apply Rdiv_lt_left; auto.
nra.
Qed.

Lemma rdiv_le (a b: R) :
  0 < b -> 0 < a -> b <= a -> / a <= / b. 
Proof. 
intros. 
replace (/b) with (1/b) by nra.
apply Rcomplements.Rle_div_r; auto.
rewrite Rmult_comm.
apply Rdiv_le_left; auto.
nra.
Qed.

Lemma rdiv_mult_eq :
forall a b, b <> 0 -> a/b = a * (1/b) .
Proof.
(intros; field_simplify; nra).
Qed.

Lemma Rminus_le_minus a b c :
 b <= c -> a - c <= a - b.
Proof.  nra. Qed.

Lemma Rminus_lt_minus a b c :
 b < c -> a - c < a - b.
Proof.  nra. Qed.

Lemma defualt_abs_le_fmax t :
@default_abs t <= fmax t.
Proof.
replace (fmax t) with (1 * fmax t) by nra.
unfold default_abs, fmax; apply Rmult_le_compat; try nra.
apply bpow_ge_0.
apply bpow_le.
apply Z.le_sub_le_add_r.
apply Z.le_sub_le_add_r.
Search fprec femax.
eapply Z.le_trans with (fprec t + fprec t + femax t)%Z; 
  [ | repeat apply Zplus_le_compat_r; apply Z.lt_le_incl; apply fprec_lt_femax].
eapply Z.le_trans with (fprec t + fprec t + fprec t)%Z;
[ |  repeat apply Zplus_le_compat_l;apply Z.lt_le_incl; apply fprec_lt_femax ].
eapply Z.le_trans with (1 + fprec t + fprec t)%Z;
[ |  repeat apply Zplus_le_compat_r;apply Z.lt_le_incl;apply fprec_gt_one].
eapply Z.le_trans with (1 + 1 + fprec t)%Z;
[ |  repeat apply Zplus_le_compat_r; repeat apply Zplus_le_compat_l; apply Z.lt_le_incl;
apply fprec_gt_one].
eapply Z.le_trans with (1 + 1 + 1)%Z;
[ lia |  repeat apply Zplus_le_compat_r; repeat apply Zplus_le_compat_l; apply Z.lt_le_incl;
apply fprec_gt_one].
Qed.

Lemma bpow_femax_lb t : 
4 <= bpow Zaux.radix2 (femax t).
Proof. 
pose proof fprec_gt_one t.
pose proof fprec_lt_femax t.
assert (1 < femax t)%Z.
eapply Z.lt_trans with (fprec t); auto.
eapply Rle_trans with (bpow Zaux.radix2 2).
unfold bpow; simpl; nra.
apply bpow_le; lia.
Qed.

Lemma bpow_fprec_lb t : 
2 <= bpow Zaux.radix2 (fprec t).
Proof. 
pose proof fprec_gt_one t.
eapply Rle_trans with (bpow Zaux.radix2 1).
unfold bpow; simpl; nra.
apply bpow_le; lia.
Qed.

Lemma default_abs_ub t :
@default_abs t <= 1.
Proof.
unfold default_abs.
pose proof bpow_gt_0 Zaux.radix2 (femax t).
pose proof bpow_gt_0 Zaux.radix2 (fprec t).
replace (3 - femax t - fprec t)%Z with (3 +- femax t +- fprec t)%Z by lia.
rewrite !bpow_plus.
rewrite <- !Rmult_assoc.
replace (/ 2 * bpow Zaux.radix2 3) with 4; [|simpl;nra].
rewrite !bpow_opp, !Rcomplements.Rle_div_r. 
field_simplify; try nra.
eapply Rle_trans; [| apply Rmult_le_compat ;[ | | apply bpow_fprec_lb | apply bpow_femax_lb  ]]; try nra.
apply Rlt_gt. 
replace (/ bpow Zaux.radix2 (femax t)) with (1 / bpow Zaux.radix2 (femax t)) by nra.
apply Rdiv_lt_0_compat; try nra.
apply Rlt_gt;
replace (/ bpow Zaux.radix2 (fprec t)) with (1 / bpow Zaux.radix2 (fprec t)) by nra;
apply Rdiv_lt_0_compat; try nra.
Qed.

Lemma default_rel_ub t :
@default_rel t <= 1.
Proof.
unfold default_rel.
pose proof bpow_gt_0 Zaux.radix2 (fprec t).
rewrite !bpow_plus.
rewrite <- !Rmult_assoc.
rewrite Rmult_comm.
rewrite <- !Rmult_assoc.
replace (bpow Zaux.radix2 1 * / 2) with 1; [|simpl;nra].
rewrite !bpow_opp, !Rcomplements.Rle_div_r. 
field_simplify; try nra.
replace 1 with  (bpow Zaux.radix2 0).
apply bpow_le.
pose proof fprec_gt_one t; lia.
simpl; auto.
apply Rlt_gt;
replace (/ bpow Zaux.radix2 (fprec t)) with (1 / bpow Zaux.radix2 (fprec t)) by nra;
apply Rdiv_lt_0_compat; try nra.
Qed.


Lemma fun_bnd_pos_1 : 
forall t n
(Hn : @g1 t (n + 1) n <= fmax t), 
0 <= (fmax t - @default_abs t) / (1 + @default_rel t) - @g1 t n (n-1).
Proof.
intros;
apply Rle_0_minus. apply Generic_proof.Rdiv_le_mult_pos;
[apply default_rel_plus_1_gt_0 | apply Rminus_plus_le_minus].
assert (Hn': (n=0)%nat \/ (1<=n)%nat) by lia; destruct Hn'; subst.
{ simpl. unfold g1, g. simpl; field_simplify. apply defualt_abs_le_fmax. }
assert (Hn': (n=1)%nat \/ (1 < n)%nat) by lia; destruct Hn'; subst.
{ simpl. unfold g1, g. simpl; field_simplify.
eapply Rle_trans.
apply Rplus_le_compat. 
apply Rmult_le_compat.
apply default_abs_ge_0. 
apply default_rel_ge_0.
apply default_abs_ub.
apply default_rel_ub.
apply Rmult_le_compat_l; try nra.
apply default_abs_ub.
eapply Rle_trans; [| apply bpow_femax_lb]; nra. }
eapply Rle_trans. apply mult_d_e_g1_le'; try lia. 
replace (S n) with (n + 1)%nat by lia.
replace (S (n - 1)) with n by lia; auto.
Qed.


Lemma fun_bnd_le (t : type) (n : nat) :
forall (Hn : @g1 t (S n + 1) (S n) <= fmax t), 
fun_bnd t (S n) <= fun_bnd t n.
Proof.
assert (Hn': (n=0)%nat \/ (1<=n)%nat) by lia; destruct Hn'; subst.
{ intros; simpl. unfold fun_bnd. apply Rmult_le_compat; try apply Rabs_pos.
apply fun_bnd_pos_1; auto. simpl. unfold g. simpl; field_simplify; nra.
apply Rminus_le_minus. simpl. unfold g1, g; field_simplify; simpl.
field_simplify. apply default_abs_ge_0.
simpl; unfold g; field_simplify; simpl; try nra. }
intros; unfold fun_bnd.
assert (0 < 1 + INR (S n) * (@g t (S n - 1) + 1)).
{ 
apply Rplus_lt_le_0_compat; try nra.
apply Rmult_le_pos; try apply pos_INR.
apply Rplus_le_le_0_compat; try nra; apply g_pos. }
assert (
INR n * @g t (n - 1) + INR n + 1 > 0).
{ 
apply Rplus_lt_le_0_compat; try nra.
apply Rplus_le_lt_0_compat; [| apply lt_0_INR; lia].
apply Rmult_le_pos; try apply pos_INR.
apply g_pos. }
apply Rmult_le_compat; try apply Rabs_pos.
apply fun_bnd_pos_1; auto.
apply Rdiv_le_0_compat_Raux; try nra.
apply Rminus_le_minus.
replace (S n -1)%nat with (S (n-1))%nat by lia.
apply g1n_le_g1Sn; auto.
apply Rcomplements.Rle_div_r.
apply Rlt_gt.
replace (/ (1 + INR (S n) * (@g t (S n - 1) + 1))) with 
  (1/(1 + INR (S n) * (@g t (S n - 1) + 1))) by nra.
apply Rdiv_lt_0_compat; try nra.
field_simplify; try nra.
apply Rcomplements.Rle_div_r; try nra.
rewrite Rmult_1_l.
apply Rplus_le_compat; try nra.
apply Rplus_le_compat.
apply Rmult_le_compat; [ apply pos_INR | apply g_pos | | ].
apply le_INR; lia.
replace (S n - 1)%nat with (S (n-1))%nat by lia.
apply le_g_Sn.
apply le_INR; lia.
Qed.


Lemma length_split {A : Type} (l : list (A * A)) :
length (fst (List.split l)) = length (snd (List.split l)).
Proof. 
induction l; [simpl; auto | ].
destruct a; simpl; destruct (List.split l); simpl.
simpl in IHl; lia.
Qed.

Lemma fun_bound_pos t n :
forall (Hn : @g1 t (n + 1) n <= fmax t), 
0 <= fun_bnd t n. 
Proof.
intros;
unfold fun_bnd; apply Rmult_le_pos.
apply fun_bnd_pos_1; auto.
apply Rdiv_le_0_compat_Raux; try nra.
apply Rplus_lt_le_0_compat; try nra.
apply Rmult_le_pos; try apply pos_INR.
apply Rplus_le_le_0_compat; try nra; apply g_pos.
Qed.

Lemma combine_split {A : Type} (l : list (A * A)) :
combine (fst (List.split l)) (snd (List.split l)) = l.
Proof.
induction l; [simpl; auto | ].
destruct a; simpl; destruct (List.split l); simpl.
simpl in IHl; rewrite IHl; auto.
Qed.


Lemma finite_sum_from_bounded : 
  forall (t: type) (v1 v2: list (ftype t))
  (fp : ftype t) 
  (Hfp: fma_dot_prod_rel (List.combine v1 v2) fp)
  (Hn : @g1 t (S  (length (List.combine v1 v2)) + 1) (S (length (List.combine v1 v2))) <= fmax t),
  (forall x, In x (List.combine v1 v2) -> 
    Binary.is_finite _ _ (fst x) = true /\ 
    Binary.is_finite _ _ (snd x) = true /\ 
    Rabs (FT2R (fst x)) < sqrt  (fun_bnd t (length (List.combine v1 v2))) /\
    Rabs (FT2R (snd x)) < sqrt  (fun_bnd t (length (List.combine v1 v2))))-> 
  Binary.is_finite _ _ fp = true. 
Proof.
intros ? ? ? .
induction (List.combine v1 v2).
{ intros; inversion Hfp; subst; simpl; auto. }
{ intros. inversion Hfp; subst.
assert (Hn' : @g1 t (S (length l) + 1) (S (length l)) <= fmax t).
{ eapply Rle_trans; [ | apply Hn]; simpl. set (n:= (length l + 1)%nat).
  replace (length l) with (n-1)%nat by lia.
  replace (S(n-1))%nat with (S n - 1)%nat by lia; apply g1n_le_g1Sn; lia. }
assert (Hin: forall x : (ftype t * ftype t),
       In x l -> Binary.is_finite _ _ (fst x) = true /\
       Binary.is_finite _ _ (snd x) = true /\
       Rabs (FT2R (fst x)) < sqrt (fun_bnd t (length l)) /\
       Rabs (FT2R (snd x)) < sqrt (fun_bnd t (length l))).
  { intros. repeat split; [apply H; simpl; auto | apply H; simpl; auto  | | ]. 
    eapply Rlt_le_trans; [apply H; simpl; auto | apply sqrt_le_1_alt; apply fun_bnd_le; auto  ].
    eapply Rlt_le_trans; [apply H; simpl; auto | apply sqrt_le_1_alt; apply fun_bnd_le; auto ]. }
assert (Hfina : Binary.is_finite (fprec t) (femax t) (fst a) = true /\
        Binary.is_finite (fprec t) (femax t) (snd a) = true) by
  (split; apply H; simpl; auto); destruct Hfina as (Hfina1 & Hfina2).
specialize (IHl s H3 Hn' Hin). 
apply is_finite_fma_no_overflow'; auto. 
unfold fma_no_overflow, rounded.
destruct (@generic_round_property t (FT2R (fst a) * FT2R (snd a) + FT2R s)) as 
  (del & eps & Hed & Hd & He & Hrn );
rewrite Hrn; clear Hrn.
destruct (dotprod_rel_R_exists_fma t l s H3) as (rs & Hrs).
destruct (sum_rel_R_abs_exists_fma t l s H3) as (rs_abs & Habs).
pose proof fma_dotprod_forward_error_rel l
   s H3 IHl rs rs_abs Hrs Habs as Hacc. 
apply Rabs_le_minus in Hacc.
set (n:=(length l)) in *.
assert (Hacc' : Rabs (FT2R s) <= (@g t n + 1) * rs_abs + @g1 t n (n - 1)).
{ eapply Rle_trans. 
apply Hacc. replace (g n * rs_abs + g1 n (n - 1) + Rabs rs)
with ((@g t n * rs_abs + Rabs rs) + @g1 t n (n - 1)) by nra. 
apply Rplus_le_compat_r.
field_simplify.
apply Rplus_le_compat_l. 
rewrite <- (@R_dot_prod_rel_Rabs_eq (map FR2 l)); try nra; auto.
apply (@dot_prod_sum_rel_R_Rabs (map FR2 l)); auto. } clear Hacc.
pose proof dotprodR_rel_bound' as C.
pose proof dotprodR_rel_bound'' as D.
eapply Rle_lt_trans; [apply Rabs_triang |].
rewrite Rabs_mult.
eapply Rle_lt_trans; [apply Rplus_le_compat |]. 
apply Rmult_le_compat; try apply Rabs_pos.
eapply Rle_trans; [apply Rabs_triang |].
apply Rplus_le_compat.
rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos.
apply Rlt_le; apply H; simpl; auto.
apply Rlt_le; apply H; simpl; auto.
eapply Rle_trans.
apply Hacc'.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l. 
apply Rplus_le_le_0_compat; try nra. apply g_pos.
apply D. 
apply fun_bound_pos.
apply Hn'.
apply Habs.
intros; split; apply Rlt_le; apply H; simpl; auto.
assert (HD: Rabs (1 + del) <= (1 + @default_rel t )).
{ eapply Rle_trans; [apply Rabs_triang| rewrite Rabs_R1; apply Rplus_le_compat_l].
eapply Rle_trans; [apply Hd |];  nra. }
apply HD.
apply He.
rewrite sqrt_def.
{
(*algebra*)
unfold fun_bnd.
replace (length (a :: l)) with (S n) by (simpl; lia).
set (x:= (@g t ((S n) - 1) + 1)).
set (y:= (1 + INR (S n) * x)).
set (z:= @g1 t (S n) ((S n) - 1)).
set (u := ((fmax t - @default_abs t) / (1 + @default_rel t) - z) * (1 / y)).
rewrite <- !Rplus_assoc.
replace (( u + (@g t n + 1) * (INR (length l) *  u)))
  with ( u * (1 + (@g t n + 1) * (INR (length l))))
  by nra.
apply Rcomplements.Rlt_minus_r.
apply Rcomplements.Rlt_div_r. 
apply Rlt_gt; apply default_rel_plus_1_gt_0.
apply Rcomplements.Rlt_minus_r.
assert (0 < 1 + (@g t n + 1) * INR (length l)).
{ apply Rplus_lt_le_0_compat; try nra.
apply Rmult_le_pos; try apply pos_INR.
apply Rplus_le_le_0_compat; try nra; apply g_pos. }
apply Rcomplements.Rlt_div_r; auto.
assert (0 < 1 / (1 + INR (S (length l)) * (@g t (S (length l) - 1) + 1))).
{ apply Rcomplements.Rdiv_lt_0_compat; try nra.
apply Rplus_lt_le_0_compat; try nra.
apply Rmult_le_pos; try apply pos_INR.
apply Rplus_le_le_0_compat; try nra; apply g_pos. }
assert (0 < 1 + INR (S n) * (@g t (S n - 1) + 1)).
{ 
apply Rplus_lt_le_0_compat; try nra.
apply Rmult_le_pos; try apply pos_INR.
apply Rplus_le_le_0_compat; try nra; apply g_pos. }
rewrite rdiv_mult_eq; try nra.
unfold u, z, y, x.
apply Rmult_lt_compat.
apply fun_bnd_pos_1; auto.
apply Rlt_le; auto.
unfold fmax.
apply Rminus_lt_minus.
replace n with (length l).
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl. subst.
simpl. unfold g1, g; field_simplify; simpl. field_simplify; apply default_abs_gt_0.
apply length_not_empty_nat in H4.
replace (S (length l) - 1)%nat with (S (length l - 1))%nat by lia.
apply g1n_lt_g1Sn; auto.
subst n; auto.
apply Rcomplements.Rlt_div_r.
apply Rlt_gt.
replace (/ (1 + INR (S n) * (@g t (S n - 1) + 1))) with 
  (1/(1 + INR (S n) * (@g t (S n - 1) + 1))) by nra.
apply Rdiv_lt_0_compat; try nra. 
field_simplify; try nra.
apply Rcomplements.Rlt_div_r; try nra.
rewrite Rmult_1_l.
apply Rplus_lt_le_compat; try nra.
apply Rplus_le_lt_compat.
rewrite Rmult_comm.
apply Rmult_le_compat; [ apply pos_INR | apply g_pos | | ].
apply le_INR; lia.
replace (S n - 1)%nat with (n)%nat by lia; try nra.
unfold n. 
apply lt_INR; lia.
}
apply fun_bound_pos; auto.
}
Qed.


End NAN.