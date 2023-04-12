Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common op_defs dotprod_model sum_model.
Require Import float_acc_lems list_lemmas.
Require Import fma_dot_acc sum_acc.

Require Import Reals.
Open Scope R.

Section NAN.
Variable NAN: Nans.

Definition fmax (t: type) := bpow Zaux.radix2 (femax t).

Lemma is_finite_sum_no_overflow' (t : type) :
  forall x y
  (Hfinx: Binary.is_finite (fprec t) (femax t) x = true)
  (Hfiny: Binary.is_finite (fprec t) (femax t) y = true)
  (Hov :   Bplus_no_overflow t (FT2R x) (FT2R y)),
 Binary.is_finite (fprec t) (femax t) (BPLUS t x y ) = true.
Proof.
intros.
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t)
                      BinarySingleNaN.mode_NE x y Hfinx Hfiny ).
unfold Bplus_no_overflow, FT2R in Hov.
apply Rlt_bool_true in Hov.
rewrite Hov in H; simpl in H; destruct H as (_ & B & _); simpl; auto.
Qed.

Definition fun_bnd (t : type) (n : nat) :=
fmax t / (1 + default_rel t) * 1 / (1 + INR n * (g t (n - 1) + 1)) .

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

Lemma fun_bnd_le (t : type) (n : nat) :
fun_bnd t (S n) <= fun_bnd t n.
Proof. 
intros; unfold fun_bnd. apply Rmult_le_compat_l.
rewrite Rmult_1_r.
apply Rcomplements.Rdiv_le_0_compat.
unfold fmax; apply bpow_ge_0.
eapply Rlt_trans with 1; try nra.
apply default_rel_plus_1_gt_1.
apply rdiv_le;  try (
apply Rplus_lt_le_0_compat; try nra;
apply Rmult_le_pos; [apply pos_INR| ];
apply Rplus_le_le_0_compat; try nra;
apply g_pos ).
apply Rplus_le_compat_l.
apply Rmult_le_compat; [apply pos_INR | | |].
apply Rplus_le_le_0_compat; try nra; apply g_pos.
apply le_INR; try lia.
unfold g; field_simplify.
apply Rle_pow.
apply default_rel_plus_1_ge_1.
simpl; lia.
Qed.


Lemma finite_sum_from_bounded : 
  forall (t: type) (l: list (ftype t))
  (fs : ftype t) 
  (Hfs: sum_rel_Ft t l fs),
  (forall x, In x l -> 
    Binary.is_finite _ _ x = true /\ Rabs (FT2R x) < fun_bnd t (length l)) -> 
  Binary.is_finite _ _ fs = true. 
Proof.
intros ?.
induction l.
{ intros; inversion Hfs; subst; simpl; auto. }
{ intros. inversion Hfs; subst.
assert (Hin: forall x : ftype t,
       In x l -> Binary.is_finite _ _ x = true /\
       Rabs (FT2R x) < fun_bnd t (length l)).
  { intros. split; [apply H; simpl; auto | ]. 
    eapply Rlt_le_trans; [apply H; simpl; auto | ].
    apply fun_bnd_le. }  
assert (Hfina : Binary.is_finite (fprec t) (femax t) a = true) by
  (apply H; simpl; auto).
unfold sum.
fold (@sum_rel_Ft NAN t) in H3.
specialize (IHl s H3 Hin). 
apply is_finite_sum_no_overflow'; auto. 
unfold Bplus_no_overflow.
assert (A: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R a) ) by (apply Binary.generic_format_B2R).
assert (B: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R s) ) by (apply Binary.generic_format_B2R).
destruct (Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R a) (FT2R s) A B) as (d & Hd & Hd').
unfold Relative.u_ro in Hd. fold (default_rel t) in Hd.
assert ( H1: Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
    (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
    (FT2R a + FT2R s)  =  Generic_fmt.round Zaux.radix2
        (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
        (Generic_fmt.Znearest (fun x0 : Z => negb (Z.even x0)))
        (FT2R a + FT2R s)) by auto.
rewrite <- H1 in Hd'; clear H1; rewrite Hd'; clear Hd'.
destruct (sum_rel_R_exists t l s H3) as (rs & Hrs).
destruct (sum_rel_R_abs_exists t l s H3) as (rs_abs & Habs).
pose proof sum_forward_error NAN t l s rs rs_abs H3 Hrs Habs IHl as H1.
pose proof sum_rel_bound' as C.
pose proof sum_rel_bound'' as D.
rewrite Rabs_minus_sym in H1.
apply Rabs_le_minus in H1.
eapply Rle_lt_trans.
rewrite Rabs_mult.
apply Rmult_le_compat; try apply Rabs_pos.
eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat ].
apply Rlt_le; apply H; simpl; auto.
assert (Rabs (FT2R s) <= (g t (length l - 1) + 1) * rs_abs).
{ eapply Rle_trans; [apply H1| field_simplify; apply Rplus_le_compat_l].
  eapply Rle_trans; [ eapply sum_rel_R_Rabs; [apply Hrs | apply Habs] |] . 
  eapply Req_le; eapply sum_rel_R_Rabs_eq; apply Habs. }
eapply Rle_trans.
apply H0.
apply Rmult_le_compat_l. 
apply Rplus_le_le_0_compat; try nra. apply g_pos.
apply D. apply Habs.
intros. apply Rlt_le. apply H; simpl; auto.
assert (HD: Rabs (1 + d) <= (1 + default_rel t )).
{ eapply Rle_trans; [apply Rabs_triang| rewrite Rabs_R1; apply Rplus_le_compat_l].
eapply Rle_trans; [apply Hd |].
apply Rdiv_le_left.
apply Fourier_util.Rlt_zero_pos_plus1. 
apply default_rel_gt_0.
eapply Rle_trans with (default_rel t * 1); try nra. }
apply HD.
(*algebra*)
unfold fun_bnd; rewrite Rmult_1_r.
set (x:= (g t (length (a :: l) - 1) + 1)).
set (y:= (1 + INR (length (a :: l)) * x)).
set (z:= (fmax t / (1 + default_rel t) / y)).
replace ((z + (g t (length l - 1) + 1) * (INR (length l) * z)))
  with (z * (1 + (g t (length l - 1) + 1) * (INR (length l))))
  by nra.
rewrite Rmult_comm.
rewrite <- Rmult_assoc.
assert (Hy : 0 < y).
{ unfold y.
  apply Rplus_lt_le_0_compat; try nra.
  apply Rmult_le_pos; [apply pos_INR|].
  unfold x. apply Rplus_le_le_0_compat; try nra.
  apply g_pos. }
assert (Hy' : y <> 0). { apply Stdlib.Rlt_neq_sym; auto. }
assert (H0: (1 + default_rel t) * z = fmax t / y).
{ unfold z; field_simplify; auto. 
split; auto. 
apply tech_Rplus; try nra.
apply default_rel_gt_0. }
rewrite H0.
rewrite rdiv_mult_eq; auto.
replace (bpow Zaux.radix2 (femax t)) with 
  (bpow Zaux.radix2 (femax t) * 1) by nra.
rewrite Rmult_assoc.
apply Rmult_lt_compat_l. apply bpow_gt_0.
rewrite Rmult_comm.
rewrite <- rdiv_mult_eq; auto.
apply Rdiv_lt_left; auto.
rewrite Rmult_1_l.
unfold y.
apply Rplus_le_lt_compat; try nra.
rewrite Rmult_comm.
eapply Rle_lt_trans with  (INR (length l) * x).
apply Rmult_le_compat_l; [apply pos_INR|]. 
unfold x.
apply Rplus_le_compat_r.
unfold g. 
apply Rplus_le_compat_r.
apply Rle_pow.
apply default_rel_plus_1_ge_1.
simpl; lia.
apply Rmult_lt_compat_r.
unfold x.
apply Rle_lt_0_plus_1; apply g_pos.
apply lt_INR; simpl; try lia. }
Qed.



End NAN.