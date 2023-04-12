(* This file contains lemmas regarding the accuracy of floating point 
  operations such as BPLUS, BFMA, and BMULT. *)

Require Import vcfloat.VCFloat.
Require Import common op_defs.

Section GenFloat.
Context {t : type}.

Lemma Bmult_0R {NAN: Nans} a f :
Binary.is_finite (fprec t) (femax t) (BMULT a f) = true ->
FT2R a = 0 -> 
(BMULT a f) = neg_zero \/ (BMULT a f) = pos_zero.
Proof. intros; destruct f; destruct a; simpl; try discriminate;
destruct s; destruct s0; simpl; auto; 
unfold FT2R, Binary.B2R in H0; simpl in H0;
apply Float_prop.eq_0_F2R in H0;
discriminate.
Qed.

Lemma Bplus_0R {NAN: Nans} a f :
Binary.is_finite (fprec t) (femax t) (BPLUS a f) = true ->
FT2R f = 0 -> 
FT2R (BPLUS a f) = FT2R a.
Proof.
intros; destruct f; destruct a; simpl; try discriminate;
destruct s; destruct s0; simpl; auto;
unfold FT2R, Binary.B2R in H0; simpl in H0;
apply Float_prop.eq_0_F2R in H0;
discriminate.
Qed.

Lemma Bfma_mult_0R {NAN: Nans} a f s :
Binary.is_finite (fprec t) (femax t) (BFMA a f s) = true ->
FT2R a = 0 -> 
FT2R (BFMA a f s) = FT2R s.
Proof. intros; destruct f; destruct a; destruct s; simpl; try discriminate;
destruct s; destruct s0; destruct s1; simpl; auto; 
unfold FT2R, Binary.B2R in H0; simpl in H0;
apply Float_prop.eq_0_F2R in H0;
discriminate.
Qed.


Lemma neg_zero_is_finite:
Binary.is_finite (fprec t) (femax t) neg_zero = true.
Proof. simpl; auto. Qed.

Definition fma_no_overflow (x y z: R) : Prop :=
  (Rabs (rounded t  (x * y + z)) < Raux.bpow Zaux.radix2 (femax t))%R.

Definition Bmult_no_overflow (x y: R) : Prop :=
  (Rabs (rounded t  (x * y)) < Raux.bpow Zaux.radix2 (femax t))%R.

Notation D := (@default_rel t).
Notation E := (@default_abs t).

Lemma generic_round_property:
  forall (x: R),
exists delta epsilon : R,
   delta * epsilon = 0 /\
  (Rabs delta <= D)%R /\
  (Rabs epsilon <= E)%R /\
   Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
               x = (x * (1+delta)+epsilon)%R.
Proof.
intros.
destruct (Relative.error_N_FLT Zaux.radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t) 
             (fprec_gt_0 t) (fun x0 : Z => negb (Z.even x0)) x)
  as [delta [epsilon [? [? [? ?]]]]].
exists delta, epsilon.
repeat split; auto.
Qed.

Lemma fma_accurate {NAN: Nans} : 
   forall x (FINx: Binary.is_finite (fprec t) (femax t) x = true) 
          y (FINy: Binary.is_finite (fprec t) (femax t) y = true) 
          z (FINz: Binary.is_finite (fprec t) (femax t) z = true)
          (FIN: fma_no_overflow (FT2R x) (FT2R y) (FT2R z)), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= D /\
   Rabs epsilon <= E /\ 
   (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1+delta) + epsilon)%R.
Proof.
intros.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t)
                      BinarySingleNaN.mode_NE x y z FINx FINy FINz).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) (FT2R x * FT2R y + FT2R z)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
-
destruct H as [? _].
fold (@BFMA NAN t) in H.
rewrite H.
apply generic_round_property.
-
red in FIN. unfold rounded in FIN.
Lra.lra.
Qed.

Lemma is_finite_fma_no_overflow {NAN: Nans}:
  forall x y z
  (HFINb : Binary.is_finite (fprec t) (femax t) (BFMA x y z) = true),
  fma_no_overflow (FT2R x) (FT2R y) (FT2R z).
Proof.
intros.
red. set (ov:= bpow Zaux.radix2 (femax t)).
pose proof Rle_or_lt ov (Rabs (rounded t (FT2R x * FT2R y + FT2R z)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
assert (HFIN: Binary.is_finite (fprec t) (femax t) x = true /\
  Binary.is_finite (fprec t) (femax t) y = true /\ 
  Binary.is_finite (fprec t) (femax t) z = true).
{ unfold BFMA in HFINb. 
    destruct x; destruct y; destruct z; simpl in *; try discriminate; auto.
    all: destruct s; destruct s0; destruct s1; simpl in *; try discriminate; auto. }
destruct HFIN as (A & B & C).
unfold rounded, FT2R, ov in H.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE x y z A B C) as
  H0.
simpl in H0; simpl in H;
rewrite H in H0. clear H. fold (@BFMA NAN t) in H0.
destruct (BFMA x y z); try discriminate.
Qed.

Lemma fma_accurate' {NAN: Nans} : 
   forall (x y z : ftype t)
          (FIN: Binary.is_finite _ _ (BFMA x y z) = true), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= D /\
   Rabs epsilon <= E /\ 
   (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1+delta) + epsilon)%R.
Proof.
intros.
assert (FIN2: Binary.is_finite (fprec t) (femax t) x = true /\
        Binary.is_finite (fprec t) (femax t) y = true /\
        Binary.is_finite (fprec t) (femax t) z = true).
destruct x; destruct y; destruct z; simpl in *; try discriminate; auto;
destruct s; destruct s0; destruct s1; try discriminate; auto.
destruct FIN2 as (FINx & FINy & FINz).
apply fma_accurate; auto.
apply is_finite_fma_no_overflow; auto.
Qed.

Lemma BMFA_finite_e {NAN: Nans} :
 forall (a u f : ftype t)
 (Hfin : Binary.is_finite _ _ (BFMA a f u) = true),
 Binary.is_finite _ _ a = true  /\ 
 Binary.is_finite _ _ f = true /\ 
 Binary.is_finite _ _ u = true.
Proof.
intros.
destruct a,f,u; inversion Hfin; clear Hfin; subst; 
 try solve [split; [ | split]; simpl; auto; constructor; auto].
all: try solve [destruct s,s0,s1; discriminate].
Qed.


Lemma BMULT_accurate {NAN: Nans}: 
   forall  x y (FIN: Bmult_no_overflow  (FT2R x) (FT2R y)), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= D /\
   Rabs epsilon <= E /\ 
   (@FT2R t (BMULT x y) = (FT2R x * FT2R y) * (1+delta) + epsilon)%R.
Proof.
intros.
pose proof (Binary.Bmult_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
                (mult_nan t) BinarySingleNaN.mode_NE x y).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) (FT2R x * FT2R y)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
destruct H as [? _].
unfold BMULT, BINOP.
rewrite H.
apply generic_round_property.
red in FIN. unfold rounded in FIN.
Lra.lra.
Qed.

Lemma is_finite_BMULT_no_overflow {NAN: Nans} :
  forall (x y : ftype t) 
  (HFINb : Binary.is_finite (fprec t) (femax t) (BMULT x y) = true),
  Bmult_no_overflow  (FT2R x) (FT2R y).
Proof.
intros.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) 
  (Rabs (rounded t (FT2R x * FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H; red.
unfold rounded, FT2R  in H.
pose proof (Binary.Bmult_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan t) BinarySingleNaN.mode_NE x y) as
  H0.
simpl in H0; simpl in H;
rewrite H in H0.  unfold BMULT, BINOP in HFINb.
destruct ((Binary.Bmult (fprec t) (femax t) (fprec_gt_0 t) 
             (fprec_lt_femax t) (mult_nan t) BinarySingleNaN.mode_NE x y));
simpl;  try discriminate.
Qed.

Lemma BMULT_accurate' {NAN: Nans}: 
  forall 
  (x y : ftype t) 
  (FIN: Binary.is_finite _ _ (BMULT x y) = true), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= D /\
   Rabs epsilon <= E /\ 
   (@FT2R t (BMULT x y) = (FT2R x * FT2R y) * (1+delta) + epsilon)%R.
Proof.
intros. 
pose proof BMULT_accurate  x y (is_finite_BMULT_no_overflow x y FIN); auto.
Qed.

Lemma BMULT_finite_e {NAN: Nans} :
 forall (a b : ftype t)
 (Hfin : Binary.is_finite _ _ (BMULT a b) = true),
 Binary.is_finite _ _ a = true  /\ 
 Binary.is_finite _ _ b = true.
Proof.
intros.
destruct a,b; inversion Hfin; clear Hfin; subst; auto.
Qed.

Lemma BPLUS_finite_e {NAN: Nans}:
 forall (a b : ftype t)
 (Hfin : Binary.is_finite _ _ (BPLUS a b) = true),
 Binary.is_finite _ _ a = true  /\ 
 Binary.is_finite _ _ b = true.
Proof.
intros.
destruct a,b; inversion Hfin; clear Hfin; subst; simpl; auto.
destruct s,s0; discriminate; auto.
Qed.


Definition Bplus_no_overflow (t: type) (x y: R) : Prop :=
  (Rabs ( Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE)  (x + y )) < Raux.bpow Zaux.radix2 (femax t))%R.

Lemma BPLUS_neg_zero {NAN: Nans} (a : ftype t) :
  Binary.is_finite _ _ a = true ->
  BPLUS a neg_zero = a.
Proof.
destruct a; unfold neg_zero; simpl; try discriminate; auto.
destruct s; auto.
Qed.

Lemma BPLUS_B2R_zero_r {NAN: Nans}  (a : ftype t) :
  Binary.is_finite _ _ a = true ->
  FT2R (BPLUS a (Zconst t 0)) = FT2R a.
Proof.
destruct a; unfold neg_zero; simpl; try discriminate; auto.
destruct s; auto.
Qed.

Lemma BPLUS_B2R_zero_l {NAN: Nans}  (a : ftype t) :
  Binary.is_finite _ _ a = true ->
  FT2R (BPLUS (Zconst t 0) a) = FT2R a.
Proof.
destruct a; unfold neg_zero; simpl; try discriminate; auto.
destruct s; auto.
Qed.

Lemma BPLUS_pzero_assoc_r {NAN: Nans}  (a b : ftype t) :
  Binary.is_finite _ _ a = true ->
  Binary.is_finite _ _ b = true ->
  BPLUS (BPLUS a (Zconst t 0)) b = BPLUS a (BPLUS (Zconst t 0) b).
Proof. intros;
destruct a; destruct b; destruct s; destruct s0; simpl; try discriminate; auto.
Qed.

Lemma BPLUS_pzero_symm {NAN: Nans}  (a : ftype t) :
  Binary.is_finite _ _ a = true ->
  BPLUS a (Zconst t 0) = BPLUS (Zconst t 0) a.
Proof. intros;
destruct a;  destruct s; simpl; try discriminate; auto.
Qed.


Lemma BPLUS_accurate {NAN: Nans} :
 forall      x (FINx: Binary.is_finite (fprec t) (femax t) x = true) 
             y (FINy: Binary.is_finite (fprec t) (femax t) y = true) 
          (FIN: Bplus_no_overflow t (FT2R x) (FT2R y)), 
  exists delta, 
   Rabs delta <= D /\
   (FT2R (BPLUS x y ) = (FT2R x + FT2R y) * (1+delta))%R.
Proof.
intros. 
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t)
                      BinarySingleNaN.mode_NE x y FINx FINy).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) (FT2R x + FT2R y)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
-
destruct H as [? _].
unfold BPLUS, BINOP.
rewrite H. 
assert (A: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R x) ) by (apply Binary.generic_format_B2R).
assert (B: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R y) ) by (apply Binary.generic_format_B2R).
pose proof Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R x) (FT2R y) A B.
unfold Relative.u_ro in H1. fold (D) in H1.
destruct H1 as (d & Hd & Hd').
assert (  Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
    (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
    (FT2R x + FT2R y)  =  Generic_fmt.round Zaux.radix2
        (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
        (Generic_fmt.Znearest (fun x0 : Z => negb (Z.even x0)))
        (FT2R x + FT2R y)) by auto.
rewrite <- H1 in Hd'. clear H1. rewrite Hd'; clear Hd'.
exists d; split; auto.
eapply Rle_trans; [apply Hd |].
apply Rdiv_le_left.
apply Fourier_util.Rlt_zero_pos_plus1. 
apply default_rel_gt_0.
eapply Rle_trans with (D * 1); try nra.
-
red in FIN.
Lra.lra.
Qed.

Lemma is_finite_sum_no_overflow {NAN: Nans}  :
  forall x y
  (HFINb : Binary.is_finite (fprec t) (femax t) (BPLUS x y) = true),
  Bplus_no_overflow t (FT2R x) (FT2R y).
Proof.
intros.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) (Rabs (rounded t (FT2R x + FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
assert (HFIN: Binary.is_finite (fprec t) (femax t) x = true /\
  Binary.is_finite (fprec t) (femax t) y = true).
{ unfold BPLUS, BINOP in HFINb. 
    destruct x; destruct y; simpl in *; try discriminate; auto.
    destruct s; destruct s0; simpl in *; try discriminate; auto.
}
destruct HFIN as (A & B).
unfold rounded, FT2R in H.
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE x y A B) as
  H0;
rewrite H in H0;
destruct H0 as ( C & _).
unfold BPLUS, BINOP in HFINb.
destruct ((Binary.Bplus (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
             (plus_nan t) BinarySingleNaN.mode_NE x y));
simpl; try discriminate.
Qed.


Lemma BPLUS_accurate' {NAN: Nans} :
  forall x y 
  (FIN: Binary.is_finite _ _ (BPLUS x y) = true), 
  exists delta, 
   Rabs delta <= D /\
   (@FT2R t (BPLUS x y ) = (FT2R x + FT2R y) * (1+delta))%R.
Proof.
intros.
assert (A: Binary.is_finite (fprec t) (femax t) x = true /\
  Binary.is_finite (fprec t) (femax t) y = true).
{ destruct x; destruct y; simpl; try discriminate; auto; 
  destruct s; destruct s0; simpl; try discriminate; auto. }
destruct A as (A & B).
pose proof BPLUS_accurate x A y B (is_finite_sum_no_overflow x y FIN); 
  auto.
Qed.


End GenFloat.