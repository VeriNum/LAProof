(* This file contains lemmas regarding the accuracy of floating point 
  operations such as BPLUS, BFMA, and BMULT. *)

Require Import vcfloat.VCFloat.
From LAProof.accuracy_proofs 
  Require Import common op_defs.
Set Warnings "-notation-overriden, -parsing".
Require Import mathcomp.ssreflect.ssreflect.

Section GenFloat.
Context {NAN: Nans} {t : type} {STD: is_standard t}.

Lemma Bmult_0R a f :
is_finite (BMULT a f) = true ->
FT2R a = 0 -> 
(BMULT a f) = (ftype_of_float neg_zero)
   \/ (BMULT a f) = (ftype_of_float pos_zero).
Proof.
  rewrite is_finite_Binary/BMULT/BINOP //= 
    -!B2R_float_of_ftype /pos_zero/neg_zero/Binary.Bmult
    !float_of_ftype_of_float.
  destruct (float_of_ftype f); 
  destruct (float_of_ftype a); 
  destruct s; destruct s0 => //=; 
  move => FIN HA; try discriminate FIN; auto;
  try apply Float_prop.eq_0_F2R in HA;
  try repeat (destruct m0; try discriminate HA).
Qed.

Lemma Bplus_0R a f :
is_finite (BPLUS a f) = true ->
FT2R f = 0 -> 
FT2R (BPLUS a f) = FT2R a.
Proof.
  rewrite is_finite_Binary/BMULT/BINOP //= 
    -!B2R_float_of_ftype /pos_zero/neg_zero/Binary.Bmult
    !float_of_ftype_of_float.
  destruct (float_of_ftype f); 
  destruct (float_of_ftype a); 
  destruct s; destruct s0 => //=; 
  move => FIN HA; try discriminate FIN; auto;
  try apply Float_prop.eq_0_F2R in HA;
  try repeat (destruct m0; try discriminate HA).
Qed.

Lemma Bfma_mult_0R a f s :
is_finite (BFMA a f s) = true ->
FT2R a = 0 -> 
FT2R (BFMA a f s) = FT2R s.
Proof. 
  rewrite is_finite_Binary/BMULT/BINOP //= 
    -!B2R_float_of_ftype /pos_zero/neg_zero/Binary.Bmult
    !float_of_ftype_of_float.
  destruct (float_of_ftype f); 
  destruct (float_of_ftype a);
  destruct (float_of_ftype s);  
  destruct s0; destruct s1; destruct s2 => //=; 
  move => FIN HA; try discriminate FIN; auto;
  try apply Float_prop.eq_0_F2R in HA;
  try repeat (destruct m0; try discriminate HA).
Qed.

Fact neg_zero_is_finite:
is_finite (ftype_of_float neg_zero) = true.
Proof. 
  rewrite /neg_zero is_finite_Binary 
  float_of_ftype_of_float //=.
Qed.

Fact FT2R_neg_zero :
  FT2R (ftype_of_float neg_zero) = 0.
Proof.
rewrite -B2R_float_of_ftype 
  float_of_ftype_of_float //=.
Qed.

Fact FT2R_pos_zero :
  FT2R (ftype_of_float pos_zero) = 0.
Proof.
rewrite -B2R_float_of_ftype 
  float_of_ftype_of_float //=.
Qed.

Fact FT2R_Zconst_0 :
  FT2R (Zconst t 0) = 0.
Proof.
rewrite -B2R_float_of_ftype 
  float_of_ftype_of_float //=.
Qed.


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

Lemma fma_accurate  : 
   forall x (FINx: is_finite x = true) 
          y (FINy: is_finite y = true) 
          z (FINz: is_finite z = true)
          (FIN: fma_no_overflow (FT2R x) (FT2R y) (FT2R z)), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= D /\
   Rabs epsilon <= E /\ 
   (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1+delta) + epsilon)%R.
Proof.
move => x FINx y FINy z FINz FIN; 
move : FINx FINy FINz.
rewrite !is_finite_Binary //= 
    -!B2R_float_of_ftype 
    !float_of_ftype_of_float.
move => FINx FINy FINz.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  
                (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t)
                      BinarySingleNaN.mode_NE 
                (float_of_ftype x) 
                (float_of_ftype y)
                (float_of_ftype z) FINx FINy FINz).
cbv zeta in H. move: H; rewrite !B2R_float_of_ftype; move => H.
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

Lemma is_finite_fma_no_overflow_aux : 
  forall x y z
  (HFINb : is_finite (BFMA x y z) = true),
  Binary.is_finite _ _  (Binary.Bfma (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE
      (float_of_ftype x) (float_of_ftype y) (float_of_ftype z)) = true. 
Proof.
intros. 
rewrite is_finite_Binary in HFINb.
unfold BFMA in HFINb.
set (F:=
  (Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t) 
  (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE
     (float_of_ftype x) (float_of_ftype y) (float_of_ftype z))) in *.
destruct F; simpl; auto;
rewrite float_of_ftype_of_float in HFINb;
simpl in HFINb; auto.
Qed.

Lemma is_finite_fma_no_overflow : 
  forall x y z
  (HFINb : is_finite (BFMA x y z) = true),
  fma_no_overflow (FT2R x) (FT2R y) (FT2R z).
Proof.
intros.
red. set (ov:= bpow Zaux.radix2 (femax t)).
pose proof Rle_or_lt ov (Rabs (rounded t (FT2R x * FT2R y + FT2R z)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
pose proof is_finite_fma_no_overflow_aux x y z HFINb.
assert (HFIN: is_finite x = true /\
  is_finite y = true /\ 
  is_finite z = true).
{ rewrite !is_finite_Binary. 
destruct (float_of_ftype x);
destruct (float_of_ftype y);
destruct (float_of_ftype z);
simpl in *; try discriminate; repeat split; auto.
all: destruct s; destruct s0; destruct s1; simpl in *; try discriminate; auto. }
destruct HFIN as (A & B & C). 
unfold rounded, ov in H. 
set (xb := float_of_ftype x).
set (yb := float_of_ftype y).
set (zb := float_of_ftype z).
rewrite !is_finite_Binary in A B C.
pose proof (Binary.Bfma_correct (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t) 
        BinarySingleNaN.mode_NE xb yb zb A B C) as H1.
simpl in H1, H.
rewrite <- !B2R_float_of_ftype in H.
fold xb yb zb in H, H0.
rewrite H in H1; clear H.
destruct 
(Binary.Bfma _ _ _ _ _ _ xb yb zb);
 try discriminate.
Qed.

Lemma BFMA_finite_e :
 forall (a f u : ftype t)
 (Hfin : is_finite (BFMA a f u) = true),
 is_finite a = true  /\ 
 is_finite f = true /\ 
 is_finite u = true.
Proof.
intros.
pose proof is_finite_fma_no_overflow_aux a f u Hfin.
rewrite !is_finite_Binary; repeat split;
destruct (float_of_ftype a);
destruct (float_of_ftype f);
destruct (float_of_ftype u); 
destruct s; destruct s0; 
destruct s1; try discriminate; auto.
Qed.

Lemma fma_accurate'  : 
   forall  (x y z : ftype t)
          (FIN:  is_finite  (BFMA x y z) = true), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= @default_rel t /\
   Rabs epsilon <= @default_abs t /\ 
   (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1+delta) + epsilon)%R.
Proof.
intros.
pose proof (BFMA_finite_e _ _ _ FIN) as H;  
  destruct H as (A & B & C).
apply fma_accurate => //. 
pose proof is_finite_fma_no_overflow_aux x y z FIN.
apply is_finite_fma_no_overflow; auto.
Qed.

Lemma BMULT_accurate : 
  forall (x y : ftype t) (FIN: Bmult_no_overflow (FT2R x) (FT2R y)), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= @default_rel t /\
   Rabs epsilon <= @default_abs t /\ 
   (FT2R (BMULT x y) = (FT2R x * FT2R y) * (1+delta) + epsilon)%R.
Proof.
intros.
set (xb := float_of_ftype x).
set (yb := float_of_ftype y).
pose proof (Binary.Bmult_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
                (mult_nan t) BinarySingleNaN.mode_NE xb yb).
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) 
              (Binary.B2R _ _ xb * Binary.B2R _ _ yb)))
        (Raux.bpow Zaux.radix2 (femax t))). 
destruct H0.
{ destruct H as [? _].
unfold BMULT, BINOP. fold xb yb.
rewrite FT2R_ftype_of_float H.
rewrite <- B2R_float_of_ftype;
  fold xb yb.
unfold xb, yb.
rewrite !B2R_float_of_ftype.
apply generic_round_property. } 
red in FIN. unfold rounded in FIN.
unfold xb, yb in H0.
rewrite !B2R_float_of_ftype in H0.
lra.
Qed.

Lemma is_finite_BMULT_no_overflow :
 forall (x y : ftype t) 
  (HFINb : is_finite (BMULT x y) = true),
  Bmult_no_overflow (FT2R x) (FT2R y).
Proof.
intros.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) 
  (Rabs (rounded t (FT2R x * FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H; red.
unfold rounded in H.
set (xb := float_of_ftype x).
set (yb := float_of_ftype y).
pose proof (Binary.Bmult_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan t) BinarySingleNaN.mode_NE xb yb) as
  H0.
rewrite <- !B2R_float_of_ftype in H.
rewrite <- !B2R_float_of_ftype.
fold xb yb in H; rewrite H in H0. 
fold xb yb. unfold BMULT, BINOP in HFINb.
fold xb yb in HFINb. 
  rewrite is_finite_Binary float_of_ftype_of_float in HFINb.
destruct ((Binary.Bmult _ _ _ _ _ _ xb yb));
simpl;  try discriminate. 
Qed.

Lemma BMULT_accurate' : 
  forall
  (x y : ftype t) 
  (FIN: is_finite (BMULT  x y) = true), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= @default_rel t /\
   Rabs epsilon <= @default_abs t /\ 
   (FT2R (BMULT x y) = (FT2R x * FT2R y) * (1+delta) + epsilon)%R.
Proof.
intros. 
pose proof BMULT_accurate x y (is_finite_BMULT_no_overflow x y FIN); auto.
Qed.

Lemma BMULT_finite_e :
 forall (a b : ftype t)
 (Hfin : is_finite (BMULT  a b) = true),
 is_finite a = true  /\ 
 is_finite b = true.
Proof.
unfold BMULT, BINOP; intros.
rewrite is_finite_Binary float_of_ftype_of_float in Hfin.
rewrite !is_finite_Binary.
destruct (float_of_ftype a), (float_of_ftype b); 
  inversion Hfin; clear Hfin; subst; auto.
Qed.

Lemma BPLUS_finite_e :
 forall (a b : ftype t)
 (Hfin : is_finite (BPLUS  a b) = true),
 is_finite a = true  /\ 
 is_finite b = true.
Proof.
unfold BPLUS, BINOP; intros.
rewrite is_finite_Binary float_of_ftype_of_float in Hfin.
rewrite !is_finite_Binary.
destruct (float_of_ftype a), (float_of_ftype b); 
  inversion Hfin; clear Hfin; subst; simpl; auto.
destruct s,s0; discriminate; auto.
Qed.

Lemma BMINUS_finite_sub :
 forall (a b : ftype t)
 (Hfin : is_finite (BMINUS a b) = true),
 is_finite a = true  /\ 
 is_finite b = true.
Proof.
unfold BMINUS, BINOP; intros.
rewrite is_finite_Binary float_of_ftype_of_float in Hfin.
rewrite !is_finite_Binary.
destruct (float_of_ftype a), (float_of_ftype b); 
  inversion Hfin; clear Hfin; subst; simpl; auto.
destruct s,s0; discriminate; auto.
Qed.


Definition Bplus_no_overflow (x y: R) : Prop :=
  (Rabs ( Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE)  (x + y )) < Raux.bpow Zaux.radix2 (femax t))%R.


Lemma BPLUS_B2R_zero (a : ftype t):
  is_finite a = true ->
  FT2R (BPLUS a (Zconst t 0)) = FT2R a.
Proof.
unfold BPLUS, BINOP, Zconst; 
rewrite is_finite_Binary FT2R_ftype_of_float
  -B2R_float_of_ftype float_of_ftype_of_float; intros.
destruct (float_of_ftype a);
unfold neg_zero; simpl; try discriminate; auto.
destruct s; simpl; auto.
Qed.

Lemma BPLUS_accurate :
 forall      (x : ftype t) (FINx: is_finite x = true) 
             (y : ftype t) (FINy: is_finite y = true) 
          (FIN: Bplus_no_overflow (FT2R x) (FT2R y)), 
  exists delta, 
   Rabs delta <= @default_rel t /\
   (FT2R (BPLUS x y ) = (FT2R x + FT2R y) * (1+delta))%R.
Proof.
intros.
rewrite !is_finite_Binary in FINx FINy.
set (xb := float_of_ftype x).
set (yb := float_of_ftype y).
pose proof (Binary.Bplus_correct  (fprec t) (femax t) (fprec_gt_0 t) 
                    (fprec_lt_femax t) (plus_nan t)
                      BinarySingleNaN.mode_NE xb yb FINx FINy).
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) 
                  (Binary.B2R _ _ xb + Binary.B2R _ _ yb)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
-
destruct H as [? _].
unfold BPLUS, BINOP.
fold xb yb.
rewrite FT2R_ftype_of_float H.
assert (A: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R x) ).
rewrite <- B2R_float_of_ftype.
apply Binary.generic_format_B2R.
assert (B: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R y) ).
rewrite <- B2R_float_of_ftype.
apply Binary.generic_format_B2R.
pose proof Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R x) (FT2R y) A B.
unfold Relative.u_ro in H1. fold (@default_rel t) in H1.
destruct H1 as (d & Hd & Hd').
assert (  Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
    (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
    (FT2R x + FT2R y)  =  Generic_fmt.round Zaux.radix2
        (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
        (Generic_fmt.Znearest (fun x0 : Z => negb (Z.even x0)))
        (FT2R x + FT2R y)) by auto.
rewrite <- H1 in Hd'. clear H1. 
rewrite <- !B2R_float_of_ftype in Hd'.
fold xb yb in Hd'.
rewrite Hd'; clear Hd'.
exists d; split; auto.
eapply Rle_trans; [apply Hd |].
apply Rdiv_le_left.
apply Fourier_util.Rlt_zero_pos_plus1. 
apply default_rel_gt_0.
eapply Rle_trans with (@default_rel t * 1); try nra.
f_equal. unfold xb, yb; rewrite !B2R_float_of_ftype; auto.
red in FIN.
rewrite <-!B2R_float_of_ftype in FIN; auto.
fold xb yb in FIN; lra.
Qed.

Lemma is_finite_sum_no_overflow :
  forall x y
  (HFINb : is_finite (BPLUS x y) = true),
  Bplus_no_overflow (FT2R x) (FT2R y).
Proof.
intros x y.
rewrite is_finite_Binary; intros.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) (Rabs (rounded t (FT2R x + FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
assert (HFIN: is_finite x = true /\ is_finite y = true).
{ unfold BPLUS, BINOP in HFINb. rewrite !is_finite_Binary. 
    rewrite float_of_ftype_of_float in HFINb;
    destruct (float_of_ftype x), (float_of_ftype y); 
    simpl in *; split; try discriminate; auto; 
    destruct s; destruct s0; simpl in *; try discriminate; auto. }
unfold rounded in H.
rewrite !is_finite_Binary in HFIN.
destruct HFIN as (A & B). 
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE 
  (float_of_ftype x) (float_of_ftype y) A B) as
  H0.
rewrite <- !B2R_float_of_ftype in H.
rewrite H in H0;
destruct H0 as ( C & _).
unfold BPLUS, BINOP in HFINb.
    rewrite float_of_ftype_of_float in HFINb.
destruct ((Binary.Bplus (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
             (plus_nan t) BinarySingleNaN.mode_NE 
  (float_of_ftype x) (float_of_ftype y)));
simpl; try discriminate.
Qed.

Lemma no_overflow_sum_is_finite :
  forall x y
  (H1  : is_finite x = true)
  (H2  : is_finite y = true) 
  (Hov : Bplus_no_overflow (FT2R x) (FT2R y)),
  is_finite (BPLUS x y) = true.
Proof.
intros x y.
rewrite !is_finite_Binary; 
  unfold Bplus_no_overflow, BPLUS, BINOP; intros.
rewrite float_of_ftype_of_float.
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE 
  (float_of_ftype x) (float_of_ftype y) H1 H2) as
  H0.
remember (Rlt_bool _ _ ) as HB; destruct HB.  
destruct H0 as (_ & HP  &_); auto.
exfalso.
unfold Rlt_bool in HeqHB.
remember (Rcompare _ _) as HR; destruct HR; try discriminate.
symmetry in HeqHR. 
apply Rcompare_Eq_inv in HeqHR.
rewrite !B2R_float_of_ftype in HeqHR; nra.
symmetry in HeqHR. 
apply Rcompare_Gt_inv in HeqHR.
rewrite !B2R_float_of_ftype in HeqHR; nra.
Qed.

Lemma BPLUS_accurate' :
  forall (x y : ftype t) 
  (FIN: is_finite (BPLUS  x y) = true), 
  exists delta, 
   Rabs delta <= @default_rel t /\
   (FT2R (BPLUS x y ) = (FT2R x + FT2R y) * (1+delta))%R.
Proof.
intros.
eapply BPLUS_accurate.
1,2: rewrite is_finite_Binary; 
rewrite is_finite_Binary in FIN;
unfold BPLUS, BINOP in FIN;
rewrite float_of_ftype_of_float in FIN;
destruct (float_of_ftype x); destruct (float_of_ftype y); 
        simpl; try discriminate; auto; 
  destruct s; destruct s0; simpl; try discriminate; auto.
apply is_finite_sum_no_overflow; auto.
Qed.

Definition Bminus_no_overflow (x y: R) : Prop :=
  (Rabs ( Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE)  (x - y )) < Raux.bpow Zaux.radix2 (femax t))%R.


Lemma is_finite_minus_no_overflow :
  forall x y
  (HFINb : is_finite (BMINUS x y) = true),
  Bminus_no_overflow (FT2R x) (FT2R y).
Proof.
intros.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) (Rabs (rounded t (FT2R x - FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
assert (HFIN: is_finite x = true /\is_finite y = true).
rewrite !is_finite_Binary; 
rewrite is_finite_Binary in HFINb.
{ unfold BMINUS, BINOP in HFINb. 
rewrite float_of_ftype_of_float in HFINb;
    destruct (float_of_ftype x); destruct (float_of_ftype y); 
          simpl in *; split; try discriminate; auto;
    destruct s; destruct s0; simpl in *; try discriminate; auto. }
rewrite !is_finite_Binary in HFIN;
rewrite !is_finite_Binary in HFINb;
destruct HFIN as (A & B).
unfold rounded in H.
pose proof (Binary.Bminus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE 
    (float_of_ftype x) (float_of_ftype y) A B) as
  H0.
rewrite <- !B2R_float_of_ftype in H.
rewrite H in H0;
destruct H0 as ( C & _).
unfold BMINUS, BINOP in HFINb.
rewrite float_of_ftype_of_float in HFINb.
destruct ((Binary.Bminus (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
             (plus_nan t) BinarySingleNaN.mode_NE 
              (float_of_ftype x) (float_of_ftype y)));
simpl; try discriminate.
Qed.

Lemma no_overflow_minus_is_finite :
  forall x y
  (H1  : is_finite x = true)
  (H2  : is_finite y = true) 
  (Hov : Bminus_no_overflow (FT2R x) (FT2R y)),
  is_finite (BMINUS x y) = true.
Proof.
intros x y.
rewrite !is_finite_Binary; 
  unfold Bminus_no_overflow, BMINUS, BINOP; intros.
rewrite float_of_ftype_of_float.
pose proof (Binary.Bminus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE 
  (float_of_ftype x) (float_of_ftype y) H1 H2) as
  H0.
remember (Rlt_bool _ _ ) as HB; destruct HB.  
destruct H0 as (_ & HP  &_); auto.
exfalso.
unfold Rlt_bool in HeqHB.
remember (Rcompare _ _) as HR; destruct HR; try discriminate.
symmetry in HeqHR. 
apply Rcompare_Eq_inv in HeqHR.
rewrite !B2R_float_of_ftype in HeqHR; nra.
symmetry in HeqHR. 
apply Rcompare_Gt_inv in HeqHR.
rewrite !B2R_float_of_ftype in HeqHR; nra.
Qed.

Lemma BMINUS_accurate :
 forall      (x : ftype t) (FINx: is_finite x = true) 
             (y : ftype t) (FINy: is_finite y = true) 
          (FIN: Bminus_no_overflow (FT2R x) (FT2R y)), 
  exists delta, 
   Rabs delta <= @default_rel t /\
   (FT2R (BMINUS x y ) = (FT2R x - FT2R y) * (1+delta))%R.
Proof.
intros.
rewrite !is_finite_Binary in FINx FINy.
set (xb := float_of_ftype x).
set (yb := float_of_ftype y).
pose proof (Binary.Bminus_correct  (fprec t) (femax t) (fprec_gt_0 t) 
                    (fprec_lt_femax t) (plus_nan t)
                      BinarySingleNaN.mode_NE xb yb FINx FINy).
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) 
                  (Binary.B2R _ _ xb - Binary.B2R _ _ yb)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
-
destruct H as [? _].
unfold BMINUS, BINOP.
fold xb yb.
rewrite FT2R_ftype_of_float H.
assert (A: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R x) ).
rewrite <- B2R_float_of_ftype.
apply Binary.generic_format_B2R.
assert (B: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (-FT2R y) ).
rewrite <- B2R_float_of_ftype.
apply Generic_fmt.generic_format_opp.
apply Binary.generic_format_B2R.
pose proof Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R x) (-FT2R y) A B.
unfold Relative.u_ro in H1. fold (@default_rel t) in H1.
destruct H1 as (d & Hd & Hd').
assert (  Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
    (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
    (FT2R x - FT2R y)  =  Generic_fmt.round Zaux.radix2
        (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
        (Generic_fmt.Znearest (fun x0 : Z => negb (Z.even x0)))
        (FT2R x - FT2R y)) by auto.
replace (_ +- _) with ( FT2R x - FT2R y) in Hd' by nra.
rewrite <- H1 in Hd'. clear H1. 
rewrite <- !B2R_float_of_ftype in Hd'.
fold xb yb in Hd'.
rewrite Hd'; clear Hd'.
exists d; split; auto.
eapply Rle_trans; [apply Hd |].
apply Rdiv_le_left.
apply Fourier_util.Rlt_zero_pos_plus1. 
apply default_rel_gt_0.
eapply Rle_trans with (@default_rel t * 1); try nra.
f_equal. unfold xb, yb; rewrite !B2R_float_of_ftype; auto.
red in FIN.
rewrite <-!B2R_float_of_ftype in FIN; auto.
fold xb yb in FIN; lra.
Qed.

Lemma BMINUS_accurate' :
  forall (x y : ftype t) 
  (FIN: is_finite (BMINUS  x y) = true), 
  exists delta, 
   Rabs delta <= @default_rel t /\
   (FT2R (BMINUS x y ) = (FT2R x - FT2R y) * (1+delta))%R.
Proof.
intros.
eapply BMINUS_accurate.
1,2: rewrite is_finite_Binary; 
rewrite is_finite_Binary in FIN;
unfold BMINUS, BINOP in FIN;
rewrite float_of_ftype_of_float in FIN;
destruct (float_of_ftype x); destruct (float_of_ftype y); 
        simpl; try discriminate; auto; 
  destruct s; destruct s0; simpl; try discriminate; auto.
apply is_finite_minus_no_overflow; auto.
Qed.


End GenFloat.