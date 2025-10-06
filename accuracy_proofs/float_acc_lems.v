(* This file contains lemmas regarding the accuracy of floating point 
  operations such as BPLUS, BFMA, and BMULT. *)

(*Require Import vcfloat.VCFloat.*)
From LAProof.accuracy_proofs Require Import preamble common.
Set Warnings "-notation-overriden, -parsing".
(*Require Import mathcomp.ssreflect.ssreflect.*)

Section GenFloat.
Context {NAN: FPCore.Nans} {t : type} .
 
Lemma Bmult_0R (a f: ftype t) :
Binary.is_finite (BMULT a f) = true ->
FT2R a = 0 -> 
(BMULT a f) = neg_zero
   \/ (BMULT a f) = pos_zero.
Proof.
  rewrite (*is_finite_Binary*) /BMULT/BINOP //= 
    (*-!B2R_float_of_ftype*) /pos_zero/neg_zero/Binary.Bmult
    (*!float_of_ftype_of_float*).
  destruct f,a,s,s0 => //=; 
  move => FIN HA; try discriminate FIN; auto;
  try apply Float_prop.eq_0_F2R in HA;
  try repeat (destruct m0; try discriminate HA).
Qed.

Lemma Bplus_0R (a f: ftype t) :
Binary.is_finite (BPLUS a f) = true ->
FT2R f = 0 -> 
FT2R (BPLUS a f) = FT2R a.
Proof.
  rewrite /BMULT/BINOP //= 
    /pos_zero/neg_zero/Binary.Bmult.
  destruct f,a,s,s0 => //=; 
  move => FIN HA; try discriminate FIN; auto;
  try apply Float_prop.eq_0_F2R in HA;
  try repeat (destruct m0; try discriminate HA).
Qed.

Lemma Bfma_mult_0R (a f s : ftype t):
Binary.is_finite (BFMA a f s) = true ->
FT2R a = 0 -> 
FT2R (BFMA a f s) = FT2R s.
Proof. 
  rewrite /BMULT/BINOP //= .
  destruct f; 
  destruct a;
  destruct s;  
  destruct s0; destruct s1;  destruct s => //=; 
  move => FIN HA; try discriminate FIN; auto;
  try apply Float_prop.eq_0_F2R in HA;
  try repeat (destruct m0; try discriminate HA).
Qed.

Fact neg_zero_is_finite:
Binary.is_finite  (@neg_zero t) = true.
Proof. reflexivity. Qed. 

Fact FT2R_neg_zero :
  FT2R (@neg_zero t) = 0.
Proof. reflexivity. Qed.

Fact FT2R_pos_zero :
  FT2R (@pos_zero t) = 0.
Proof. reflexivity. Qed.

Fact FT2R_Zconst_0 :
  FT2R (Zconst t 0) = 0.
Proof. reflexivity. Qed.

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
               x = (x * (1+delta)+epsilon)%Re.
Proof.
intros.
destruct (Relative.error_N_FLT Zaux.radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t) 
             (fprec_gt_0 t) (fun x0 : Z => negb (Z.even x0)) x)
  as [delta [epsilon [? [? [? ?]]]]].
exists delta, epsilon.
repeat split; auto.
Qed.

Lemma fma_accurate  : 
   forall (x: ftype t) (FINx: Binary.is_finite x = true) 
          (y: ftype t) (FINy: Binary.is_finite y = true) 
          (z: ftype t) (FINz: Binary.is_finite z = true)
          (FIN: fma_no_overflow (FT2R x) (FT2R y) (FT2R z)), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= D /\
   Rabs epsilon <= E /\ 
   (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1+delta) + epsilon)%Re.
Proof.
move => x FINx y FINy z FINz FIN.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  
                (fprec_gt_0 t) (fprec_lt_femax t) (FPCore.fma_nan (fprec t) (femax t) (fprec_gt_one t))
                      BinarySingleNaN.mode_NE x y z FINx FINy FINz).
fold (@FT2R t) in H.
fold (@BFMA NAN t) in H.
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
rewrite H.
apply generic_round_property.
-
red in FIN. unfold rounded in FIN.
Lra.lra.
Qed.

(*
Lemma is_finite_fma_no_overflow_aux : 
  forall x y z
  (HFINb : Binary.is_finite (BFMA x y z) = true),
  Binary.is_finite  (Binary.Bfma (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE
      (float_of_ftype x) (float_of_ftype y) (float_of_ftype z)) = true. 
Proof.
intros. 
rewrite is_finite_Binary in HFINb.
unfold BFMA in HFINb.
set (F:=
  (Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t) 
  (fprec_lt_femax t) (fma_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE
     (float_of_ftype x) (float_of_ftype y) (float_of_ftype z))) in *.
destruct F; simpl; auto;
rewrite float_of_ftype_of_float in HFINb;
simpl in HFINb; auto.
Qed.
*)

Lemma is_finite_fma_no_overflow : 
  forall (x y z: ftype t)
  (HFINb : Binary.is_finite (BFMA x y z) = true),
  fma_no_overflow (FT2R x) (FT2R y) (FT2R z).
Proof.
intros.
red. set (ov:= bpow Zaux.radix2 (femax t)).
pose proof Rle_or_lt ov (Rabs (rounded t (FT2R x * FT2R y + FT2R z)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
(*pose proof is_finite_fma_no_overflow_aux x y z HFINb.*)
assert (HFIN: Binary.is_finite x = true /\
  Binary.is_finite y = true /\ 
  Binary.is_finite z = true)
 by (destruct x,y,z; destruct s; destruct s0; destruct s1;
       simpl in *; try discriminate; repeat split; auto).
destruct HFIN as (A & B & C). 
unfold rounded, ov in H. 
pose proof (Binary.Bfma_correct (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (FPCore.fma_nan (fprec t) (femax t) (fprec_gt_one t)) 
        BinarySingleNaN.mode_NE x y z A B C) as H1.
simpl in H1, H.
rewrite H in H1; clear H.
fold (BFMA x y z) in *.
destruct (BFMA x y z); discriminate.
Qed.

Lemma BFMA_finite_e :
 forall (a f u : ftype t)
 (Hfin : Binary.is_finite (BFMA a f u) = true),
 Binary.is_finite  a = true  /\ 
 Binary.is_finite  f = true /\ 
 Binary.is_finite  u = true.
Proof.
intros.
repeat split;
destruct a,f,u; destruct s; destruct s0; destruct s1; try discriminate; auto.
Qed.

Lemma fma_accurate'  : 
   forall  (x y z : ftype t)
          (FIN:  Binary.is_finite (BFMA x y z) = true), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= @default_rel t /\
   Rabs epsilon <= @default_abs t /\ 
   (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1+delta) + epsilon)%Re.
Proof.
intros.
pose proof (BFMA_finite_e _ _ _ FIN) as H;  
  destruct H as (A & B & C).
apply fma_accurate => //. 
apply is_finite_fma_no_overflow; auto.
Qed.

Lemma BMULT_accurate : 
  forall (x y : ftype t) (FIN: Bmult_no_overflow (FT2R x) (FT2R y)), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= @default_rel t /\
   Rabs epsilon <= @default_abs t /\ 
   (FT2R (BMULT x y) = (FT2R x * FT2R y) * (1+delta) + epsilon)%Re.
Proof.
intros.
pose proof (Binary.Bmult_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
                (FPCore.mult_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE x y).
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) 
              (Binary.B2R _ _ x * Binary.B2R _ _ y)))
        (Raux.bpow Zaux.radix2 (femax t))). 
fold (@FT2R t) in H,H0.
destruct H0.
- destruct H as [? _].
  unfold BMULT, BINOP.
  rewrite {}H.
  apply generic_round_property.
-
red in FIN. unfold rounded in FIN.
lra.
Qed.

Lemma is_finite_BMULT_no_overflow :
 forall (x y : ftype t) 
  (HFINb : Binary.is_finite (BMULT x y) = true),
  Bmult_no_overflow (FT2R x) (FT2R y).
Proof.
intros.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) 
  (Rabs (rounded t (FT2R x * FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H; red.
unfold rounded in H.
pose proof (Binary.Bmult_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (FPCore.mult_nan (fprec t) (femax t) (fprec_gt_one t))   BinarySingleNaN.mode_NE x y) as
  H0.
rewrite {}H in H0. 
unfold BMULT, BINOP in HFINb.
destruct ((Binary.Bmult _ _ _ _ _ _ x y));
simpl;  try discriminate. 
Qed.

Lemma BMULT_accurate' : 
  forall
  (x y : ftype t) 
  (FIN: Binary.is_finite (BMULT  x y) = true), 
  exists delta, exists epsilon,
   delta * epsilon = 0 /\
   Rabs delta <= @default_rel t /\
   Rabs epsilon <= @default_abs t /\ 
   (FT2R (BMULT x y) = (FT2R x * FT2R y) * (1+delta) + epsilon)%Re.
Proof.
intros. 
pose proof BMULT_accurate x y (is_finite_BMULT_no_overflow x y FIN); auto.
Qed.

Lemma BMULT_finite_e :
 forall (a b : ftype t)
 (Hfin : Binary.is_finite (BMULT  a b) = true),
 Binary.is_finite a = true  /\ 
 Binary.is_finite b = true.
Proof.
unfold BMULT, BINOP; intros.
destruct a,b; inversion Hfin; clear Hfin; subst; auto.
Qed.

Lemma BPLUS_finite_e :
 forall (a b : ftype t)
 (Hfin : Binary.is_finite (BPLUS  a b) = true),
 Binary.is_finite a = true  /\ 
 Binary.is_finite b = true.
Proof.
unfold BPLUS, BINOP; intros.
destruct a,b; inversion Hfin; clear Hfin; subst; simpl; auto.
destruct s,s0; discriminate; auto.
Qed.

Lemma BMINUS_finite_sub :
 forall (a b : ftype t)
 (Hfin : Binary.is_finite (BMINUS a b) = true),
 Binary.is_finite a = true  /\ 
 Binary.is_finite b = true.
Proof.
unfold BMINUS, BINOP; intros.
destruct a,b; inversion Hfin; clear Hfin; subst; simpl; auto.
destruct s,s0; discriminate; auto.
Qed.


Definition Bplus_no_overflow (x y: R) : Prop :=
  (Rabs ( Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE)  (x + y )) < Raux.bpow Zaux.radix2 (femax t))%R.


Lemma BPLUS_B2R_zero (a : ftype t):
  Binary.is_finite a ->
  FT2R (BPLUS a (Zconst t 0)) = FT2R a.
Proof.
unfold BPLUS, BINOP, Zconst; intros;
destruct a;
unfold neg_zero; simpl; try discriminate; auto.
destruct s; simpl; auto.
Qed.

Lemma BPLUS_accurate :
 forall      (x : ftype t) (FINx: Binary.is_finite x = true) 
             (y : ftype t) (FINy: Binary.is_finite y = true) 
          (FIN: Bplus_no_overflow (FT2R x) (FT2R y)), 
  exists delta, 
   Rabs delta <= @default_rel t /\
   (FT2R (BPLUS x y ) = (FT2R x + FT2R y) * (1+delta))%Re.
Proof.
intros.
pose proof (Binary.Bplus_correct  (fprec t) (femax t) (fprec_gt_0 t) 
                    (fprec_lt_femax t) (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t))
                      BinarySingleNaN.mode_NE x y FINx FINy).
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) 
                  (Binary.B2R _ _ x + Binary.B2R _ _ y)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
-
destruct H as [? _].
unfold BPLUS, BINOP.
fold (@FT2R t) in *.
rewrite {}H.
assert (A: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R x) )
  by apply Binary.generic_format_B2R.
assert (B: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R y) )
 by apply Binary.generic_format_B2R.
assert (H1 := Plus_error.FLT_plus_error_N_ex   Zaux.radix2 (SpecFloat.emin (fprec t) (femax t))
 (fprec t) (fun x0 : Z => negb (Z.even x0)) (FT2R x) (FT2R y) A B).
unfold Relative.u_ro in H1. fold (@default_rel t) in H1.
destruct H1 as (d & Hd & Hd').
assert (H1:  Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
    (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
    (FT2R x + FT2R y)  =  Generic_fmt.round Zaux.radix2
        (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
        (Generic_fmt.Znearest (fun x0 : Z => negb (Z.even x0)))
        (FT2R x + FT2R y)) by auto.
rewrite <- H1 in Hd'. clear H1. 
rewrite {}Hd'.
exists d; split; auto.
eapply Rle_trans; [apply Hd |].
apply Rdiv_le_left.
apply Fourier_util.Rlt_zero_pos_plus1. 
apply default_rel_gt_0.
eapply Rle_trans with (@default_rel t * 1); try nra.
-
red in FIN.
fold (@FT2R t) in *.
lra.
Qed.

Lemma is_finite_sum_no_overflow :
  forall (x y: ftype t)
  (HFINb : Binary.is_finite (BPLUS x y) = true),
  Bplus_no_overflow (FT2R x) (FT2R y).
Proof.
intros.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) (Rabs (rounded t (FT2R x + FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
assert (HFIN: Binary.is_finite x = true /\ Binary.is_finite y = true).
{ unfold BPLUS, BINOP in HFINb.
    destruct x,y;
    simpl in *; split; try discriminate; auto; 
    destruct s; destruct s0; simpl in *; try discriminate; auto. }
unfold rounded in H.
destruct HFIN as (A & B). 
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
      x y A B) as
  H0.
rewrite H in H0;
destruct H0 as ( C & _).
unfold BPLUS, BINOP in HFINb.
destruct ((Binary.Bplus (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
             (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE x y));
simpl; try discriminate.
Qed.

Lemma no_overflow_sum_is_finite :
  forall (x y: ftype t)
  (H1  : Binary.is_finite x = true)
  (H2  : Binary.is_finite y = true) 
  (Hov : Bplus_no_overflow (FT2R x) (FT2R y)),
  Binary.is_finite (BPLUS x y) = true.
Proof.
unfold Bplus_no_overflow, BPLUS, BINOP; intros.
pose proof (Binary.Bplus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
  x y H1 H2) as
  H0.
remember (Rlt_bool _ _ ) as HB; destruct HB.  
destruct H0 as (_ & HP  &_); auto.
exfalso.
fold (@FT2R t) in *.
unfold Rlt_bool in HeqHB.
remember (Rcompare _ _) as HR; destruct HR; try discriminate.
symmetry in HeqHR. 
apply Rcompare_Eq_inv in HeqHR.
nra.
symmetry in HeqHR. 
apply Rcompare_Gt_inv in HeqHR.
nra.
Qed.

Lemma BPLUS_accurate' :
  forall (x y : ftype t) 
  (FIN: Binary.is_finite (BPLUS  x y) = true), 
  exists delta, 
   Rabs delta <= @default_rel t /\
   (FT2R (BPLUS x y ) = (FT2R x + FT2R y) * (1+delta))%Re.
Proof.
unfold BPLUS, BINOP.
intros.
eapply BPLUS_accurate.
1,2: destruct x,y; simpl; try discriminate; auto; 
  destruct s; destruct s0; simpl; try discriminate; auto.
apply is_finite_sum_no_overflow; auto.
Qed.

Definition Bminus_no_overflow (x y: R) : Prop :=
  (Rabs ( Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE)  (x - y )) < Raux.bpow Zaux.radix2 (femax t))%R.


Lemma is_finite_minus_no_overflow :
  forall (x y: ftype t)
  (HFINb : Binary.is_finite (BMINUS x y) = true),
  Bminus_no_overflow (FT2R x) (FT2R y).
Proof.
intros.
pose proof Rle_or_lt (bpow Zaux.radix2 (femax t)) (Rabs (rounded t (FT2R x - FT2R y)))  as Hor;
  destruct Hor; auto.
apply Rlt_bool_false in H.
assert (HFIN: Binary.is_finite x = true /\ Binary.is_finite y = true).
{ unfold BMINUS, BINOP in HFINb. 
    destruct x,y;
          simpl in *; split; try discriminate; auto;
    destruct s; destruct s0; simpl in *; try discriminate; auto. }
destruct HFIN as (A & B).
unfold rounded in H.
pose proof (Binary.Bminus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
    x y A B) as
  H0.
rewrite H in H0;
destruct H0 as ( C & _).
unfold BMINUS, BINOP in HFINb.
destruct ((Binary.Bminus (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) 
             (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
              x y));
simpl; try discriminate.
Qed.

Lemma no_overflow_minus_is_finite :
  forall (x y: ftype t)
  (H1  : Binary.is_finite x = true)
  (H2  : Binary.is_finite y = true) 
  (Hov : Bminus_no_overflow (FT2R x) (FT2R y)),
  Binary.is_finite (BMINUS x y) = true.
Proof.
unfold Bminus_no_overflow, BMINUS, BINOP; intros.
pose proof (Binary.Bminus_correct  (fprec t) (femax t)  
    (fprec_gt_0 t) (fprec_lt_femax t) (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
    x y H1 H2) as
  H0.
remember (Rlt_bool _ _ ) as HB; destruct HB.  
destruct H0 as (_ & HP  &_); auto.
exfalso.
unfold Rlt_bool in HeqHB.
fold (@FT2R t) in *.
remember (Rcompare _ _) as HR; destruct HR; try discriminate.
symmetry in HeqHR. 
apply Rcompare_Eq_inv in HeqHR.
nra.
symmetry in HeqHR. 
apply Rcompare_Gt_inv in HeqHR.
nra.
Qed.

Lemma BMINUS_accurate :
 forall      (x : ftype t) (FINx: Binary.is_finite x = true) 
             (y : ftype t) (FINy: Binary.is_finite y = true) 
          (FIN: Bminus_no_overflow (FT2R x) (FT2R y)), 
  exists delta, 
   Rabs delta <= @default_rel t /\
   (FT2R (BMINUS x y ) = (FT2R x - FT2R y) * (1+delta))%Re.
Proof.
intros.
pose proof (Binary.Bminus_correct  (fprec t) (femax t) (fprec_gt_0 t) 
                    (fprec_lt_femax t) (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t))
                      BinarySingleNaN.mode_NE x y FINx FINy).
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) 
                  (Binary.B2R _ _ x - Binary.B2R _ _ y)))
        (Raux.bpow Zaux.radix2 (femax t))).
fold (@FT2R t) in *.
destruct H0.
-
destruct H as [? _].
unfold BMINUS, BINOP.
rewrite H.
assert (A: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (FT2R x) ).
apply Binary.generic_format_B2R.
assert (B: Generic_fmt.generic_format Zaux.radix2
       (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
       (-FT2R y) ).
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
rewrite {}Hd'.
exists d; split; auto.
eapply Rle_trans; [apply Hd |].
apply Rdiv_le_left.
apply Fourier_util.Rlt_zero_pos_plus1. 
apply default_rel_gt_0.
eapply Rle_trans with (@default_rel t * 1); try nra.
-
red in FIN. lra.
Qed.

Lemma BMINUS_accurate' :
  forall (x y : ftype t) 
  (FIN: Binary.is_finite (BMINUS  x y) = true), 
  exists delta, 
   Rabs delta <= @default_rel t /\
   (FT2R (BMINUS x y ) = (FT2R x - FT2R y) * (1+delta))%Re.
Proof.
intros.
eapply BMINUS_accurate.
1,2: unfold BMINUS, BINOP in FIN;
destruct x,y; simpl; try discriminate; auto; 
  destruct s; destruct s0; simpl; try discriminate; auto.
apply is_finite_minus_no_overflow; auto.
Qed.

Lemma BPLUS_correct (a b: ftype t): 
  Binary.is_finite (BPLUS a b) = true ->
  (Binary.is_finite a = true /\
  Binary.is_finite b = true) /\
  FT2R (BPLUS a b) = 
  Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
  (FT2R a + FT2R b).
Proof.
intros * FIN. 
pose proof (is_finite_sum_no_overflow a b FIN).
apply Rlt_bool_true in H.
assert (Binary.is_finite a = true /\ Binary.is_finite b = true)
 by (unfold BPLUS, BINOP in FIN; 
    destruct a,b;
       simpl in FIN; split; try discriminate; auto ;
          match goal with | H: Binary.is_finite 
                   (Binary.Bplus _ _ _ _ _ _ (Binary.B754_infinity _ _ ?s)
                      (Binary.B754_infinity _ _ ?s0)) = _ |- Binary.is_finite  _ = _ =>
            destruct s; destruct s0; try discriminate; auto end).
split; auto.
destruct H0.
 pose proof (Binary.Bplus_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
        a b H0 H1) as H3.
rewrite {}H in H3.
apply H3.
Qed.

Lemma BMULT_correct (a b: ftype t): 
  Binary.is_finite (BMULT a b) = true ->
  (Binary.is_finite a = true /\
  Binary.is_finite b = true) /\
  FT2R (BMULT a b) = 
  Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
  (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
  (FT2R a * FT2R b).
Proof.
intros * FIN. 
pose proof (is_finite_BMULT_no_overflow a b FIN).
apply Rlt_bool_true in H.
assert (Binary.is_finite a = true /\ Binary.is_finite b = true)
 by (unfold BMULT, BINOP in FIN; 
    destruct a,b;
       simpl in FIN; split; try discriminate; auto ;
          match goal with | H: Binary.is_finite 
                   (Binary.Bplus _ _ _ _ _ _ (Binary.B754_infinity _ _ ?s)
                      (Binary.B754_infinity _ _ ?s0)) = _ |- Binary.is_finite  _ = _ =>
            destruct s; destruct s0; try discriminate; auto end).
split; auto.
destruct H0.
pose proof (Binary.Bmult_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (FPCore.mult_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
        a b). 
rewrite {}H in H2.
apply H2.
Qed.


Lemma BFMA_correct (a b s: ftype t) :
  Binary.is_finite (BFMA a b s) = true ->
 (Binary.is_finite a = true /\ Binary.is_finite b = true /\ Binary.is_finite s = true) /\
  FT2R (BFMA a b s) = 
    Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
    (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
    (FT2R a * FT2R b + FT2R s).
Proof.
intros * FIN.
pose proof (is_finite_fma_no_overflow a b s FIN) as H4; apply Rlt_bool_true in H4;
  unfold common.rounded in H4.
assert (H : Binary.is_finite a = true /\ Binary.is_finite b = true /\ Binary.is_finite s = true).
    unfold BFMA, BINOP in FIN.
    destruct a,b,s; auto; destruct s0,s1,s; discriminate.
split; auto.
destruct H as [? [? ?]].
pose proof (Binary.Bfma_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (FPCore.fma_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE 
        a b s H H0 H1) as H3; cbv zeta in H3.
fold (@FT2R t) in H3.
rewrite {}H4 in H3.
fold (BFMA a b s) in H3.
apply H3.
Qed.


End GenFloat.


