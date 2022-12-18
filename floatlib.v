Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

Set Bullet Behavior "Strict Subproofs".

Definition BFMA {NAN: Nans} {t: type} : forall (x y z: ftype t), ftype t :=
    Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t)
      (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE.


Definition float_eqv {t: type} (x y : ftype t) : Prop :=
  match x, y with
    | Binary.B754_zero _ _ b1, Binary.B754_zero _ _ b2 => True
    | Binary.B754_zero _ _ _, _ => False
    | _, Binary.B754_zero _ _ _ => False
    | Binary.B754_finite _ _ b1 m1 e1 _, Binary.B754_finite _ _ b2 m2 e2 _ =>
          b1 = b2 /\  m1 = m2 /\ e1 = e2
    | Binary.B754_finite _ _ _ _ _ _, _ => False
    | _, Binary.B754_finite _ _ _ _ _ _ => False
    | _, _ => True
  end.

Lemma float_eqv_refl {t}: forall x: ftype t, float_eqv x x.
Proof.
destruct x; simpl; auto.
Qed.

#[export] Hint Resolve float_eqv_refl : core.

Lemma float_eqv_sym {t: type}: forall x y : ftype t, float_eqv x y -> float_eqv y x.
Proof.
destruct x,y; simpl; auto.
intros [? [? ?]].
subst. auto.
Qed.

Lemma float_eqv_trans {t: type}: 
  forall x y z : ftype t, float_eqv x y -> float_eqv y z -> float_eqv x z.
Proof.
destruct x,y,z; simpl; intros; auto; try contradiction.
destruct H as [? [? ?]]; destruct H0 as [? [? ?]]; subst; auto.
Qed.

Add Parametric Relation {t: type}: (ftype t) (@float_eqv t)
  reflexivity proved by float_eqv_refl
  symmetry proved by float_eqv_sym
  transitivity proved by float_eqv_trans
   as float_eqv_rel.

Definition floatlist_eqv {t: type} : list (ftype t) -> list (ftype t) -> Prop :=
 Forall2 float_eqv.

(*
Add Parametric Morphism {t: type}: 
  with float_eqv ==> floatlist_eqv ==> floatlist_eqv
  as floatlist_cons_mor.
Proof.
intros. intro. simpl. rewrite H, H0; auto.
Qed.
*)

Definition floatlistlist_eqv {t: type} : list (list (ftype t)) -> list (list (ftype t)) -> Prop :=
 Forall2 floatlist_eqv.


Definition strict_float_eqv {t: type} (x y : ftype t) : Prop :=
  match x, y with
    | Binary.B754_zero _ _ b1, Binary.B754_zero _ _ b2 => True
    | Binary.B754_finite _ _ b1 m1 e1 _, Binary.B754_finite _ _ b2 m2 e2 _ =>
          b1 = b2 /\  m1 = m2 /\ e1 = e2
    | _, _ => False
  end.

Definition finite {t} (x: ftype t) := strict_float_eqv x x.

Lemma strict_float_eqv_refl {t: type}: forall (x: ftype t),
 Binary.is_finite _ _ x = true -> strict_float_eqv x x.
Proof.
intros.
destruct x; try discriminate; hnf; auto.
Qed.

Lemma strict_float_eqv_sym {t: type}: forall x y : ftype t, 
   strict_float_eqv x y -> strict_float_eqv y x.
Proof.
destruct x,y; simpl; auto.
intros [? [? ?]].
subst. auto.
Qed.

Lemma strict_float_eqv_trans {t: type}: 
  forall x y z : ftype t, strict_float_eqv x y -> strict_float_eqv y z -> strict_float_eqv x z.
Proof.
destruct x,y,z; simpl; intros; auto; try contradiction.
destruct H as [? [? ?]]; destruct H0 as [? [? ?]]; subst; auto.
Qed.

Add Parametric Relation {t: type}: (ftype t) (@strict_float_eqv t)
  symmetry proved by strict_float_eqv_sym
  transitivity proved by strict_float_eqv_trans
   as strict_float_eqv_rel.

Add Parametric Morphism {t: type} : BFMA
 with signature (@strict_float_eqv t) ==> strict_float_eqv ==> float_eqv ==> float_eqv
  as BFMA_mor.
Proof.
intros.
destruct x,y; inv H; try apply I;
destruct x0,y0; inv  H0; try apply I;
destruct x1,y1; inv H1; try apply I;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
subst; simpl; auto;
repeat proof_irr;
try reflexivity.
unfold BFMA, Binary.Bfma, BinarySingleNaN.Bfma, Binary.BSN2B, Binary.B2BSN;
 simpl;
destruct s, s2; simpl; try reflexivity;
unfold BinarySingleNaN.Bfma_szero; simpl;
destruct s0,s1; simpl; try reflexivity.
Qed.

Definition strict_floatlist_eqv {t: type} : list (ftype t) -> list (ftype t) -> Prop :=
 Forall2 strict_float_eqv.

Definition strict_floatlistlist_eqv {t: type} : list (list (ftype t)) -> list (list (ftype t)) -> Prop :=
 Forall2 strict_floatlist_eqv.

(* Infix "==" := float_eqv (at level 70, no associativity). *)

Lemma Forall_Forall2diag {A: Type}:
   forall (P: A -> A -> Prop) al,
    Forall (fun x => P x x) al <-> Forall2 P al al.
Proof.
split; try solve [induction 1; auto].
intro.
induction al; auto.
inv H.
constructor; auto.
Qed.

#[export] Instance zerof {t} : Inhabitant (ftype t) := (Zconst t 0).

Lemma BFMA_zero1: forall {t} y s, 
  strict_float_eqv y y ->
  float_eqv (BFMA (Zconst t 0) y s) s.
Proof.
intros.
intros.
change (Zconst t 0) with 
  (Binary.B754_zero (fprec t)  (femax t) false).
unfold BFMA, BPLUS, BINOP in *.
destruct y, s; try discriminate; simpl; auto.
Qed.

Lemma BFMA_zero2: forall {t} x s, 
  strict_float_eqv x x ->
  float_eqv (BFMA x (Zconst t 0) s) s.
Proof.
intros.
intros.
change (Zconst t 0) with 
  (Binary.B754_zero (fprec t)  (femax t) false).
unfold BFMA, BPLUS, BINOP in *.
destruct x, s; try discriminate; simpl; auto.
Qed.

