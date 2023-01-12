Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import Coq.Relations.Relations Coq.Classes.Morphisms Coq.Classes.RelationPairs Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Definition BFMA {NAN: Nans} {t: type} : forall (x y z: ftype t), ftype t :=
    Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t)
      (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE.

Definition matrix t := list (list (ftype t)).
Definition vector t := list (ftype t).

Definition dotprod {NAN: Nans} {t: type} (v1 v2: list (ftype t)) : ftype t :=
  fold_left (fun s x12 => BFMA (fst x12) (snd x12) s) 
                (List.combine v1 v2)  (Zconst t 0).

Definition norm2 {NAN: Nans} {t} (v: vector t) := dotprod v v.

Definition matrix_vector_mult {NAN: Nans}{t: type} (m: matrix t) (v: vector t) : vector t :=
      map (fun row => dotprod row v) m.

Definition matrix_matrix_mult {NAN: Nans}{t: type} (m1 m2: matrix t) : matrix t :=
  map (matrix_vector_mult m1) m2.

Definition matrix_cols {t} (m: matrix t) cols :=
    Forall (fun r => Zlength r = cols) m.

Definition matrix_rows {t} (m: matrix t) : Z := Zlength m.

Definition map2 {A B C: Type} (f: A -> B -> C) al bl :=
  map (uncurry f) (List.combine al bl).

Definition opp_matrix {NAN: Nans}{t:type} (m: matrix t) : matrix t :=
  map (map (BOPP t)) m.

Definition matrix_add {NAN: Nans}{t} : matrix t -> matrix t -> matrix t :=
  map2 (map2 (BPLUS t)).

Definition vector_add {NAN: Nans}{t:type} (v1 v2 : vector t) :=
  map2 (BPLUS t) v1 v2.

Definition vector_sub {NAN: Nans}{t:type} (v1 v2 : vector t) :=
  map2 (BMINUS t) v1 v2.

Definition matrix_index {t} (m: matrix t) (i j: nat) :=
 nth j (nth i m nil) (Zconst t 0).

Definition matrix_by_index {t} (rows cols: nat) 
          (f: nat -> nat -> ftype t) : matrix t :=
     map (fun i => map (f i) (seq 0 cols)) (seq 0 rows).

Definition matrix_rows_nat {t} (m: matrix t) := length m.

Definition matrix_cols_nat {t} (m: matrix t) cols :=
    Forall (fun r => length r = cols) m.

(* see https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/RelationPairs.20rewriting.20really.20slow *)
Global Instance proper_pair1: forall A B RA1 RA2 RB1 RB2 (RA : relation A) (RB : relation B),
    Proper (RA1 ==> RA2 ==> Basics.flip Basics.impl) RA
    -> Proper (RB1 ==> RB2 ==> Basics.flip Basics.impl) RB
    -> Proper (RA1 * RB1 ==> RA2 * RB2 ==> Basics.flip Basics.impl) (RA * RB)%signature.
Proof. cbv; intuition eauto. Qed.

Global Instance proper_pair2: forall A B RA1 RA2 RB1 RB2 (RA : relation A) (RB : relation B),
    Proper (RA1 ==> RA2 ==> Basics.impl) RA
    -> Proper (RB1 ==> RB2 ==> Basics.impl) RB
    -> Proper (RA1 * RB1 ==> RA2 * RB2 ==> Basics.impl) (RA * RB)%signature.
Proof. cbv; intuition eauto. Qed.

Definition feq {t: type} : relation (ftype t) :=
 fun x y =>
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

Lemma feq_refl {t}: reflexive (ftype t) feq.
Proof.
intro x; destruct x; simpl; auto.
Qed.

Lemma feq_refl' {t}: forall x: ftype t, feq x x. 
exact feq_refl.
Qed.

#[export] Hint Resolve feq_refl': core.

Lemma feq_sym {t}: symmetric (ftype t) feq.
Proof.
intros x y; destruct x,y; simpl; auto.
intros [? [? ?]].
subst. auto.
Qed.

Lemma feq_trans {t: type}: transitive (ftype t) feq.
Proof.
intros x y z.
destruct x,y,z; simpl; intros; auto; try contradiction.
destruct H as [? [? ?]]; destruct H0 as [? [? ?]]; subst; auto.
Qed.

Add Parametric Relation {t: type}: (ftype t) (@feq t)
  reflexivity proved by feq_refl
  symmetry proved by feq_sym
  transitivity proved by feq_trans
   as feq_rel.

Lemma list_eqv_refl: forall {T} {rel: relation T} {EQrel: Equivalence rel},
   reflexive (list T) (Forall2 rel).
Proof.
intros.
red.
induction x; constructor; auto. reflexivity.
Qed.

Lemma list_eqv_sym: forall {T} {rel: relation T} {EQrel: Equivalence rel},
   symmetric (list T) (Forall2 rel).
Proof.
intros.
red.
induction x; destruct y; intros; inversion H; clear H; subst;  constructor; auto.
symmetry; auto.
Qed.

Lemma list_eqv_trans: forall {T} {rel: relation T} {EQrel: Equivalence rel},
   transitive (list T) (Forall2 rel).
Proof.
intros.
red.
induction x; destruct y,z; intros; inversion H; inversion H0; clear H H0; subst;  constructor; auto.
rewrite H4; auto.
eapply IHx; eauto.
Qed.

Add Parametric Relation {T: Type} (rel: relation T) {EQrel: Equivalence rel}: (list T) (Forall2 rel)
  reflexivity proved by list_eqv_refl
  symmetry proved by list_eqv_sym
  transitivity proved by list_eqv_trans
   as list_eqv_rel.


Lemma test_pair: forall t (a a': ftype t) (b b': vector t),
  feq a a' -> Forall2 feq b b' ->
  (feq * Forall2 feq)%signature (a,b) (a',b').
Proof.
intros.
rewrite H. 
rewrite H0. 
reflexivity.
Abort.  (* no need to save this *)

Add Parametric Morphism {T: Type} (rel: relation T): (@Some T)
  with signature rel ==> option_rel rel
  as Some_mor.
Proof.
intros. constructor; auto.
Qed.

Add Parametric Morphism {t: Type} (rel: t -> t -> Prop) : (@cons t)
  with signature rel ==> Forall2 rel ==> Forall2 rel
  as cons_mor.
Proof.
intros.
constructor; auto.
Qed.

Definition strict_feq {t: type} : relation (ftype t) :=
 fun x y =>
  match x, y with
    | Binary.B754_zero _ _ b1, Binary.B754_zero _ _ b2 => True
    | Binary.B754_finite _ _ b1 m1 e1 _, Binary.B754_finite _ _ b2 m2 e2 _ =>
          b1 = b2 /\  m1 = m2 /\ e1 = e2
    | _, _ => False
  end.

#[export] Instance subrelation_strict_feq {t: type}: subrelation (@strict_feq t) (@feq t).
Proof.
red; intros.
destruct x,y; inv H; simpl; auto.
Qed.

Definition finite {t} (x: ftype t) := strict_feq x x.

Lemma strict_feq_refl {t: type}: forall (x: ftype t),
 Binary.is_finite _ _ x = true -> strict_feq x x.
Proof.
intros.
destruct x; try discriminate; hnf; auto.
Qed.

Lemma strict_feq_sym {t: type}: symmetric (ftype t) strict_feq.
Proof.
intros x y.
destruct x,y; simpl; auto.
intros [? [? ?]].
subst. auto.
Qed.

Lemma strict_feq_trans {t: type}:  transitive (ftype t) strict_feq.
Proof.
intros x y z.
destruct x,y,z; simpl; intros; auto; try contradiction.
destruct H as [? [? ?]]; destruct H0 as [? [? ?]]; subst; auto.
Qed.

Add Parametric Relation {t: type}: (ftype t) (@strict_feq t)
  symmetry proved by strict_feq_sym
  transitivity proved by strict_feq_trans
   as strict_feq_rel.

#[export] Hint Extern 100 (Proper ?R ?x) => 
 (* See https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/rewriting.20with.20PERs *)
    (red; auto with typeclass_instances)    : typeclass_instances.

Add Parametric Morphism {NAN: Nans}{t: type} : BFMA
 with signature (@feq t) ==> feq ==> feq ==> feq
  as BFMA_mor.
Proof.
intros.    
destruct x,y; inv H; try apply I;
destruct x0,y0; inv  H0; try apply I;
destruct x1,y1; inv H1; try apply I;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
subst; simpl; auto;
repeat proof_irr;
try reflexivity;
repeat match goal with s: bool |- _ => destruct s end;
try reflexivity.
all: unfold BFMA, Binary.Bfma, BinarySingleNaN.Bfma, Binary.BSN2B, Binary.B2BSN;
simpl;
set (K := _ (proj1 _)); clearbody K; destruct K; simpl; auto.
Qed.

Lemma matrix_by_index_rows:
  forall {t} rows cols (f: nat -> nat -> ftype t),
  matrix_rows_nat (matrix_by_index rows cols f) = rows.
Proof.
intros.
unfold matrix_by_index, matrix_rows_nat.
rewrite map_length. rewrite seq_length. auto.
Qed.

Local Open Scope nat.

Lemma matrix_by_index_cols:
  forall {t} rows cols (f: nat -> nat -> ftype t),
  matrix_cols_nat (matrix_by_index rows cols f) cols.
Proof.
intros.
unfold matrix_by_index, matrix_cols_nat.
pose (k := 0). change (seq 0 rows) with (seq k rows).
clearbody k. revert k; induction rows; intros; constructor; auto.
rewrite map_length, seq_length. auto.
Qed.

Lemma nth_map_seq:
  forall {A} (f: nat -> A) d (i n: nat), i < n -> nth i (map f (seq 0 n)) d = f i.
Proof.
intros.
assert (i < n) by lia.
clear H.
transitivity (f (i+0)); [ | f_equal; lia].
set (k := 0 ) in *.
clearbody k.
revert k i H0; induction n; simpl; intros.
destruct i; auto; lia.
destruct i.
destruct k; auto; lia.
rewrite (IHn (S k) i).
f_equal; lia.
lia.
Qed.


Lemma matrix_by_index_index:
  forall {t} rows cols (f: nat -> nat -> ftype t) i j,
   i < rows -> j < cols ->
   matrix_index (matrix_by_index rows cols f) i j = f i j.
Proof.
 intros.
 unfold matrix_index, matrix_by_index.
 rewrite nth_map_seq; auto.
 rewrite nth_map_seq; auto.
Qed.

Lemma matrix_extensionality_strong: 
  forall {t} (m1 m2: matrix t) cols,
  matrix_rows_nat m1 = matrix_rows_nat m2 ->
  matrix_cols_nat m1 cols -> matrix_cols_nat m2 cols ->
  (forall i j, i < matrix_rows_nat m1 -> j < cols ->
        matrix_index m1 i j = matrix_index m2 i j) ->
    m1 = m2.
Proof.
 induction m1; destruct m2; simpl; intros; inv H; auto.
 inv H0. inv H1.
 f_equal.
 clear - H3 H2.
 specialize (H2 O).
 unfold matrix_index in H2. simpl in H2.
 revert l H3 H2; induction a; destruct l; simpl; intros; inv H3; f_equal; auto.
 apply (H2 O); try lia.
 apply IHa; auto. intros j ? ?. apply (H2 (S j)); try lia.
 eapply IHm1; eauto.
 intros i j ? ?. apply (H2 (S i) j); lia.
Qed.

Lemma matrix_extensionality: 
  forall {t} (m1 m2: matrix t) cols,
  matrix_rows_nat m1 = matrix_rows_nat m2 ->
  matrix_cols_nat m1 cols -> matrix_cols_nat m2 cols ->
  (forall i j, i < matrix_rows_nat m1 -> j < cols ->
        feq (matrix_index m1 i j) (matrix_index m2 i j)) ->
  Forall2 (Forall2 feq) m1 m2.
Proof.
 induction m1; destruct m2; simpl; intros; inv H; constructor; auto.
 specialize (H2 O).
 unfold matrix_index in H2. simpl in H2.
 inv H0. inv H1.
 clear - l H3 H2.
 revert l H3 H2; induction a; destruct l; simpl; intros; inv H3; constructor.
 apply (H2 O); try lia.
 apply IHa; auto. intros j ? ?. apply (H2 (S j)); try lia.
 inv H0. inv H1.
 fold (matrix_cols_nat m1 (length a)) in H6.
 fold (matrix_cols_nat m2 (length a)) in H5.
 eapply IHm1; eauto.
 intros i j ? ?. apply (H2 (S i) j); lia.
Qed.

Lemma matrix_index_prop:
 forall {t} (P: ftype t -> Prop) (m: matrix t) (cols i j : nat), 
    matrix_cols_nat m cols ->
    Forall (Forall P) m -> 
    i < matrix_rows_nat m -> j < cols ->
    P (matrix_index m i j).
Proof.
induction m; intros.
inv H1.
inv H0.
simpl in H1.
inv H.
unfold matrix_index.
destruct i; simpl.
clear - H2 H5.
revert j H2; induction H5; intros.
inv H2.
destruct j; simpl; auto.
apply IHForall. simpl in H2; lia.
eapply IHm; eauto.
lia.
Qed.

Lemma Forall_map: forall  {A B} (P: B -> Prop) (f: A -> B) (al: list A),
  Forall (Basics.compose P f) al ->
  Forall P (map f al).
Proof.
induction 1; constructor; auto.
Qed.

Lemma Forall_seq: forall (P: nat -> Prop) (lo n: nat),
  (forall i, lo <= i < lo+n -> P i) ->
  Forall P (seq lo n).
Proof.
intros.
revert lo H; induction n; simpl; intros; constructor.
apply H. lia.
apply IHn; intros.
apply H; lia.
Qed.

Lemma BPLUS_BOPP_diag: 
  forall {NAN: Nans} {t} (x: ftype t), finite x -> BPLUS t x (BOPP t x) = Zconst t 0.
Proof.
intros.
destruct x,s; inv H; try reflexivity;
unfold BPLUS, BOPP, BINOP, Binary.Bplus, Binary.Bopp, Binary.BSN2B,
   BinarySingleNaN.binary_normalize, BinarySingleNaN.binary_normalize,
   BinarySingleNaN.binary_normalize; simpl;
 unfold BinarySingleNaN.binary_normalize, BinarySingleNaN.Fplus_naive,
  SpecFloat.cond_Zopp;
replace (_ + _)%Z with 0%Z by lia; reflexivity.
Qed.

Lemma all_nth_eq:
 forall {A} d (al bl: list A),
  length al = length bl ->
  (forall i, i < length al -> nth i al d = nth i bl d) -> 
  al=bl.
Proof.
induction al; destruct bl; simpl; intros; try discriminate; f_equal.
apply (H0 0 ltac:(lia)).
apply IHal.
lia.
intros.
apply (H0 (S i)). lia.
Qed.

(* Infix "==" := feq (at level 70, no associativity). *)

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

Lemma BFMA_zero1: forall {NAN: Nans} {t} y s, 
  strict_feq y y ->
  feq (BFMA (Zconst t 0) y s) s.
Proof.
intros.
intros.
change (Zconst t 0) with 
  (Binary.B754_zero (fprec t)  (femax t) false).
unfold BFMA, BPLUS, BINOP in *.
destruct y, s; try discriminate; simpl; auto.
Qed.

Lemma BFMA_zero2: forall  {NAN: Nans}{t} x s, 
  strict_feq x x ->
  feq (BFMA x (Zconst t 0) s) s.
Proof.
intros.
intros.
change (Zconst t 0) with 
  (Binary.B754_zero (fprec t)  (femax t) false).
unfold BFMA, BPLUS, BINOP in *.
destruct x, s; try discriminate; simpl; auto.
Qed.

Lemma BPLUS_0_l: forall  {NAN: Nans} {t} x, finite x -> 
      feq (BPLUS t (Zconst t 0) x) x.
Proof.
  intros. destruct x; try contradiction;
 destruct s; simpl; auto.
Qed.

Lemma BPLUS_0_r: forall {NAN: Nans} {t} x, finite x -> 
      feq (BPLUS t x (Zconst t 0)) x.
Proof.
  intros. destruct x; try contradiction;
 destruct s; simpl; auto.
Qed.

Lemma finite_0: forall t,  finite (Zconst t 0).
Proof.
intros; apply I.
Qed.

Lemma norm2_snoc:
  forall  {NAN: Nans}{t} (al: vector t) (x: ftype t),
   norm2 (al ++ [x]) = BFMA x x (norm2 al).
 Proof.
  intros. unfold norm2, dotprod.
 rewrite combine_app by auto.
 rewrite fold_left_app. reflexivity.
 Qed.

Lemma BMULT_congr:
 forall  {NAN: Nans}{t} (x x' y y': ftype t), feq x x' -> feq y y' -> 
   feq (BMULT t x y) (BMULT t x' y').
Proof.
intros.
destruct x,x'; inv H; try constructor;
destruct y,y'; inv H0; try constructor.
destruct H2,H1; subst. repeat proof_irr.
apply feq_refl.
Qed.

Lemma BMINUS_congr:
 forall  {NAN: Nans}{t} (x x' y y': ftype t), feq x x' -> feq y y' -> 
   feq (BMINUS t x y) (BMINUS t x' y').
Proof.
intros.
destruct x,x'; inv H; try constructor;
destruct y,y'; inv H0; try constructor;
repeat lazymatch goal with
   |  H: _ /\ _ |- _ => destruct H; subst
  |  s: bool |- _ => first [clear s | destruct s] 
  end;
repeat proof_irr; 
  simpl; auto;
 destruct (Binary.Bfma _ _ _ _ _ _ _ _ _); auto.
Qed.

Lemma Forall2_rev:  forall {t} (rel: relation t) (x x': list t),
    Forall2 rel x x' -> Forall2 rel (rev x) (rev x').
Proof.
induction 1.
constructor.
simpl.
apply Forall2_app; auto.
Qed.

Lemma Forall2_rel_refl: forall {A: Type} (rel: relation A), 
   (forall x, rel x x) -> forall al, Forall2 rel al al.
Proof.
unfold reflexive; intros.
induction al; constructor; auto.
Qed.
#[export] Hint Resolve Forall2_rel_refl  : core.

Lemma Forall2_subrelation: forall {A: Type} (f g: A -> A -> Prop) (al bl: list A),
  subrelation f g -> Forall2 f al bl  -> Forall2 g al bl.
Proof.
induction 2; constructor; auto.
Qed.
#[export] Hint Resolve Forall2_subrelation: core.

Lemma dotprod_congr  {NAN: Nans}{t} (x x' y y' : vector t):
 Forall2 strict_feq x x' ->
 Forall2 strict_feq y y' ->
 length x = length y ->
 feq (dotprod x y) (dotprod x' y').
Proof.
 intros.
 unfold dotprod.
 pose proof (Forall2_length H).
 pose proof (Forall2_length H0).
 rewrite <- !fold_left_rev_right.
 apply Forall2_rev in H, H0.
 rewrite !rev_combine by lia.
 clear - H H0.
 set (a := rev x) in *; clearbody a. set (a' := rev x') in *; clearbody a'.
 set (b := rev y) in *; clearbody b. set (b' := rev y') in *; clearbody b'.
 revert b b' H0; induction H; simpl; intros; auto.
 inv H1. auto. simpl. apply BFMA_mor; auto; apply subrelation_strict_feq; auto.
Qed.

Lemma norm2_congr: 
  forall {NAN: Nans} {t} (x x': vector t), 
           Forall2 feq x x' -> 
           feq (norm2 x) (norm2 x').
Proof.
intros.
unfold norm2.
unfold dotprod.
 rewrite <- !fold_left_rev_right.
 apply Forall2_rev in H.
 rewrite !rev_combine by lia.
set (a := rev x) in *. set (b := rev x') in *. clearbody a. clearbody b.
induction H; simpl; intros; auto.
set (u := fold_right _ _ _) in *. clearbody u.
set (u' := fold_right _ _ _) in *. clearbody u'.
clear - H IHForall2.
destruct x0,y, u,u'; inv H; inv IHForall2;
try constructor;
auto;
try (destruct s,s0,s1,s2; constructor).
destruct H1; subst m0 e1. proof_irr.
unfold BFMA, Binary.Bfma, Binary.BSN2B, BinarySingleNaN.Bfma, Binary.B2BSN;
destruct s0,s1,s2; simpl; try constructor;
destruct (BinarySingleNaN.SF2B _ _); try constructor; auto.
destruct H0,H1; subst m0 m2 e1 e3.
repeat proof_irr.
unfold BFMA, Binary.Bfma, Binary.BSN2B,
 BinarySingleNaN.Bfma.
destruct (Binary.B2BSN (fprec t) (femax t)
        (Binary.B754_finite (fprec t) (femax t) s0 m e e0));
 try constructor; auto.
Qed.

Local Open Scope Z.

Lemma Znth_vector_sub:
 forall  {NAN: Nans}{t} i (x y: vector t) , Zlength x = Zlength y ->
   0 <= i < Zlength x ->
   Znth i (vector_sub x y) = BMINUS t (Znth i x) (Znth i y).
Proof.
intros.
unfold vector_sub, map2.
rewrite Znth_map by (rewrite Zlength_combine; lia).
rewrite Znth_combine by lia.
reflexivity.
Qed.

Lemma BFMA_xx_mor:
 forall  {NAN: Nans}{t} (x x' s s': ftype t), 
  feq x x' -> 
  feq s s' ->
  feq (BFMA x x s) (BFMA x' x' s').
Proof.
intros.
red.
unfold BFMA.
destruct x,x'; inv H; simpl; auto;
 destruct s,s'; inv H0; simpl; auto;
repeat proof_irr; 
repeat lazymatch goal with
   |  H: _ /\ _ |- _ => destruct H; subst
  |  s: bool |- _ => first [clear s | destruct s] 
  end;
repeat proof_irr; 
  simpl; auto;
try solve [destruct (Binary.Bfma _ _ _ _ _ _ _ _ _); auto].
all:
unfold Binary.Bfma, Binary.BSN2B, BinarySingleNaN.Bfma, Binary.B2BSN; simpl;
set (K := _ (proj1 _)); clearbody K; destruct K; simpl; auto.
Qed.


Lemma vector_sub_congr: forall {NAN: Nans} {t} (x x' y y': vector t),
  Forall2 feq x x' -> Forall2 feq y y' ->
  Forall2 feq (vector_sub x y) (vector_sub x' y').
Proof.
induction x; destruct x'; intros; inv H.
constructor.
specialize (IHx x').
inv H0. constructor.
specialize (IHx _ _ H6 H1).
constructor; auto.
apply BMINUS_congr; auto.
Qed.

Lemma norm2_loose_congr: 
 forall {NAN: Nans}{t} (x x': vector t),  Forall2 feq x x' -> feq (norm2 x) (norm2 x').
Proof.
intros.
unfold norm2.
unfold dotprod.
rewrite <- !fold_left_rev_right.
pose proof (Forall2_length H).
rewrite !rev_combine by auto.
clear H0.
apply Forall2_rev in H.
set (a := rev x) in *. clearbody a.
set (b := rev x') in *. clearbody b.
induction H.
constructor.
simpl.
apply BFMA_xx_mor; auto.
Qed.

Lemma strict_feq_i1:
  forall  {t} (x y: ftype t), 
    finite x -> feq x y ->
    strict_feq x y.
Proof.
 intros.
 red in H.
 destruct x; inv H;
 destruct y; inv H0. constructor. constructor; auto.
Qed.

Lemma FMA_one: forall {NAN: Nans}{t} (x y: ftype t),
  feq (BFMA x y (Zconst t 0)) (BMULT t x y).
Proof.
unfold BFMA, BMULT, BINOP.
intros.
(*unfold Binary.Bmult, Binary.Bfma, Binary.BSN2B, Binary.B2BSN, BinarySingleNaN.Bfma,
  BinarySingleNaN.Bfma_szero .
*)
destruct x,y; try destruct s; try destruct s0; try apply I.
-
Abort.  (* Not at all easy to prove, though probably true *)

Lemma nth_map_inrange {A} (d': A) {B: Type}:
  forall (f: A -> B) i al d,
   (i < length al)%nat ->
   nth i (map f al) d = f (nth i al d').
Proof.
intros.
revert i H; induction al; destruct i; simpl; intros; inv H; auto.
apply IHal; auto. lia.
apply IHal; auto. lia.
Qed.

Add Parametric Morphism {t: type} : (Binary.is_finite (fprec t) (femax t))
  with signature feq ==> eq
  as is_finite_mor.
Proof.
intros.
destruct x, y; inv H; reflexivity.
Qed.

Lemma strict_floatlist_eqv_i1: 
   forall {t} (a b: list (ftype t)),
    Forall finite a -> Forall2 feq a b -> Forall2 strict_feq a b.
Proof.
induction 2; inv H;constructor.
apply strict_feq_i1; auto.
apply IHForall2; auto.
Qed.

Lemma finite_is_finite: forall {t} (x: ftype t),
   finite x <-> Binary.is_finite _ _ x = true.
Proof.
split; intros;
destruct x; inv H; try reflexivity.
constructor; auto.
Qed.

Lemma feq_strict_feq:
 forall {t} (x y: ftype t),
   finite x -> feq x y -> strict_feq x y.
Proof.
 intros.
 destruct x; inv H; destruct y; inv H0; constructor; auto.
Qed.

Lemma strict_feq_finite1:
  forall {t} (x y: ftype t),
    strict_feq x y -> finite x.
Proof.
intros.
destruct x,y; inv H; constructor; auto.
Qed.

Lemma finite_dotprod_e: forall {NAN: Nans}{t} (x y: vector t),
  Zlength x = Zlength y ->
  finite (dotprod x y) -> Forall finite x /\ Forall finite y.
Proof.
intros.
rewrite !Zlength_correct in H. apply Nat2Z.inj in H.
unfold dotprod in H0.
rewrite <- fold_left_rev_right in H0.
rewrite rev_combine in H0 by auto.
rewrite <- (rev_length x), <- (rev_length y) in H.
assert (Forall finite (rev x) /\ Forall finite (rev y)).
2:rewrite <- (rev_involutive x), <- (rev_involutive y);
   destruct H1; split; apply Forall_rev; auto.
forget (rev x) as a; forget (rev y) as b.
revert b H H0; induction a; destruct b; intros; inv H.
split; constructor.
specialize (IHa _ H2).
simpl in H0.
set (u := fold_right _ _ _) in *. clearbody u.
assert (finite a /\ finite f /\ finite u); [ | split; constructor; tauto].
clear - H0.
apply finite_is_finite in H0.
destruct a,f,u; inv H0; try solve [split3; constructor; auto].
destruct s,s0,s1; inv H1.
destruct s,s0,s1; inv H1.
destruct s,s0,s1; inv H1.
Qed.


Lemma finite_norm2_e: forall {NAN: Nans}{t} (x: vector t),
  finite (norm2 x) -> Forall finite x.
Proof.
intros.
apply finite_dotprod_e in H; auto.
destruct H; auto.
Qed.

Lemma matrix_by_index_prop:
 forall {t} (f: nat -> nat -> ftype t) (P: ftype t -> Prop) rows cols,
  P (Zconst t 0) ->
  (forall i j, (i < rows)%nat -> (j < cols)%nat -> P (f i j)) ->
  Forall (Forall P) (matrix_by_index rows cols f).
Proof.
intros.
unfold matrix_by_index.
apply Forall_nth; intros.
rewrite map_length, seq_length in H1.
rewrite nth_map_seq by auto.
apply Forall_nth; intros.
rewrite map_length, seq_length in H2.
rewrite nth_map_seq by auto.
apply H0; auto.
Qed.

Lemma Zmatrix_cols_nat: 
 forall {t} (m: matrix t) cols,
  matrix_cols_nat m cols  <-> matrix_cols m (Z.of_nat cols).
Proof.
induction m; simpl; intros; split; intro; inv H; constructor; auto.
apply Zlength_correct.
clear - H3.
induction H3; constructor; auto. rewrite <- H; apply Zlength_correct.
rewrite Zlength_correct in H2. lia.
clear - H3.
induction H3; constructor; auto. rewrite Zlength_correct in H; lia.
Qed.

Lemma Zlength_seq: forall lo n, Zlength (seq lo n) = Z.of_nat n.
Proof.
intros. rewrite Zlength_correct. f_equal. apply seq_length.
Qed.
#[export] Hint Rewrite Zlength_seq : sublist rep_lia.

Lemma Zmatrix_rows_nat: forall {t} (m: matrix t), Z.of_nat (matrix_rows_nat m) = matrix_rows m.
Proof.
unfold matrix_rows.
induction m; simpl; auto. list_solve.
Qed.

Add Parametric Morphism {NAN: Nans}{t: type}: (@norm2 _ t)
  with signature Forall2 feq ==> feq
 as norm2_mor.
Proof.
exact norm2_congr.
Qed.

Add Parametric Morphism {NAN: Nans}{t: type}: (@vector_sub _ t)
  with signature Forall2 feq ==> Forall2 feq ==> Forall2 feq
  as vector_sub_mor.
Proof.
intros; eapply vector_sub_congr; eauto.
Qed.

Add Parametric Morphism {T: Type} (rel: relation T): (@Zlength T)
  with signature Forall2 rel ==> eq
  as Zlength_mor.
Proof.
induction 1; auto.
rewrite !Zlength_cons; f_equal; auto.
Qed.

Add Parametric Morphism {t: type}: (@finite t)
  with signature feq ==> iff
  as finite_rel.
Proof.
destruct x,y; split; intros; inv H0; inv H; constructor; auto.
Qed.

Add Parametric Morphism {NAN: Nans}{t}: (@dotprod _ t)
 with signature Forall2 feq ==> Forall2 feq ==> feq
 as dotprod_mor.
Proof.
intros.
unfold dotprod.
set (a := Zconst t 0) at 1.
set (a' := Zconst t 0).
assert (feq a a') by reflexivity.
clearbody a. clearbody a'.
revert x0 y0 H0 a a' H1; induction H; intros.
destruct x0, y0; inv H0; simpl; auto.
destruct x0,y0; inv H1; simpl; auto.
eapply IHForall2; eauto.
apply BFMA_mor; auto.
Qed.


Add Parametric Morphism {NAN: Nans}{t}: (BPLUS t)
 with signature feq ==> feq ==> feq
 as BPLUS_mor.
Proof.
intros.
destruct x,y; inv H; destruct x0,y0; inv H0; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
subst;
repeat proof_irr; 
try constructor; auto.
Qed.

Add Parametric Morphism {NAN: Nans}{t}: (BMINUS t)
 with signature feq ==> feq ==> feq
 as BMINUS_mor.
Proof.
intros.
destruct x,y; inv H; destruct x0,y0; inv H0; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
subst;
repeat proof_irr; 
try constructor; auto.
Qed.

Add Parametric Morphism {NAN: Nans}{t}: (BMULT t)
 with signature feq ==> feq ==> feq
 as BMULT_mor.
Proof.
intros.
destruct x,y; inv H; destruct x0,y0; inv H0; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
subst;
repeat proof_irr; 
try constructor; auto.
Qed.

Add Parametric Morphism {NAN: Nans}{t}: (BDIV t)
 with signature feq ==> strict_feq ==> feq
 as BDIV_mor.
Proof.
intros.
destruct x,y; inv H; destruct x0,y0; inv H0; 
repeat match goal with s: bool |- _ => destruct s end; simpl in *;
repeat match goal with H: _ /\ _ |- _ => destruct H end;
subst;
repeat proof_irr; 
try constructor;
reflexivity.
Qed.

Add Parametric Morphism {NAN: Nans} {t}: (@matrix_vector_mult _ t)
 with signature Forall2 (Forall2 feq) ==> Forall2 feq ==> Forall2 feq
 as matrix_vector_mult_mor.
Proof.
intros.
unfold matrix_vector_mult.
apply Forall2_map.
induction H; simpl; intros; constructor; auto.
apply dotprod_mor; auto.
Qed.

Add Parametric Morphism {t}: (BCMP t) 
 with signature eq ==> eq ==> strict_feq ==> strict_feq ==> eq
 as BCMP_mor.
Proof.
intros.
destruct x,y1; inv H; destruct x0,y2; inv H0; simpl.
destruct y,s,s0,s1,s2;simpl; auto.
destruct H1; subst.
proof_irr.
destruct y0,s,s0,s2; simpl; auto.
destruct H2; subst.
proof_irr.
destruct y0,s,s0,s1; simpl; auto.
destruct H1,H2; subst.
repeat proof_irr.
destruct y0,s0,s1; simpl; auto.
Qed.

