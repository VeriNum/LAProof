Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import Coq.Relations.Relations Coq.Classes.Morphisms Coq.Classes.RelationPairs Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Definition BFMA {NAN: Nans} {t: type} : forall (x y z: ftype t), ftype t :=
    Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t)
      (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE.


Definition matrix t := list (list (ftype t)).
Definition vector t := list (ftype t).

Definition dotprod {t: type} (v1 v2: list (ftype t)) : ftype t :=
  fold_left (fun s x12 => BFMA (fst x12) (snd x12) s) 
                (List.combine v1 v2)  (Zconst t 0).

Definition norm2 {t} (v: vector t) := dotprod v v.

Definition matrix_vector_mult {t: type} (m: matrix t) (v: vector t) : vector t :=
      map (fun row => dotprod row v) m.

Definition matrix_matrix_mult {t: type} (m1 m2: matrix t) : matrix t :=
  map (matrix_vector_mult m1) m2.

Definition matrix_cols {t} (m: matrix t) cols :=
    Forall (fun r => Zlength r = cols) m.

Definition matrix_rows {t} (m: matrix t) : Z := Zlength m.

Definition map2 {A B C: Type} (f: A -> B -> C) al bl :=
  map (uncurry f) (List.combine al bl).

Definition opp_matrix {t:type} (m: matrix t) : matrix t :=
  map (map (BOPP t)) m.

Definition matrix_add {t} : matrix t -> matrix t -> matrix t :=
  map2 (map2 (BPLUS t)).

Definition vector_add {t:type} (v1 v2 : vector t) :=
  map2 (BPLUS t) v1 v2.

Definition vector_sub {t:type} (v1 v2 : vector t) :=
  map2 (BMINUS t) v1 v2.

Definition matrix_index {t} (m: matrix t) (i j: nat) :=
 nth j (nth i m nil) (Zconst t 0).

Definition matrix_by_index {t} (rows cols: nat) 
          (f: nat -> nat -> ftype t) : matrix t :=
     map (fun i => map (f i) (seq 0 cols)) (seq 0 rows).

Definition matrix_rows_nat {t} (m: matrix t) := length m.

Definition matrix_cols_nat {t} (m: matrix t) cols :=
    Forall (fun r => length r = cols) m.

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

(*
Definition list_eqv {t: Type} : relation t ->  relation (list t) :=
  @Forall2 t t.
*)

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

(*
Add Parametric Relation {T: Type} (rel: relation T) {EQrel: Equivalence rel}: (list T) (list_eqv rel)
  reflexivity proved by list_eqv_refl
  symmetry proved by list_eqv_sym
  transitivity proved by list_eqv_trans
   as list_eqv_rel.
*)

Add Parametric Relation {T: Type} (rel: relation T) {EQrel: Equivalence rel}: (list T) (Forall2 rel)
  reflexivity proved by list_eqv_refl
  symmetry proved by list_eqv_sym
  transitivity proved by list_eqv_trans
   as list_eqv_rel.


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

Add Parametric Morphism {t: type} : BFMA
 with signature (@strict_feq t) ==> strict_feq ==> feq ==> feq
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
  forall {t} (x: ftype t), finite x -> BPLUS t x (BOPP t x) = Zconst t 0.
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

Lemma BFMA_zero1: forall {t} y s, 
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

Lemma BFMA_zero2: forall {t} x s, 
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

Lemma BPLUS_0_l: forall t x, finite x -> 
      feq (BPLUS t (Zconst t 0) x) x.
Proof.
  intros. destruct x; try contradiction;
 destruct s; simpl; auto.
Qed.

Lemma BPLUS_0_r: forall t x, finite x -> 
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
  forall {t} (al: vector t) (x: ftype t),
   norm2 (al ++ [x]) = BFMA x x (norm2 al).
 Proof.
  intros. unfold norm2, dotprod.
 rewrite combine_app by auto.
 rewrite fold_left_app. reflexivity.
 Qed.

Lemma BMULT_congr:
 forall {t} (x x' y y': ftype t), feq x x' -> feq y y' -> 
   feq (BMULT t x y) (BMULT t x' y').
Proof.
intros.
destruct x,x'; inv H; try constructor;
destruct y,y'; inv H0; try constructor.
destruct H2,H1; subst. repeat proof_irr.
apply feq_refl.
Qed.

Lemma BMINUS_congr:
 forall {t} (x x' y y': ftype t), feq x x' -> feq y y' -> 
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

Lemma dotprod_congr {t} (x x' y y' : vector t):
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
 inv H1. auto. simpl. apply BFMA_mor; auto.
Qed.


Lemma norm2_congr: 
  forall {t} (x x': vector t), 
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
 forall {t} i (x y: vector t) , Zlength x = Zlength y ->
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
 forall {t} (x x' s s': ftype t), 
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
 destruct (Binary.Bfma _ _ _ _ _ _ _ _ _); auto.
Qed.


Lemma vector_sub_congr: forall {t} (x x' y y': vector t),
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
 forall {t} (x x': vector t),  Forall2 feq x x' -> feq (norm2 x) (norm2 x').
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
  forall {t} (x y: ftype t), 
    finite x -> feq x y ->
    strict_feq x y.
Proof.
 intros.
 red in H.
 destruct x; inv H;
 destruct y; inv H0. constructor. constructor; auto.
Qed.

