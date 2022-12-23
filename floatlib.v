Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.

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

Definition matrix_eqv {t} : matrix t -> matrix t -> Prop :=
  Forall2 (Forall2 float_eqv).

Lemma matrix_eqv_refl {t: type} : reflexive _ (@matrix_eqv t).
Proof.
intro m.
induction m; constructor; auto.
induction a; constructor; auto.
Qed.

Lemma matrix_eqv_sym {t: type} : symmetric _ (@matrix_eqv t).
Proof.
red.
unfold matrix_eqv.
induction x; destruct y; intros; inv H; constructor; auto.
clear - H3.
induction H3; constructor; auto.
symmetry; auto.
Qed.

Lemma matrix_eqv_trans {t: type} : transitive _ (@matrix_eqv t).
Proof.
red.
unfold matrix_eqv.
induction x; destruct y,z; intros; inv H; inv H0; constructor; auto.
clear - H3 H4.
revert a H4; induction H3; intros; inv H4; constructor; auto.
etransitivity; eauto.
eauto.
Qed.

Add Parametric Relation {t: type}: (matrix t) (@matrix_eqv t)
  reflexivity proved by matrix_eqv_refl
  symmetry proved by matrix_eqv_sym
  transitivity proved by matrix_eqv_trans
   as matrix_eqv_rel.

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
        float_eqv (matrix_index m1 i j) (matrix_index m2 i j)) ->
  matrix_eqv m1 m2.
Proof.
 unfold matrix_eqv.
 induction m1; destruct m2; simpl; intros; inv H; auto.
 inv H0. inv H1.
 constructor. 
 clear - H3 H2.
 specialize (H2 O).
 unfold matrix_index in H2. simpl in H2.
 revert l H3 H2; induction a; destruct l; simpl; intros; inv H3; auto.
 constructor.
 apply (H2 O); try lia.
 apply IHa; auto. intros j ? ?. apply (H2 (S j)); try lia.
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

Lemma BPLUS_0_l: forall t x, finite x -> 
      float_eqv (BPLUS t (Zconst t 0) x) x.
Proof.
  intros. destruct x; try contradiction;
 destruct s; simpl; auto.
Qed.
Lemma BPLUS_0_r: forall t x, finite x -> 
      float_eqv (BPLUS t x (Zconst t 0)) x.
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
 forall {t} (x x' y y': ftype t), float_eqv x x' -> float_eqv y y' -> 
   float_eqv (BMULT t x y) (BMULT t x' y').
Proof.
intros.
destruct x,x'; inv H; try constructor;
destruct y,y'; inv H0; try constructor.
destruct H2,H1; subst. repeat proof_irr.
apply float_eqv_refl.
Qed.

Lemma BMINUS_congr:
 forall {t} (x x' y y': ftype t), float_eqv x x' -> float_eqv y y' -> 
   float_eqv (BMINUS t x y) (BMINUS t x' y').
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

Lemma floatlist_eqv_rev:  forall {t} (x x': vector t),
 floatlist_eqv x x' -> floatlist_eqv (rev x) (rev x').
Proof.
induction 1.
constructor.
simpl.
apply Forall2_app; auto.
Qed.

Lemma strict_floatlist_eqv_rev:  forall {t} (x x': vector t),
 strict_floatlist_eqv x x' -> strict_floatlist_eqv (rev x) (rev x').
Proof.
induction 1.
constructor.
simpl.
apply Forall2_app; auto.
Qed.

Lemma dotprod_congr {t} (x x' y y' : vector t):
 strict_floatlist_eqv x x' ->
 strict_floatlist_eqv y y' ->
 length x = length y ->
 float_eqv (dotprod x y) (dotprod x' y').
Proof.
 intros.
 unfold dotprod.
 pose proof (Forall2_length H).
 pose proof (Forall2_length H0).
 rewrite <- !fold_left_rev_right.
 apply strict_floatlist_eqv_rev in H, H0.
 rewrite !rev_combine by lia.
 clear - H H0.
 set (a := rev x) in *; clearbody a. set (a' := rev x') in *; clearbody a'.
 set (b := rev y) in *; clearbody b. set (b' := rev y') in *; clearbody b'.
 revert b b' H0; induction H; simpl; intros; auto.
 inv H1. auto. simpl. apply BFMA_mor; auto.
Qed.


Lemma norm2_congr: 
  forall {t} (x x': vector t), 
           floatlist_eqv x x' -> 
           float_eqv (norm2 x) (norm2 x').
Proof.
intros.
unfold norm2.
unfold dotprod.
 rewrite <- !fold_left_rev_right.
 apply floatlist_eqv_rev in H.
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
  float_eqv x x' -> 
  float_eqv s s' ->
  float_eqv (BFMA x x s) (BFMA x' x' s').
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
  floatlist_eqv x x' -> floatlist_eqv y y' ->
  floatlist_eqv (vector_sub x y) (vector_sub x' y').
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
 forall {t} (x x': vector t),  floatlist_eqv x x' -> float_eqv (norm2 x) (norm2 x').
Proof.
intros.
unfold norm2.
unfold dotprod.
rewrite <- !fold_left_rev_right.
pose proof (Forall2_length H).
rewrite !rev_combine by auto.
clear H0.
apply floatlist_eqv_rev in H.
set (a := rev x) in *. clearbody a.
set (b := rev x') in *. clearbody b.
induction H.
constructor.
simpl.
apply BFMA_xx_mor; auto.
Qed.

Lemma strict_float_eqv_i1:
  forall {t} (x y: ftype t), 
    finite x -> float_eqv x y ->
    strict_float_eqv x y.
Proof.
 intros.
 red in H.
 destruct x; inv H;
 destruct y; inv H0. constructor. constructor; auto.
Qed.

