Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import Coq.Relations.Relations Coq.Classes.Morphisms Coq.Classes.RelationPairs Coq.Classes.RelationClasses.
Require Export vcfloat.FPLib.
Set Bullet Behavior "Strict Subproofs".

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
  map (map (@BOPP NAN t)) m.

Definition matrix_add {NAN: Nans}{t} : matrix t -> matrix t -> matrix t :=
  map2 (map2 (@BPLUS _ t)).

Definition vector_add {NAN: Nans}{t:type} (v1 v2 : vector t) :=
  map2 (@BPLUS _ t) v1 v2.

Definition vector_sub {NAN: Nans}{t:type} (v1 v2 : vector t) :=
  map2 (@BMINUS _ t) v1 v2.

Definition matrix_index {t} (m: matrix t) (i j: nat) :=
 nth j (nth i m nil) (Zconst t 0).

Definition matrix_by_index {t} (rows cols: nat) 
          (f: nat -> nat -> ftype t) : matrix t :=
     map (fun i => map (f i) (seq 0 cols)) (seq 0 rows).

Definition matrix_rows_nat {t} (m: matrix t) := length m.

Definition matrix_cols_nat {t} (m: matrix t) cols :=
    Forall (fun r => length r = cols) m.

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

#[export] Instance zerof {t} : Inhabitant (ftype t) := (Zconst t 0).

Lemma norm2_snoc:
  forall  {NAN: Nans}{t} (al: vector t) (x: ftype t),
   norm2 (al ++ [x]) = BFMA x x (norm2 al).
 Proof.
  intros. unfold norm2, dotprod.
 rewrite combine_app by auto.
 rewrite fold_left_app. reflexivity.
 Qed.

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
   Znth i (vector_sub x y) = BMINUS (Znth i x) (Znth i y).
Proof.
intros.
unfold vector_sub, map2.
rewrite Znth_map by (rewrite Zlength_combine; lia).
rewrite Znth_combine by lia.
reflexivity.
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

