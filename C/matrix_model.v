(** * LAProof.C.matrix_model: Functional models of matrix operations *)

(** * Prologue: typical imports for MathComp floating-point matrix functional models *)

(* BEGIN This part copied from iterative_methods/cholesky/cholesky_model.v, 
   modified a bit, should really unify these libraries somehow *)

(** Don't import all of VST, since we have no separation-logic reasoning here;
  import only the part of VST for reasoning about functional models. *) 
Require Import VST.floyd.functional_base.

(** Other useful imported libraries. *)
Import ListNotations.
Require Import Permutation.
Require Import vcfloat.FPStdLib.
Require Import vcfloat.FPStdCompCert.

(** In contrast to certain other modules (e.g., [C.spec_densemat]
  where we [Require] mathcomp but carefully don't [Import] most of it), 
  here we intend to do lots of mathcomp reasoning, so we [Require Import]. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun bigop finset fingroup perm order.
From mathcomp Require Import div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.

(** Now we adjust all the settings that mathcomp has modified *)
(* begin show *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
(* end show *)

(** * MathComp matrices over a nonring *)

(** Most MathComp matrix operations, such as matrix multiplication, are parameterized
  over a Ring or Field structure.  When you do the dot-products in a matrix multiply, it
  doesn't matter what order you add up the element products, because addition in a Ring
  is associative-commutative.  But our functional models of matrix algorithms are in floating point,
  which is not a Ring or Field because (for example) addition is not associative.

  MathComp handles this by having some matrix operations (such as transpose [tr_mx]
  and the very definition of a  [@matrix _ _ _] (notated as ['M[_]_(_,_)]) be parameterized
  only over a [Type] when they don't need a Ring structure; it is only the operators whose
  natural mathematics need additional properties, that require a Ring or Field.

  That means we can use natural MathComp operations such as blocking and transpose
  on floating-point matrices ['M[ftype t]_(m,n)] but we cannot use MathComp's matrix multiply
   [mulmx].   Instead, if we multiply floating-point matrices, we must define it ourselves in
  a way that specifies exactly what order of operations is done, or (if a relation instead of a
  function) what order(s) are permitted.

  The definition [update_mx] is an example of an operation that naturally does not require
  a Ring structure.  The definition [subtract_loop], below, is an example of the other kind; 
  we can't use MathComp's dot-product to define it, so we write a definition that explicitly
  specifies the order of additions. 
 *)

Definition update_mx {T} [m n] (M: 'M[T]_(m,n)) (i: 'I_m) (j: 'I_n) (x: T) : 'M[T]_(m,n) :=
    \matrix_(i',j') if  andb (Nat.eq_dec i' i) (Nat.eq_dec j' j) then x else M i' j'.

Definition neg_zero {t}: ftype t := Binary.B754_zero (fprec t) (femax t) true.

(** * Functional model of Cholesky decomposition (jik algorithm) *)
(** The next three definitions, up to [cholesky_jik_spec], are adapted from
  similar definitions in coq-libvalidsdp by P. Roux et al. *)


Definition subtract_loop {t} [n] (A R: 'M[ftype t]_n) (i j k: 'I_n) : ftype t :=
  fold_left BMINUS  (map (fun k' => BMULT (R k' i) (R k' j)) (take k (ord_enum n)))  (A i j).

Definition cholesky_jik_ij {t} [n: nat] (A R: 'M[ftype t]_n) (i j: 'I_n) : Prop :=
     (forall Hij: (i<j)%N, R i j = BDIV (subtract_loop A R i j i) (R i i))  
   /\ (forall Hij: i=j, R i j = BSQRT (subtract_loop A R i j i)).

Definition cholesky_jik_spec {t} [n: nat] (A R: 'M[ftype t]_n) : Prop :=
  forall i j, cholesky_jik_ij A R i j.

(** When we have run the "Cholesky jik algorithm" only up to iteration (i,j),
   the matrix is only initialized above row i, and in row i up to column j, so we
  need this subrelation in our loop invariant. *)
Definition cholesky_jik_upto {t} [n] (imax: 'I_n) (jmax : 'I_n.+1) (A R : 'M[ftype t]_n) : Prop :=
  forall (i j: 'I_n),
      ((j<jmax)%N -> cholesky_jik_ij A R i j)
   /\ (nat_of_ord j = nat_of_ord jmax -> (i<imax)%N -> cholesky_jik_ij A R i j)
   /\ ((j>jmax)%N -> R i j = A i j)
   /\ (nat_of_ord j= nat_of_ord jmax -> (i>=imax)%N -> R i j = A i j).

(** The functional model above assumes that we compute every dot-product in left-to-right order.
  But the algorithm should work equally accurately no matter what the order, so we
 have this alternate presentation that permits any order of summation. *)

(* BEGIN adapted from iterative_methods/sparse/sparse_model.v *)
Inductive sum_any {t}: forall (v: list (ftype t)) (s: ftype t), Prop :=
| Sum_Any_0: sum_any nil (Zconst t 0)
| Sum_Any_1: forall x y, feq x y -> sum_any [x] y
| Sum_Any_split: forall al bl a b c, sum_any al a -> sum_any bl b -> feq (BPLUS a b) c -> sum_any (al++bl) c
| Sum_Any_perm: forall al bl s, Permutation al bl -> sum_any al s -> sum_any bl s.
(* END copied form iterative_methods/sparse/sparse_model.v *)

Definition subtract_loop' {t} [n] (A R: 'M[ftype t]_n) (i j k: 'I_n) : ftype t -> Prop :=
  sum_any (A i j :: map (fun k' => BOPP (BMULT (R k' i) (R k' j))) (take k (ord_enum n))).

Definition cholesky_jik_ij' {t} [n: nat] (A R: 'M[ftype t]_n) (i j: 'I_n) : Prop :=
     ((i < j)%N -> exists x, subtract_loop' A R i j i x /\ R i j = BDIV x (R i i))
   /\ (i=j -> exists x, subtract_loop' A R i j i x /\ R i j = BSQRT x).

(** Supporting lemmas for proving steps of the Cholesky "jik" algorithm *)

(* duplicates floatlib.zerof, so at least keep it local *)
Local Instance zerof {t} : Inhabitant (ftype t) := (Zconst t 0).

(* BEGIN copied from iterative_methods/cholesky/verif_cholesky.v *)

Lemma update_i_lt_j_aux: forall [n] [i j: 'I_n], (i<j)%N -> (i.+1<n)%N.
Proof.
 intros.
 pose proof (ltn_ord j).
 lia.
Qed.


Lemma in_take_ord_enum: forall [n] (i x: 'I_n), x \in (take i (ord_enum n)) -> (x<i)%N.
Proof.
intros.
assert (nat_of_ord x \in map (@nat_of_ord n) (take i (ord_enum n))).
apply map_f; auto.
rewrite map_take in H0.
rewrite val_ord_enum in H0.
rewrite take_iota in H0.
rewrite mem_iota in H0. lia.
Qed.

Lemma eq_in_subrange: 
  forall n T (i: 'I_n) (f f': 'I_n -> T),
    (forall (a: 'I_n), (a<i)%N -> f a = f' a) ->
      map f (take i (ord_enum n)) = map f' (take i (ord_enum n)).
Proof.
intros.
apply eq_in_map.
intros ? ?; auto.
apply H.
apply in_take_ord_enum; auto.
Qed.

Definition lshift1 [n: nat] (k: ordinal n) : ordinal (S n) 
 := Ordinal (ltn_trans (ltn_ord k) (leqnn (S n))).


Lemma update_i_lt_j:
  forall {t} n (i j: 'I_n) (A R: 'M[ftype t]_n)
   (Hij: (i < j)%N)
   (i1: 'I_n)
   (Hi1: nat_of_ord i1 = S i),
   cholesky_jik_upto i (lshift1 j) A R ->
   let rij := BDIV (subtract_loop A R i j i) (R i i) in
    @cholesky_jik_upto t n i1 (lshift1 j) A (update_mx R i j rij).
Proof.
intros * Hij i1 Hi1 H1 rij i' j'.
subst rij.
simpl.
split; [ | split3]; intros * H2.
-
specialize (H1 i' j').
destruct H1 as [H1 _]. specialize (H1 H2).
split; intros * H4.
+
destruct H1 as [H1 _]. specialize (H1 H4). 
unfold update_mx.
rewrite !mxE.
destruct (Nat.eq_dec j j'); [lia |].
destruct (Nat.eq_dec _ _); simpl.
* destruct (Nat.eq_dec _ _); [ lia | simpl].
  apply ord_inj in e; subst i.
  rewrite H1. f_equal.
  unfold subtract_loop.
  f_equal.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE; simpl. 
  destruct (Nat.eq_dec _ _); auto; lia.
  destruct (Nat.eq_dec _ _); auto; lia.
* rewrite H1. f_equal.
  unfold subtract_loop.
  f_equal.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE.
  repeat destruct (Nat.eq_dec _ _); try lia; auto.
+ destruct H1 as [_ H1].
  unfold update_mx. subst i'.
  rewrite !mxE.
  destruct (Nat.eq_dec _ _); try lia.
  *
  destruct (Nat.eq_dec _ _); try lia.
  specialize (H1 (Logic.eq_refl _)).
  rewrite H1. simpl. f_equal.
  unfold subtract_loop.
  f_equal.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE.
  f_equal; repeat (destruct (Nat.eq_dec _ _); try lia); auto.
  *
  specialize (H1 (Logic.eq_refl _)).
  rewrite H1. simpl. f_equal.
  unfold subtract_loop.
  f_equal.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE. simpl in H2.
  f_equal; repeat (destruct (Nat.eq_dec _ _); try lia); auto.
- red in H1|-*.
  apply ord_inj in H2.
  subst j'.
  simpl in *.
  intro H3.
  split; intros; [ | subst; lia].
  unfold update_mx. 
  rewrite !mxE.
  destruct (Nat.eq_dec j j); [simpl; clear e | lia].
  destruct (Nat.eq_dec j i'); try lia. simpl.
   replace (if proj_sumbool (Nat.eq_dec i i') then R i' i' else R i' i') 
      with (R i' i') by (destruct (Nat.eq_dec _ _); auto).
   destruct (Nat.eq_dec _ _); simpl.
  * assert (i' = i) by (apply ord_inj; auto). subst i'. clear e.
    clear n0 H3.
    f_equal.
  match goal with |- _ = _ _ ?ff _ _ _ => set (f:=ff) end.
  unfold subtract_loop.
  f_equal.
  apply eq_in_subrange; intros a H3; simpl.
  subst f. rewrite !mxE.
  destruct (Nat.eq_dec _ _); try lia; auto.
  destruct (Nat.eq_dec _ _); try lia; auto.
  * assert (i'<i)%N by lia.  clear n1 H3 n0.
   specialize (H1 i' j). destruct H1 as [_ [H1 _]].
   destruct H1 as [H1 _]; auto; try lia.
   rewrite H1; auto.
   f_equal.
  unfold subtract_loop.
  f_equal.
  apply eq_in_subrange; intros a H3; simpl.
  rewrite !mxE.
  f_equal;
  repeat (destruct (Nat.eq_dec _ _)); try lia; auto.
- unfold update_mx. rewrite !mxE.
  specialize (H1 i' j').
  destruct H1 as [_ [_ [H1 _]]].
  repeat (destruct (Nat.eq_dec _ _)); try lia; auto.
- intros.
  specialize (H1 i' j'). destruct H1 as [_ [_ [_ H1]]].
  assert (j'=j) by (apply ord_inj; auto).
  subst. clear H2.
  unfold update_mx. rewrite !mxE.  
  repeat (destruct (Nat.eq_dec _ _)); try lia; auto.
  simpl. apply H1; auto. lia.
Qed.

Lemma length_ord_enum: forall n, length (ord_enum n) = n.
Proof.
intros.
pose proof val_ord_enum n.
simpl in H.
transitivity (length (iota 0 n)).
transitivity (length (map (nat_of_ord (n:=n)) (ord_enum n))).
rewrite length_map; auto.
f_equal; auto.
apply size_iota.
Qed.

Lemma size_ord_enum: forall n, size (ord_enum n) = n.
Proof. exact length_ord_enum. Qed.

Lemma nth_ord_enum': forall n (d i: 'I_n), nth d (ord_enum n) i = i.
Proof.
intros.
pose proof (val_ord_enum n).
simpl in H.
apply ord_inj.
pose proof ltn_ord i.
rewrite <- nth_map with (x2:=nat_of_ord d).
rewrite H. rewrite nth_iota. lia. lia.
rewrite size_ord_enum.
auto.
Qed.

Lemma take_snoc: forall {T} (d: T) (k: nat) (al: seq T), 
       (k<size al)%N -> 
       take k.+1 al = take k al ++ [nth d al k].
Proof.
intros.
revert k H; induction al; destruct k; simpl; intros; try lia.
rewrite take0. auto.
f_equal; auto.
Qed.

Lemma subtract_another:
  forall {t} n (i j k: 'I_n) (A R: 'M[ftype t]_n)
    (Hij: (i <= j)%N) 
    (Hkj: (k < j)%N)
    (k1: 'I_n)
    (Hk1: nat_of_ord k1 = S k),
    subtract_loop A R i j k1 = 
     BMINUS (subtract_loop A R i j k) (BMULT (R k i) (R k j)).
Proof.
intros.
assert (Datatypes.is_true (leq (S (S (nat_of_ord k))) n)).
  pose proof ltn_ord k1; lia.
assert (k1 = @Ordinal n (S k) H). apply ord_inj; auto.
subst k1.
unfold subtract_loop at 1.
rewrite (take_snoc i).
  2: (rewrite  size_ord_enum; pose proof ltn_ord k;  lia).
rewrite !map_cat.
simpl map.
rewrite fold_left_app; simpl; f_equal.
rewrite nth_ord_enum'. auto.
Qed.

(* END copied from iterative_methods/cholesky/verif_cholesky.v *)

Lemma cholesky_jik_upto_zero:
  forall t n (A: 'M[ftype t]_n) (zero: 'I_n), nat_of_ord zero=O -> cholesky_jik_upto zero (lshift1 zero) A A.
Proof.
intros i j; split; [ | split3]; simpl; try lia; auto.
Qed.

Lemma cholesky_jik_upto_newrow:
 forall t n (j: 'I_n) (A R: 'M[ftype t]_n),
  cholesky_jik_upto j (lshift1 j) A R ->
  cholesky_jik_upto (@Ordinal n 0 (leq_ltn_trans (leq0n j) (ltn_ord j)))
     (@Ordinal n.+1 (j.+1)%N (ltn_ord j)) A (update_mx R j j (BSQRT (subtract_loop A R j j j))).
Proof.
pose proof I.
intros.
intros i' j'.
destruct (H0 i' j') as [? [? [? ?]]]; clear H0.
split; [ | split3]; intros; try split; hnf; intros; try lia.
-
 clear H4. simpl in H0.
 destruct (Nat.eq_dec j' j).
 + apply ord_inj in e. subst j'. clear H1 H3. specialize (H2 (Logic.eq_refl _) Hij).
   unfold update_mx at 1. rewrite mxE.
   destruct (Nat.eq_dec _ _); [lia  |]. simpl.
   destruct H2.
   rewrite H1; [ |apply Hij]. f_equal.
   * unfold subtract_loop. f_equal.
     apply eq_in_subrange.
     intros. unfold update_mx. rewrite !mxE.
     repeat (destruct (Nat.eq_dec _ _)); try lia. auto.
   * unfold update_mx. rewrite !mxE.
     repeat (destruct (Nat.eq_dec _ _)); try lia. auto.
 + simpl in *. destruct (H1 ltac:(lia)); clear H1 H5. specialize (H4 ltac:(lia)). clear H2 H3.
   unfold update_mx at 1. rewrite mxE.
   repeat destruct (Nat.eq_dec _ _); try lia. simpl.
   rewrite H4. f_equal.
   * unfold subtract_loop. f_equal.
     apply eq_in_subrange.
     intros. unfold update_mx. rewrite !mxE.
     repeat destruct (Nat.eq_dec _ _); try lia; auto.
   * unfold update_mx. rewrite mxE.
     repeat destruct (Nat.eq_dec _ _); try lia; auto.
- subst j'. simpl in *.
  destruct (Nat.eq_dec i' j).
 + apply ord_inj in e. subst. unfold update_mx. rewrite !mxE.
   repeat destruct (Nat.eq_dec _ _); try lia; auto. simpl.
   f_equal.
   unfold subtract_loop. f_equal.
   apply eq_in_subrange.
   intros. rewrite !mxE.
   repeat destruct (Nat.eq_dec _ _); try lia; auto. 
 + unfold update_mx at 1. rewrite mxE.
   repeat destruct (Nat.eq_dec _ _); try lia; auto. 
   simpl.
   destruct (H1 ltac:(lia)). rewrite H6; auto.
   f_equal.
   unfold subtract_loop. f_equal.
   apply eq_in_subrange.
   intros. unfold update_mx. rewrite !mxE.
   repeat destruct (Nat.eq_dec _ _); try lia; auto.
- simpl in *; lia. 
- simpl in *. lia.
- unfold update_mx. rewrite !mxE. simpl in *.
   repeat destruct (Nat.eq_dec _ _); try lia; auto.
- unfold update_mx. rewrite !mxE. simpl in *. clear H5.
  repeat destruct (Nat.eq_dec _ _); try lia; apply H3; lia.
Qed.

(** Functional models of forward substitution and back substitution *)

Definition forward_subst_step {t: type} [n: nat] 
         (L: 'M[ftype t]_n) (x: 'cV[ftype t]_n) (i: 'I_n) 
     : 'cV_n  :=
   update_mx x i ord0
    (BDIV (fold_left BMINUS
           (map (fun j => BMULT (L i j) (x j ord0)) (take i (ord_enum n)))
           (x i ord0))
          (L i i)).

Definition forward_subst [t: type] [n]
         (L: 'M[ftype t]_n) (x: 'cV[ftype t]_n) : 'cV_n :=
  fold_left (forward_subst_step L) (ord_enum n) x.

Definition backward_subst_step {t: type} [n: nat]
         (U: 'M[ftype t]_n) (x: 'cV[ftype t]_n) (i: 'I_n) : 'cV_n :=
    update_mx x i ord0
      (BDIV (fold_left BMINUS 
              (map (fun j => BMULT (U i j) (x j ord0)) (drop (i+1) (ord_enum n)))
              (x i ord0))
         (U i i)).

Definition backward_subst {t: type} [n: nat]
         (U: 'M[ftype t]_n) (x: 'cV[ftype t]_n) : 'cV[ftype t]_n :=
     fold_left (backward_subst_step U) (rev (ord_enum n)) x.

(** * Definitions for manipulating triangular matrices *)

(** [joinLU n L U]   produces a matrix whose upper-triangle (including diagonal) matches U,
         and whose lower_triangle (excluding diagonal) matches L *)
Definition joinLU {T} [n] (L U : 'M[T]_n) : 'M[T]_n :=
 \matrix_(i,j) if (i<=j)%N then U i j else L i j.

Definition mirror_UT {T} [n] (U: 'M[T]_n) : 'M[T]_n :=
  joinLU U^T U.
(*
Inductive block_cholesky {t: type}: forall (n: Z) (A R: Z -> Z -> ftype t), Prop :=
| Block_cholesky_1: forall A R, A 0 0 = BSQRT(R 0 0) -> block_cholesky 1 A R
| Block_cholesky_plus: forall n1 n2 A R,
   block_cholesky n1 A R ->
   blocksolve A n b c B
*)
