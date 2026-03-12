(** * Dot Product Definitions and Properties

    This file develops the theory of dot products in three settings:
    floating-point arithmetic (with and without FMA), and real-number
    arithmetic.  The three treatments are connected by relational
    characterizations that make it straightforward to transfer
    accuracy bounds from the real model to the floating-point
    implementations.

    ** Overview of contents

    - [dotprod]: a generic, parameterised dot-product computed via
      [foldl] over a zipped pair of lists.  Specialised to
      - [dotprodF]  - IEEE floating-point (BMULT / BPLUS),
      - [fma_dotprod] - IEEE floating-point with fused multiply-add
        (BFMA), and
      - [dotprodR]   - real arithmetic (Rmult / Rplus).

    - Inductive relations that characterize the value produced by each
      variant:
      - [dot_prod_rel]     for [dotprodF],
      - [fma_dot_prod_rel] for [fma_dotprod],
      - [dotprod_any] / [dotprod_any']  for arbitrary reassociation /
        reordering of a floating-point dot product,
      - [R_dot_prod_rel]   for [dotprodR].

    - Key lemmas connecting implementations to their relations:
      - [dotprodF_rel_fold_right] - [dot_prod_rel] holds for
        [dotprodF].
      - [fma_dot_prod_rel_fold_right] - [fma_dot_prod_rel] holds for
        [fma_dotprod].
      - [dotprodR_rel] - [R_dot_prod_rel] holds for [dotprodR].
      - [dotprod_rel_dotprod_any] - every result of [dot_prod_rel]
        can be witnessed by [dotprod_any].

    - Bound lemmas for the real dot product:
      - [dotprodR_rel_bound'] - |⟨u,v⟩| ≤ n·a when each component
        has absolute value at most √a.
      - [dotprodR_rel_bound''] - same bound but for the dot product
         of absolute values ⟨|u|,|v|⟩.
      - [dot_prod_sum_rel_R_Rabs] - |⟨u,v⟩| ≤ ⟨|u|,|v|⟩.

    - Non-zero-detection lemmas ([Section NonZeroDP]):  when every
      entry of a vector has real value 0 the floating-point (and real)
      dot products are 0.
*)

From LAProof.accuracy_proofs Require Import preamble common float_acc_lems.
Require Import FunctionalExtensionality.
Require Import Permutation.

(** ** Generic dot product

    [dotprod mult plus zero v1 v2] computes the inner product of two 
    lists using the supplied binary operations and additive
    identity.  The result is obtained by zipping the two lists,
    multipltying pointwise, and summing with [foldl]. *)
    
Definition dotprod {A} (mult plus : A -> A -> A) (zero : A)
                   (v1 v2 : list A) : A :=
  foldl (Basics.flip plus) zero (map (uncurry mult) (zip v1 v2)).

(** If the left argument is [nil] the result is zero, regardless of
    the right argument. *)
    
Lemma dotprod_nil_l :
  forall A (l : list A) (mult plus : A -> A -> A) (zero : A),
    dotprod mult plus zero nil l = zero.
Proof. destruct l; auto. Qed.

(** If the right argument is [nil] the result is zero, regardless of
    the left argument. *)
    
Lemma dotprod_nil_r :
  forall A (l : list A) (mult plus : A -> A -> A) (zero : A),
    dotprod mult plus zero l nil = zero.
Proof. destruct l; auto. Qed.

(** When the right list is a singleton, the dot product reduces
    to a single multiplication. *)
    
Lemma dotprod_single :
  forall A (l : list A)
    (mult plus : A -> A -> A) (zero a2 : A)
    (Hpz : forall y, plus y zero = y)
    (Hmz : forall y, mult zero y = zero),
  let a1 := nth zero l 0 in
  dotprod mult plus zero l [a2] = mult a1 a2.
Proof.
  intros; simpl; destruct l.
  - rewrite dotprod_nil_l. subst a1. simpl; auto.
  - unfold dotprod. rewrite /= {2}/Basics.flip Hpz. destruct l; auto.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Floating-point dot product *)
(* ------------------------------------------------------------------ *)

Section DotProdFloat.
Context {NAN : FPCore.Nans} {t : type}.

(** [dotprodF v1 v2] is the standard left-to-right floating-point dot
    product using IEEE multiplication [BMULT] and addition [BPLUS],
    starting from the positive zero. *)
    
Definition dotprodF (v1 v2 : list (ftype t)) : ftype t :=
  dotprod BMULT BPLUS pos_zero v1 v2.

(** [dot_prod_rel l s] is the inductive relation that characterizes the
    value s obtained by computing the dot product of the list of
    pairs l in left-to-right order using IEEE arithmetic. *)
    
Inductive dot_prod_rel :
    list (ftype t * ftype t) -> ftype t -> Prop :=
| dot_prod_rel_nil  :
    dot_prod_rel nil pos_zero
| dot_prod_rel_cons :
    forall l (xy : ftype t * ftype t) s,
      dot_prod_rel l s ->
      dot_prod_rel (xy :: l)
                   (BPLUS (BMULT (fst xy) (snd xy)) s).

(** [dotprod_any' h v s] witnesses that s can be obtained as the
    floating-point dot product of the pairs in v by _any_
    parenthesisation of depth at most h, including arbitrary
    permutations of the summands (via [Dotprod_Any_perm]).  This
    relation supports accuracy analyses that do not depend on a
    particular evaluation order. *)
    
Inductive dotprod_any' :
    forall (h : nat) (v : list (ftype t * ftype t))
           (s : ftype t), Prop :=
| Dotprod_Any_1 :
    forall x,
      dotprod_any' O [x] (BMULT (fst x) (snd x))
| Dotprod_Any_split :
    forall n1 n2 al bl a b,
      dotprod_any' n1 al a ->
      dotprod_any' n2 bl b ->
      dotprod_any' (S (Nat.max n1 n2)) (al ++ bl) (BPLUS a b)
| Dotprod_Any_perm :
    forall n al bl s,
      Permutation al bl ->
      dotprod_any' n al s ->
      dotprod_any' n bl s.

(** [dotprod_any h v s] extends [dotprod_any'] to handle the empty
    list, where the dot product is positive zero. *)
    
Inductive dotprod_any :
    forall (h : nat) (v : list (ftype t * ftype t))
           (s : ftype t), Prop :=
| Dotprod_Any_None :
    dotprod_any O nil pos_zero
| Dotprod_Any_Some :
    forall n v s,
      dotprod_any' n v s ->
      dotprod_any n v s.

(** Every value related to a list by [dot_prod_rel] is (up to [feq])
    also witnessed by [dotprod_any], provided all pairwise products
    are finite.  This is the key lemma that bridges the sequential
    IEEE relation and the order-independent [dotprod_any] relation. *)
    
Lemma dotprod_rel_dotprod_any :
  forall (z : ftype t) (v : list (ftype t * ftype t)) s
    (Hz   : iszero z)
    (Hfin : Forall (fun xy =>
                Binary.is_finite (BMULT (fst xy) (snd xy))) v),
    dot_prod_rel v s ->
    exists s', feq s s' /\ dotprod_any (Nat.pred (size v)) v s'.
Proof.
  destruct v as [ | [x y] v]; intros * Hz Hfin H.
  - destruct z; try discriminate; clear Hfin.
    inversion H; clear H; subst;
      (eexists; split; [ | constructor]; reflexivity).
  - revert x y s z Hfin Hz H;
      induction v as [ | [x y] v]; simpl; intros.
    + inversion H; clear H; subst.
      inversion Hfin; clear Hfin; subst.
      rename H2 into Hfin. rename H1 into Hfin1.
      inversion H3; clear H3; subst.
      simpl in *.
      eexists.
      split; [ | constructor; constructor].
      simpl.
      apply BPLUS_0_r. apply strict_feq_refl; auto.
    + inversion Hfin; clear Hfin; subst.
      rename H3 into Hfin. rename H2 into Hfin1.
      inversion H; clear H; subst.
      specialize (IHv x y s0 z Hfin Hz H3).
      simpl in *.
      change (cons (x0, y0) (cons (x, y) v))
        with ([(x0, y0)] ++ cons (x, y) v).
      replace (S (size v)) with (S (Nat.max O (size v))) by lia.
      destruct IHv as [s1 [? ?]].
      eexists.
      inversion H0; clear H0; subst.
      simpl in H1.
      split.
      2:{ constructor 2.
          eapply Dotprod_Any_split; auto.
          apply Dotprod_Any_1.
          eassumption. }
      clear z Hz H3 H1.
      rewrite H; auto.
Qed.

(** [dot_prod_rel] characterizes [dotprodF]: the relation holds for
    the reversed zip of the two input lists. *)
    
Lemma dotprodF_rel_fold_right :
  forall (v1 v2 : list (ftype t)),
    dot_prod_rel (rev (zip v1 v2)) (dotprodF v1 v2).
Proof.
  intros v1 v2. unfold dotprodF, dotprod.
  rewrite -(revK (map _ (zip v1 v2))) foldl_rev -map_rev.
  induction (rev _) as [ | [x y] l]; constructor; auto.
Qed.

End DotProdFloat.

(* ------------------------------------------------------------------ *)
(** ** Floating-point dot product with FMA *)
(* ------------------------------------------------------------------ *)

Section DotProdFMA.
Context {NAN : FPCore.Nans} {t : type}.

(** [fma_dotprod v1 v2] computes the dot product o
    using IEEE fused multiply-add. *)
    
Definition fma_dotprod (v1 v2 : list (ftype t)) : ftype t :=
  foldl (fun s x12 => BFMA (fst x12) (snd x12) s)
        pos_zero (zip v1 v2).

(** [fma_dot_prod_rel l s] is the FMA analogue of [dot_prod_rel]:
    s is the value obtained by accumulating [BFMA] from the left
    over the pair list l. *)
    
Inductive fma_dot_prod_rel :
    list (ftype t * ftype t) -> ftype t -> Prop :=
| fma_dot_prod_rel_nil  :
    fma_dot_prod_rel nil (Zconst t 0)
| fma_dot_prod_rel_cons :
    forall l (xy : ftype t * ftype t) s,
      fma_dot_prod_rel l s ->
      fma_dot_prod_rel (xy :: l)
                       (BFMA (fst xy) (snd xy) s).

(** Note: there is no [fma_dotprod_any] analogue of [dotprod_any],
    because the FMA model is inherently sequential - it accumulates
    products one at a time into a single running sum and does not
    naturally support arbitrary reassociation. *)

(** [fma_dot_prod_rel] characterizes [fma_dotprod]: the relation holds
    for the reversed zip of the two input lists. *)
    
Lemma fma_dot_prod_rel_fold_right :
  forall (v1 v2 : list (ftype t)),
    fma_dot_prod_rel (rev (zip v1 v2)) (fma_dotprod v1 v2).
Proof.
  intros v1 v2.
  unfold fma_dotprod.
  rewrite -{2}(revK (zip v1 v2)) foldl_rev.
  induction (rev _).
  { simpl; auto. apply fma_dot_prod_rel_nil. }
  simpl. apply fma_dot_prod_rel_cons. auto.
Qed.

End DotProdFMA.

(* ------------------------------------------------------------------ *)
(** ** Real-number dot product *)
(* ------------------------------------------------------------------ *)

Section RealDotProd.

(** [dotprodR l1 l2] is the exact real dot product of l1 and l2,
    defined as an instance of the generic [dotprod] over ℝ. *)
    
Definition dotprodR (l1 l2 : seq R) : R :=
  dotprod Rmult Rplus 0%R l1 l2.

(** [R_dot_prod_rel l s] is the real analogue of [dot_prod_rel]:
    s is the value of the dot product of the pair list l in ℝ. *)
    
Inductive R_dot_prod_rel : list (R * R) -> R -> Prop :=
| R_dot_prod_rel_nil  :
    R_dot_prod_rel nil 0%R
| R_dot_prod_rel_cons :
    forall l xy s,
      R_dot_prod_rel l s ->
      R_dot_prod_rel (xy :: l) (fst xy * snd xy + s).

(** The value witnessed by [R_dot_prod_rel] is unique. *)

Lemma R_dot_prod_rel_eq :
  forall l a b,
    R_dot_prod_rel l a ->
    R_dot_prod_rel l b ->
    a = b.
Proof.
  induction l.
  { intros a b Ha Hb. inversion Ha; inversion Hb; auto. }
  intros a0 b0 Ha Hb; inversion Ha; inversion Hb; subst; f_equal.
  apply IHl; auto.
Qed.

(** [Rabsp p] replaces each component of the pair p by its absolute
    value.  It is used to build the absolute-value dot product that bounds
    |⟨u, v⟩|. *)
    
Definition Rabsp (p : R * R) : R * R :=
  (Rabs (fst p), Rabs (snd p)).

(** [FR2 x12] converts a pair of floating-point values to a pair of
    real numbers using [FT2R]. *)
    
Definition FR2 {t : type} (x12 : ftype t * ftype t) : R * R :=
  (FT2R (fst x12), FT2R (snd x12)).

(** Convenience rewriting rule: (FT2R a, FT2R a0) = FR2 (a, a0). *)

Lemma FT2R_FR2 t :
  forall a a0 : ftype t, (FT2R a, FT2R a0) = FR2 (a, a0).
Proof. reflexivity. Qed.

(** [sum_fold l] sums the elements of l using [foldr]. *)

Definition sum_fold (l : list R) : R := foldr Rplus 0%R l.

(** [dotprodR nil u = 0] for any u. *)

Lemma dotprodR_nil_l u : dotprodR nil u = 0.
Proof. intros; apply dotprod_nil_l. Qed.

(** [dotprodR u nil = 0] for any u. *)

Lemma dotprodR_nil_r u : dotprodR u nil = 0.
Proof. intros; apply dotprod_nil_r. Qed.

(** [Basics.flip Rplus] is propositionally equal to [Rplus] because
    real addition is commutative. *)
    
Lemma flip_Rplus : Basics.flip Rplus = Rplus.
Proof.
  rewrite /Basics.flip;
  do 2 (apply FunctionalExtensionality.functional_extensionality; intro); lra.
Qed.

Lemma Rplus_rewrite : (fun x y => x + y)%Re = Rplus.
Proof. reflexivity. Qed.

(** The sum [sum_fold l] equals [sum_fold (rev l)] because real
    addition is commutative and associative. *)
    
Lemma sum_rev l : sum_fold l = sum_fold (rev l).
Proof.
  rewrite /sum_fold -foldl_rev foldl_foldr.
  f_equal;
    do 2 (apply FunctionalExtensionality.functional_extensionality; intro); lra.
  hnf; intros; lra.
  hnf; intros; lra.
Qed.

(** [R_dot_prod_rel] characterizes [dotprodR]: for any v1 and v2,
    [R_dot_prod_rel (zip v1 v2) (dotprodR v1 v2)]. *)
    
Lemma dotprodR_rel :
  forall (v1 v2 : list R),
    R_dot_prod_rel (zip v1 v2) (dotprodR v1 v2).
Proof.
  intros; unfold dotprodR, dotprod.
  induction (zip v1 v2).
  { simpl. apply R_dot_prod_rel_nil. }
  evar (z : R).
  replace (foldl _ _ _) with z.
  apply R_dot_prod_rel_cons; apply IHl.
  subst z.
  clear.
  rewrite !foldl_foldr; [ | compute; intros; lra..].
  destruct a as [x y]; simpl.
  rewrite Rplus_comm //.
Qed.

(** The value of the real dot product relation is injective in s. *)

Lemma dotprodR_rel_inj :
  forall l s1 s2,
    R_dot_prod_rel l s1 ->
    R_dot_prod_rel l s2 ->
    s1 = s2.
Proof.
  induction l; intros;
  inversion H; clear H; inversion H0; clear H1; subst; f_equal; auto.
Qed.

(** Reversing the second argument is equivalent to reversing the
    first, when both lists have the same length. *)
    
Lemma dotprodR_rev :
  forall (v1 v2 : list R),
    size v1 = size v2 ->
    dotprodR v1 (rev v2) = dotprodR (rev v1) v2.
Proof.
  intros.
  rewrite /dotprodR /dotprod
          -{1}(revK v1) -rev_zip ?size_rev //.
  rewrite {2}flip_Rplus map_rev foldl_rev foldl_foldr //;
    compute; intros; lra.
Qed.

(** Zipping then mapping [FR2] is the same as mapping [FT2R]
    componentwise before zipping. *)
    
Lemma map_FR2_zip :
  forall {t} (v1 v2 : seq (ftype t)),
    map FR2 (zip v1 v2) = zip (map FT2R v1) (map FT2R v2).
Proof.
  induction v1; destruct v2; simpl; f_equal; auto.
Qed.

(** Zipping then mapping [Rabsp] is the same as mapping [Rabs]
    componentwise before zipping. *)
    
Lemma map_Rabsp_zip :
  forall (v1 v2 : seq R),
    map Rabsp (zip v1 v2) = zip (map Rabs v1) (map Rabs v2).
Proof.
  induction v1; destruct v2; simpl; f_equal; auto.
Qed.

(** The real dot product of the real images of v1 and v2 satisfies
    [R_dot_prod_rel] on the reversed [FR2]-mapped zip, and equals the
    [sum_fold] of the pointwise products. *)
    
Lemma R_dot_prod_rel_fold_right t :
  forall (v1 v2 : list (ftype t)),
    size v1 = size v2 ->
    let prods :=
      map (uncurry Rmult) (map FR2 (zip v1 v2)) in
    R_dot_prod_rel (rev (map FR2 (zip v1 v2))) (sum_fold prods).
Proof.
  intros.
  subst prods.
  rewrite map_FR2_zip.
  move :(dotprodR_rel (rev (map FT2R v1)) (rev (map FT2R v2))).
  rewrite dotprodR_rev ?size_rev ?size_map // revK
          /sum_fold /dotprodR /dotprod
          foldl_foldr //.
  2,3: compute; intros; lra.
  rewrite -rev_zip ?size_map ?flip_Rplus //.
Qed.

(** Variant of [R_dot_prod_rel_fold_right] expressing the sum as
    [dotprodR (map FT2R v1) (map FT2R v2)]. *)
    
Lemma R_dot_prod_rel_fold_right' t :
  forall (v1 v2 : list (ftype t)),
    size v1 = size v2 ->
    let prods :=
      map (uncurry Rmult) (map FR2 (zip v1 v2)) in
    R_dot_prod_rel (rev (map FR2 (zip v1 v2)))
                   (dotprodR (map FT2R v1) (map FT2R v2)).
Proof.
  intros.
  replace (dotprodR _ _) with (sum_fold prods).
  apply R_dot_prod_rel_fold_right; auto.
  rewrite sum_rev /sum_fold /dotprodR /dotprod
          -foldl_rev revK /prods map_FR2_zip //.
Qed.

(** [R_dot_prod_rel] for the absolute-value dot product: the reversed zip
    of [Rabsp ∘ FR2] satisfies the relation with value [sum_fold prods]. *)
    
Lemma R_dot_prod_rel_fold_right_Rabs t :
  forall (v1 v2 : list (ftype t)),
    size v1 = size v2 ->
    let prods :=
      map (uncurry Rmult) (map Rabsp (map FR2 (zip v1 v2))) in
    R_dot_prod_rel (rev (map Rabsp (map FR2 (zip v1 v2))))
                   (sum_fold prods).
Proof.
  intros.
  subst prods.
  rewrite map_FR2_zip map_Rabsp_zip.
  move :(dotprodR_rel (rev (map Rabs (map FT2R v1)))
                      (rev (map Rabs (map FT2R v2)))).
  rewrite dotprodR_rev ?size_rev ?size_map // revK
          /sum_fold /dotprodR /dotprod
          foldl_foldr //.
  2,3: compute; intros; lra.
  rewrite -rev_zip ?size_map ?flip_Rplus //.
Qed.

(** Variant of [R_dot_prod_rel_fold_right_Rabs] expressing the sum as
    [dotprodR (map Rabs (map FT2R v1)) (map Rabs (map FT2R v2))]. *)
    
Lemma R_dot_prod_rel_fold_right_Rabs' t :
  forall (v1 v2 : list (ftype t)),
    size v1 = size v2 ->
    let prods :=
      map (uncurry Rmult) (map Rabsp (map FR2 (zip v1 v2))) in
    R_dot_prod_rel (rev (map Rabsp (map FR2 (zip v1 v2))))
                   (dotprodR (map Rabs (map FT2R v1))
                             (map Rabs (map FT2R v2))).
Proof.
  intros.
  replace (dotprodR _ _) with (sum_fold prods).
  apply R_dot_prod_rel_fold_right_Rabs; auto.
  rewrite sum_rev /sum_fold /dotprodR /dotprod
          -foldl_rev revK /prods map_FR2_zip map_Rabsp_zip //.
Qed.

(** If the pair list is a singleton a, then the dot product
    relation forces [rs = fst a * snd a]. *)
    
Lemma R_dot_prod_rel_single rs a :
  R_dot_prod_rel [:: a] rs -> rs = fst a * snd a.
Proof.
  intros.
  inversion H.
  inversion H3; subst.
  apply Rplus_0_r.
Qed.

(** The converse of [R_dot_prod_rel_single]: the singleton relation
    holds with value [fst a * snd a]. *)
    
Lemma R_dot_prod_rel_single' a :
  R_dot_prod_rel [:: a] (fst a * snd a).
Proof.
  replace (fst a * snd a)%Re with (fst a * snd a + 0)%Re
    by apply Rplus_0_r.
  apply R_dot_prod_rel_cons; apply R_dot_prod_rel_nil.
Qed.

(** When all pairs in [l] have been replaced by their absolute values
    (via [Rabsp]), the resulting sum is non-negative, so [Rabs s = s]. *)
    
Lemma R_dot_prod_rel_Rabs_eq :
  forall l s,
    R_dot_prod_rel (map Rabsp l) s -> Rabs s = s.
Proof.
  induction l; intros; inversion H; clear H; subst.
  apply Rabs_R0.
  unfold Rabsp. destruct a; simpl.
  replace (Rabs (Rabs r * Rabs r0 + s0))%Re
    with  (Rabs r * Rabs r0 + s0)%Re;
    try nra.
  symmetry.
  rewrite Rabs_pos_eq; try nra.
  apply Rplus_le_le_0_compat.
  apply Rmult_le_pos; apply Rabs_pos.
  rewrite <- IHl; try apply Rabs_pos; auto.
Qed.

(** The absolute value of the exact dot product is bounded by the
    absolute-value dot product: [|⟨u, v⟩| ≤ ⟨|u|, |v|⟩]. *)
    
Lemma dot_prod_sum_rel_R_Rabs :
  forall l s1 s2,
    R_dot_prod_rel l s1 ->
    R_dot_prod_rel (map Rabsp l) s2 ->
    Rabs s1 <= Rabs s2.
Proof.
  induction l.
  { intros.
    inversion H. inversion H0. nra. }
  intros.
  inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  unfold Rabsp; destruct a; simpl.
  eapply Rle_trans; [apply Rabs_triang |].
  replace (Rabs (Rabs r * Rabs r0 + s0))%Re
    with  (Rabs r * Rabs r0 + s0)%Re.
  eapply Rplus_le_compat; try nra.
  rewrite Rabs_mult; nra.
  rewrite <- (R_dot_prod_rel_Rabs_eq l); auto.
  symmetry.
  rewrite Rabs_pos_eq; try nra.
  apply Rplus_le_le_0_compat.
  apply Rmult_le_pos; apply Rabs_pos.
  rewrite <- (R_dot_prod_rel_Rabs_eq l); auto.
  apply Rabs_pos.
Qed.

(** Scaling the left factor of every pair by a scalar << a >> scales the
    dot product by a.  Formally, if [R_dot_prod_rel (zip u v) r]
    then [R_dot_prod_rel (zip (map (Rmult a) u) v) (a * r)]. *)
    
Lemma dot_prod_zip_map_Rmult a u v r :
  size u = size v ->
  R_dot_prod_rel (zip u v) r ->
  R_dot_prod_rel (zip (map (Rmult a) u) v) (a * r).
Proof.
  intros.
  move :(dotprodR_rel u v) => H1.
  move :(dotprodR_rel_inj _ _ _ H0 H1) => H2.
  subst r. clear H0 H1.
  move :(dotprodR_rel (map (Rmult a) u) v) => H3.
  replace (Rmult a (dotprodR u v)) with (dotprodR (map (Rmult a) u) v); auto.
  clear - H.
  unfold dotprodR, dotprod.
  rewrite !foldl_foldr.
  2,3,4,5: compute; intros; lra.
  revert v H; induction u; destruct v; intros; inversion H; clear H; subst;
    simpl.
  compute; lra.
  rewrite IHu; auto.
  rewrite {1 3}/Basics.flip. lra.
Qed.

(** Given a floating-point dot-product computation witnessed by
    [dot_prod_rel], there exists a real value rp related to the
    real-image list by [R_dot_prod_rel]. *)
    
Lemma dotprod_rel_R_exists {NAN : FPCore.Nans} {t : type} :
  forall (l : list (ftype t * ftype t)) (fp : ftype t),
    dot_prod_rel l fp ->
    exists rp, R_dot_prod_rel (map FR2 l) rp.
Proof.
  intros ?. induction l.
  { simpl; exists 0. apply R_dot_prod_rel_nil. }
  intros ? H2. inversion H2; subst.
  destruct (IHl s H3) as (rs & Hrs); clear IHl.
  exists (FT2R (fst a) * FT2R (snd a) + rs); simpl.
  apply R_dot_prod_rel_cons; auto.
Qed.

(** FMA analogue of [dotprod_rel_R_exists]: given a computation
    witnessed by [fma_dot_prod_rel], there exists a real value related
    to the real-image list. *)
    
Lemma dotprod_rel_R_exists_fma {NAN : FPCore.Nans} {t : type} :
  forall (l : list (ftype t * ftype t)) (fp : ftype t),
    fma_dot_prod_rel l fp ->
    exists rp, R_dot_prod_rel (map FR2 l) rp.
Proof.
  intros ?. induction l.
  { simpl; exists 0. apply R_dot_prod_rel_nil. }
  intros ? H2. inversion H2; subst.
  destruct (IHl s H3) as (rs & Hrs); clear IHl.
  exists (FT2R (fst a) * FT2R (snd a) + rs); simpl.
  apply R_dot_prod_rel_cons; auto.
Qed.

(** FMA analogue for the absolute-value dot product: given
    [fma_dot_prod_rel l fp], there exists a real value related to
    [map Rabsp (map FR2 l)]. *)
    
Lemma sum_rel_R_abs_exists_fma {NAN : FPCore.Nans} {t : type} :
  forall (l : list (ftype t * ftype t)) (fp : ftype t),
    fma_dot_prod_rel l fp ->
    exists rp, R_dot_prod_rel (map Rabsp (map FR2 l)) rp.
Proof.
  intros ?. induction l.
  { simpl; exists 0. apply R_dot_prod_rel_nil. }
  intros ? H2. inversion H2; subst.
  destruct (IHl s H3) as (rs & Hrs); clear IHl.
  exists (Rabs (FT2R (fst a)) * Rabs (FT2R (snd a)) + rs); simpl.
  apply R_dot_prod_rel_cons; auto.
Qed.

(** Component-wise bound on the real dot product:
    if every component of the pairs in [l] has absolute value at most
    [√a], then [|⟨u, v⟩| ≤ n · a], where [n = length l].
    This is a standard building block for rounding error bounds. *)
    
Lemma dotprodR_rel_bound' :
  forall (t : type) (l : list (ftype t * ftype t)) (rp a : R)
    (Ha  : 0 <= a)
    (Hrp : R_dot_prod_rel (map FR2 l) rp)
    (Hin : forall x, In x l ->
             Rabs (FT2R (fst x)) <= sqrt a /\
             Rabs (FT2R (snd x)) <= sqrt a),
    Rabs rp <= INR (length l) * a.
Proof.
  induction l; intros.
  { inversion Hrp; subst; simpl; rewrite Rabs_R0; nra. }
  inversion Hrp; subst.
  eapply Rle_trans; [apply Rabs_triang |].
  eapply Rle_trans; [apply Rplus_le_compat |].
  rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos.
  apply Hin; simpl; auto.
  apply Hin; simpl; auto.
  apply IHl; auto;
    [ apply Ha | intros; apply Hin; simpl; auto].
  rewrite sqrt_def; auto. apply Req_le;
  replace (length (a :: l)) with (S (length l)) by auto.
  rewrite S_INR; nra.
Qed.

(** Variant of [dotprodR_rel_bound'] for the absolute-value
    relation: if [R_dot_prod_rel (map Rabsp (map FR2 l)) rs_abs] and
    every component has absolute value at most √a, then
    rs_abs ≤ n · a. *)
    
Lemma dotprodR_rel_bound'' :
  forall (t : type) (l : list (ftype t * ftype t)) (rs_abs a : R)
    (Ha  : 0 <= a)
    (Hrp : R_dot_prod_rel (map Rabsp (map FR2 l)) rs_abs)
    (Hin : forall x, In x l ->
             Rabs (FT2R (fst x)) <= sqrt a /\
             Rabs (FT2R (snd x)) <= sqrt a),
    rs_abs <= INR (length l) * a.
Proof.
  induction l; intros; inversion Hrp; clear Hrp; subst.
  compute; nra.
  eapply Rle_trans; [apply Rplus_le_compat |].
  apply Rmult_le_compat;
    [ destruct a; simpl; apply Rabs_pos
    | destruct a; simpl; apply Rabs_pos | | ].
  apply Hin; simpl; auto.
  apply Hin; simpl; auto.
  apply IHl; auto;
    [ apply Ha | intros; apply Hin; simpl; auto].
  rewrite sqrt_def; auto. apply Req_le;
  replace (length (a :: l)) with (S (length l)) by auto.
  rewrite S_INR; nra.
Qed.

End RealDotProd.

(* ------------------------------------------------------------------ *)
(** ** Non-zero detection for dot products *)
(* ------------------------------------------------------------------ *)

Section NonZeroDP.
Context {NAN : FPCore.Nans} {t : type}.

Variables (v1 v2 : list (ftype t)).
Hypothesis (Hlen : size v1 = size v2).

Notation v1R := (map FT2R v1).

(** [Req_bool] and the boolean equality [eq_op] coincide on ℝ. *)

Lemma Req_eq : forall x y, Req_bool x y = eq_op x y.
Proof.
  intros.
  destruct (Req_bool_spec x y); symmetry; apply /eqP; auto.
Qed.

(** If every component of [v1] has real value 0 (i.e. [nnzR v1R = 0]),
    and the IEEE dot product [fp] is finite, then [FT2R fp = 0].
    This justifies early exit when the first operand is the zero
    vector. *)
    
Lemma dot_prod_rel_nnzR :
  forall (fp : ftype t)
    (Hfp  : dot_prod_rel (zip v1 v2) fp)
    (Hfin : Binary.is_finite fp = true),
    nnzR v1R == 0%nat -> FT2R fp = 0.
Proof.
  Print nnzR.
  intros.
  rewrite nnzR_lemma in H.
  revert H Hfp Hlen Hfin. revert v2 fp.
  induction v1; intros. 
  - destruct v2; try discriminate; inversion Hfp; auto.
  - inversion Hfp; subst. 
    rewrite /pos_zero /Zconst  => //=.
    destruct xy => //=.
    simpl BPLUS in Hfin, Hfp.
    destruct v2 as [  | v2a v2r]; [discriminate |].
    inversion H0; clear H0; subst.
    move :H => /= /andP [H H0].
    move : (BPLUS_correct _ _ Hfin) => [[H2 H3] H4].
    rewrite {}H4.
    have Hs: FT2R s = 0 by (apply (IHl v2r) => //; auto).
    rewrite Hs Rplus_0_r.
    have Ha:  FT2R a = 0 by move: H => /eqP //.
    rewrite (proj2 (BMULT_correct _ _ H2)).
    rewrite Ha Rmult_0_l !Generic_fmt.round_0 //. 
Qed.

(** FMA analogue of [dot_prod_rel_nnzR]: when [nnzR v1R = 0] and the
    FMA dot product is finite, [FT2R fp = 0]. *)
    
Lemma fma_dot_prod_rel_nnzR :
  forall (fp : ftype t)
    (Hfp  : fma_dot_prod_rel (zip v1 v2) fp)
    (Hfin : Binary.is_finite fp = true),
    nnzR v1R == 0%nat -> FT2R fp = 0.
Proof.
  intros.
  rewrite nnzR_lemma in H.
  move : v2 fp H Hfp Hlen Hfin.
  clear Hlen.
  induction v1; destruct v0; intros; inversion Hlen; clear Hlen.
  - inversion Hfp; auto.
  - inversion Hfp; clear Hfp; subst.
    rewrite /Zconst => //=.
    move :H => /= /andP [H8 H9].
    move : (BFMA_correct _ _ _ Hfin) => /= [[H2 [H3 H6]] H7].
    rewrite H7.
    rewrite (IHl _ _ H9 H4); auto.
    move :H8 => /eqP => H8.
    rewrite -H8.
    rewrite Rplus_0_r Rmult_0_l !Generic_fmt.round_0 //.
Qed.

(** Real analogue: when [nnzR v1R = 0], the real dot product [rp]
    obtained via [R_dot_prod_rel (map FR2 (zip v1 v2)) rp] is 0. *)
    
Lemma R_dot_prod_rel_nnzR :
  forall (rp : R)
    (Hrp : R_dot_prod_rel (map FR2 (zip v1 v2)) rp),
    nnzR v1R == 0%nat -> rp = 0.
Proof.
  intros ? ? H.
  rewrite nnzR_lemma in H.
  revert v2 rp H Hrp Hlen.
  induction v1; intros.
  - destruct v2; try discriminate; auto.
    inversion Hrp; auto.
  - destruct v2; try discriminate; auto.
    inversion Hrp; subst.
    unfold FR2, fst, snd.
    move :H => /= /andP [H H0].
    move :H => /eqP H.
    simpl in Hlen.
    rewrite -H Rmult_0_l.
    rewrite (IHl _ _ H0 H3). lra. lia.
Qed.

(** Absolute-value dot product analogue of [R_dot_prod_rel_nnzR]:
    when [nnzR v1R = 0], the absolute-value sum [rp_abs] is 0. *)
    
Lemma R_dot_prod_rel_nnzR_abs :
  forall (rp_abs : R)
    (Hra : R_dot_prod_rel (map Rabsp (map FR2 (zip v1 v2))) rp_abs),
    nnzR v1R == 0%nat -> rp_abs = 0.
Proof.
  intros ? ? H.
  rewrite nnzR_lemma in H.
  revert H Hra Hlen. revert v2 rp_abs.
  induction v1; intros.
  - simpl in *. inversion Hra. auto.
    destruct v2; try discriminate; auto.
  - destruct v2; try discriminate.
    inversion Hra; subst.
    unfold FR2, Rabsp, fst, snd.
    move :H => /= /andP [H H0].
    move :H => /eqP H.
    simpl in Hlen.
    rewrite -H Rabs_R0 Rmult_0_l (IHl _ _ H0 H3).
    lra. lia.
Qed.

End NonZeroDP.