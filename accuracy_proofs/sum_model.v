(** * Floating-Point Summation: Functional Models and Equivalences

    This file defines and relates several functional models for floating-point
    summation of lists. It provides both real-valued and floating-point
    relational specifications of summation, as well as a non-deterministic
    "any-order" floating-point summation predicate. The key contributions are:

    - [sum_rel]: A general inductive relation specifying summation over a list
      given a default element and a binary operation. Instantiated to both
      real ([sum_rel_R]) and floating-point ([sum_rel_Ft]) arithmetic.

    - [sum_any'], [sum_any]: An inductive predicate capturing floating-point
      summation in _any_ order and _any_ binary tree structure, modulo
      permutation. This is useful for reasoning about implementations that
      reorder or restructure summation for efficiency.

    - [sumR]: A fold-based functional definition of real summation, shown
      equivalent to [sum_rel_R].

    - [sumF]: A fold-based functional definition of floating-point summation,
      shown equivalent to [sum_rel_Ft].

    Key lemmas include:

    - [sum_rel_sum_any]: Every [sum_rel] summation can be realized as a
      [sum_any] summation (up to floating-point equality [feq]).

    - [sum_rel_R_abs], [sum_rel_R_Rabs]: Bounds on the absolute value of a
      real sum in terms of the sum of absolute values of its elements.

    - [sum_rel_bound], [sum_rel_bound'], [sum_rel_bound'']: Uniform bounds
      on the magnitude of a real sum given elementwise bounds.

    - [sum_rel_R_permute], [sumR_permute]: Summation is invariant under
      permutation of the input list.

    - [subtract_loop_sum_any]: The subtraction loop idiom (used in, e.g.,
      Cholesky decomposition implementations) can be related to [sum_any],
      enabling accuracy theorems for [sum_rel] to transfer to subtraction loops.
*)

From LAProof.accuracy_proofs Require Import preamble common float_acc_lems.
From Stdlib Require Import Permutation.

(** ** General Summation Relation

    [sum_rel default sum_op l s] holds when << s >> is the result of folding
    [sum_op] over the list << l >> from the right, starting from << default >>.
    The empty list yields << default >>, and a cons << a :: l >> yields
    [sum_op a s] where << s >> is the sum of << l >>. *)
    
Inductive sum_rel {A : Type} (default : A) (sum_op : A -> A -> A)
    : list A -> A -> Prop :=
  | sum_rel_nil  : sum_rel default sum_op [] default
  | sum_rel_cons : forall l a s,
      sum_rel default sum_op l s ->
      sum_rel default sum_op (a :: l) (sum_op a s).

(** [sum_rel_R] is [sum_rel] instantiated to real-number addition. *)

Definition sum_rel_R := @sum_rel R 0%R Rplus.

(** ** Any-Order Floating-Point Summation

    [sum_any' h v s] captures the idea that a list << v >> of floating-point
    values can be summed in _any_ binary tree structure of depth at most << h >>,
    up to reordering. The constructors are:

    - [Sum_Any_1]: A singleton list trivially sums to its element.
    - [Sum_Any_split]: Two sublists can be summed independently and their
      results combined with [BPLUS].
    - [Sum_Any_perm]: The summation result is invariant under permutation
      of the input list. *)
      
Inductive sum_any' {NAN : FPCore.Nans} {t} :
    forall (h : nat) (v : list (ftype t)) (s : ftype t), Prop :=
  | Sum_Any_1     : forall x,
      sum_any' O [x] x
  | Sum_Any_split : forall n1 n2 al bl a b,
      sum_any' n1 al a ->
      sum_any' n2 bl b ->
      sum_any' (S (Nat.max n1 n2)) (al ++ bl) (BPLUS a b)
  | Sum_Any_perm  : forall n al bl s,
      Permutation al bl ->
      sum_any' n al s ->
      sum_any' n bl s.

(** [sum_any h v s] extends [sum_any'] to handle the empty list, which sums
    to << pos_zero >>. *)
    
Inductive sum_any {NAN : FPCore.Nans} {t : type} :
    forall (h : nat) (v : list (ftype t)) (s : ftype t), Prop :=
  | Sum_Any_None : sum_any O nil pos_zero
  | Sum_Any_Some : forall n v s,
      sum_any' n v s ->
      sum_any n v s.

(** ** Equivalence Between [sum_rel] and [sum_any]

    Every [sum_rel] floating-point summation (starting from a zero value)
    can be realized as a [sum_any] summation, up to floating-point equality.
    The height of the [sum_any] tree is << Nat.pred (size v) >>. *)
    
Lemma sum_rel_sum_any :
  forall {NAN : FPCore.Nans} {t} z (v : list (ftype t)) s
         (Hz : iszero z),
    sum_rel z BPLUS v s ->
    exists s', feq s s' /\ sum_any (Nat.pred (size v)) v s'.
Proof.
  destruct v; intros.
  - (* empty list *)
    destruct z; try discriminate; clear Hz;
    inversion H; clear H; subst;
    (eexists; split; [ | constructor]; reflexivity).
  - (* non-empty list *)
    revert f s z Hz H; induction v; simpl; intros.
    + (* singleton list *)
      inversion H; clear H; subst.
      inversion H3; clear H3; subst.
      destruct s0; try discriminate.
      destruct s;
        (eexists; split; [ | constructor; constructor];
         destruct f; try reflexivity;
         destruct s; reflexivity).
    + (* cons case *)
      inversion H; clear H; subst.
      specialize (IHv a s0 z Hz H3).
      change (cons f (cons a v)) with ([f] ++ cons a v).
      replace (S (size v)) with (S (Nat.max O (size v))) by lia.
      destruct IHv as [s1 [Hfeq Hany]].
      eexists.
      inversion Hany; clear Hany; subst.
      simpl in H.
      split.
      2: { constructor 2.
           eapply Sum_Any_split; auto.
           apply Sum_Any_1.
           eassumption. }
      clear z Hz H3 H.
      rewrite Hfeq; auto.
Qed.

(** ** Bounds via Absolute Value Summation *)

(** A real sum is bounded above by the sum of absolute values of its
    elements. *)
    
Lemma sum_rel_R_abs :
  forall l s1 s2,
    sum_rel_R l s1 ->
    sum_rel_R (map Rabs l) s2 ->
    s1 <= s2.
Proof.
  induction l.
  - intros s1 s2 H1 H2.
    inversion H1; inversion H2; nra.
  - intros s1 s2 H1 H2.
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    eapply Rplus_le_compat; [apply Rle_abs |].
    fold sum_rel_R in H4, H3.
    apply IHl; auto.
Qed.

(** The sum of absolute values is non-negative. *)

Lemma sum_rel_R_Rabs_pos :
  forall l s,
    sum_rel_R (map Rabs l) s ->
    0 <= s.
Proof.
  induction l.
  - intros s H.
    inversion H; compute; nra.
  - intros s H.
    inversion H; subst; clear H.
    fold sum_rel_R in H3.
    specialize (IHl s0 H3).
    apply Rplus_le_le_0_compat; auto;
      apply Rabs_pos.
Qed.

(** The sum of absolute values equals its own absolute value (i.e., it is
    non-negative, so [Rabs s = s]). *)
    
Lemma sum_rel_R_Rabs_eq :
  forall l s,
    sum_rel_R (map Rabs l) s ->
    Rabs s = s.
Proof.
  induction l.
  - intros s H.
    inversion H.
    apply Rabs_R0.
  - intros s H.
    inversion H; subst; clear H.
    replace (Rabs (Rabs a + s0)) with (Rabs a + s0); try nra.
    symmetry.
    rewrite Rabs_pos_eq; try nra.
    apply Rplus_le_le_0_compat.
    + apply Rabs_pos.
    + eapply Rle_trans with (Rabs s0).
      * apply Rabs_pos.
      * eapply Req_le.
        fold sum_rel_R in H3.
        apply IHl; auto.
Qed.

(** The absolute value of any real sum is bounded by the sum of absolute
    values: [Rabs s1 <= Rabs s2] when << s2 >> is the sum of [Rabs] applied
    elementwise to << l >>. *)
    
Lemma sum_rel_R_Rabs :
  forall l s1 s2,
    sum_rel_R l s1 ->
    sum_rel_R (map Rabs l) s2 ->
    Rabs s1 <= Rabs s2.
Proof.
  induction l.
  - intros s1 s2 H1 H2.
    inversion H1; inversion H2; nra.
  - intros s1 s2 H1 H2.
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    fold sum_rel_R in H4, H3.
    eapply Rle_trans; [apply Rabs_triang |].
    replace (Rabs (Rabs a + s0)) with (Rabs a + s0).
    + eapply Rplus_le_compat; try nra.
      eapply Rle_trans with (Rabs s0).
      * apply IHl; auto.
      * apply Req_le.
        eapply sum_rel_R_Rabs_eq; apply H3.
    + symmetry.
      rewrite Rabs_pos_eq; try nra.
      apply Rplus_le_le_0_compat.
      * apply Rabs_pos.
      * eapply Rle_trans with (Rabs s0).
        -- apply Rabs_pos.
        -- apply Req_le.
           eapply sum_rel_R_Rabs_eq; apply H3.
Qed.

(** ** Singleton Summation Lemmas *)

(** A [sum_rel_R] derivation for a singleton list determines the sum uniquely. *)

Lemma sum_rel_R_single :
  forall (a : R) (fs : R),
    sum_rel_R [a] fs ->
    fs = a.
Proof.
  intros a fs H.
  inversion H; subst; auto.
  inversion H3; subst.
  apply Rplus_0_r.
Qed.

(** A real value is the [sum_rel_R] of its own singleton list. *)

Lemma sum_rel_R_single' :
  forall (a : R),
    sum_rel_R [a] a.
Proof.
  intros a.
  unfold sum_rel_R.
  replace a with (a + 0) at 2 by nra.
  apply sum_rel_cons.
  apply sum_rel_nil.
Qed.

(** ** Permutation Invariance *)

(** Inserting an element into an arbitrary position in the middle of a
    split list preserves the [sum_rel_R] sum (with the element added). *)
    
Lemma sum_rel_R_app_cons :
  forall l' l'' a s,
    sum_rel_R (l' ++ l'') s ->
    sum_rel_R (l' ++ a :: l'') (a + s).
Proof.
  induction l'; simpl.
  - intros l'' a s H.
    apply sum_rel_cons; auto.
  - intros l'' a0 s H.
    inversion H; subst; clear H.
    specialize (IHl' l'' a0 s0 H3).
    replace (a0 + (a + s0)) with (a + (a0 + s0)) by nra.
    apply sum_rel_cons; auto.
Qed.


(** [sum_rel_R] is invariant under list permutation. *)

Lemma sum_rel_R_permute :
  forall (l l0 : list R)
         (Hper : Permutation l l0)
         (rs : R)
         (Hrs : sum_rel_R l rs),
    sum_rel_R l0 rs.
Proof.
  intros l.
  induction l.
  - intros l0 Hper rs Hrs.
    inversion Hrs; subst.
    apply Permutation_nil in Hper; subst; simpl; auto.
  - intros l0 Hper rs Hrs.
    apply Permutation_sym in Hper.
    pose proof Permutation_vs_cons_inv Hper as Hinv.
    destruct Hinv as (l' & l'' & Heq); subst.
    apply Permutation_sym in Hper.
    pose proof (@Permutation_cons_app_inv R l l' l'' a Hper) as Hperm'.
    inversion Hrs; subst.
    fold sum_rel_R in H2.
    specialize (IHl (l' ++ l'') Hperm' s H2).
    clear Hrs.
    apply sum_rel_R_app_cons; auto.
Qed.

(** [sum_rel_R] over mapped floating-point values is invariant under
    permutation of the floating-point list. *)
    
Lemma sum_rel_R_permute_t :
  forall (t : type) (l l0 : list (ftype t))
         (Hper : Permutation l l0)
         (rs : R)
         (Hrs : sum_rel_R (map FT2R l) rs),
    sum_rel_R (map FT2R l0) rs.
Proof.
  intros t l l0 Hper rs Hrs.
  apply sum_rel_R_permute with (map FT2R l); auto.
  apply Permutation_map; auto.
Qed.

(** ** Uniform Bound on Sum Magnitude

    Given a pointwise bound << a >> on the absolute values of list elements,
    the magnitude of the sum is bounded by [INR] << (size l) * a >>. *)
    
Lemma sum_rel_bound :
  forall (l : list R) (rs a : R)
         (Hrs : sum_rel_R l rs)
         (Hin : forall x, In x l -> Rabs x <= a),
    Rabs rs <= INR (size l) * a.
Proof.
  induction l; intros rs a1 Hrs Hin.
  - inversion Hrs; subst; simpl; rewrite Rabs_R0; nra.
  - inversion Hrs; subst.
    eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans.
    + apply Rplus_le_compat.
      * apply Hin; simpl; auto.
      * apply IHl; [apply H2 | intros x Hx; apply Hin; simpl; auto].
    + apply Req_le.
      replace (size (a :: l)) with (size l + 1)%nat by (simpl; lia).
      rewrite plus_INR; simpl; nra.
Qed.

(** ** [sumR]: Functional Real Summation

    [sumR] is a computable fold-right definition of real summation. *)
    
Definition sumR := foldr Rplus 0.

(** The sum of absolute values via [sumR] is non-negative. *)

Lemma sumRabs_pos :
  forall x,
    0 <= sumR (map Rabs x).
Proof.
  induction x; simpl; try nra.
  apply Rplus_le_le_0_compat; [apply Rabs_pos | nra].
Qed.

(** The absolute value of [sumR] of absolute values equals itself. *)

Lemma sumRabs_Rabs :
  forall x,
    Rabs (sumR (map Rabs x)) = sumR (map Rabs x).
Proof.
  intros x.
  rewrite Rabs_pos_eq; auto.
  apply sumRabs_pos.
Qed.

(** Scalar multiplication distributes over [sumR]. *)

Lemma sumR_mult :
  forall x a,
    sumR x * a = sumR (map (Rmult a) x).
Proof.
  induction x; simpl; intros a1.
  - nra.
  - rewrite <- IHx; nra.
Qed.

(** The absolute value of a real sum is bounded by the sum of absolute
    values. *)
    
Lemma sumR_le_sumRabs :
  forall x,
    Rabs (sumR x) <= Rabs (sumR (map Rabs x)).
Proof.
  induction x; simpl; [nra |].
  rewrite sumRabs_Rabs in IHx.
  eapply Rle_trans.
  2: rewrite Rabs_pos_eq.
  - apply Rabs_triang.
  - apply Rplus_le_compat_l; auto.
  - apply Rplus_le_le_0_compat;
      [apply Rabs_pos | apply sumRabs_pos].
Qed.

(** Inserting an element at an arbitrary position in a split list preserves
    the [sumR] value (with that element added). *)
    
Lemma sumR_app_cons :
  forall l' l'' a,
    a + sumR (l' ++ l'') = sumR (l' ++ a :: l'').
Proof.
  induction l'; simpl. 
  - intros; nra.
  - intros; rewrite <- IHl'; nra. 
Qed.

(** [sumR] is invariant under list permutation. *)

Lemma sumR_permute :
  forall x x0
         (Hper : Permutation x x0),
    sumR x = sumR x0.
Proof.
  intros x.
  induction x; intros x0 Hper.
  - apply Permutation_nil in Hper; subst; simpl; auto.
  - apply Permutation_sym in Hper.
    pose proof Permutation_vs_cons_inv Hper as Hinv.
    destruct Hinv as (l' & l'' & Heq); subst.
    apply Permutation_sym in Hper.
    pose proof (@Permutation_cons_app_inv R x l' l'' a Hper) as Hperm'.
    specialize (IHx (l' ++ l'') Hperm').
    simpl.
    rewrite IHx sumR_app_cons; auto.
Qed.

(** [sumR] is invariant under list reversal. *)

Lemma sumR_rev :
  forall l,
    sumR (rev l) = sumR l.
Proof.
  move => l.
  apply sumR_permute.
  rewrite rev_list_rev.
  apply Permutation_sym.
  apply Permutation_rev.
Qed.

(** ** Uniform Bounds on Floating-Point Sums via Real Arithmetic *)

(** Bound on [sum_rel_R] over [FT2R]-mapped floating-point lists, given
    a pointwise bound on [Rabs (FT2R x)]. *)
    
Lemma sum_rel_bound' :
  forall (t : type) (l : list (ftype t)) (rs a : R)
         (Hrs : sum_rel_R (map FT2R l) rs)
         (Hin : forall x, In x l -> Rabs (FT2R x) <= a),
    Rabs rs <= INR (size l) * a.
Proof.
  induction l; intros rs a1 Hrs Hin.
  - inversion Hrs; subst; simpl; rewrite Rabs_R0; nra.
  - inversion Hrs; subst.
    eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans.
    + apply Rplus_le_compat.
      * apply Hin; simpl; auto.
      * apply IHl; [apply H2 | intros x Hx; apply Hin; simpl; auto].
    + apply Req_le.
      replace (size (a :: l)) with (size l + 1)%nat by (simpl; lia).
      rewrite plus_INR; simpl; nra.
Qed.

(** Bound on the sum of absolute values of [FT2R]-mapped floating-point
    list elements, given a pointwise bound. *)
Lemma sum_rel_bound'' :
  forall (t : type) (l : list (ftype t)) (rs_abs a : R)
         (Hrs : sum_rel_R (map Rabs (map FT2R l)) rs_abs)
         (Hin : forall x, In x l -> Rabs (FT2R x) <= a),
    rs_abs <= INR (size l) * a.
Proof.
  induction l; intros rs_abs ? Hrs Hin.
  - inversion Hrs; subst; simpl; compute; nra.
  - inversion Hrs; subst.
    fold sum_rel_R in H2.
    eapply Rle_trans.
    + apply Rplus_le_compat.
      * apply Hin; simpl; auto.
      * apply IHl; [apply H2 | intros x Hx; apply Hin; simpl; auto].
    + apply Req_le.
      replace (size (a :: l)) with (size l + 1)%nat by (simpl; lia).
      rewrite plus_INR; simpl; nra.
Qed.

(** [sum_rel_R] and [sumR] agree: a [sum_rel_R] derivation yields the same
    value as [sumR]. *)
    
Lemma sum_rel_R_fold :
  forall l rs,
    sum_rel_R l rs ->
    rs = sumR l.
Proof.
  induction l.
  - intros rs H.
    inversion H; simpl; auto.
  - intros rs H.
    inversion H; subst.
    fold sum_rel_R in H3.
    specialize (IHl s H3).
    subst; simpl; auto.
Qed.

(** Scalar multiplication distributes over [sum_rel_R]: if << l >> sums to << s >>,
    then [map (Rmult a) l] sums to << a * s >>. *)
    
Lemma sum_map_Rmult :
  forall (l : list R) (s a : R),
    sum_rel_R l s ->
    sum_rel_R (map (Rmult a) l) (a * s).
Proof.
  induction l; intros s ? H; simpl.
  - inversion H; subst; rewrite Rmult_0_r; auto.
  - inversion H; subst.
    destruct l.
    + simpl. inversion H3; subst. rewrite Rplus_0_r.
      apply sum_rel_R_single'.
    + fold sum_rel_R in H3.
      specialize (IHl s0 a0 H3).
      simpl.
      rewrite Rmult_plus_distr_l.
      apply sum_rel_cons.
      fold sum_rel_R.
      simpl in IHl; auto.
Qed.

(** ** Floating-Point Summation Instances and Properties *)

Section WithSTD.
Context {NAN : FPCore.Nans} {t : type}.

(** [sum_rel_Ft] is [sum_rel] instantiated to floating-point addition with
    default value << neg_zero >>. *)
    
Definition sum_rel_Ft := @sum_rel (ftype t) neg_zero BPLUS.

(** For a finite floating-point value << fs >>, a [sum_rel_Ft] derivation for a
    singleton list determines the sum uniquely. *)
    
Lemma sum_rel_Ft_single :
  forall (fs a : ftype t),
    Binary.is_finite fs = true ->
    sum_rel_Ft [a] fs ->
    fs = a.
Proof.
  move => fs a Hfin Hs.
  inversion Hs; subst.
  inversion H2; subst.
  rewrite /sum /BPLUS /BINOP /neg_zero.
  move: Hfin.
  destruct a;
    try discriminate Hfin => //;
    destruct s => //.
Qed.

(** For any floating-point list and [sum_rel_Ft] derivation, there exists a
    corresponding real-valued sum under [sum_rel_R]. *)
    
Lemma sum_rel_R_exists :
  forall (l : list (ftype t)) (fs : ftype t)
         (Hfs : sum_rel_Ft l fs),
    exists rs, sum_rel_R (map FT2R l) rs.
Proof.
  intros l.
  induction l.
  - simpl; intros fs Hfs.
    exists 0. apply sum_rel_nil.
  - intros fs Hfs.
    inversion Hfs; subst.
    fold sum_rel_Ft in H2.
    destruct (IHl s H2) as (rs & Hrs); clear IHl.
    exists (FT2R a + rs); simpl.
    apply sum_rel_cons; auto.
Qed.

(** For any floating-point list and [sum_rel_Ft] derivation, there exists a
    corresponding sum of absolute values under [sum_rel_R]. *)
    
Lemma sum_rel_R_abs_exists :
  forall (l : list (ftype t)) (fs : ftype t)
         (Hfs : sum_rel_Ft l fs),
    exists rs, sum_rel_R (map Rabs (map FT2R l)) rs.
Proof.
  intros l.
  induction l.
  - simpl; intros fs Hfs.
    exists 0. apply sum_rel_nil.
  - intros fs Hfs.
    inversion Hfs; subst.
    fold sum_rel_Ft in H2.
    destruct (IHl s H2) as (rs & Hrs); clear IHl.
    exists (Rabs (FT2R a) + rs); simpl.
    apply sum_rel_cons; auto.
Qed.

(** If the result << fs >> of a [sum_rel_Ft] computation is finite, then every
    element of the input list is also finite. *)
    
Lemma is_finite_in :
  forall (l : list (ftype t)) (fs : ftype t),
    sum_rel_Ft l fs ->
    Binary.is_finite fs = true ->
    forall a, In a l -> Binary.is_finite a = true.
Proof.
  induction l => //=.
  move => fs Hsum Hfin a1 [Heq | Hin]; subst.
  - inversion Hsum; subst.
    move: Hfin; rewrite /sum => Hfin.
    destruct (BPLUS_finite_e a1 s); auto.
  - inversion Hsum; clear Hsum; subst.
    fold sum_rel_Ft in H2.
    eapply IHl; try eassumption.
    destruct (BPLUS_finite_e a s); auto.
Qed.

(** [sumF] is a computable fold-left definition of floating-point summation,
    accumulating with [BPLUS] from << neg_zero >>. *)
    
Definition sumF := foldl (Basics.flip (@BPLUS _ t)) neg_zero.

(** [sum_rel_Ft] over a reversed list agrees with [sumF] on the original list. *)

Lemma sum_rel_Ft_fold :
  forall l fs,
    sum_rel_Ft (rev l) fs ->
    fs = sumF l.
Proof.
  intros l fs H.
  rewrite /sumF -(revK l) foldl_rev.
  revert fs H.
  induction (rev l).
  - intros fs H; inversion H; simpl; auto.
  - intros fs H.
    inversion H; subst.
    fold sum_rel_Ft in H3.
    specialize (IHl0 s H3).
    subst; simpl; auto.
Qed.

(** ** Subtraction Loop

    The subtraction loop << foldl BMINUS c al >> (used in, e.g., Cholesky
    decomposition) is floating-point equal to [sumF] << (c :: map BOPP al) >>,
    i.e., summing << c >> followed by the negations of << al >>. This enables
    accuracy theorems for [sum_rel] to transfer to subtraction-loop
    implementations. *)
    
Lemma subtract_loop_sumR :
  forall (c : ftype t) (al : list (ftype t)),
    feq (foldl BMINUS c al) (sumF (c :: map BOPP al)).
Proof.
  intros. 
  revert c; induction al; simpl; intros.
  - destruct c; try destruct s; reflexivity.
  - rewrite {}IHal /sumF -/(ftype t). 
    simpl.
    set x := Basics.flip BPLUS neg_zero (BMINUS c a).
    set y := Basics.flip BPLUS (Basics.flip BPLUS neg_zero c) (BOPP a).
    assert (Hfeq : feq x y) by
      (rewrite /x /y /Basics.flip !BPLUS_neg_zero BPLUS_comm MINUS_PLUS_BOPP //; auto).
    clearbody x; clearbody y.
    revert x y Hfeq.
    induction al; simpl; intros x y Hfeq; auto.
    apply IHal; auto.
    apply BPLUS_mor; auto.
Qed.

(** Every floating-point list has at least one [sum_rel_Ft] derivation. *)

Lemma sum_rel_Ft_exists :
  forall (l : list (ftype t)),
    exists s, sum_rel_Ft l s.
Proof.
  unfold sum_rel_Ft.
  induction l; simpl.
  - eexists; constructor.
  - destruct IHl as [s Hs].
    eexists; constructor; eauto.
Qed.

(** The subtraction loop << foldl BMINUS c al >> can be related to [sum_any],
    establishing that it falls within the framework of any-order summation.
    The resulting [sum_any] tree has height << size al >> and input list
    << rev (c :: map BOPP al) >>. *)
    
Lemma subtract_loop_sum_any :
  forall (c : ftype t) (al : list (ftype t)),
    exists s,
      feq (foldl BMINUS c al) s /\
      sum_any (size al) (rev (c :: map BOPP al)) s.
Proof.
  intros c al.
  assert (Hexists : exists s : ftype t,
            sum_rel neg_zero BPLUS (rev (c :: map BOPP al)) s /\
            feq (foldl BMINUS c al) s).
  - destruct (sum_rel_Ft_exists (rev (c :: map BOPP al))) as [s Hs].
    exists s; split; auto.
    apply sum_rel_Ft_fold in Hs.
    subst s.
    apply subtract_loop_sumR.
  - destruct Hexists as [s [Hrel Hfeq]].
    apply sum_rel_sum_any in Hrel; [ | reflexivity].
    destruct Hrel as [s' [Hfeq' Hany]].
    exists s'.
    split.
    + rewrite <- Hfeq'; auto.
    + simpl in Hany.
      rewrite size_rev /= size_map in Hany.
      auto.
Qed.

End WithSTD.