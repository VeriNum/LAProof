(** * Forward and Mixed Error Bounds for Floating-Point Dot Products

    This file establishes accuracy lemmas for both FMA-based and non-FMA-based
    floating-point dot product computations. These results are foundational
    building blocks used in [dot_acc.v] and [fma_dot_acc.v] to prove the main
    accuracy theorems.

    The proofs are structured around two inductive relations:
    - [dot_prod_rel]     : relates a list of floating-point pairs to their
                           computed (non-FMA) floating-point dot product.
    - [fma_dot_prod_rel] : relates a list of floating-point pairs to their
                           computed FMA-based floating-point dot product.
    - [R_dot_prod_rel]   : the analogous real-arithmetic dot product relation,
                           used to state the ideal (exact) result.

    The error bounds are expressed using the standard relative and absolute
    error model parameters: [default_rel] and [default_abs].

    ** Summary of Main Results

    *** Forward Error Bounds

    - [dotprod_forward_error_rel]: Bounds the absolute error of a non-FMA
      floating-point dot product relative to the exact real dot product.

    - [fma_dotprod_forward_error_rel]: The analogous forward error bound for
      FMA-based dot products.

    *** Sparse Forward Error Bounds

    - [sparse_dotprod_forward_error_rel]: A tighter forward error bound for
      non-FMA dot products that exploits zero entries in one of the input
      vectors, replacing the vector length with the number of nonzeros.

    - [sparse_fma_dotprod_forward_error]: The analogous sparse bound for
      FMA-based dot products.

    *** Mixed Error Bounds

    - [dotprod_mixed_error_rel]: Shows that the computed non-FMA dot product
      can be expressed as an exact dot product of slightly perturbed inputs
      plus a small absolute error term.

    - [fma_dotprod_mixed_error_rel]: The analogous mixed error representation
      for FMA-based dot products, with a slightly tighter absolute error term.
*)

From LAProof.accuracy_proofs Require Import
  preamble
  common
  dotprod_model
  float_acc_lems.

(** * Section 1: Forward Error Bound — Non-FMA Dot Product *)

Section ForwardErrorRel1.
(**
    Forward error bound for the non-FMA dot product, using the inductive
    relation [dot_prod_rel].
*)

Context {NAN : FPCore.Nans} {t : type}.

Notation g  := (@g t).
Notation g1 := (@g1 t).
Notation D  := (@default_rel t).
Notation E  := (@default_abs t).


(** [dotprod_forward_error_rel] establishes the standard forward error bound
    for the non-FMA floating-point dot product.

    Given:
    - vF     : a list of floating-point input pairs,
    - fp     : the computed (finite) floating-point dot product satisfying
                 [dot_prod_rel vF fp],
    - rp     : the exact real dot product satisfying [R_dot_prod_rel (map FR2 vF) rp],
    - rp_abs : the dot product of absolute values satisfying
                 [R_dot_prod_rel (map Rabsp (map FR2 vF)) rp_abs],

    the absolute error satisfies:
    << |FT2R fp - rp| <= g(|vF|) * rp_abs + g1(|vF|, |vF| - 1) >>
*)

Lemma dotprod_forward_error_rel :
  forall (vF  : seq (ftype t * ftype t))
         (fp  : ftype t)
         (Hfp : dot_prod_rel vF fp)
         (Hfin : Binary.is_finite fp = true)
         (rp rp_abs : R)
         (Hrp : R_dot_prod_rel (map FR2 vF) rp)
         (Hra : R_dot_prod_rel (map Rabsp (map FR2 vF)) rp_abs),
    Rabs (FT2R fp - rp) <= g (size vF) * rp_abs + g1 (size vF) (size vF - 1).
Proof.
induction vF.
{ (* base case: empty list *)
  intros;
  inversion Hrp; inversion Hfp; inversion Hra; subst.
  rewrite /g /g1 /= !Rminus_diag Rabs_R0 !Rmult_0_l; lra. }
intros. rename vF into l.
assert (Hl : l = [::] \/ l <> [::])
  by (destruct l; auto; right; congruence).
destruct Hl.
- (* case: singleton list *)
  subst; simpl.
  rewrite (R_dot_prod_rel_single rp (FR2 a)); auto.
  inversion Hfp. inversion H2; subst.
  destruct (BPLUS_correct _ _ Hfin) as [[A Hz] ?].
  rewrite Bplus_0R; auto.
  destruct (BMULT_accurate' _ _ A) as (d' & e' & Hed' & Hd' & He' & B).
  unfold g1, g; simpl.
  inversion Hra. inversion H4; subst.
  rewrite {}B Rmult_1_r !Rplus_0_r.
  field_simplify. field_simplify_Rabs.
  destruct a; simpl.
  eapply Rle_trans; [apply Rabs_triang |].
  rewrite Rabs_mult.
  eapply Rle_trans.
  { apply Rplus_le_compat.
    - apply Rmult_le_compat; try apply Rabs_pos.
      + apply Rle_refl.
      + apply Hd'.
    - apply He'. }
  rewrite Rmult_comm.
  apply Rplus_le_compat; try nra.
  rewrite Rmult_assoc; rewrite -Rabs_mult; nra.
- (* case: non-empty tail *)
  intros; inversion Hfp; inversion Hrp; inversion Hra; subst.
  destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
  (* apply induction hypothesis to the tail *)
  specialize (IHvF s H3 B s0 s1 H7 H11).
  destruct (BPLUS_accurate' (BMULT (fst a) (snd a)) s Hfin) as (d' & Hd' & Hplus).
  rewrite Hplus; clear Hplus.
  destruct (BMULT_accurate' (fst a) (snd a) A) as (d & e & Hed & Hd & He & Hmul).
  rewrite Hmul; clear Hmul.
  apply size_not_empty_nat in H.
  destruct a; cbv [FR2 Rabsp fst snd]; simpl.
  set (n := size l) in *.
  set (F := FT2R f * FT2R f0).
  field_simplify_Rabs.
  replace (F * d * d' + F * d + F * d' + e * d' + e + FT2R s * d' + FT2R s - s0)
    with ((F * d * d' + F * d + F * d' + FT2R s * d') + (FT2R s - s0) + (1 + d') * e)
    by nra.
  eapply Rle_trans; [apply Rabs_triang |].
  eapply Rle_trans;
    [apply Rplus_le_compat;
      [eapply Rle_trans; [apply Rabs_triang |] |] |].
  { apply Rplus_le_compat_l; apply IHvF. }
  { rewrite Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos | apply He]. }
  rewrite Rplus_assoc.
  eapply Rle_trans;
    [apply Rplus_le_compat_r;
      eapply Rle_trans; [apply Rabs_triang |] |].
  apply Rplus_le_compat_l.
  rewrite Rabs_mult Rmult_comm.
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hd' |].
  { apply Rabs_le_minus in IHvF.
    assert (Hs : Rabs (FT2R s) <= g (size l) * s1 + g1 (size l) (size l - 1) + s1).
    { eapply Rle_trans; [apply IHvF |].
      apply Rplus_le_compat_l.
      rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 l) s1); auto.
      apply (dot_prod_sum_rel_R_Rabs (map FR2 l)); auto. }
    apply Hs. }
  field_simplify.
  fold D E n.
  rewrite !Rplus_assoc.
  replace (Rabs (F * d * d' + (F * d + F * d')) +
           (D * g n * s1 +
            (D * s1 +
             (D * g1 n (n - 1) +
              (s1 * g n + (g1 n (n - 1) + Rabs (1 + d') * E))))))
    with (Rabs (F * d * d' + (F * d + F * d')) +
          ((1 + D) * g n * s1 + D * s1) +
          (D * g1 n (n - 1) + (g1 n (n - 1) + Rabs (1 + d') * E)))
    by nra.
  replace (n.+1 - 1)%nat with n by lia.
  replace (s1 * g (S n) + (g (S n) * Rabs (FT2R f) * Rabs (FT2R f0) + g1 (S n) n))
    with (g (S n) * Rabs (FT2R f * FT2R f0) + s1 * g (S n) + g1 (S n) n)
    by (rewrite Rmult_assoc -Rabs_mult; nra).
  apply Rplus_le_compat; [apply Rplus_le_compat |].
  + (* bound on |F * d * d' + (F * d + F * d')| *)
    eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans;
      [apply Rplus_le_compat;
        [rewrite !Rabs_mult
        | eapply Rle_trans; [apply Rabs_triang |]] |].
    { apply Rmult_le_compat;
        [rewrite -!Rabs_mult; apply Rabs_pos | apply Rabs_pos | | apply Hd'].
      apply Rmult_le_compat_l; [rewrite -!Rabs_mult; apply Rabs_pos | apply Hd]. }
    { apply Rplus_le_compat; rewrite Rabs_mult.
      - apply Rmult_le_compat_l; [apply Rabs_pos | apply Hd].
      - apply Rmult_le_compat_l; [apply Rabs_pos | apply Hd']. }
    rewrite -!Rabs_mult.
    fold D F.
    replace (Rabs F * D * D + (Rabs F * D + Rabs F * D))
      with (((1 + D) * (1 + D) - 1) * Rabs F) by nra.
    apply Rmult_le_compat_r; [apply Rabs_pos |].
    unfold D, g.
    apply Rplus_le_compat; try nra.
    rewrite <- tech_pow_Rmult.
    apply Rmult_le_compat_l;
      [eapply Rle_trans with 1; try nra; apply default_rel_plus_1_ge_1 |].
    eapply Rle_trans with ((1 + D) ^ 1); try nra.
    fold D; nra.
    apply Rle_pow; auto with commonDB.
  + (* bound on the g-weighted sum term *)
    apply Req_le.
    rewrite one_plus_d_mul_g.
    rewrite Rmult_comm.
    repeat f_equal; try lia.
  + (* bound on the g1 absolute error term *)
    rewrite <- Rplus_assoc.
    eapply Rle_trans;
      [apply Rplus_le_compat_l;
        apply Rmult_le_compat_r;
          [unfold E; apply default_abs_ge_0
          | eapply Rle_trans; [apply Rabs_triang |]] |].
    { rewrite Rabs_R1. apply Rplus_le_compat_l; apply Hd'. }
    rewrite !Rmult_plus_distr_r Rmult_1_l. 
    rewrite <- !Rplus_assoc.
    replace (D * g1 n (n - 1) + g1 n (n - 1))
      with (g1 n (n - 1) * (1 + D)) by nra.
    rewrite one_plus_d_mul_g1; [| lia].
    rewrite Rplus_assoc.
    replace (E + D * E) with ((1 + D) * E) by nra.
    eapply Rle_trans; [apply plus_d_e_g1_le; lia |].
    apply Req_le; f_equal; lia.
Qed.

End ForwardErrorRel1.

(** * Section 2: Forward Error Bound — FMA Dot Product *)

Section ForwardErrorRel2.
(**
    Forward error bound for the FMA-based dot product, using the inductive
    relation [fma_dot_prod_rel]. The bound takes the same form as the non-FMA
    case but uses FMA accuracy lemmas internally.
*)

Context {NAN : FPCore.Nans} {t : type}.

Variable  (vF : list (ftype t * ftype t)).
Notation   vR  := (map FR2 vF).
Notation   vR' := (map Rabsp (map FR2 vF)).

Variable  (fp   : ftype t).
Hypothesis Hfp  : fma_dot_prod_rel vF fp.
Hypothesis Hfin : Binary.is_finite fp = true.

Variable  (rp rp_abs : R).
Hypothesis Hrp  : R_dot_prod_rel vR rp.
Hypothesis Hra  : R_dot_prod_rel vR' rp_abs.

Notation g  := (@g t).
Notation g1 := (@g1 t).
Notation D  := (@default_rel t).
Notation E  := (@default_abs t).

(** [fma_dotprod_forward_error_rel] establishes the standard forward error bound
    for the FMA-based floating-point dot product.

    The absolute error satisfies:
    
    << |FT2R fp - rp| <= g(|vF|) * rp_abs + g1(|vF|, |vF| - 1) >>
    
    where << rp >> is the exact real dot product and << rp_abs >> is the dot product
    of absolute values.
*)

Lemma fma_dotprod_forward_error_rel :
  Rabs (FT2R fp - rp) <= g (size vF) * rp_abs + g1 (size vF) (size vF - 1).
Proof.
revert Hfp Hrp Hra Hfin. revert fp rp rp_abs.
induction vF.
{ (* base case: empty list *)
  intros;
  inversion Hrp; inversion Hfp; inversion Hra; subst.
  unfold g, g1; simpl.
  rewrite !Rminus_diag Rabs_R0.
  field_simplify; try apply default_rel_sep_0;
    try apply Stdlib.Rdiv_pos_compat; try nra;
  apply default_rel_gt_0. }
intros.
assert (Hl : l = [] \/ l <> []).
{ destruct l; auto.
  right; eapply hd_error_some_nil; simpl; auto. }
destruct Hl.
- (* case: singleton list *)
  subst; simpl.
  rewrite (R_dot_prod_rel_single rp (FR2 a)); [| auto].
  inversion Hfp. inversion H2; subst.
  pose proof fma_accurate' (fst a) (snd a) (Zconst t 0) Hfin as Hacc.
  destruct Hacc as (e & d & Hz & He & Hd & A).
  rewrite A; clear A.
  inversion Hra; inversion H3; subst.
  unfold g1, g; simpl.
  rewrite Rmult_1_r !Rplus_0_r.
  replace (1 + @default_rel t - 1) with (@default_rel t) by nra.
  field_simplify_Rabs.
  destruct a; simpl.
  rewrite Rminus_diag Rplus_0_r Rmult_1_r Rmult_1_l.
  eapply Rle_trans; [apply Rabs_triang |].
  apply Rplus_le_compat; try nra.
  rewrite Rmult_comm !Rabs_mult.
  apply Rmult_le_compat; try apply Rabs_pos; try apply Rle_refl; auto.
  rewrite <- Rabs_mult; apply Rabs_pos.
- (* case: non-empty tail *)
  intros; inversion Hfp; inversion Hrp; inversion Hra; subst.
  destruct (BFMA_finite_e _ _ _ Hfin) as (A & B & C).
  (* apply induction hypothesis to the tail *)
  specialize (IHl s s0 s1 H3 H7 H11 C).
  pose proof (fma_accurate' (fst a) (snd a) s Hfin) as Hplus.
  destruct Hplus as (d' & e' & Hz & Hd' & He' & Hplus).
  rewrite Hplus; clear Hplus.
  destruct a; cbv [FR2 Rabsp fst snd]; simpl.
  set (n := size l).
  field_simplify_Rabs.
  replace (FT2R f * FT2R f0 * d' + FT2R s * d' + FT2R s + e' - s0)
    with (d' * (FT2R f * FT2R f0) + d' * FT2R s + (FT2R s - s0) + e')
    by nra.
  eapply Rle_trans;
    [apply Rabs_triang
    | eapply Rle_trans;
        [apply Rplus_le_compat_r; apply Rabs_triang |]].
  eapply Rle_trans;
    [apply Rplus_le_compat_r |].
  { apply Rplus_le_compat_r; apply Rabs_triang. }
  eapply Rle_trans;
    [apply Rplus_le_compat_r; apply Rplus_le_compat_l |].
  { apply IHl. }
  eapply Rle_trans;
    [apply Rplus_le_compat; [apply Rplus_le_compat_r | apply He'] |].
  { apply Rplus_le_compat.
    - rewrite Rabs_mult.
      apply Rmult_le_compat_r; [apply Rabs_pos | apply Hd'].
    - rewrite Rabs_mult.
      apply Rmult_le_compat; try apply Rabs_pos.
      + apply Hd'.
      + apply Rabs_le_minus in IHl.
        assert (Hs : Rabs (FT2R s) <=
                     g (size l) * s1 + g1 (size l) (size l - 1) + s1).
        { eapply Rle_trans; [apply IHl |].
          apply Rplus_le_compat_l.
          rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 l) s1); auto.
          apply (dot_prod_sum_rel_R_Rabs (map FR2 l)); auto. }
        apply Hs. }
  fold n.
  set (F := Rabs (FT2R f * FT2R f0)).
  rewrite !Rmult_plus_distr_l.
  replace (D * F + (D * (g n * s1) + D * g1 n (n - 1) + D * s1) +
           (g n * s1 + g1 n (n - 1)) + E)
    with (D * F + ((1 + D) * g n * s1 + D * s1) +
          g1 n (n - 1) * (1 + D) + E)
    by nra.
  rewrite one_plus_d_mul_g one_plus_d_mul_g1.
  rewrite Rplus_assoc.
  apply Rplus_le_compat; [apply Rplus_le_compat |].
  + rewrite <- Rabs_mult; fold F.
    apply Rmult_le_compat_r; [unfold F; apply Rabs_pos |].
    apply d_le_g_1; lia.
  + apply Rmult_le_compat_r.
    { rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 l) s1); auto.
      apply Rabs_pos. }
    apply Req_le; f_equal; auto; lia.
  + replace (n.+1 - 1)%nat with n by lia.
    apply plus_e_g1_le.
  + unfold n; destruct l; try congruence; simpl; lia.
Qed.

End ForwardErrorRel2.

(** * Section 3: Mixed Error Bound — Non-FMA Dot Product *)

Section MixedErrorRel1.
(**
    Mixed (componentwise relative + global absolute) error bound for the
    non-FMA dot product.

    This section establishes that the computed dot product can be
    expressed as an exact dot product of perturbed inputs, up to a small
    absolute error.
*)

Context {NAN : FPCore.Nans} {t : type}.

Notation g  := (@g t).
Notation g1 := (@g1 t).
Notation D  := (@default_rel t).
Notation E  := (@default_abs t).

Variables (v1 v2 : list (ftype t)).
Hypothesis Hlen : size v1 = size v2.
Notation   vF   := (zip v1 v2).

Variable  (fp   : ftype t).
Hypothesis Hfp  : dot_prod_rel vF fp.
Hypothesis Hfin : Binary.is_finite fp = true.

Notation neg_zero := (@common.neg_zero t).

(** [dotprod_mixed_error_rel] establishes the mixed error representation for
    the non-FMA floating-point dot product.
*)

Lemma dotprod_mixed_error_rel :
  exists (u : list R) (eta : R),
    size u = size v2 /\
    R_dot_prod_rel (zip u (map FT2R v2)) (FT2R fp - eta) /\
    (forall n, (n < size v2)%nat ->
      exists delta,
        nth 0 u n = FT2R (nth neg_zero v1 n) * (1 + delta) /\
        Rabs delta <= g (size v2)) /\
    Rabs eta <= g1 (size v2) (size v2).
Proof.
revert Hfp Hfin Hlen. revert fp v1.
induction v2.
{ (* base case: empty v2 *)
  simpl; intros.
  replace v1 with (@nil (ftype t)) in *
    by (symmetry; apply length_zero_iff_nil; auto).
  exists [], 0; repeat split.
  - inversion Hfp; subst.
    rewrite Rminus_0_r; simpl; auto.
    apply R_dot_prod_rel_nil.
  - intros; exists 0; split.
    + assert (n = 0)%nat by lia; subst; simpl; nra.
    + rewrite Rabs_R0; unfold g; nra.
  - rewrite Rabs_R0; unfold g1, g; simpl; nra. }
intros.
destruct v1; intros.
{ simpl in Hlen.
  pose proof Nat.neq_0_succ (size l); contradiction. }
assert (Hv1 : l = [] \/ l <> []).
{ destruct l; auto.
  right; eapply hd_error_some_nil; simpl; auto. }
assert (Hlen1 : size l0 = size l) by (simpl in Hlen; auto).
destruct Hv1.
assert (l0 = []) by (subst l; destruct l0; auto; discriminate).
subst; clear Hlen1.
- (* case: singleton lists *)
  clear IHl.
  inversion Hfp; subst.
  inversion H2; subst; clear H2.
  simpl in Hfp, Hfin; unfold fst, snd.
  destruct (BPLUS_correct _ _ Hfin) as [[Hfa _] Hplus].
  destruct (BMULT_correct _ _ Hfa) as [[Ha Hf] _].
  destruct (BMULT_accurate' f a Hfa) as (d & e & Hed & Hd & He & Hacc).
  exists [FT2R f * (1 + d)], e; repeat split.
  + simpl.
    rewrite Hplus; simpl.
    rewrite Rplus_0_r round_FT2R Hacc.
    replace (FT2R f * FT2R a * (1 + d) + e - e)
      with (FT2R f * (1 + d) * FT2R a + 0) by (simpl; nra).
    apply R_dot_prod_rel_cons; apply R_dot_prod_rel_nil.
  + intros; exists d; split; auto.
    simpl in H.
    destruct n; [simpl; auto | lia].
    eapply Rle_trans; [apply Hd | apply d_le_g_1; simpl; auto].
  + eapply Rle_trans; [apply He |].
    apply e_le_g1; simpl in *; auto.
- (* case: cons lists — apply induction hypothesis *)
  move : (size_not_empty_nat l H) => Hlen3.
  inversion Hfp; subst.
  unfold fst, snd in Hfin, Hfp; unfold fst, snd.
  destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
  destruct (BMULT_finite_e _ _ A) as (C & _).
  specialize (IHl s l0 H3 B Hlen1).
  destruct (BPLUS_accurate' (BMULT f a) s Hfin) as (d' & Hd' & Hplus).
  rewrite Hplus; clear Hplus.
  destruct (BMULT_accurate' f a A) as (d & e & Hed & Hd & He & Hmul).
  rewrite Hmul; clear Hmul.
  destruct IHl as (u & eta & Hlenu & Hurel & Hun & Heta).
  exists (FT2R f * (1 + d) * (1 + d') :: map (Rmult (1 + d')) u),
         (e * (1 + d') + eta * (1 + d')).
  repeat split.
  + simpl; rewrite size_map; auto.
  + (* show the exact dot product relation holds *)
    pose proof dot_prod_zip_map_Rmult (1 + d') u (map FT2R l) (FT2R s - eta).
    rewrite size_map in H0.
    specialize (H0 Hlenu Hurel); simpl.
    replace ((FT2R f * FT2R a * (1 + d) + e + FT2R s) * (1 + d') -
             (e * (1 + d') + eta * (1 + d')))
      with (FT2R f * (1 + d) * (1 + d') * FT2R a + (FT2R s - eta) * (1 + d'))
      by nra.
    apply R_dot_prod_rel_cons; rewrite Rmult_comm; auto.
  + (* componentwise relative error bounds *)
    intros.
    destruct n.
    { simpl.
      exists ((1 + d) * (1 + d') - 1); split.
      - field_simplify; nra.
      - field_simplify_Rabs.
        eapply Rle_trans; [apply Rabs_triang |].
        eapply Rle_trans;
          [apply Rplus_le_compat;
            [apply Rabs_triang | apply Hd'] |].
        eapply Rle_trans;
          [apply Rplus_le_compat_r;
            apply Rplus_le_compat; [| apply Hd] |].
        { rewrite Rabs_mult.
          apply Rmult_le_compat; try apply Rabs_pos; [apply Hd | apply Hd']. }
        eapply Rle_trans with ((1 + D) * (1 + D) - 1); try nra.
        unfold g.
        apply Rplus_le_compat; try nra.
        rewrite <- tech_pow_Rmult.
        apply Rmult_le_compat; try nra;
          try (eapply Rle_trans with 1; try nra; apply default_rel_plus_1_ge_1).
        eapply Rle_trans with ((1 + D) ^ 1); try nra.
        apply Rle_pow;
          try (eapply Rle_trans with 1; try nra; apply default_rel_plus_1_ge_1).
        rewrite <- Hlen1; auto; lia. }
    simpl in H0.
    assert (Hn : (n < size l)%nat) by lia.
    specialize (Hun n Hn).
    destruct Hun as (delta & Hun & Hdelta).
    simpl.
    replace 0 with (Rmult (1 + d') 0) by nra.
    rewrite (nth_map R0); [| lia].
    rewrite Hun.
    exists ((1 + d') * (1 + delta) - 1).
    split; [nra |].
    field_simplify_Rabs.
    eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans;
      [apply Rplus_le_compat; [apply Rabs_triang | apply Hdelta] |].
    eapply Rle_trans;
      [apply Rplus_le_compat_r; rewrite Rabs_mult |].
    { apply Rplus_le_compat;
        [apply Rmult_le_compat; try apply Rabs_pos; [apply Hd' | apply Hdelta] |].
      apply Hd'. }
    replace (D * g (size l) + D + g (size l))
      with ((1 + D) * g (size l) * 1 + D * 1) by nra.
    rewrite one_plus_d_mul_g Rmult_1_r.
    apply Req_le; f_equal; lia.
  + (* global absolute error bound *)
    simpl.
    eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans;
      [apply Rplus_le_compat;
        [rewrite Rabs_mult | rewrite Rabs_mult] |].
    { eapply Rmult_le_compat; try apply Rabs_pos.
      - apply He.
      - eapply Rle_trans; [apply Rabs_triang |].
        rewrite Rabs_R1.
        apply Rplus_le_compat_l; apply Hd'. }
    { eapply Rmult_le_compat; try apply Rabs_pos.
      - apply Heta.
      - eapply Rle_trans; [apply Rabs_triang |].
        rewrite Rabs_R1.
        apply Rplus_le_compat_l; apply Hd'. }
    rewrite Rplus_comm one_plus_d_mul_g1'.
    assert (Hp : (1 <= S (size l))%nat) by lia.
    pose proof @plus_d_e_g1_le' t (size l) (S (size l)) ltac:(lia) Hp as HYP.
    eapply Rle_trans; [| apply HYP].
    apply Req_le; nra.
Qed.

End MixedErrorRel1.

(** * Section 4: Mixed Error Bound — FMA Dot Product *)

Section MixedErrorRel2.
(**
    Mixed (componentwise relative + global absolute) error bound for the
    FMA-based dot product.

    The structure mirrors [MixedErrorRel1] but uses [fma_dot_prod_rel] and
    FMA accuracy lemmas, yielding the tighter absolute error bound
    due one fewer rounding step.
*)

Context {NAN : FPCore.Nans} {t : type}.

Notation g  := (@g t).
Notation g1 := (@g1 t).
Notation D  := (@default_rel t).
Notation E  := (@default_abs t).

Variables (v1 v2 : list (ftype t)).
Hypothesis Hlen : size v1 = size v2.
Notation   vF   := (zip v1 v2).

Variable  (fp   : ftype t).
Hypothesis Hfp  : fma_dot_prod_rel vF fp.
Hypothesis Hfin : Binary.is_finite fp = true.

Notation neg_zero := (@common.neg_zero t).

(** [fma_dotprod_mixed_error_rel] establishes the mixed error representation for
    the FMA-based floating-point dot product.

    The bound on the absolute error is one step tighter than the non-FMA case 
    because each FMA step introduces only one rounding error.
*)

Lemma fma_dotprod_mixed_error_rel :
  exists (u : list R) (eta : R),
    size u = size v1 /\
    R_dot_prod_rel (zip u (map FT2R v2)) (FT2R fp - eta) /\
    (forall n, (n < size v2)%nat ->
      exists delta,
        nth 0 u n = FT2R (nth neg_zero v1 n) * (1 + delta) /\
        Rabs delta <= g (size v2)) /\
    Rabs eta <= g1 (size v2) (size v2 - 1).
Proof.
revert Hfp Hfin Hlen. revert fp v1.
induction v2.
{ (* base case: empty v2 *)
  simpl; intros.
  replace v1 with (@nil (ftype t)) in *
    by (symmetry; apply length_zero_iff_nil; auto).
  exists [], 0; repeat split.
  - inversion Hfp; subst.
    rewrite Rminus_0_r; simpl; auto.
    apply R_dot_prod_rel_nil.
  - intros; exists 0; split.
    + assert (n = 0)%nat by lia; subst; simpl; try nra.
    + rewrite Rabs_R0; unfold g; try nra.
  - rewrite Rabs_R0; unfold g1, g; simpl; nra. }
intros.
destruct v1; intros.
{ simpl in Hlen.
  pose proof Nat.neq_0_succ (size l); contradiction. }
assert (Hv1 : l = [] \/ l <> []).
{ destruct l; auto.
  right; eapply hd_error_some_nil; simpl; auto. }
assert (Hlen1 : size l0 = size l) by (simpl in Hlen; auto).
destruct Hv1.
assert (l0 = []) by (destruct l0, l; auto; discriminate).
subst; clear Hlen1.
- (* case: singleton lists *)
  inversion Hfp; subst.
  inversion H2; subst; clear H2.
  simpl in Hfp, Hfin.
  pose proof fma_accurate' f a (Zconst t 0) Hfin as Hacc.
  destruct Hacc as (d & e & Hde & Hd & He & Hacc).
  exists [FT2R f * (1 + d)], e; repeat split.
  + simpl.
    rewrite Hacc FT2R_Zconst_0 Rplus_0_r.
    replace ((FT2R f * FT2R a) * (1 + d) + e - e)
      with (FT2R f * (1 + d) * FT2R a + 0) by (simpl; nra).
    apply R_dot_prod_rel_cons; apply R_dot_prod_rel_nil.
  + intros; exists d; split; auto.
    simpl in H.
    destruct n; [simpl; auto | lia].
    eapply Rle_trans; [apply Hd | apply d_le_g_1; simpl; auto].
  + eapply Rle_trans; [apply He |].
    unfold g1, g; simpl; nra.
- (* case: cons lists — apply induction hypothesis *)
  pose proof (size_not_empty_nat l H) as Hlen3.
  inversion Hfp; subst.
  destruct (BFMA_finite_e _ _ _ Hfin) as (A' & B' & C').
  specialize (IHl s l0).
  destruct IHl as (u & eta & Hlenu & A & B & C); auto.
  simpl in Hfin.
  pose proof fma_accurate' f a s Hfin as Hacc.
  destruct Hacc as (d & e & Hz & Hd & He & Hacc).
  unfold fst, snd; rewrite Hacc.
  exists (FT2R f * (1 + d) :: map (Rmult (1 + d)) u),
         (e + eta * (1 + d)).
  repeat split.
  + simpl; rewrite size_map; auto.
  + (* show the exact dot product relation holds *)
    pose proof dot_prod_zip_map_Rmult (1 + d) u (map FT2R l) (FT2R s - eta).
    rewrite size_map in H0.
    rewrite Hlen1 in Hlenu.
    specialize (H0 Hlenu A); simpl.
    replace ((FT2R f * FT2R a + FT2R s) * (1 + d) + e - (e + eta * (1 + d)))
      with (FT2R f * (1 + d) * FT2R a + (FT2R s - eta) * (1 + d))
      by nra.
    apply R_dot_prod_rel_cons; rewrite Rmult_comm; auto.
  + (* componentwise relative error bounds *)
    intros.
    destruct n.
    { simpl.
      exists d; split; auto.
      eapply Rle_trans; [apply Hd |].
      apply d_le_g_1; lia. }
    assert (n < size l)%nat by (simpl in H0; lia); clear H0.
    specialize (B n H1).
    destruct B as (delta & B & HB); simpl.
    replace 0 with (Rmult (1 + d) 0) by nra.
    rewrite (nth_map R0); [| lia].
    rewrite B.
    exists ((1 + d) * (1 + delta) - 1).
    split; [nra |].
    field_simplify_Rabs.
    eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans;
      [apply Rplus_le_compat; [apply Rabs_triang | apply HB] |].
    eapply Rle_trans;
      [apply Rplus_le_compat_r; rewrite Rabs_mult |].
    { apply Rplus_le_compat;
        [apply Rmult_le_compat; try apply Rabs_pos; [apply Hd | apply HB] |].
      apply Hd. }
    replace (D * g (size l) + D + g (size l))
      with ((1 + D) * g (size l) * 1 + D * 1) by nra.
    rewrite one_plus_d_mul_g Rmult_1_r.
    apply Req_le; f_equal; lia.
  + (* global absolute error bound *)
    simpl.
    eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans;
      [apply Rplus_le_compat;
        [apply He | rewrite Rabs_mult] |].
    { eapply Rmult_le_compat; try apply Rabs_pos.
      - apply C.
      - eapply Rle_trans; [apply Rabs_triang |].
        rewrite Rabs_R1.
        eapply Rle_trans; [apply Rplus_le_compat_l; apply Hd |].
        apply Rle_refl. }
    rewrite one_plus_d_mul_g1.
    2: { destruct l; [contradiction | simpl; lia]. }
    unfold g1; field_simplify.
    rewrite Rplus_assoc.
    apply Rplus_le_compat.
    { apply Rmult_le_compat; try apply g_pos.
      - apply Rmult_le_pos; [apply default_abs_ge_0 | apply pos_INR].
      - apply Rmult_le_compat; try apply default_abs_ge_0; try apply pos_INR.
        + apply Req_le; auto.
        + apply le_INR; lia. 
      - apply Req_le; f_equal; auto; lia. }
    set (n := size l).
    replace (INR (S n)) with (INR n + 1)%R.
    { apply Req_le.
      unfold GRing.one, GRing.add; simpl; nra. }
    apply transitivity with (INR (n + 1)).
    { rewrite plus_INR; simpl; auto. }
    f_equal; simpl; lia.
Qed.

End MixedErrorRel2.

(** * Section 5: Sparse Forward Error Bound — Non-FMA Dot Product *)

Section SparseErrorRel1.
(**
    Sparse forward error bound for the non-FMA dot product.

    When a vector in the product contains many zeros, the error bound can be 
    sharpened by replacing the vector length with the number of nonzero entries.  
    This follows from the observation that multiplying by zero
    contributes no rounding error, and thus such terms can be excluded from
    the error accumulation.
*)

Context {NAN : FPCore.Nans} {t : type}.

Variables (v1 v2 : list (ftype t)).
Hypothesis (Hlen : size v1 = size v2).

Variable  (fp   : ftype t).
Hypothesis Hfp  : dot_prod_rel (zip v1 v2) fp.
Hypothesis Hfin : Binary.is_finite fp = true.

Notation v1R    := (map FT2R v1).
Notation nnzR   := (nnzR v1R).

Variable  (rp rp_abs : R).
Hypothesis Hrp  : R_dot_prod_rel (map FR2 (zip v1 v2)) rp.
Hypothesis Hra  : R_dot_prod_rel (map Rabsp (map FR2 (zip v1 v2))) rp_abs.

Notation g  := (@common.g t).
Notation g1 := (@common.g1 t).

(** [sparse_dotprod_forward_error_rel] establishes the sparse forward error
    bound for the non-FMA dot product.This is tighter than the dense bound.
*)

Lemma sparse_dotprod_forward_error_rel :
  Rabs (FT2R fp - rp) <= g nnzR * rp_abs + g1 nnzR (nnzR - 1).
Proof.
revert Hlen Hfp Hfin Hrp Hra.
revert rp rp_abs fp v2.
induction v1; intros.
{ (* base case: empty v1 *)
  simpl in Hlen; symmetry in Hlen; apply length_zero_iff_nil in Hlen; subst.
  inversion Hfp; inversion Hrp; subst; simpl; field_simplify_Rabs.
  rewrite Rabs_Ropp Rabs_R0.
  apply Rplus_le_le_0_compat; auto with commonDB.
  apply Rmult_le_pos; auto with commonDB.
  rewrite <- (R_dot_prod_rel_Rabs_eq [] rp_abs); auto.
  apply Rabs_pos. }
destruct v2; try discriminate.
assert (Hlen1 : size l = size l0) by (simpl; auto).
set (n2 := (common.nnzR (map FT2R l))%nat) in *.
inversion Hrp. inversion Hfp. inversion Hra; subst.
simpl in Hfin.
destruct (BPLUS_correct _ _ Hfin) as [[Haf Hs0] Hplus].
specialize (IHl s s1 s0 l0 Hlen1 H6 Hs0 H2 H10).
simpl fst; simpl snd.
(* case split on whether the head entry is zero *)
destruct (Req_EM_T (FT2R a) 0%R).
- (* head is zero: contributes no rounding error *)
  simpl map; rewrite e.
  move : (nnzR_cons [seq FT2R i | i <- l]) => /eqP H8; rewrite {}H8.
  replace (FT2R (BPLUS (BMULT a f) s0)) with (FT2R s0).
  + change GRing.zero with R0.
    field_simplify_Rabs.
    eapply Rle_trans; [apply IHl |].
    apply Req_le; f_equal; try nra.
    unfold n2, common.nnzR.
    rewrite Rabs_R0 Rmult_0_l Rplus_0_l.
    simpl count; auto.
  + rewrite {}Hplus.
    pose proof Bmult_0R a f Haf e as A.
    destruct A as [A | A]; auto; rewrite A.
    * by rewrite Rplus_0_l round_FT2R.
    * by rewrite FT2R_pos_zero Rplus_0_l round_FT2R.
- (* head is nonzero: contributes to the error budget *)
  unfold common.nnzR.
  simpl count.
  replace (0 != FT2R a) with true by (symmetry; apply /eqP; auto).
  simpl.
  set (l1 := (map FT2R l)) in *.
  change (count _ _) with n2.
  (* case split on whether the tail has any nonzeros *)
  assert (H7 : (n2 = 0)%nat \/ (1 <= n2)%nat) by lia.
  destruct H7 as [H7 | H7].
  + (* tail is all zeros: only one nonzero product *)
    rewrite H7.
    assert (H0 : eq_op n2 0%N) by lia.
    pose proof R_dot_prod_rel_nnzR l l0 Hlen1 s H2 H0; subst.
    pose proof dot_prod_rel_nnzR l l0 Hlen1 s0 H6 Hs0 H0.
    pose proof R_dot_prod_rel_nnzR_abs l l0 Hlen1 s1 H10 H0; subst.
    rewrite Bplus_0R; auto.
    destruct (BMULT_accurate' a f Haf) as (d' & e' & Hed' & Hd' & He' & Hacc).
    rewrite Hacc; clear Hacc.
    unfold g1, g; simpl.
    field_simplify; field_simplify_Rabs.
    eapply Rle_trans; [apply Rabs_triang |].
    apply Rplus_le_compat.
    { rewrite Rabs_mult Rmult_comm Rabs_mult Rmult_assoc.
      apply Rmult_le_compat_r; auto with commonDB.
      rewrite <- Rabs_mult; apply Rabs_pos. }
    eapply Rle_trans; [apply He' |]; auto with commonDB; nra.
  + (* tail has nonzeros: full inductive step *)
    destruct (BPLUS_accurate' (BMULT a f) s0 Hfin) as (d' & Hd' & Hacc).
    rewrite Hacc; clear Hacc.
    destruct (BMULT_accurate' a f Haf) as (d & e & Hed & Hd & He & Hacc).
    rewrite Hacc; clear Hacc.
    set (F := FT2R a * FT2R f).
    field_simplify_Rabs.
    replace (F * d * d' + F * d + F * d' + e * d' + e + FT2R s0 * d' + FT2R s0 - s)
      with ((F * d * d' + F * d + F * d' + FT2R s0 * d') +
            (FT2R s0 - s) + (1 + d') * e)
      by nra.
    eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans;
      [apply Rplus_le_compat;
        [eapply Rle_trans; [apply Rabs_triang |] |] |].
    { apply Rplus_le_compat_l; apply IHl. }
    { rewrite Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos | apply He]. }
    rewrite Rplus_assoc.
    eapply Rle_trans;
      [apply Rplus_le_compat_r;
        eapply Rle_trans; [apply Rabs_triang |] |].
    apply Rplus_le_compat_l.
    rewrite Rabs_mult Rmult_comm.
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hd' |].
    { apply Rabs_le_minus in IHl.
      assert (Hs : Rabs (FT2R s0) <=
                   g n2 * s1 + g1 n2 (n2 - 1) + s1).
      { eapply Rle_trans; [apply IHl |].
        apply Rplus_le_compat.
        - apply Rplus_le_compat.
          + apply Rmult_le_compat; auto with commonDB; try apply Rle_refl.
            rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 (zip l l0)) s1); auto.
            apply Rabs_pos.
          + apply Rle_refl.
        - rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 (zip l l0)) s1); auto.
          apply (dot_prod_sum_rel_R_Rabs (map FR2 (zip l l0))); auto. }
      apply Hs. }
    field_simplify.
    unfold g1, g in IHl; field_simplify in IHl.
    set (D := default_rel).
    set (E := default_abs).
    rewrite !Rplus_assoc.
    match goal with |- context [?A <= ?B] =>
      replace A with
        (Rabs (F * d * d' + (F * d + F * d')) +
         ((1 + D) * g n2 * s1 + D * s1) +
         (D * g1 n2 (n2 - 1) + (g1 n2 (n2 - 1) + Rabs (1 + d') * E)))
        by nra;
      replace B with
        (g (S n2) * Rabs F + s1 * g (S n2) + g1 (S n2) (S n2 - 1))
        by (rewrite Rmult_assoc -Rabs_mult -/F;
            replace (1 + n2)%nat with n2.+1 by lia; nra)
    end.
    apply Rplus_le_compat; [apply Rplus_le_compat |].
    * (* bound on |F * d * d' + (F * d + F * d')| *)
      unfold g.
      eapply Rle_trans; [apply Rabs_triang |].
      eapply Rle_trans;
        [apply Rplus_le_compat;
          [rewrite !Rabs_mult
          | eapply Rle_trans; [apply Rabs_triang |]] |].
      { apply Rmult_le_compat;
          [rewrite -!Rabs_mult; apply Rabs_pos | apply Rabs_pos | | apply Hd'].
        apply Rmult_le_compat_l; [rewrite -!Rabs_mult; apply Rabs_pos | apply Hd]. }
      { apply Rplus_le_compat; rewrite Rabs_mult.
        - apply Rmult_le_compat_l; [apply Rabs_pos | apply Hd].
        - apply Rmult_le_compat_l; [apply Rabs_pos | apply Hd']. }
      rewrite -!Rabs_mult.
      fold D F.
      replace (Rabs F * D * D + (Rabs F * D + Rabs F * D))
        with (((1 + D) * (1 + D) - 1) * Rabs F) by nra.
      apply Rmult_le_compat_r; [apply Rabs_pos |].
      unfold D, g.
      apply Rplus_le_compat; try nra.
      rewrite <- tech_pow_Rmult.
      apply Rmult_le_compat_l; auto with commonDB.
      eapply Rle_trans with ((1 + D) ^ 1); try nra.
      fold D; nra.
      apply Rle_pow; auto with commonDB; lia.
    * (* bound on the g-weighted sum term *)
      apply Req_le.
      unfold D, E.
      rewrite one_plus_d_mul_g Rmult_comm.
      repeat f_equal; try lia.
    * (* bound on the g1 absolute error term *)
      rewrite <- !Rplus_assoc.
      replace (D * g1 n2 (n2 - 1) + g1 n2 (n2 - 1))
        with (g1 n2 (n2 - 1) * (1 + D)) by nra.
      unfold D.
      rewrite one_plus_d_mul_g1; auto.
      eapply Rle_trans; [apply Rplus_le_compat_l |].
      { apply Rmult_le_compat_r; unfold E; auto with commonDB.
        assert (Rabs (1 + d') <= 1 + D).
        { eapply Rle_trans; [apply Rabs_triang |].
          rewrite Rabs_R1; apply Rplus_le_compat_l; apply Hd'. }
        apply H. }
      eapply Rle_trans; [apply plus_d_e_g1_le; auto |].
      apply Req_le; f_equal; lia.
Qed.

End SparseErrorRel1.

(** * Section 6: Sparse Forward Error Bound — FMA Dot Product *)

Section SparseErrorRel2.
(**
    Sparse forward error bound for the FMA-based dot product.

    As in [SparseErrorRel1], zero entries in do not contribute to
    rounding error accumulation.
*)

Context {NAN : FPCore.Nans} {t : type}.

Variables (v1 v2 : list (ftype t)).
Hypothesis (Hlen : size v1 = size v2).

Variable  (fp   : ftype t).
Hypothesis Hfp  : fma_dot_prod_rel (zip v1 v2) fp.
Hypothesis Hfin : Binary.is_finite fp = true.

Notation v1R  := (map FT2R v1).
Notation vR   := (map FR2 (zip v1 v2)).
Notation vR'  := (map Rabsp (map FR2 (zip v1 v2))).
Notation nnzR := (nnzR v1R).

Variable  (rp rp_abs : R).
Hypothesis Hrp  : R_dot_prod_rel vR rp.
Hypothesis Hra  : R_dot_prod_rel vR' rp_abs.

Notation g  := (@common.g t).
Notation g1 := (@common.g1 t).
Notation D  := (@default_rel t).
Notation E  := (@default_abs t).

(** [sparse_fma_dotprod_forward_error] establishes the sparse forward error
    bound for the FMA dot product.
*)

Lemma sparse_fma_dotprod_forward_error :
  Rabs (FT2R fp - rp) <= g nnzR * rp_abs + g1 nnzR (nnzR - 1).
Proof.
revert Hlen Hfp Hfin Hrp Hra.
revert rp rp_abs fp v2.
induction v1; intros.
{ (* base case: empty v1 *)
  simpl in Hlen; symmetry in Hlen; apply length_zero_iff_nil in Hlen; subst.
  inversion Hfp; inversion Hrp; subst; simpl; field_simplify_Rabs.
  rewrite Rabs_Ropp Rabs_R0.
  apply Rplus_le_le_0_compat; auto with commonDB.
  apply Rmult_le_pos; auto with commonDB.
  rewrite <- (R_dot_prod_rel_Rabs_eq [] rp_abs); auto.
  apply Rabs_pos. }
destruct v2; try discriminate.
assert (Hlen1 : size l = size l0) by (simpl; auto).
set (n2 := (common.nnzR (map FT2R l))%nat) in *.
inversion Hrp. inversion Hfp. inversion Hra; subst.
simpl fst in *; simpl snd in *.
destruct (BFMA_correct _ _ _ Hfin) as [[Ha [Hf Hs0]] Hfma].
specialize (IHl s s1 s0 l0 Hlen1 H6 Hs0 H2 H10).
(* case split on whether the head entry is zero *)
destruct (Req_EM_T (FT2R a) 0%R).
- (* head is zero: contributes no rounding error *)
  simpl map; rewrite e.
  move : (nnzR_cons [seq FT2R i | i <- l]) => /eqP H.
  rewrite {}H.
  replace (FT2R (BFMA a f s0)) with (FT2R s0).
  + change GRing.zero with R0.
    field_simplify_Rabs.
    eapply Rle_trans; [apply IHl |].
    apply Req_le; f_equal; try nra.
    unfold n2, common.nnzR.
    rewrite Rabs_R0 Rmult_0_l Rplus_0_l //.
  + pose proof Bfma_mult_0R a f s0 Hfin as A.
    destruct A; auto; rewrite A.
- (* head is nonzero: contributes to the error budget *)
  unfold common.nnzR.
  move : n => /eqP; rewrite eq_sym => n.
  rewrite /= n /=.
  set (l1 := (map FT2R l)) in *.
  change (count _ l1) with n2.
  (* case split on whether the tail has any nonzeros *)
  assert (A : (n2 = O)%nat \/ (1 <= n2)%nat) by lia.
  destruct A.
  + (* tail is all zeros: only one nonzero product *)
    rewrite H.
    assert (n2 == 0)%N by lia.
    pose proof R_dot_prod_rel_nnzR l l0 Hlen1 s H2 H0; subst.
    pose proof fma_dot_prod_rel_nnzR l l0 Hlen1 s0 H6 Hs0 H0.
    pose proof R_dot_prod_rel_nnzR_abs l l0 Hlen1 s1 H10 H0; subst.
    destruct (fma_accurate' a f s0 Hfin) as (e & d & ed & He & Hd & Hacc).
    rewrite Hacc H1; clear Hacc.
    unfold g1, g; simpl.
    field_simplify; field_simplify_Rabs.
    eapply Rle_trans; [apply Rabs_triang |].
    apply Rplus_le_compat.
    { rewrite Rabs_mult Rmult_comm Rabs_mult Rmult_assoc.
      apply Rmult_le_compat_r; auto with commonDB.
      rewrite <- Rabs_mult; apply Rabs_pos. }
    eapply Rle_trans; [apply Hd |]; auto with commonDB; nra.
  + (* tail has nonzeros: full inductive step *)
    pose proof (fma_accurate' a f s0 Hfin) as Hplus.
    destruct Hplus as (d' & e' & Hz & Hd' & He' & Hplus).
    rewrite Hplus; clear Hplus.
    field_simplify_Rabs.
    replace (FT2R a * FT2R f * d' + FT2R s0 * d' + FT2R s0 + e' - s)
      with (d' * (FT2R a * FT2R f) + d' * FT2R s0 + (FT2R s0 - s) + e')
      by nra.
    eapply Rle_trans;
      [apply Rabs_triang
      | eapply Rle_trans;
          [apply Rplus_le_compat_r; apply Rabs_triang |]].
    eapply Rle_trans; [apply Rplus_le_compat_r |].
    { apply Rplus_le_compat_r; apply Rabs_triang. }
    eapply Rle_trans;
      [apply Rplus_le_compat_r; apply Rplus_le_compat_l |].
    { apply IHl. }
    eapply Rle_trans;
      [apply Rplus_le_compat; [apply Rplus_le_compat_r | apply He'] |].
    { apply Rplus_le_compat.
      - rewrite Rabs_mult.
        apply Rmult_le_compat_r; [apply Rabs_pos | apply Hd'].
      - rewrite Rabs_mult.
        apply Rmult_le_compat; try apply Rabs_pos.
        + apply Hd'.
        + apply Rabs_le_minus in IHl.
          assert (Hs : Rabs (FT2R s0) <=
                       g n2 * s1 + g1 n2 (n2 - 1) + s1).
          { eapply Rle_trans; [apply IHl |].
            apply Rplus_le_compat_l.
            rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 (zip l l0)) s1); auto.
            apply (dot_prod_sum_rel_R_Rabs (map FR2 (zip l l0))); auto. }
          apply Hs. }
    set (F := Rabs (FT2R a * FT2R f)).
    rewrite !Rmult_plus_distr_l.
    replace (D * F +
             (D * (g n2 * s1) + D * g1 n2 (n2 - 1) + D * s1) +
             (g n2 * s1 + g1 n2 (n2 - 1)) + E)
      with (D * F + ((1 + D) * g n2 * s1 + D * s1) +
            g1 n2 (n2 - 1) * (1 + D) + E)
      by nra.
    rewrite one_plus_d_mul_g one_plus_d_mul_g1; auto.
    rewrite Rplus_assoc.
    apply Rplus_le_compat; [apply Rplus_le_compat |].
    * rewrite <- Rabs_mult; fold F.
      apply Rmult_le_compat_r; [unfold F; apply Rabs_pos |].
      apply d_le_g_1; lia.
    * apply Rmult_le_compat_r.
      { rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 (zip l l0)) s1); auto.
        apply Rabs_pos. }
      apply Req_le; f_equal; auto; lia.
    * eapply Rle_trans; [apply plus_e_g1_le; auto |].
      replace (1 + n2 - 1)%nat with n2 by lia.
      change (1 + n2)%nat with n2.+1.
      lra.
Qed.

End SparseErrorRel2.