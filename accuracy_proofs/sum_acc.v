(** * Floating-Point Summation Accuracy Theorems

    This file establishes backward and forward error bounds for floating-point
    summation, in both list-based and ordinal-indexed forms.

    ** Error Factors

    Throughout, the accumulated relative error factor is
    %$g(n) = (1 + \mathbf{u})^n - 1$%#\(g(n) = (1 + \mathbf{u})^n - 1\)#,
    where %$\mathbf{u}$%#\(\mathbf{u}\)# is the unit roundoff for the given
    floating-point type. It is defined in [common].

    ** Main Results

    - [bSUM]: Shows that the computed floating-point sum can be expressed as
      the exact sum of a slightly perturbed input list. Each input element is
      perturbed by a relative factor bounded by
      %$g(n-1)$%#\(g(n-1)\)#, where %$n$%#\(n\)# is the list length.

    - [Fsum_backward_error]: The ordinal-indexed analogue of [bSUM], expressing
      the same backward error bound for functions indexed by finite ordinals.

    - [fSUM]: Bounds the absolute forward error of the computed sum by
      %$g(n) \cdot \sum |x_i|$%#\(g(n) \cdot \sum |x_i|\)#, where
      %$n$%#\(n\)# is the list length.

    - [Fsum_forward_error]: The ordinal-indexed analogue of [fSUM].

    - [sum_forward_error_permute]: Shows that the forward error bound is stable
      under permutation of the input list, so the bound holds regardless of the
      order in which elements are summed.

    ** Dependencies

    This file relies on:
    - [preamble], [common]: basic setup and shared definitions
    - [sum_model]: the floating-point summation model [sumF] and [sumR]
    - [float_acc_lems]: elementary floating-point accuracy lemmas

*)

From LAProof.accuracy_proofs Require Import  preamble common sum_model float_acc_lems.
From LAProof Require mv_mathcomp.
From Stdlib Require Import Permutation.

Section WithNan.

Context {NAN : FPCore.Nans} {t : type}.

Notation g        := (@g t).
Notation D        := (@default_rel t).
Notation neg_zero := (@common.neg_zero t).

(** ** Backward Error: List Version *)

(** [bSUM] expresses the computed floating-point sum as the exact real sum of
    a slightly perturbed input list. Each element of the perturbed list differs
    from the corresponding input by a relative factor bounded by
    %$g(n-1)$%#\(g(n-1)\)#, where %$n$%#\(n\)# is the list length. *)

Theorem bSUM :
  forall (x : list (ftype t))
         (Hfin : Binary.is_finite (sumF x)),
  exists (x' : list R),
    size x' = size x /\
    FT2R (sumF x) = sumR x' /\
    (forall n,
      (n < size x')%nat ->
      exists delta,
        nth 0 x' n = FT2R (nth neg_zero x n) * (1 + delta) /\
        Rabs delta <= g (size x' - 1)).
Proof.
move=> x.
rewrite /sumF -(revK x) foldl_rev size_rev.
induction (rev x) as [| a l] => Hfin; clear x.
- (* base case: empty list *)
  exists []; repeat split; auto => //=.
- (* case a::l *)
  have Hl : l = [] \/ l <> []. {
    destruct l; auto; right; congruence.
  }
  destruct Hl as [Hl | Hl].
  + (* case empty l *)
    subst; simpl in *;
    destruct (BPLUS_finite_e _ _ Hfin) as [Ha Hb].
    exists [FT2R a]; split; [simpl; auto | split;
      [rewrite Bplus_0R|]] => //.
    unfold sumR; simpl; nra.
    intros n Hn; exists 0; simpl in Hn; split.
    rewrite Rplus_0_r Rmult_1_r.
    have H3 : (n = 1)%nat \/ (n = 0)%nat by lia.
    destruct H3 as [Hn1 | Hn0]; subst; auto.
    rewrite Rabs_R0 /g /=. lra.
  + (* case non-empty l *)
    simpl in *.
    destruct (BPLUS_finite_e _ _ Hfin) as [Ha Hb].
    (* IHl *)
    pose proof (size_not_empty_nat l Hl) as Hlen1.
    specialize (IHl Hb).
    destruct IHl as (l' & Hlen' & Hsum & Hdel); auto.
    rewrite {1}/Basics.flip in Hfin.
    (* construct l'0 *)
    pose proof (BPLUS_accurate' _ _ Hfin) as Hplus.
    destruct Hplus as (d' & Hd' & Hplus).
    rewrite /Basics.flip in Hsum, Hb, Hplus |- *.
    change (fun x z => @BPLUS NAN t x z) with (@BPLUS _ t) in Hsum, Hb, Hplus |- *.
    exists (map (Rmult (1+d')) l' ++ [:: FT2R a * (1+d')]); repeat split.
    * rewrite size_cat size_map /= Hlen' addnC //.
    * rewrite {}Hplus Hsum Rmult_plus_distr_r -sumR_app_cons cats0 sumR_mult //.
    * move=> n Hn.
      rewrite nth_cat.
      rewrite size_cat size_map in Hn |- *; simpl size in Hn.
      destruct (n < size l')%N eqn:Hn_lt.
      -- rewrite (nth_map R0); [| lia].
         specialize (Hdel n Hn_lt).
         destruct Hdel as (d & Hd1 & Hd2).
         exists ((1+d') * (1+d) - 1).
         rewrite {}Hd1; split.
         ++ fold (ftype t).
            rewrite rev_cons nth_rcons size_rev.
            destruct (n < size l)%N eqn:Hn'; [| lia]; nra.
         ++ field_simplify_Rabs.
            eapply Rle_trans;
              [apply Rabs_triang |
               eapply Rle_trans;
                 [apply Rplus_le_compat_r; apply Rabs_triang |]].
            rewrite Rabs_mult.
            replace (Rabs d' * Rabs d + Rabs d' + Rabs d)
              with ((1 + Rabs d') * Rabs d + Rabs d') by nra.
            eapply Rle_trans; [apply Rplus_le_compat |].
            apply Rmult_le_compat; try apply Rabs_pos.
            apply Fourier_util.Rle_zero_pos_plus1; try apply Rabs_pos.
            apply Rplus_le_compat_l; apply Hd'.
            apply Hd2. apply Hd'.
            replace ((1 + D) * g (size l' - 1) + D)
              with ((1 + D) * g (size l' - 1) * 1 + D * 1) by nra.
            rewrite one_plus_d_mul_g; apply Req_le.
            rewrite Rmult_1_r /=; f_equal; lia.
      -- fold (ftype t).
         assert (Hn_eq : n = size l') by lia; subst n.
         rewrite nth_rev /=; [| lia].
         rewrite -Hlen'; do 2 replace (_ - _)%N with O by lia; simpl.
         exists d'; split; auto.
         eapply Rle_trans; [apply Hd' |].
         apply d_le_g_1; lia.
Qed.

(** ** Backward Error: Indexed Version *)

(** [Fsum_backward_error] lifts [bSUM] to functions indexed by finite
    ordinals. The computed sum equals the exact sum of a perturbed family,
    with each element perturbed by a relative factor bounded by
    %$g(n-1)$%#\(g(n-1)\)#. *)

Theorem Fsum_backward_error :
  forall [n] (x : 'I_n -> ftype t)
         (Hfin : Binary.is_finite (mv_mathcomp.F.sum x)),
  exists (x' : 'I_n -> R),
    FT2R (mv_mathcomp.F.sum x) = \sum_i x' i /\
    (forall i : 'I_n,
      exists delta,
        x' i = FT2R (x i) * (1 + delta) /\
        Rabs delta <= g (n - 1)).
Proof.
move=> n x Hfin.
have Hfin' : Binary.is_finite (sumF (map x (ord_enum n))).
{ rewrite -mv_mathcomp.F.sum_sumF //. }
destruct (bSUM _ Hfin') as [x' [Hsize [Hsum Hdel]]].
rewrite size_map mv_mathcomp.size_ord_enum in Hsize; subst n.
exists (nth R0 x'); split.
- rewrite mv_mathcomp.F.sum_sumF Hsum mv_mathcomp.sumR_sum //.
- move=> i.
  destruct (Hdel i) as [delta [H2 H3]].
  { destruct i; simpl; lia. }
  exists delta.
  rewrite {}H2.
  change GRing.mul with Rmult.
  change GRing.add with Rplus.
  change (GRing.one _) with 1%Re.
  split; auto.
  clear H3; f_equal; f_equal; clear.
  destruct (size x'); clear x'.
  { simpl; destruct i; lia. }
  rewrite (nth_map (@ord0 n) common.neg_zero).
  rewrite mv_mathcomp.nth_ord_enum' //.
  rewrite mv_mathcomp.size_ord_enum.
  pose proof ltn_ord i; lia.
Qed.

(** ** Forward Error: List Version *)

(** [fSUM] bounds the absolute forward error of the computed floating-point
    sum by %$g(n) \cdot \sum |x_i|$%#\(g(n) \cdot \sum |x_i|\)#, where
    %$n$%#\(n\)# is the list length and %$|x_i|$%#\(|x_i|\)# denotes the
    componentwise absolute values of the inputs. *)

Theorem fSUM :
  forall (x : list (ftype t))
         (Hfin : Binary.is_finite (sumF x)),
    Rabs (sumR (map FT2R x) - FT2R (sumF x)) <=
      g (size x) * sumR (map Rabs (map FT2R x)).
Proof.
move=> x.
rewrite -(revK x).
induction (rev x) as [| a l]; clear x => Hfin.
- (* base case: empty list *)
  unfold g; subst; simpl.
  rewrite Rminus_0_r Rabs_R0; nra.
- (* case a::l *)
  assert (Hl : l = [] \/ l <> []) by (destruct l; auto; right; congruence).
  destruct Hl as [Hl | Hl].
  + (* case empty l *)
    subst; unfold g; simpl.
    destruct (BPLUS_finite_e _ _ Hfin) as [Ha Hb].
    rewrite Bplus_0R; auto.
    field_simplify_Rabs; field_simplify; rewrite Rabs_R0.
    apply Rmult_le_pos; auto with commonDB; apply Rabs_pos.
  + (* case non-empty l *)
    rewrite /sumF foldl_rev /= in Hfin.
    change (fun x z : ftype t => Basics.flip BPLUS z x) with (@BPLUS _ t) in Hfin.
    destruct (BPLUS_finite_e _ _ Hfin) as [Ha Hb].
    (* IHl *)
    rewrite -foldl_rev in Hb.
    specialize (IHl Hb).
    (* accuracy rewrites *)
    destruct (BPLUS_accurate' _ _ Hfin) as (d' & Hd' & Hplus).
    move :IHl.
    rewrite /sumF !foldl_rev.
    change (fun x z : ftype t => Basics.flip BPLUS z x) with (@BPLUS _ t).
    rewrite !map_rev !sumR_rev !size_rev => IHl.
    simpl.
    rewrite {}Hplus.
    (* algebra *)
    field_simplify_Rabs.
    set s0 := sumR (map FT2R l).
    set (s := foldr _ _ l).
    replace (- FT2R a * d' + s0 - FT2R s * d' - FT2R s)
      with ((s0 - FT2R s) - d' * (FT2R s + FT2R a)) by nra.
    eapply Rle_trans;
      [apply Rabs_triang |
       eapply Rle_trans; [apply Rplus_le_compat_r | rewrite !Rabs_Ropp]].
    apply IHl.
    eapply Rle_trans; [apply Rplus_le_compat_l |].
    rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos.
    apply Hd'.
    eapply Rle_trans; [apply Rabs_triang | apply Rplus_le_compat_r].
    rewrite Rabs_minus_sym in IHl; apply Rabs_le_minus in IHl; apply IHl.
    rewrite !Rmult_plus_distr_l -!Rplus_assoc.
    set (s1 := sumR (map Rabs (map FT2R l))).
    replace (g (size l) * s1 + D * (g (size l) * s1))
      with ((1 + D) * g (size l) * s1) by nra.
    eapply Rle_trans;
      [apply Rplus_le_compat_r;
       apply Rplus_le_compat_l;
       apply Rmult_le_compat_l; try apply Rabs_pos |].
    apply default_rel_ge_0.
    apply sumR_le_sumRabs.
    rewrite sumRabs_Rabs one_plus_d_mul_g Rplus_comm.
    apply size_not_empty_nat in Hl.
    apply Rplus_le_compat.
    apply Rmult_le_compat; try apply Rabs_pos;
      try apply default_rel_ge_0; try nra.
    apply d_le_g_1; lia.
    apply Req_le; f_equal; f_equal; lia.
Qed.

(** ** Forward Error: Indexed Version *)

(** [Fsum_forward_error] lifts [fSUM] to functions indexed by finite
    ordinals, giving the same %$g(n) \cdot \sum |x_i|$%#\(g(n) \cdot \sum |x_i|\)#
    bound for the absolute forward error of the indexed sum. *)

Lemma Fsum_forward_error :
  forall [n] (x : 'I_n -> ftype t)
         (Hfin : Binary.is_finite (mv_mathcomp.F.sum x)),
    Rabs (\sum_i (FT2R (x i)) - FT2R (mv_mathcomp.F.sum x)) <=
      g n * (\sum_i (Rabs (FT2R (x i)))).
Proof.
move=> n x Hfin.
have Hfin' : Binary.is_finite (sumF (map x (ord_enum n))).
{ rewrite -mv_mathcomp.F.sum_sumF //. }
move: (fSUM _ Hfin') => H.
rewrite !mv_mathcomp.sumR_sum !size_map !mv_mathcomp.size_ord_enum -map_comp in H.
rewrite mv_mathcomp.F.sum_sumF.
match goal with
| H : Rle (Rabs (Rminus ?A _)) (Rmult _ ?B)
  |- Rle (Rabs (Rminus ?A' _)) (Rmult _ ?B') =>
    replace A' with A; [replace B' with B |]; auto; clear
end.
- apply eq_bigr => i _.
  destruct n; [destruct i; lia |].
  rewrite -map_comp.
  rewrite (nth_map (@ord0 n) R0).
  rewrite mv_mathcomp.nth_ord_enum' //.
  rewrite mv_mathcomp.size_ord_enum //.
- apply eq_bigr => i _.
  destruct n; [destruct i; lia |].
  rewrite (nth_map (@ord0 n) R0).
  rewrite mv_mathcomp.nth_ord_enum' //.
  rewrite mv_mathcomp.size_ord_enum //.
Qed.

(** ** Forward Error Under Permutation *)

(** [sum_forward_error_permute'] is an auxiliary lemma: when two lists are
    permutations of each other, the forward error bound for the computed sum
    of either list can be expressed using the length of the original list.
    Used internally by [sum_forward_error_permute]. *)

Lemma sum_forward_error_permute' :
  forall (x x0 : list (ftype t))
         (Hfin  : Binary.is_finite (sumF x))
         (Hfin0 : Binary.is_finite (sumF x0))
         (Hper  : Permutation x x0),
    Rabs ((sumR (map FT2R x0)) - FT2R (sumF x0)) <=
      g (size x) * (sumR (map Rabs (map FT2R x0))).
Proof.
move=> x x0 Hfin Hfin0 Hper.
eapply Rle_trans; [apply (fSUM x0 Hfin0) |].
apply Req_le; f_equal.
change @size with @length.
rewrite (Permutation_length Hper); auto.
Qed.

(** [sum_forward_error_permute] shows that the forward error bound for the
    computed sum is invariant under permutation of the input. If two lists
    are permutations of each other, the absolute forward error for either
    computed sum is bounded by
    %$g(n) \cdot \sum |x_i|$%#\(g(n) \cdot \sum |x_i|\)#
    using the shared element set and length %$n$%#\(n\)#. *)

Theorem sum_forward_error_permute :
  forall (x x0 : list (ftype t))
         (Hfin  : Binary.is_finite (sumF x))
         (Hfin0 : Binary.is_finite (sumF x0))
         (Hper  : Permutation x x0),
    Rabs ((sumR (map FT2R x)) - FT2R (sumF x0)) <=
      g (size x) * (sumR (map Rabs (map FT2R x))).
Proof.
move=> x x0 Hfin Hfin0 Hper.
rewrite (sumR_permute (map FT2R x) (map FT2R x0));
  [| apply Permutation_map; auto].
eapply Rle_trans; [apply sum_forward_error_permute'; eauto |].
apply Req_le; f_equal; symmetry.
f_equal; apply Permutation_length; auto.
apply sumR_permute.
repeat apply Permutation_map; auto.
Qed.

End WithNan.
