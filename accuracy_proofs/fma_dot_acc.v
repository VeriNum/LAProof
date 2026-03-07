(** * FMA Dot Product Accuracy Theorems

    This file establishes three main accuracy theorems for the fused
    multiply-add (FMA) dot product computation [fma_dotprod].

    The significance of these results is that they provide rigorous
    floating-point error bounds for dot products computed using FMA
    instructions, which are critical in numerical linear algebra.

    ** Error Factors

    Throughout, the accumulated relative error factor is
    %$g(n) = (1 + \mathbf{u})^n - 1$%#\(g(n) = (1 + \mathbf{u})^n - 1\)# and
    the mixed absolute error factor is
    %$g_1(n_1, n_2) = n_1 \cdot \eta \cdot (1 + g(n_2))$%#\(g_1(n_1, n_2) = n_1 \cdot \eta \cdot (1 + g(n_2))\)#,
    where %$\mathbf{u}$%#\(\mathbf{u}\)# is the unit roundoff and
    %$\eta$%#\(\eta\)# is the underflow threshold for the given type.
    Both are defined in [common].

    ** Main Results

    - [fma_dotprod_mixed_error]: Shows that the FMA-computed dot product
      can be expressed as an exact dot product of slightly perturbed inputs
      plus a small absolute error term.

    - [fma_dotprod_forward_error]: Bounds the absolute forward error
      %$|\mathtt{fl}_{\mathrm{fma}}(v_1 \cdot v_2) - v_1 \cdot v_2|$%#\(|\mathtt{fl}_{\mathrm{fma}}(v_1 \cdot v_2) - v_1 \cdot v_2|\)#.

    - [fma_sparse_dotprod_forward_error]: Refines [fma_dotprod_forward_error]
      for sparse inputs by replacing the full vector length %$n$%#\(n\)# with
      the number of nonzero entries,
      giving a tighter bound when the input vectors are sparse.

    ** Dependencies

    This file relies on:
    - [preamble], [common]: basic setup and shared definitions
    - [dotprod_model], [sum_model]: relational models of FMA dot product
      and summation
    - [float_acc_lems]: elementary floating-point accuracy lemmas
    - [dot_acc_lemmas]: dot-product-specific accuracy lemmas
*)

From LAProof.accuracy_proofs Require Import preamble common
                                            dotprod_model sum_model
                                            float_acc_lems dot_acc_lemmas.

(** * Mixed Error *)
Section MixedError.
Context {NAN : FPCore.Nans} {t : type}.

Notation g        := (@g t).
Notation g1       := (@g1 t).
Notation D        := (@default_rel t).
Notation E        := (@default_abs t).
Notation neg_zero := (@common.neg_zero t).

Variables (v1 v2 : list (ftype t)).
Hypothesis Hlen : size v1 = size v2.
Hypothesis Hfin : Binary.is_finite (fma_dotprod v1 v2) = true.

(** [fma_dotprod_mixed_error] expresses the FMA-computed dot product as an
    exact inner product of component-wise perturbed inputs plus a small
    absolute offset. The relative perturbation on each input component is
    bounded by %$g(n)$%#\(g(n)\)# and the absolute residual by
    %$g_1(n,\,n-1)$%#\(g_1(n,n-1)\)#. *)
    
Lemma fma_dotprod_mixed_error :
  exists (u : list R) (eta : R),
    size u = size v1 /\
    FT2R (fma_dotprod v1 v2) = dotprodR u (map FT2R v2) + eta /\
    (forall n, (n < size v2)%nat ->
      exists delta,
        nth 0 u n = FT2R (nth neg_zero v1 n) * (1 + delta) /\
        Rabs delta <= g (size v2)) /\
    Rabs eta <= g1 (size v2) (size v2 - 1).
Proof.
  assert (Hzip  : size (zip v1 v2) = size v1) by (rewrite size_zip; lia).
  assert (Hlenr : size (rev v1) = size (rev v2)) by (rewrite !size_rev; auto).
  rewrite <- size_rev in Hlen.
  pose proof fma_dot_prod_rel_fold_right v1 v2 as Hrel.
  rewrite rev_zip in Hrel. 2: revert Hlen; rewrite size_rev; auto.
  revert Hlen; rewrite size_rev; intro Hlen.
  pose proof (fma_dotprod_mixed_error_rel
                (rev v1) (rev v2) Hlenr
                (fma_dotprod v1 v2) Hrel Hfin)
    as (u & eta & Hsize & Heq & Hbnd & Heta).
  exists (rev u), eta.
  repeat split.
  - (* size rev u = size v1 *)
    rewrite !size_rev in Hsize |-*; auto.
  - (* FT2R (fma_dotprod v1 v2) = dotprodR (rev u) (map FT2R v2) + eta *)
    pose proof dotprodR_rel u (map FT2R (rev v2)) as Hdot.
    assert (Heqr : dotprodR (rev u) (map FT2R v2) =
                     FT2R (fma_dotprod v1 v2) - eta).
    { eapply R_dot_prod_rel_eq; eauto.
      rewrite <- dotprodR_rev, <- map_rev; auto.
      rewrite size_rev in Hsize; rewrite size_map; auto; lia. }
    nra.
  - (* per-index bound on entries of rev u *)
    rewrite !size_rev in Hbnd.
    intros n Hn.
    rewrite size_rev in Hsize.
    assert (Hlt : (size u - S n < size v2)%nat) by lia.
    specialize (Hbnd (size u - S n)%nat Hlt).
    rewrite nth_rev in Hbnd. 2: rewrite Hlen //.
    rewrite nth_rev.          2: rewrite Hsize Hlen //.
    destruct Hbnd as (delta & Hnth & Hdelta).
    exists delta; split.
    + rewrite Hnth; repeat f_equal.
      rewrite Hlen Hsize. rewrite <- Nat.sub_succ_l; simpl; lia.
    + exact Hdelta.
  - (* |eta| <= g1(|v2|, |v2| - 1) *)
    rewrite !size_rev in Heta; auto.
Qed.

End MixedError.


(** * Forward Error *)
Section ForwardError.
Context {NAN : FPCore.Nans} {t : type}.

Variables v1 v2 : list (ftype t).

Notation v1R   := (map FT2R v1).
Notation v2R   := (map FT2R v2).
Notation v1R'  := (map Rabs v1R).
Notation v2R'  := (map Rabs v2R).
Notation n     := (size v2).
Notation g     := (@g t).
Notation g1    := (@g1 t).
Notation neg_zero := (@common.neg_zero t).

Hypothesis Hlen : size v1 = size v2.
Hypothesis Hfin : Binary.is_finite (fma_dotprod v1 v2) = true.

(** [fma_dotprod_forward_error] bounds the absolute forward error of the
    FMA-computed dot product. *)
    
Lemma fma_dotprod_forward_error :
  Rabs (FT2R (fma_dotprod v1 v2) - dotprodR v1R v2R)
    <= g n * dotprodR v1R' v2R' + g1 n (n - 1).
Proof.
  pose proof R_dot_prod_rel_fold_right' t v1 v2 Hlen as HB.
  pose proof R_dot_prod_rel_fold_right_Rabs' t v1 v2 Hlen as HC.
  simpl in HB, HC.
  rewrite <- map_rev in HC, HB.
  rewrite <- map_rev in HC.
  pose proof fma_dotprod_forward_error_rel
               (rev (zip v1 v2))
               (fma_dotprod v1 v2)
               (fma_dot_prod_rel_fold_right _ _)
               Hfin
               (dotprodR v1R v2R)
               (dotprodR v1R' v2R')
               HB HC as H.
  rewrite size_rev size_zip Hlen minnn in H.
  exact H.
Qed.

Notation nnzR := (common.nnzR v1R).

(** [fma_sparse_dotprod_forward_error] refines [fma_dotprod_forward_error]
    for sparse inputs by replacing the full vector length %$n$%#\(n\)# with
    the number of nonzero entries. *)
    
Lemma fma_sparse_dotprod_forward_error :
  Rabs (FT2R (fma_dotprod v1 v2) - dotprodR v1R v2R)
    <= g nnzR * dotprodR v1R' v2R' + g1 nnzR (nnzR - 1).
Proof.
  pose proof fma_dot_prod_rel_fold_right v1 v2 as HA.
  pose proof R_dot_prod_rel_fold_right' t v1 v2 Hlen as HB.
  pose proof R_dot_prod_rel_fold_right_Rabs' t v1 v2 Hlen as HC.
  simpl in HB, HC.
  rewrite <- map_rev in HC, HB.
  rewrite <- map_rev in HC.
  pose proof sparse_fma_dotprod_forward_error (rev v1) (rev v2) as H.
  rewrite !size_rev -rev_zip in H; auto.
  specialize (H Hlen
                (fma_dotprod v1 v2) HA Hfin
                (dotprodR v1R v2R)
                (dotprodR v1R' v2R')
                HB HC).
  rewrite map_rev in H.
  unfold common.nnzR, nnzR in H.
  rewrite !count_rev in H.
  exact H.
Qed.

End ForwardError.