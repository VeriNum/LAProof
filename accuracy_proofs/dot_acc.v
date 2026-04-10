(** * Dot Product Accuracy Proofs (Non-FMA)

    This file establishes floating-point accuracy bounds for the non-fused
    multiply-add (non-FMA) dot product computation over lists of floating-point
    numbers. It provides both mixed-error and forward-error analyses, as well
    as a refined bound for sparse vectors.

    ** Error Factors

    Throughout, the accumulated relative error factor is
    %$g(n) = (1 + \mathbf{u})^n - 1$%#\(g(n) = (1 + \mathbf{u})^n - 1\)# and
    the mixed absolute error factor is
    %$g_1(n_1, n_2) = n_1 \cdot \eta \cdot (1 + g(n_2))$%#\(g_1(n_1, n_2) = n_1 \cdot \eta \cdot (1 + g(n_2))\)#,
    where %$\mathbf{u}$%#\(\mathbf{u}\)# is the unit roundoff and
    %$\eta$%#\(\eta\)# is the underflow threshold for the given floating-point type.
    Both are defined in [common].

    ** Main Results

    - [dotprod_mixed_error]: Shows that the computed dot product can be
      expressed as an exact dot product of slightly perturbed inputs plus a
      small absolute error term. Each input component is perturbed by a
      relative factor bounded by %$g(n)$%#\(g(n)\)#, and the absolute
      residual is bounded by %$g_1(n, n)$%#\(g_1(n,n)\)#, where
      %$n$%#\(n\)# is the vector length.

    - [dotprod_forward_error]: Bounds the absolute forward error
      %$|\mathtt{fl}(v_1 \cdot v_2) - v_1 \cdot v_2|$%#\(|\mathtt{fl}(v_1 \cdot v_2) - v_1 \cdot v_2|\)#
      by %$g(n)\,(|v_1| \cdot |v_2|) + g_1(n,\, n-1)$%#\(g(n)\,(|v_1| \cdot |v_2|) + g_1(n,\,n-1)\)#,
      where %$|v|$%#\(|v|\)# denotes componentwise absolute value.

    - [sparse_dotprod_forward_error]: Refines [dotprod_forward_error] for
      sparse inputs by replacing the full vector length %$n$%#\(n\)# with
      the number of nonzero entries %$n_{\mathrm{nz}}$%#\(n_{\mathrm{nz}}\)#,
      giving a tighter bound when the input vectors are sparse.

    ** Dependencies

    This file relies on the following modules from [LAProof.accuracy_proofs]:
    - [preamble]: basic setup and notation,
    - [common]: shared definitions including << nnzR >> and << neg_zero >>,
    - [dotprod_model]: the floating-point model [dotprodF] and its relational
      characterization [dotprodF_rel_fold_right],
    - [sum_model]: summation model infrastructure,
    - [float_acc_lems]: generic floating-point accuracy lemmas,
    - [dot_acc_lemmas]: the core relational accuracy lemmas
      [dotprod_mixed_error_rel], [dotprod_forward_error_rel], and
      [sparse_dotprod_forward_error_rel] that drive the proofs here.

    ** Structure

    The file is organised into two [Section]s:
    - [MixedError]: proves [dotprod_mixed_error].
    - [ForwardError]: proves [dotprod_forward_error] and
      [sparse_dotprod_forward_error].
*)

From LAProof.accuracy_proofs Require Import
  preamble
  common
  dotprod_model
  sum_model
  float_acc_lems
  dot_acc_lemmas.

From Stdlib Require Import Reals.

Open Scope R.

(* ------------------------------------------------------------------ *)
Section MixedError.

Context {NAN : FPCore.Nans} {t : type}.

Notation g       := (@g t).
Notation g1      := (@g1 t).
Notation D       := (@default_rel t).
Notation E       := (@default_abs t).
Notation neg_zero := (@common.neg_zero t).

Variables (v1 v2 : list (ftype t)).

Hypothesis Hlen : size v1 = size v2.
Hypothesis Hfin : Binary.is_finite (dotprodF v1 v2) = true.

(** [dotprod_mixed_error] expresses the computed dot product as an exact inner
    product of component-wise perturbed inputs plus a small absolute offset.
    The relative perturbation on each input component is bounded by
    %$g(n)$%#\(g(n)\)# and the absolute residual by %$g_1(n,n)$%#\(g_1(n,n)\)#. *)

Lemma dotprod_mixed_error :
  exists (u : list R) (eta : R),
    size u = size v2
    /\ FT2R (dotprodF v1 v2) = dotprodR u (map FT2R v2) + eta
    /\ (forall n, (n < size v2)%nat ->
          exists delta,
            nth 0 u n = FT2R (nth neg_zero v1 n) * (1 + delta)
            /\ Rabs delta <= g (size v2))
    /\ Rabs eta <= g1 (size v2) (size v2).
Proof.
  assert (Hzip : size (zip v1 v2) = size v1) by
    (rewrite size_zip; lia).
  assert (Hlenr : size (rev v1) = size (rev v2)) by
    (rewrite !size_rev; auto).
  rewrite <- size_rev in Hlen.
  pose proof dotprodF_rel_fold_right v1 v2 as Hfold.
  move: Hlen; rewrite size_rev => Hlen'.
  rewrite rev_zip in Hfold; auto.
  pose proof
    (dotprod_mixed_error_rel
       (rev v1) (rev v2) Hlenr (dotprodF v1 v2) Hfold Hfin)
    as (u & eta & Hsize_u & Hval_eq & Helem_bound & Heta_bound).
  exists (rev u), eta.
  repeat split.
  - (* size *)
    move: Hsize_u; rewrite !size_rev //.
  - (* value equation *)
    pose proof dotprodR_rel u (map FT2R (rev v2)) as Hdot_rel.
    assert (Heq : dotprodR (rev u) (map FT2R v2) = FT2R (dotprodF v1 v2) - eta).
    { eapply R_dot_prod_rel_eq; eauto.
      rewrite -dotprodR_rev;
        [ | rewrite size_map; rewrite size_rev in Hsize_u; auto].
      rewrite -map_rev; auto. }
    nra.
  - (* per-element bound *)
    rewrite !size_rev in Helem_bound, Hsize_u, Heta_bound.
    intros n Hn.
    assert (Hlt : (size u - S n < size v2)%nat) by lia.
    specialize (Helem_bound (size u - S n)%nat Hlt).
    rewrite nth_rev in Helem_bound; [ | rewrite Hlen' //].
    rewrite nth_rev; [ | lia].
    destruct Helem_bound as (delta & Hval & Hdelta).
    exists delta; split.
    + rewrite Hval; repeat f_equal.
      rewrite Hlen' Hsize_u.
      rewrite <- Nat.sub_succ_l; [simpl; lia | lia].
    + exact Hdelta.
  - (* eta bound *)
    rewrite !size_rev in Heta_bound; auto.
Qed.

End MixedError.

(* ------------------------------------------------------------------ *)
Section ForwardError.

Context {NAN : FPCore.Nans} {t : type}.

Variables v1 v2 : list (ftype t).

Notation v1R  := (map FT2R v1).
Notation v2R  := (map FT2R v2).
Notation v1R' := (map Rabs v1R).
Notation v2R' := (map Rabs v2R).
Notation n    := (size v2).

Notation g  := (@g t).
Notation g1 := (@g1 t).

Hypothesis Hlen : size v1 = size v2.
Hypothesis Hfin : Binary.is_finite (dotprodF v1 v2) = true.

(** [dotprod_forward_error] bounds the absolute forward error of the computed
    dot product by %$g(n)\,(|v_1| \cdot |v_2|) + g_1(n,\,n-1)$%#\(g(n)\,(|v_1| \cdot |v_2|) + g_1(n,\,n-1)\)#,
    where %$|v|$%#\(|v|\)# denotes the componentwise absolute-value vector. *)

Lemma dotprod_forward_error :
  Rabs (FT2R (dotprodF v1 v2) - dotprodR v1R v2R)
  <= g n * dotprodR v1R' v2R' + g1 n (n - 1).
Proof.
  pose proof R_dot_prod_rel_fold_right' t v1 v2 Hlen as HB.
  pose proof R_dot_prod_rel_fold_right_Rabs' t v1 v2 Hlen as HC.
  simpl in HB, HC.
  rewrite <- map_rev in HC, HB.
  rewrite <- map_rev in HC.
  pose proof
    (dotprod_forward_error_rel
       (rev (zip v1 v2))
       (dotprodF v1 v2)
       (dotprodF_rel_fold_right _ _)
       Hfin
       (dotprodR v1R v2R)
       (dotprodR v1R' v2R')
       HB HC) as H.
  rewrite size_rev size_zip Hlen minnn in H.
  exact H.
Qed.

Notation nnzR := (common.nnzR v1R).

(** [sparse_dotprod_forward_error] refines [dotprod_forward_error] for sparse
    inputs: the vector length %$n$%#\(n\)# is replaced by the number of
    nonzero entries %$n_{\mathrm{nz}}$%#\(n_{\mathrm{nz}}\)#, yielding
    %$g(n_{\mathrm{nz}})\,(|v_1| \cdot |v_2|) + g_1(n_{\mathrm{nz}},\,n_{\mathrm{nz}}-1)$%#\(g(n_{\mathrm{nz}})\,(|v_1| \cdot |v_2|) + g_1(n_{\mathrm{nz}},\,n_{\mathrm{nz}}-1)\)#. *)

Lemma sparse_dotprod_forward_error :
  Rabs (FT2R (dotprodF v1 v2) - dotprodR v1R v2R)
  <= g nnzR * dotprodR v1R' v2R' + g1 nnzR (nnzR - 1).
Proof.
  pose proof dotprodF_rel_fold_right v1 v2 as HA.
  pose proof R_dot_prod_rel_fold_right' t v1 v2 Hlen as HB.
  pose proof R_dot_prod_rel_fold_right_Rabs' t v1 v2 Hlen as HC.
  simpl in HB, HC.
  rewrite <- map_rev in HC, HB.
  rewrite <- map_rev in HC.
  pose proof sparse_dotprod_forward_error_rel (rev v1) (rev v2) as H.
  rewrite !size_rev -rev_zip in H; auto.
  specialize (H Hlen
                (dotprodF v1 v2) HA Hfin
                (dotprodR v1R v2R)
                (dotprodR v1R' v2R')
                HB HC).
  rewrite map_rev in H.
  unfold common.nnzR, nnzR in H.
  rewrite !count_rev in H.
  exact H.
Qed.

End ForwardError.