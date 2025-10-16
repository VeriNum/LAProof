(** This file contains three main theorems for the accuracy of the fma
  dot product : fma_dotprod_mixed_error, fma_dotprod_forward_error, 
  and fma_sparse_dotprod_forward_error. *)

From LAProof.accuracy_proofs Require Import preamble common 
                                            dotprod_model sum_model
                                            float_acc_lems dot_acc_lemmas.

Section MixedError. 
Context {NAN: FPCore.Nans} {t : type}.

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).
Notation E := (@default_abs t).
Notation neg_zero := (@common.neg_zero t).

Variables (v1 v2: list (ftype t)).
Hypothesis Hlen: size v1 = size v2.
Hypothesis Hfin: Binary.is_finite(fma_dotprod v1 v2) = true.

Lemma fma_dotprod_mixed_error:
  exists (u : list R) (eta : R),
    size u = size v1 /\
    FT2R (fma_dotprod v1 v2) = dotprodR u (map FT2R v2) + eta /\
    (forall n, (n < size v2)%nat -> exists delta,
      nth 0 u n = FT2R (nth neg_zero v1 n) * (1 + delta) /\ Rabs delta <= g (size v2))  /\
    Rabs eta <= g1 (size v2) (size v2 -1).
Proof.
intros.
assert (size (zip v1 v2) = size v1) by (rewrite size_zip; lia).
assert (Hlenr : size (rev v1) = size (rev v2)) by (rewrite !size_rev; auto).
rewrite <- size_rev in Hlen.
pose proof fma_dot_prod_rel_fold_right v1 v2 as H1.
rewrite rev_zip in H1.  2: revert Hlen; rewrite size_rev; auto.
revert Hlen.
rewrite size_rev; intro.
pose proof (fma_dotprod_mixed_error_rel (rev v1) (rev v2) Hlenr (fma_dotprod v1 v2) H1 Hfin) as 
  (u & eta & H2 & H3 & H4 & H5).
exists (rev u), eta; repeat split; auto.
-
rewrite !size_rev in H2|-*; auto.
-
pose proof dotprodR_rel u (map FT2R (rev v2)). 
assert (dotprodR (rev u) (map FT2R v2) = FT2R (fma_dotprod v1 v2) - eta).
eapply R_dot_prod_rel_eq; eauto.
rewrite <- dotprodR_rev, <- map_rev. auto.
rewrite size_rev in H2; rewrite size_map; auto; lia. 
nra.
-
rewrite !size_rev in H4. 
intros.
rewrite size_rev in H2. 
assert ((size u - S n < size v2)%nat) by lia.
specialize (H4 (size u - S n)%nat H6).
rewrite nth_rev in H4. 2: rewrite Hlen //.
rewrite nth_rev. 2: rewrite H2 Hlen //.
destruct H4 as (delta & Hn & HD).
exists delta; split.
rewrite Hn; repeat f_equal.
rewrite Hlen.
rewrite H2. 
rewrite <- Nat.sub_succ_l.
simpl. lia.
rewrite Hlen. lia.
apply HD.
-  rewrite !size_rev in H5; auto.
Qed.

End MixedError.


Section ForwardError. 
Context {NAN: FPCore.Nans} {t : type}.

Variables v1 v2 : list (ftype t).
Notation v1R  := (map FT2R v1).
Notation v2R  := (map FT2R v2).
Notation v1R' := (map Rabs v1R).
Notation v2R' := (map Rabs v2R).
Notation n    := (size v2).

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation neg_zero := (@common.neg_zero t).

Hypothesis Hlen: size v1 = size v2.
Hypothesis Hfin: Binary.is_finite(fma_dotprod v1 v2) = true.

Lemma fma_dotprod_forward_error:
  Rabs (FT2R (fma_dotprod v1 v2) - dotprodR v1R v2R ) 
        <= g n * dotprodR v1R' v2R' + g1 n (n - 1).
Proof.
intros.  
pose proof R_dot_prod_rel_fold_right' t v1 v2 Hlen as HB.
pose proof R_dot_prod_rel_fold_right_Rabs' t v1 v2 Hlen as HC.
  simpl in HB, HC. rewrite <- map_rev in HC, HB.
  rewrite <- map_rev in HC.
pose proof fma_dotprod_forward_error_rel (rev (zip v1 v2)) 
  (fma_dotprod v1 v2) (fma_dot_prod_rel_fold_right _ _ ) Hfin
  (dotprodR v1R v2R) (dotprodR v1R' v2R') HB HC.
rewrite size_rev size_zip Hlen minnn in H.
auto.
Qed.

Notation nnzR := (common.nnzR v1R).

Lemma fma_sparse_dotprod_forward_error:
  Rabs (FT2R (fma_dotprod v1 v2) - dotprodR v1R v2R )  <= 
       g nnzR * dotprodR v1R' v2R' + g1 nnzR (nnzR - 1).
Proof. 
intros.  
pose proof fma_dot_prod_rel_fold_right v1 v2 as HA.
pose proof R_dot_prod_rel_fold_right' t v1 v2 Hlen as HB.
pose proof R_dot_prod_rel_fold_right_Rabs' t v1 v2 Hlen as HC.
  simpl in HB, HC. rewrite <- map_rev in HC, HB.
  rewrite <- map_rev in HC.
pose proof sparse_fma_dotprod_forward_error (rev v1) (rev v2).
  rewrite !size_rev  -rev_zip in H; auto.
specialize (H Hlen (fma_dotprod v1 v2) HA Hfin (dotprodR v1R v2R)
  (dotprodR v1R' v2R') HB HC).
rewrite map_rev in H.
unfold common.nnzR, nnzR in H.
rewrite !count_rev in H.
auto.
Qed.

End ForwardError.


