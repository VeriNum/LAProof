(** This file contains three main theorems for the accuracy of the fma
  dot product : fma_dotprod_mixed_error, fma_dotprod_forward_error, 
  and fma_sparse_dotprod_forward_error. *)

From LAProof.accuracy_proofs Require Import preamble common 
                                            dotprod_model sum_model
                                            float_acc_lems 
                                            list_lemmas dot_acc_lemmas.

Require Import Reals.
Open Scope R.

Section MixedError. 
Context {NAN: FPCore.Nans} {t : type}.

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).
Notation E := (@default_abs t).
Notation neg_zero := (@common.neg_zero t).

Variables (v1 v2: list (ftype t)).
Hypothesis Hlen: length v1 = length v2.
Hypothesis Hfin: Binary.is_finite(fma_dotprod v1 v2) = true.

Lemma fma_dotprod_mixed_error:
  exists (u : list R) (eta : R),
    length u = length v1 /\
    FT2R (fma_dotprod v1 v2) = dotprodR u (map FT2R v2) + eta /\
    (forall n, (n < length v2)%nat -> exists delta,
      List.nth n u 0 = FT2R (List.nth n v1 neg_zero) * (1 + delta) /\ Rabs delta <= g (length v2))  /\
    Rabs eta <= g1 (length v2) (length v2 -1).
Proof.
intros.
assert (Datatypes.length (combine v1 v2) = length v1) by
 (rewrite combine_length; lia).
assert (Hlenr : length (List.rev v1) = length (List.rev v2)) by (rewrite !length_rev; auto).
rewrite <- length_rev in Hlen.
pose proof fma_dot_prod_rel_fold_right v1 v2 as H1.
rewrite <- combine_rev in H1 by (revert Hlen; rewrite length_rev; auto).
revert Hlen.
rewrite length_rev; intro.
pose proof (fma_dotprod_mixed_error_rel (List.rev v1) (List.rev v2) Hlenr (fma_dotprod v1 v2) H1 Hfin) as 
  (u & eta & H2 & H3 & H4 & H5).
exists (List.rev u), eta; repeat split; auto.
-
rewrite length_rev in H2; rewrite <- length_rev in H2; auto.
-
pose proof dotprodR_rel u (map FT2R (List.rev v2)). 
assert (dotprodR (List.rev u) (map FT2R v2) = FT2R (fma_dotprod v1 v2) - eta).
eapply R_dot_prod_rel_eq; eauto.
rewrite <- dotprodR_rev, <- List.map_rev. auto.
rewrite length_rev in H2; rewrite length_map; auto; lia. 
nra.
-
rewrite !length_rev in H4. 
intros. 
assert ((length u - S n < length v2)%nat)
 by (rewrite length_rev in H2; lia). 
specialize (H4 (length u - S n)%nat H6).
rewrite rev_nth in H4.
rewrite rev_nth.
destruct H4 as (delta & Hn & HD).
exists delta; split.
rewrite Hn; repeat f_equal.
rewrite length_rev in H2. 
rewrite Hlen.
rewrite H2. 
rewrite <- Nat.sub_succ_l.
simpl. lia.
rewrite Hlen. lia.
apply HD.
rewrite length_rev in H2. 
rewrite H2; auto. lia.
rewrite Hlen; auto.
lia.
- rewrite !length_rev in H5; auto.
Qed.

End MixedError.


Section ForwardError. 
Context {NAN: FPCore.Nans} {t : type}.

Variables v1 v2 : list (ftype t).
Notation v1R  := (map FT2R v1).
Notation v2R  := (map FT2R v2).
Notation v1R' := (map Rabs v1R).
Notation v2R' := (map Rabs v2R).
Notation n    := (length v2).

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation neg_zero := (@common.neg_zero t).

Hypothesis Hlen: length v1 = length v2.
Hypothesis Hfin: Binary.is_finite(fma_dotprod v1 v2) = true.

Lemma fma_dotprod_forward_error:
  Rabs (FT2R (fma_dotprod v1 v2) - dotprodR v1R v2R ) 
        <= g n * dotprodR v1R' v2R' + g1 n (n - 1).
Proof.
intros.  
pose proof R_dot_prod_rel_fold_right' t v1 v2 as HB.
pose proof R_dot_prod_rel_fold_right_Rabs' t v1 v2 as HC.
  simpl in HB, HC. rewrite <- List.map_rev in HC, HB.
  rewrite <- List.map_rev in HC.
pose proof fma_dotprod_forward_error_rel (List.rev (combine v1 v2)) 
  (fma_dotprod v1 v2) (fma_dot_prod_rel_fold_right _ _ ) Hfin
  (dotprodR v1R v2R) (dotprodR v1R' v2R') HB HC.
rewrite List.length_rev length_combine Hlen Nat.min_id in H.
auto.
Qed.

Notation nnzR := (common.nnzR v1R).

Lemma fma_sparse_dotprod_forward_error:
  Rabs (FT2R (fma_dotprod v1 v2) - dotprodR v1R v2R )  <= 
       g nnzR * dotprodR v1R' v2R' + g1 nnzR (nnzR - 1).
Proof. 
intros.  
pose proof fma_dot_prod_rel_fold_right v1 v2 as HA.
pose proof R_dot_prod_rel_fold_right' t v1 v2 as HB.
pose proof R_dot_prod_rel_fold_right_Rabs' t v1 v2 as HC.
  simpl in HB, HC. rewrite <- List.map_rev in HC, HB.
  rewrite <- List.map_rev in HC.
pose proof sparse_fma_dotprod_forward_error (List.rev v1) (List.rev v2).
  rewrite !length_rev  combine_rev in H; auto.
specialize (H Hlen (fma_dotprod v1 v2) HA Hfin (dotprodR v1R v2R)
  (dotprodR v1R' v2R') HB HC).
change @map with @List.map in H. 
rewrite List.map_rev in H.
unfold common.nnzR, nnzR in H.
rewrite -rev_list_rev !count_rev in H.
auto.
Qed.

End ForwardError.


