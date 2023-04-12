(** This file contains three main theorems for the accuracy of the fma
  dot product : fma_dotprod_mixed_error, fma_dotprod_forward_error, 
  and fma_sparse_dotprod_forward_error. *)

Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common op_defs float_acc_lems list_lemmas.
Require Import dotprod_model sum_model dot_acc_lemmas.

Require Import Reals.
Open Scope R.

Section MixedError. 
Context {NAN: Nans} {t : type}.

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).
Notation E := (@default_abs t).

Variables (v1 v2: list (ftype t)).
Hypothesis Hlen: length v1 = length v2.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) (fma_dotprod v1 v2) = true.

Lemma fma_dotprod_mixed_error:
  exists (u : list R) (eta : R),
    length u = length v1 /\
    FT2R (fma_dotprod v1 v2) = dotprodR u (map FT2R v2) + eta /\
    (forall n, (n < length v2)%nat -> exists delta,
      nth n u 0 = FT2R (nth n v1 neg_zero) * (1 + delta) /\ Rabs delta <= g (length v2))  /\
    Rabs eta <= g1 (length v2) (length v2 -1).
Proof.
intros.
assert (Datatypes.length (combine v1 v2) = length v1) by
 (rewrite combine_length; lia).
assert (Hlenr : length (rev v1) = length (rev v2)) by (rewrite !rev_length; auto).
rewrite <- rev_length in Hlen.
pose proof fma_dot_prod_rel_fold_right v1 v2 as H1.
rewrite <- combine_rev in H1. 
rewrite rev_length in Hlen.
pose proof (fma_dotprod_mixed_error_rel (rev v1) (rev v2) Hlenr (fma_dotprod v1 v2) H1 Hfin) as 
  (u & eta & H2 & H3 & H4 & H5).
exists (rev u), eta; repeat split; auto.
rewrite rev_length in H2; rewrite <- rev_length in H2; auto.
pose proof dotprodR_rel u (map FT2R (rev v2)). 
assert (dotprodR (rev u) (map FT2R v2) = FT2R (fma_dotprod v1 v2) - eta).
eapply R_dot_prod_rel_eq; eauto.
rewrite <- dotprodR_rev, <- map_rev. auto.
rewrite rev_length in H2; rewrite map_length; auto; lia. 
nra. 
rewrite !rev_length in H4. 
intros. 
assert ((length u - S n < length v2)%nat).
{ rewrite rev_length in H2. 
rewrite H2. rewrite Hlen. 
apply Nat.sub_lt; try lia.
}
specialize (H4 (length u - S n)%nat H6).
rewrite rev_nth in H4.
rewrite rev_nth.
destruct H4 as (delta & Hn & HD).
exists delta; split.
rewrite Hn; repeat f_equal.
rewrite rev_length in H2. 
rewrite Hlen.
rewrite H2. 
rewrite <- Nat.sub_succ_l.
simpl. lia.
apply Arith_prebase.lt_le_S_stt; auto. lia.
apply HD.
rewrite rev_length in H2. 
rewrite H2; auto. lia.
rewrite Hlen; auto.
rewrite !rev_length in H5; auto.
rewrite rev_length in Hlen; auto.
Qed.

End MixedError.


Section ForwardError. 
Context {NAN: Nans} {t : type}.

Variables v1 v2 : list (ftype t).
Notation v1R  := (map FT2R v1).
Notation v2R  := (map FT2R v2).
Notation v1R' := (map Rabs v1R).
Notation v2R' := (map Rabs v2R).
Notation n    := (length v2).

Notation g := (@g t).
Notation g1 := (@g1 t).

Hypothesis Hlen: length v1 = length v2.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) (fma_dotprod v1 v2) = true.

Lemma fma_dotprod_forward_error:
  Rabs (FT2R (fma_dotprod v1 v2) - dotprodR v1R v2R ) 
        <= g n * dotprodR v1R' v2R' + g1 n (n - 1).
Proof.
intros.  
pose proof R_dot_prod_rel_fold_right' t v1 v2 as HB.
pose proof R_dot_prod_rel_fold_right_Rabs' t v1 v2 as HC.
  simpl in HB, HC. rewrite <- map_rev in HC, HB.
  rewrite <- map_rev in HC.
pose proof fma_dotprod_forward_error_rel (rev (combine v1 v2)) 
  (fma_dotprod v1 v2) (fma_dot_prod_rel_fold_right _ _ ) Hfin
  (dotprodR v1R v2R) (dotprodR v1R' v2R') HB HC.
rewrite rev_length, combine_length, Hlen, Nat.min_id in H;
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
  simpl in HB, HC. rewrite <- map_rev in HC, HB.
  rewrite <- map_rev in HC.
pose proof @sparse_fma_dotprod_forward_error NAN t (rev v1) (rev v2).
  rewrite !rev_length,  combine_rev in H; auto.
specialize (H Hlen (fma_dotprod v1 v2) HA Hfin (dotprodR v1R v2R)
  (dotprodR v1R' v2R') HB HC). 
rewrite map_rev in H.
unfold common.nnzR, nnz in H.
rewrite count_occ_rev, rev_length in H. 
unfold common.nnzR, nnz; auto.
Qed.

End ForwardError.


