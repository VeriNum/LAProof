Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
From LAProof.accuracy_proofs Require Import common 
                                            float_acc_lems 
                                            op_defs 
                                            list_lemmas
                                            dotprod_model 
                                            dot_acc 
                                            sum_model 
                                            sum_acc.
Require Import Reals.
Open Scope R.


Section TwoNorm. 
Context {NAN: Nans} {t : type} {STD : is_standard t}.

Definition two_normF (x: list (ftype t)) : R := sqrt (FT2R (dotprodF x x)).
Definition two_normR (x: list R) : R := sqrt (dotprodR x x).

Variable (x : list (ftype t)).
Notation xR := (map FT2R x).
Notation n:= (length x). 
Hypothesis Hfin: is_finite (dotprodF x x) = true.

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation neg_zero := (ftype_of_float neg_zero).

(* two norm mixed error bound *)
Lemma bfVNRM2:
  exists (x' : list R) (eta : R),
   two_normF x = sqrt (dotprodR x' xR + eta) /\
    (forall m, (m < n)%nat -> exists delta,
      nth m x' 0 = FT2R (nth m x neg_zero) * (1 + delta) /\ Rabs delta <= g n)  /\
    Rabs eta <= g1 n n.
Proof.
destruct (dotprod_mixed_error x x eq_refl Hfin) 
  as (x' & eta & Hlen & Hrel & H1 & H2).
exists x', eta; repeat split; auto.
unfold two_normF, two_normR.
rewrite Hrel. f_equal; nra.
Qed.

End TwoNorm. 

Section OneNorm.
Context {NAN: Nans} {t : type} {STD : is_standard t}.

Definition one_normF (x: list (ftype t)) : R := FT2R (sumF x).
Definition one_normR (x: list R) : R := fold_right Rplus 0 x.

Variables (x : list (ftype t)).
Hypothesis Hfin: is_finite (sumF x) = true. 

Notation xR := (map FT2R x).
Notation n:= (length x). 
Notation g := (@g t).
Notation neg_zero := (ftype_of_float neg_zero).

(* one norm backward error bound *)
Lemma bfVNRM1:
    exists (x': list R), 
    one_normF x = one_normR x' /\
    (forall m, (m < n)%nat -> exists delta, 
        nth m x' 0 = FT2R (nth m x neg_zero) * (1 + delta) /\ Rabs delta <= g (n - 1)).
Proof.
destruct (bSUM x Hfin) as (x' & Hlen & Hrel & Hn). 
  rewrite Hlen in Hn.
exists x'; repeat split; auto.
Qed.

End OneNorm.