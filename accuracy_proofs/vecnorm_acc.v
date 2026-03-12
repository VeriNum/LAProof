(** * Floating-Point Vector Norm Accuracy Bounds

    This file establishes error bounds for floating-point computations of
    the two-norm (Euclidean) and one-norm of a vector.

    ** Error Factors

    Throughout, the accumulated relative error factor is
    %$g(n) = (1 + \mathbf{u})^n - 1$%#\(g(n) = (1 + \mathbf{u})^n - 1\)# and
    the mixed absolute error factor is
    %$g_1(n_1, n_2) = n_1 \cdot \eta \cdot (1 + g(n_2))$%#\(g_1(n_1, n_2) = n_1 \cdot \eta \cdot (1 + g(n_2))\)#,
    where %$\mathbf{u}$%#\(\mathbf{u}\)# is the unit roundoff and
    %$\eta$%#\(\eta\)# is the underflow threshold for the given type.
    Both are defined in [common].

    ** Main Results

    - [bfVNRM2]: Shows that the floating-point two-norm can be expressed as
      the square root of a mixed-error dot product: one copy of the input
      appears componentwise perturbed, and a small absolute residual accounts
      for underflow.

    - [bfVNRM1]: Shows that the floating-point one-norm equals the exact
      one-norm of a slightly perturbed input vector.

    ** Dependencies

    This file relies on:
    - [preamble], [common]: basic setup and shared definitions
    - [dotprod_model], [sum_model]: relational models of dot product and summation
    - [float_acc_lems]: elementary floating-point accuracy lemmas
    - [dot_acc], [sum_acc]: dot product and summation accuracy theorems
*)

From LAProof.accuracy_proofs Require Import
  preamble
  common
  dotprod_model
  sum_model
  float_acc_lems
  dot_acc
  sum_acc.

(** * Two-Norm *)

Section TwoNorm.

Context {NAN : FPCore.Nans} {t : type}.

(** The floating-point two-norm: the square root of the floating-point dot
    product of a vector with itself, coerced to a real number. *)
    
Definition two_normF (x : list (ftype t)) : R :=
  sqrt (FT2R (dotprodF x x)).

(** The exact real-valued two-norm: the square root of the real dot product
    of a vector with itself. *)
    
Definition two_normR (x : list R) : R :=
  sqrt (dotprodR x x).

Variable (x : list (ftype t)).

Notation xR       := (map FT2R x).
Notation n        := (size x).
Notation g        := (@g t).
Notation g1       := (@g1 t).
Notation neg_zero := (@common.neg_zero t).

(** We assume the floating-point dot product [dotprodF x x] is finite,
    which is necessary for [two_normF x] to be well-defined. *)
Hypothesis Hfin : Binary.is_finite (dotprodF x x) = true.

(** [bfVNRM2] expresses the floating-point two-norm as the square root of
    a mixed-error dot product. One copy of the input appears componentwise
    perturbed by a relative factor bounded by %$g(n)$%#\(g(n)\)#, and an
    absolute residual bounded by %$g_1(n, n)$%#\(g_1(n,n)\)# accounts for
    underflow. *)
    
Lemma bfVNRM2 :
  exists (x' : list R) (eta : R),
    two_normF x = sqrt (dotprodR x' xR + eta) /\
    (forall m, (m < n)%nat ->
      exists delta,
        nth 0 x' m = FT2R (nth neg_zero x m) * (1 + delta) /\
        Rabs delta <= g n) /\
    Rabs eta <= g1 n n.
Proof.
  destruct (dotprod_mixed_error x x Logic.eq_refl Hfin)
    as (x' & eta & Hlen & Hrel & H1 & H2).
  exists x', eta.
  repeat split; auto.
  unfold two_normF, two_normR.
  rewrite Hrel.
  f_equal; nra.
Qed.

End TwoNorm.

(** * One-Norm *)

Section OneNorm.

Context {NAN : FPCore.Nans} {t : type}.

(** The floating-point one-norm: the real value of the floating-point
    left-to-right accumulation of the vector entries. *)
    
Definition one_normF (x : list (ftype t)) : R :=
  FT2R (sumF x).

(** The exact real-valued one-norm: the sum of a list of real numbers. *)

Definition one_normR (x : list R) : R :=
  fold_right Rplus 0 x.

Variables (x : list (ftype t)).

(** We assume the floating-point sum [sumF x] is finite, which is necessary
    for [one_normF x] to be well-defined. *)

Hypothesis Hfin : Binary.is_finite (sumF x) = true.

Notation xR       := (map FT2R x).
Notation n        := (size x).
Notation g        := (@g t).
Notation neg_zero := (@common.neg_zero t).

(** [bfVNRM1] shows that the floating-point one-norm equals the exact
    one-norm of a perturbed input vector, where each component is perturbed
    by a relative factor bounded by %$g(n-1)$%#\(g(n-1)\)#. *)
    
Lemma bfVNRM1 :
  exists (x' : list R),
    one_normF x = one_normR x' /\
    (forall m, (m < n)%nat ->
      exists delta,
        nth 0 x' m = FT2R (nth neg_zero x m) * (1 + delta) /\
        Rabs delta <= g (n - 1)).
Proof.
  destruct (bSUM x Hfin) as (x' & Hlen & Hrel & Hn).
  rewrite Hlen in Hn.
  exists x'.
  repeat split; auto.
Qed.

End OneNorm.