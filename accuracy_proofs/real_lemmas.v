(** ** Real Arithmetic Auxiliary Lemmas *)

From Stdlib Require Import Reals.Reals Reals.RIneq.
From Stdlib Require Import Psatz.

Open Scope R_scope.

(** Strict monotonicity of reciprocal: [0 < b < a -> /a < /b]. *)

Lemma rdiv_lt (a b : R) :
  0 < b -> 0 < a -> b < a -> / a < / b.
Proof.
  intros Ha Hb Hlt.
  apply Rinv_lt_contravar.
  - nra.
  - nra.
Qed.

(** Non-strict monotonicity of reciprocal: [0 < b <= a -> /a <= /b]. *)

Lemma rdiv_le (a b : R) :
  0 < b -> 0 < a -> b <= a -> / a <= / b.
Proof.
  intros Ha Hb Hle.
  apply Rinv_le_contravar; nra.
Qed.

(** Division equals multiplication by reciprocal. *)

Lemma rdiv_mult_eq (a b : R) :
  b <> 0 -> a / b = a * (1 / b).
Proof. nra. Qed.

(** Subtraction is anti-monotone in the subtrahend (non-strict). *)

Lemma Rminus_le_minus (a b c : R) :
  b <= c -> a - c <= a - b.
Proof. nra. Qed.

(** Subtraction is anti-monotone in the subtrahend (strict). *)

Lemma Rminus_lt_minus (a b c : R) :
  b < c -> a - c < a - b.
Proof. nra. Qed.

(** Addition is compatible with mixed [<=]/[<] ordering. *)

Lemma Rplus_le_lt_compat (a1 a2 b1 b2 : R) :
  a1 <= a2 -> b1 < b2 -> a1 + b1 < a2 + b2.
Proof. nra. Qed.

(** Multiplication is compatible with mixed [<]/[<=] ordering. *)

Lemma Rmult_le_lt_compat (a1 a2 b1 b2 : R) :
  0 < a1 -> 0 < b1 -> a1 < a2 -> b1 <= b2 -> a1 * b1 < a2 * b2.
Proof. nra. Qed.