(** * Logical views of strided C arrays. *)

Require Import VST.floyd.proofauto.

Set Bullet Behavior "Strict Subproofs".

(** [strided_from start inc N X] is the logical length-[N] vector whose
    element [i] is stored at array index [start + i*inc]. *)
Definition strided_from {A} `{Inhabitant A}
    (start inc N : Z) (X : list A) : list A :=
  map (fun i => Znth (start + i*inc) X) (upto (Z.to_nat N)).

(** The starting index computed by GSL's [OFFSET(N,inc)] macro. *)
Definition blas_offset (N inc : Z) : Z :=
  if 0 <? inc then 0 else (N-1) * (-inc).

Definition blas_strided {A} `{Inhabitant A}
    (inc N : Z) (X : list A) : list A :=
  strided_from (blas_offset N inc) inc N X.

Lemma Zlength_strided_from: forall {A} `{Inhabitant A} start inc N (X: list A),
  0 <= N -> Zlength (strided_from start inc N X) = N.
Proof.
  intros. unfold strided_from.
  rewrite Zlength_map, Zlength_upto, Z2Nat.id by lia. reflexivity.
Qed.

Lemma strided_from_snoc: forall {A} `{Inhabitant A} start inc k (X: list A),
  0 <= k ->
  strided_from start inc (k+1) X =
  strided_from start inc k X ++ [Znth (start + k*inc) X].
Proof.
  intros A ? start inc k X Hk. unfold strided_from.
  replace (Z.to_nat (k+1)) with (Z.to_nat k + 1)%nat by lia.
  rewrite upto_app, map_app. f_equal.
  cbn [upto map]. rewrite Z.add_0_r, Z2Nat.id by lia. reflexivity.
Qed.
