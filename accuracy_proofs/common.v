(* This file contains basic definitions and lemmas common to all other files in 
  the repository. *)

From LAProof.accuracy_proofs Require Import preamble.

Definition rounded t r:=
(Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
     (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) r).

Definition neg_zero  {t: type} := Binary.B754_zero (fprec t) (femax t) true.
Definition pos_zero  {t: type} := Binary.B754_zero (fprec t) (femax t) false.
Definition Beq_dec_t {t: type}
    (x y  : ftype t) : {x = y} + {x <> y}.
    apply (Beq_dec (fprec t) (femax t)  x y).
  Defined. 

Create HintDb commonDB discriminated.

Global Hint Resolve 
  bpow_gt_0 bpow_ge_0 pos_INR lt_0_INR pow_le: commonDB.

Delimit Scope R_scope with Re.
Open Scope R_scope.

Lemma rev_list_rev: @rev = @List.rev.
Proof.
apply FunctionalExtensionality.functional_extensionality_dep; intro T.
apply FunctionalExtensionality.functional_extensionality; intro al.
unfold rev.
change @catrev with rev_append.
rewrite rev_append_rev app_nil_r //.
Qed.

Lemma size_not_empty_nat {A} (l: seq A) :  l <> [] ->  Nat.le 1 (size l).
Proof.
intros.
destruct l; try congruence; compute; lia.
Qed.


Section WithType.
Context {NAN: FPCore.Nans} {t : type}.

Definition iszero {t} (x: ftype t) : bool := 
  match x with Binary.B754_zero _ _ _ => true | _ => false end.

Lemma iszeroR_iszeroF: forall x: ftype t,  Binary.is_finite x -> FT2R x = R0 -> iszero x.
Proof.
destruct x; intros; auto.
exfalso; clear - H0.
rewrite /FT2R /= /Defs.F2R /= in H0.
destruct s; simpl in H0.
-
assert  (IZR (Z.neg m) * bpow Zaux.radix2 e < 0)%Re; [clear | lra]; rewrite /IZR.
apply Rmult_neg_pos.
move :(IPR_gt_0 m); lra.
move :(bpow_gt_0 Zaux.radix2 e); lra.
-
assert  (0 < IZR (Z.pos m) * bpow Zaux.radix2 e)%Re; [clear | lra]; rewrite /IZR.
apply Rmult_pos_pos.
apply IPR_gt_0.
apply bpow_gt_0.
Qed.

(** Number of nonzeros *)

Definition nnzF:  seq (ftype t) -> nat :=
    count (fun x => negb (iszero x)).

Definition nnzR:  seq R -> nat :=
    count (fun x => negb (0 == x)).

Lemma nnzF_zero l: (nnzF l == 0%nat) = (size l == count iszero l).
Proof.
rewrite /nnzF (eq_sym (size l)) -all_count.
elim l => // a l' IH.
case :a => //.
Qed.

Lemma nnzR_zero l: (nnzR l == 0%nat) = (size l == count (eq_op 0) l).
Proof.
rewrite /nnzR (eq_sym (size l)) -all_count.
elim l => // a l' IH /=.
rewrite -{}IH /=; case (0 == a); lia.
Qed.

Lemma nnzF_lemma l:  (nnzF l == 0%nat) = all iszero l.
Proof.
rewrite !nnzF_zero all_count (eq_sym (size _)) //.
Qed.

Lemma nnzR_lemma l:  (nnzR l == 0%nat) = (all (eq_op R0) l).
Proof.
rewrite !nnzR_zero all_count (eq_sym (size _)) //.
Qed.

Lemma nnzF_is_zero_cons a l: nnzF (a::l) == 0%nat -> nnzF l == 0%nat.
Proof.
rewrite !nnzF_lemma (all_cat _ [:: a] l) => /andP [H H'] //.
Qed.

Lemma nnzR_is_zero_cons a l: nnzR (a::l) == 0%nat -> nnzR l == 0%nat.
Proof.
rewrite !nnzR_lemma (all_cat _ [:: a] l) => /andP [H H'] //.
Qed.

Lemma nnzR_cons l : 
  nnzR (0%Re :: l) == nnzR l.
Proof.
rewrite /= eq_refl //.
Qed.

Definition default_rel : R :=
  / 2 * Raux.bpow Zaux.radix2 (- fprec t + 1).

Definition default_abs : R :=
  / 2 * Raux.bpow Zaux.radix2 (3 - femax t - fprec t).

Lemma default_rel_sep_0 : 
  default_rel <> R0.
Proof.
apply Rabs_lt_pos;
rewrite Rabs_pos_eq; [apply Rmult_lt_0_compat; try Lra.nra | 
  apply Rmult_le_pos; try Lra.nra]; auto with commonDB.
Qed.
Hint Resolve default_rel_sep_0 : commonDB.

Lemma default_rel_gt_0 : 
  0 < default_rel.
Proof. apply Rmult_lt_0_compat; try nra;
auto with commonDB.
Qed.
Hint Resolve default_rel_gt_0 : commonDB.
 
Lemma default_rel_ge_0 : 
  0 <= default_rel.
Proof. apply Rlt_le; auto with commonDB. Qed.
Hint Resolve default_rel_ge_0 : commonDB.

Lemma default_rel_plus_1_ge_1:
 1 <= 1 + default_rel.
Proof. 
rewrite Rplus_comm. 
apply Rcomplements.Rle_minus_l; field_simplify. 
auto with commonDB.
Qed.
Hint Resolve default_rel_plus_1_ge_1 : commonDB.

Lemma default_rel_plus_0_ge_1:
 0 <= 1 + default_rel.
Proof. suff: 1 <= 1 + default_rel; try nra; auto with commonDB. Qed. 
Hint Resolve default_rel_plus_0_ge_1 : commonDB.

Lemma default_rel_plus_1_gt_1:
 1 < 1 + default_rel.
Proof.
rewrite Rplus_comm; apply Rcomplements.Rlt_minus_l;
  field_simplify; auto with commonDB.
Qed.
Hint Resolve default_rel_plus_1_gt_1 : commonDB.

Lemma default_rel_plus_1_gt_0 :
 0 < 1 + default_rel.
Proof. 
eapply Rlt_trans with 1; [nra | ].
auto with commonDB.
Qed.
Hint Resolve default_rel_plus_1_gt_0 : commonDB.

Lemma default_rel_plus_1_ge_1' n:
 1 <= (1 + default_rel) ^ n.
Proof. 
induction n; simpl; auto; try nra.
eapply Rle_trans with (1 * 1); try nra.
apply Rmult_le_compat; try nra.
auto with commonDB.
Qed.
Hint Resolve default_rel_plus_1_ge_1': commonDB.

Lemma default_abs_gt_0 : 
  0 < default_abs .
Proof. 
unfold default_abs.
apply Rmult_lt_0_compat; auto with commonDB; nra.
Qed.
Hint Resolve default_abs_gt_0: commonDB.

Lemma default_abs_ge_0 :
  0 <= default_abs .
Proof. apply Rlt_le; auto with commonDB. Qed.
Hint Resolve default_abs_ge_0: commonDB.

Lemma abs_le_rel :
 default_abs <= default_rel.
Proof. 
apply: Rmult_le_compat; try nra; auto with commonDB.
apply: bpow_le => //; pose proof fprec_gt_one t; pose proof fprec_lt_femax t; lia.
Qed.

End WithType.

Global Hint Resolve 
  default_rel_sep_0
  default_rel_gt_0
  default_rel_ge_0
  default_rel_plus_1_ge_1
  default_rel_plus_1_gt_0
  default_rel_plus_1_ge_1'
  default_abs_ge_0
  default_abs_gt_0
  default_rel_plus_1_ge_1
  abs_le_rel
  default_rel_plus_0_ge_1
: commonDB.

Section WithType.
Context {NAN: FPCore.Nans} {t: type}.

Notation D := (@default_rel t).
Notation E := (@default_abs t).

Definition g (n: nat) : R := ((1 + D) ^ n - 1).

Lemma g_pos n: 
  0 <= g n. 
Proof. 
unfold g. induction n.
simpl; nra. eapply Rle_trans; [apply IHn| apply Rplus_le_compat; try nra].
simpl. eapply Rle_trans with (1 * (1+D )^n); try nra.
apply Rmult_le_compat; try nra. rewrite Rplus_comm. apply Rcomplements.Rle_minus_l.
field_simplify. 
auto with commonDB.
Qed.
Hint Resolve g_pos : commonDB.

Lemma le_g_Sn  n : 
  g n <= g  (S n).
Proof. 
induction n; unfold g; simpl.
  { field_simplify; auto with commonDB. }
  unfold g in IHn. eapply Rplus_le_compat; try nra.
  eapply Rmult_le_compat_l.
  apply Rplus_le_le_0_compat; try nra; try apply default_rel_ge_0.
  rewrite tech_pow_Rmult. apply Rle_pow; try lia.
  rewrite Rplus_comm. apply Rcomplements.Rle_minus_l.
  field_simplify; auto with commonDB. 
Qed.
Hint Resolve le_g_Sn : commonDB.

Lemma d_le_g n:
D <= g  (n + 1).
Proof. unfold g. induction n; simpl; field_simplify; try nra.
eapply Rle_trans; [apply IHn|].
apply Rplus_le_compat_r.
replace (D  * (1 + D ) ^ (n + 1)%coq_nat + (1 + D ) ^ (n + 1)%coq_nat)
with 
((1 + D ) ^ (n + 1)%coq_nat * (D   + 1)) by nra.
eapply Rle_trans with ((1 + D ) ^ (n + 1) * 1); try nra.
change Init.Nat.add with addn.
eapply Rmult_le_compat; try nra.
{ apply pow_le. apply Fourier_util.Rle_zero_pos_plus1 ; auto with commonDB. }
apply Rcomplements.Rle_minus_l. field_simplify; auto with commonDB. 
Qed.
Hint Resolve d_le_g : commonDB.


Lemma d_le_g_1  n:
(1<= n)%nat -> D  <= g n.
Proof. 
intros; unfold g. 
eapply Rle_trans with ((1 + D )^1 - 1).
field_simplify; nra.
apply Rplus_le_compat; try nra.
apply Rle_pow; try lia.
auto with commonDB. Qed.
Hint Resolve d_le_g_1 : commonDB.

Lemma one_plus_d_mul_g  a n:
  (1 + D ) * g  n * a + D  * a  = g (n + 1) * a.
Proof. unfold g. rewrite Rmult_minus_distr_l. rewrite tech_pow_Rmult. 
field_simplify. f_equal. rewrite Rmult_comm; repeat f_equal; lia.
Qed.
Hint Resolve one_plus_d_mul_g : commonDB.

Definition g1 (n1: nat) (n2: nat) : R := 
  INR n1 * E* (1 + g n2 ).

Lemma g1_pos n m : 0 <= g1 n m. 
Proof. unfold g1.
apply Rmult_le_pos; try apply pos_INR.
apply Rmult_le_pos; try apply pos_INR.
apply default_abs_ge_0. unfold g; field_simplify.
apply pow_le.
apply Fourier_util.Rle_zero_pos_plus1.
auto with commonDB.
Qed.
Hint Resolve g1_pos : commonDB.

Lemma one_plus_d_mul_g1 n:
(1 <= n )%nat ->
g1 n (n - 1) * (1 + D )  =  g1 n n.
Proof.
intros.
unfold g1, g; field_simplify.
symmetry. replace n with (S (n-1)) at 2.
rewrite <- tech_pow_Rmult.
field_simplify; nra.
rewrite <- Nat.sub_succ_l; auto; lia.
Qed.
Hint Resolve g1_pos : commonDB.

Lemma one_plus_d_mul_g1'  n m:
g1 n m * (1 + D)  =  g1 n (S m).
Proof.
intros.
unfold g1, g; field_simplify.
symmetry. 
rewrite <- tech_pow_Rmult.
field_simplify; nra.
Qed.
Hint Resolve g1_pos : commonDB.

Hint Resolve  fprec_lt_femax :commonDB.
Lemma e_le_g1  n:
(1 <= n )%nat ->
E <= g1 n n.
Proof.
intros; unfold g1. eapply Rle_trans with (1 * E * 1); try nra.
apply: Rmult_le_compat; first (field_simplify; auto with commonDB); try nra.
apply: Rmult_le_compat => //; auto with commonDB; try nra.
replace 1 with (INR 1) by (simpl; nra).
apply le_INR; auto with commonDB; lia.
rewrite Rplus_comm -Rcomplements.Rle_minus_l; field_simplify;
auto with commonDB.
Qed.
Hint Resolve e_le_g1 : commonDB.


Lemma plus_d_e_g1_le' n m:
(1 <= n )%nat -> (1 <= m)%nat ->
g1 n m + (1 + D) * E <= g1 (S n) m.
Proof.
intros; replace (S n) with (n + 1)%nat by lia.
rewrite /g1; field_simplify.
replace (INR (n + 1)) with (INR n + 1).
rewrite !Rmult_plus_distr_l !Rmult_1_r 
-Rplus_assoc -!Rmult_plus_distr_l Rmult_comm.
apply: Rplus_le_compat_r.
rewrite Rplus_comm -Rplus_assoc.
apply: Rplus_le_compat; try nra.
rewrite Rplus_comm.
apply: Rplus_le_compat; try nra.
apply: Rmult_le_compat_l; auto with commonDB.
field_simplify. 
apply: Rminus_plus_le_minus.
rewrite Rplus_comm.
suff H1: (1 + D)^1  <= (1 + D) ^ m; try nra.
apply: Rle_pow; auto with commonDB.
lia.
rewrite plus_INR; simpl; nra.
Qed.
Hint Resolve plus_d_e_g1_le' : commonDB.


Lemma mult_d_e_g1_le' n m:
(1 <= n )%nat -> (1 <= m)%nat ->
g1 n m * (1 + D) + E <= g1 (S n) (S m).
Proof.
intros; replace (S n) with (n + 1)%nat by lia.
replace (S m) with (m + 1)%nat by lia.
unfold g1, g; field_simplify.
replace (INR (n + 1)) with (INR n + 1) by 
  (rewrite plus_INR; simpl; nra).
replace (INR (m + 1)) with (INR m + 1) by
  (rewrite plus_INR; simpl; nra).
rewrite !Rmult_plus_distr_l !Rmult_1_r. replace
(INR n * E * (1 + D) ^ m * D +
INR n * E * (1 + D) ^ m) with
(INR n * E * (1 + D) ^ m * (1 + D)) by nra.
rewrite !Rmult_plus_distr_r.
apply: Rplus_le_compat.
rewrite !Rmult_assoc  Rmult_comm !Rmult_assoc.
apply: Rmult_le_compat_l; try nra. 
apply: Rmult_le_compat_l; auto with commonDB. 
rewrite -Rmult_assoc Rmult_comm.
apply: Rmult_le_compat_l; auto with commonDB.
rewrite Rmult_comm tech_pow_Rmult.
replace (S m) with (m + 1)%nat by lia; nra.
replace (E) with (E * 1) at 1 by nra.
apply Rmult_le_compat_l; [apply  default_abs_ge_0 | ];
auto with commonDB.
Qed.
Hint Resolve mult_d_e_g1_le' : commonDB.

Lemma plus_d_e_g1_le n:
(1 <= n )%nat ->
g1 n n + (1 + D) * E <= g1 (S n) n.
Proof.  auto with commonDB. Qed. 
Hint Resolve plus_d_e_g1_le : commonDB.

Lemma plus_e_g1_le n:
g1 n n + E <= g1 (S n) n.
Proof.
rewrite /g1.
replace (S n) with (n + 1)%nat by lia.
replace (INR (n + 1)) with (INR n + 1).
rewrite Rmult_assoc Rmult_assoc.
apply: Rle_trans; 
  [ apply: Rle_refl| rewrite Rmult_plus_distr_r].
apply: Rplus_le_compat_l.
rewrite Rmult_plus_distr_l Rmult_1_l Rmult_1_r. 
suff : E + 0 * 0 <= E + E * g n; first by nra.
apply: Rplus_le_compat_l. 
apply: Rmult_le_compat; try nra;
auto with commonDB.
rewrite plus_INR; simpl; nra. 
Qed.
Hint Resolve plus_e_g1_le : commonDB.

Lemma g1n_le_g1Sn n:
(1 <= n )%nat ->
g1 n (n - 1) <= g1 (S n) (S (n - 1)).
Proof.
rewrite /g1 => Hn.
replace (S n) with (n + 1)%nat by lia.
replace (INR (n + 1)) with (INR n + 1).
apply: Rmult_le_compat.
apply: Rmult_le_pos; auto with commonDB.
rewrite /g; field_simplify; apply pow_le;
auto with commonDB.
apply: Rmult_le_compat; try nra; auto with commonDB.
apply: Rplus_le_compat_l; auto with commonDB.
rewrite plus_INR; simpl; nra. 
Qed.
Hint Resolve g1n_le_g1Sn : commonDB.

Lemma g1n_le_g1Sn' n:
g1 n n <= g1 (S n) (S n).
Proof.
rewrite /g1. 
replace (S n) with (n + 1)%nat by lia.
replace (INR (n + 1)) with (INR n + 1).
apply: Rmult_le_compat.
apply: Rmult_le_pos; auto with commonDB.
rewrite /g; field_simplify; apply pow_le;
auto with commonDB.
apply: Rmult_le_compat; try nra; auto with commonDB.
apply: Rplus_le_compat_l; auto with commonDB.
rewrite addnC.
auto with commonDB. 
rewrite plus_INR; simpl; nra.
Qed.
Hint Resolve g1n_le_g1Sn' : commonDB.

Lemma Rplus_le_lt_compat a1 a2 b1 b2 :
 a1 <= a2 -> b1 < b2 ->  a1 + b1 < a2 + b2.
Proof.  nra. Qed.

Lemma Rmult_le_lt_compat a1 a2 b1 b2 :
 0 < a1 -> 0 < b1 -> a1 < a2 -> b1 <= b2 ->  a1 * b1 < a2 * b2.
Proof.  nra. Qed.

Lemma g1n_lt_g1Sn n:
(1 <= n )%nat ->
g1 n (n - 1) < g1 (S n) (S (n - 1)).
Proof.
rewrite /g1 => Hn.
replace (S n) with (n + 1)%nat by lia.
apply: Rmult_lt_compat.
apply: Rmult_le_pos; auto with commonDB.
rewrite /g; field_simplify; apply pow_le;
auto with commonDB.
apply: Rmult_le_lt_compat; try nra; auto with commonDB.
apply lt_0_INR; lia.
suff : INR n < INR n + 1 ; simpl; try nra. 
move => H.
rewrite plus_INR; simpl; nra. 
rewrite /g; field_simplify. 
apply: Rlt_pow; auto with commonDB.
suff : 0 < D; try nra; auto with commonDB.
Qed.

Lemma round_FT2R a :
  (Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
     (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE) (FT2R a)) = @FT2R t a.
Proof. 
rewrite Generic_fmt.round_generic //.
apply Binary.generic_format_B2R.
Qed.


Lemma BMINUS_neg_zero: forall (c: ftype t), feq (BMINUS neg_zero (BOPP c)) c.
Proof. destruct c; try destruct s; reflexivity. Qed.

Lemma foldl_congr: forall  (op: ftype t -> ftype t -> ftype t)
                                          (Hop: forall x y, feq x y -> forall x' y', feq x' y' ->
                                                  feq (op x x') (op y y'))
                                           (u v: ftype t) al bl, 
  feq u v -> Forall2 feq al bl -> feq (foldl op u al) (foldl op v bl).
Proof.
intros.
revert u v H bl H0; induction al; destruct bl; simpl; intros; inversion H0; clear H0; subst; auto.
Qed.

Lemma BPLUS_neg_zero: forall (c: ftype t), feq (BPLUS c neg_zero) c.
Proof. destruct c; try destruct s; reflexivity. Qed.

Lemma BPLUS_comm: forall (x y: ftype t),  feq (BPLUS x y) (BPLUS y x).
Proof.
destruct x, y; try destruct s; try destruct s0; try reflexivity;
unfold BPLUS, BINOP, feq, Binary.Bplus, Binary.BSN2B, BinarySingleNaN.SF2B; simpl;
rewrite (Z.min_comm e1 e);
rewrite ?(Pos.add_comm (fst (SpecFloat.shl_align m0 e1 (Z.min e e1)))).
1,4: destruct (BinarySingleNaN.SF2B _ _); simpl; auto.
1,2: destruct (BinarySingleNaN.binary_normalize _ _ _ _ _ _ _ _); simpl; auto.
Qed.

Lemma MINUS_PLUS_BOPP: forall x y: ftype t, feq (BMINUS x y) (BPLUS x (BOPP y)).
Proof.
destruct x, y; try destruct s; try destruct s0; try reflexivity;
unfold BMINUS, BPLUS, BINOP, BOPP, UNOP, feq, Binary.Bplus, Binary.Bminus, 
   Binary.BSN2B, BinarySingleNaN.SF2B, Binary.build_nan; simpl.
1,4: destruct (BinarySingleNaN.binary_normalize _ _ _ _ _ _ _ _); auto.
1,2: destruct (BinarySingleNaN.SF2B _ _); auto.
Qed.

End WithType. 

Global Hint Resolve 
  g_pos
  le_g_Sn
  d_le_g
  d_le_g_1
  g1_pos
  plus_d_e_g1_le'
  one_plus_d_mul_g1
  e_le_g1
  mult_d_e_g1_le'
  plus_d_e_g1_le
  plus_e_g1_le
  g1n_le_g1Sn
  Rplus_le_lt_compat
  Rmult_le_lt_compat
  g1n_lt_g1Sn
: commonDB.

Ltac field_simplify_Rabs :=
match goal with 
|- Rabs ?a <= _ =>
field_simplify a;
(repeat split; 
try match goal with |-?z <> 0 =>
field_simplify z (*; Interval.Tactic.interval *)
end)
end.
