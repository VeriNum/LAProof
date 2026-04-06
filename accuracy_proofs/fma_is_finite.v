(** * Finite Sum from Bounded Inputs

    This file establishes key lemmas for proving finiteness of floating-point
    dot products computed via fused multiply-add (FMA) operations. The central
    result, [finite_sum_from_bounded], shows that if all input vector elements
    are bounded in absolute value, then the accumulated
    floating-point dot product remains finite.

    The proof strategy relies on:
    - A bound function [fun_bnd t n] that decreases monotonically in n,
      ensuring that element-wise bounds suffice to prevent overflow at each
      FMA step.
    - Forward error analysis for FMA-based dot products, connecting floating-point
      accumulation to real-valued dot products.

    ** Key Definitions

    - [fun_bnd t n] : A per-element magnitude bound such that dot products of
      vectors of length n whose entries satisfy this bound do not overflow.

    ** Key Lemmas

    - [fun_bnd_le] : The bound [fun_bnd t n] is non-increasing in n.
    - [fun_bound_pos] : The bound [fun_bnd t n] is non-negative.
    - [finite_sum_from_bounded] : Element-wise bounds on inputs
      imply finiteness of the entire FMA dot product accumulation.
*)

From LAProof.accuracy_proofs Require Import
  preamble
  real_lemmas
  common
  dotprod_model
  sum_model
  float_acc_lems
  dot_acc_lemmas
  sum_acc.

Import Zorder.

Section NAN.

Context {NAN : FPCore.Nans} {t : type}.

Notation fmax := (@fmax t).

(** ** Bound Function *)

(** [fun_bnd t n] is used to construct a bound that will not cause
    overflow during FMA-based dot product of vectors of length n. *)

Definition fun_bnd (t : type) (n : nat) :=
  let x := (fmax - @default_abs t) / (1 + @default_rel t) - @g1 t n (n - 1) in
  let y := 1 / (1 + INR n * (@g t (n - 1) + 1)) in
  x * y.


(** ** Positivity of [fun_bnd] Components *)

(** The numerator of [fun_bnd] is non-negative when the g1 bound holds. *)

Lemma fun_bnd_pos_1 :
  forall (n : nat)
    (Hn : @g1 t (n + 1) n <= fmax),
    0 <= (fmax - @default_abs t) / (1 + @default_rel t) - @g1 t n (n - 1).
Proof.
  intros n Hn.
  apply Rle_0_minus.
  apply Generic_proof.Rdiv_le_mult_pos;
    [ apply default_rel_plus_1_gt_0
    | apply Rminus_plus_le_minus ].
  assert (Hn0 : (n = 0)%nat \/ (1 <= n)%nat) by lia.
  destruct Hn0 as [Hn0 | Hn0]; subst.
  { (* n = 0 *)
    simpl; unfold g1, g; simpl; field_simplify.
    apply default_abs_le_fmax. }
  assert (Hn1 : (n = 1)%nat \/ (1 < n)%nat) by lia.
  destruct Hn1 as [Hn1 | Hn1]; subst.
  { (* n = 1 *)
    simpl; unfold g1, g; simpl; field_simplify.
    eapply Rle_trans.
    - apply Rplus_le_compat.
      + apply Rmult_le_compat;
          [ apply default_abs_ge_0
          | apply default_rel_ge_0
          | apply default_abs_ub
          | apply default_rel_ub ].
      + apply Rmult_le_compat_l; try nra.
        apply default_abs_ub.
    - eapply Rle_trans; [| apply bpow_fmax_lb_4]; nra. }
  (* n > 1 *)
  eapply Rle_trans.
  - apply mult_d_e_g1_le'; try lia.
  - replace (S n) with (n + 1)%nat by lia.
    replace (S (n - 1)) with n by lia.
    auto.
Qed.

(** ** Monotonicity of [fun_bnd] *)

(** [fun_bnd t n] is non-increasing. *)
    
Lemma fun_bnd_le (n : nat) :
  forall (Hn : @g1 t (S n + 1) (S n) <= fmax),
    fun_bnd t (S n) <= fun_bnd t n.
Proof.
  assert (Hn0 : (n = 0)%nat \/ (1 <= n)%nat) by lia.
  destruct Hn0 as [Hn0 | Hn0]; subst.
  { (* n = 0 *)
    intros Hn; simpl; unfold fun_bnd.
    apply Rmult_le_compat; try apply Rabs_pos.
    - apply fun_bnd_pos_1; auto.
    - simpl; unfold g; simpl; field_simplify; nra.
    - apply Rminus_le_minus; simpl; unfold g1, g;
        field_simplify; simpl; field_simplify;
        apply default_abs_ge_0.
    - simpl; unfold g; field_simplify; simpl; nra. }
  (* n >= 1 *)
  intros Hn; unfold fun_bnd.
  assert (Hpos_Sn : 0 < 1 + INR (S n) * (@g t (S n - 1) + 1)).
  { apply Rplus_lt_le_0_compat; try nra.
    apply Rmult_le_pos;
      [ apply pos_INR
      | apply Rplus_le_le_0_compat; try nra; apply g_pos ]. }
  assert (Hpos_n : INR n * @g t (n - 1) + INR n + 1 > 0).
  { apply Rplus_lt_le_0_compat; try nra.
    apply Rplus_le_lt_0_compat;
      [ apply Rmult_le_pos; [apply pos_INR | apply g_pos]
      | apply lt_0_INR; lia ]. }
  apply Rmult_le_compat; try apply Rabs_pos.
  - apply fun_bnd_pos_1; auto.
  - apply Rdiv_le_0_compat_Raux; try nra.
  - apply Rminus_le_minus.
    replace (S n - 1)%nat with (S (n - 1))%nat by lia.
    apply g1n_le_g1Sn; auto.
  - apply Rcomplements.Rle_div_r.
    apply Rlt_gt.
    replace (/ (1 + INR (S n) * (@g t (S n - 1) + 1)))
      with (1 / (1 + INR (S n) * (@g t (S n - 1) + 1))) by nra.
    apply Rdiv_lt_0_compat; try nra.
    field_simplify; try nra.
    apply Rcomplements.Rle_div_r; try nra.
    rewrite Rmult_1_l.
    apply Rplus_le_compat; try nra.
    apply Rplus_le_compat.
    + apply Rmult_le_compat;
        [ apply pos_INR
        | apply g_pos
        | apply le_INR; lia
        | replace (S n - 1)%nat with (S (n - 1))%nat by lia;
          apply le_g_Sn ].
    + apply le_INR; lia.
Qed.

(** ** List Splitting Lemmas *)

(** The two halves of l have equal length. *)

Lemma length_split {A : Type} (l : list (A * A)) :
  length (fst (List.split l)) = length (snd (List.split l)).
Proof.
  induction l as [| a l IHl]; [simpl; auto |].
  destruct a; simpl.
  destruct (List.split l); simpl in *; lia.
Qed.

(** [fun_bnd t n] is non-negative. *)

Lemma fun_bound_pos (n : nat) :
  forall (Hn : @g1 t (n + 1) n <= fmax),
    0 <= fun_bnd t n.
Proof.
  intros Hn; unfold fun_bnd.
  apply Rmult_le_pos.
  - apply fun_bnd_pos_1; auto.
  - apply Rdiv_le_0_compat_Raux; try nra.
    apply Rplus_lt_le_0_compat; try nra.
    apply Rmult_le_pos;
      [ apply pos_INR
      | apply Rplus_le_le_0_compat; try nra; apply g_pos ].
Qed.

(** Splitting and recombining a list of pairs is the identity. *)

Lemma combine_split {A : Type} (l : list (A * A)) :
  combine (fst (List.split l)) (snd (List.split l)) = l.
Proof.
  induction l as [| a l IHl]; [simpl; auto |].
  destruct a; simpl.
  destruct (List.split l); simpl in *.
  rewrite IHl; auto.
Qed.

(** ** Main Result: Finiteness from Bounded Inputs *)

(** If every pair [(x, y)] in the combined input list satisfies:
    - both x and y are finite,
    - |FT2R x| and |FT2R y| are strictly bounded,

    and the g1 overflow condition holds for the list length, then the
    FMA dot product accumulation fp is finite.

    The proof proceeds by induction on the input list, applying the single-step
    [is_finite_fma_no_overflow'] lemma and the forward error bound
    [fma_dotprod_forward_error_rel] at each step. *)
    
Lemma finite_sum_from_bounded :
  forall (v1 v2 : list (ftype t))
    (fp : ftype t)
    (Hfp : fma_dot_prod_rel (List.combine v1 v2) fp)
    (Hn  : @g1 t (S (length (List.combine v1 v2)) + 1)
                  (S (length (List.combine v1 v2))) <= fmax),
    (forall x, In x (List.combine v1 v2) ->
        Binary.is_finite (fst x) = true /\
        Binary.is_finite (snd x) = true /\
        Rabs (FT2R (fst x)) < sqrt (fun_bnd t (length (List.combine v1 v2))) /\
        Rabs (FT2R (snd x)) < sqrt (fun_bnd t (length (List.combine v1 v2)))) ->
    Binary.is_finite fp = true.
Proof.
  intros v1 v2.
  induction (List.combine v1 v2) as [| a l IHl].
  { (* base case: empty list *)
    intros fp Hfp Hn Hbnd.
    inversion Hfp; subst; auto. }
  { (* inductive case: a :: l *)
    intros fp Hfp Hn Hbnd.
    inversion Hfp; subst.
    (* Establish the g1 bound for the shorter list *)
    assert (Hn' : @g1 t (S (length l) + 1) (S (length l)) <= fmax).
    { eapply Rle_trans; [| apply Hn]; simpl.
      set (n := (length l + 1)%nat).
      replace (length l)         with (n - 1)%nat by lia.
      replace ((n - 1).+1 + 1)%nat  with (n.+1)   by lia.
      replace ((n - 1).+2 + 1)%nat  with (n.+1.+1) by lia.
      replace ((n - 1).+1)%nat      with (n.+1 - 1)%nat by lia.
      apply g1n_le_g1Sn; lia. }
    (* Propagate element-wise bounds to the tail *)
    assert (Hin : forall x : ftype t * ftype t,
        In x l ->
        Binary.is_finite (fst x) = true /\
        Binary.is_finite (snd x) = true /\
        Rabs (FT2R (fst x)) < sqrt (fun_bnd t (length l)) /\
        Rabs (FT2R (snd x)) < sqrt (fun_bnd t (length l))).
    { intros x Hx; repeat split;
        [ apply Hbnd; simpl; auto
        | apply Hbnd; simpl; auto
        | eapply Rlt_le_trans;
            [ apply Hbnd; simpl; auto
            | apply sqrt_le_1_alt; apply fun_bnd_le; auto ]
        | eapply Rlt_le_trans;
            [ apply Hbnd; simpl; auto
            | apply sqrt_le_1_alt; apply fun_bnd_le; auto ] ]. }
    (* Finiteness of the head elements *)
    assert (Hfina : Binary.is_finite (fst a) = true /\
                    Binary.is_finite (snd a) = true).
    { split; apply Hbnd; simpl; auto. }
    destruct Hfina as [Hfina1 Hfina2].
    (* Apply the inductive hypothesis to obtain finiteness of the tail accumulator *)
    specialize (IHl s H2 Hn' Hin).
    (* Reduce to showing no overflow for the outermost FMA *)
    apply is_finite_fma_no_overflow'; auto.
    unfold fma_no_overflow, rounded.
    destruct (@generic_round_property t (FT2R (fst a) * FT2R (snd a) + FT2R s))
      as (del & eps & Hed & Hd & He & Hrn).
    rewrite Hrn; clear Hrn.
    (* Obtain real-valued dot product witnesses *)
    destruct (dotprod_rel_R_exists_fma l s H2)      as (rs      & Hrs).
    destruct (sum_rel_R_abs_exists_fma  l s H2)      as (rs_abs  & Habs).
    (* Forward error bound for the tail accumulator *)
    pose proof fma_dotprod_forward_error_rel l s H2 IHl rs rs_abs Hrs Habs as Hacc.
    apply Rabs_le_minus in Hacc.
    set (n := length l) in *.
    (* Bound the absolute value of the partial sum *)
    assert (Hacc' : Rabs (FT2R s) <=
                      (@g t n + 1) * rs_abs + @g1 t n (n - 1)).
    { eapply Rle_trans; [apply Hacc |].
      replace (g n * rs_abs + g1 n (n - 1) + Rabs rs)
        with ((@g t n * rs_abs + Rabs rs) + @g1 t n (n - 1)) by nra.
      apply Rplus_le_compat_r.
      field_simplify.
      apply Rplus_le_compat_l.
      rewrite <- (@R_dot_prod_rel_Rabs_eq (map FR2 l)); try nra; auto.
      apply (@dot_prod_sum_rel_R_Rabs (map FR2 l)); auto. }
    clear Hacc.
    pose proof dotprodR_rel_bound'  as C.
    pose proof dotprodR_rel_bound'' as D.
    (* Upper bound on the FMA output *)
    eapply Rle_lt_trans; [apply Rabs_triang |].
    rewrite Rabs_mult.
    eapply Rle_lt_trans; [apply Rplus_le_compat |].
    { apply Rmult_le_compat; try apply Rabs_pos.
      - eapply Rle_trans; [apply Rabs_triang |].
        apply Rplus_le_compat.
        + rewrite Rabs_mult.
          apply Rmult_le_compat; try apply Rabs_pos;
            apply Rlt_le; apply Hbnd; simpl; auto.
        + eapply Rle_trans; [apply Hacc' |].
          apply Rplus_le_compat_r.
          apply Rmult_le_compat_l;
            [ apply Rplus_le_le_0_compat; try nra; apply g_pos | apply D ].
          * apply fun_bound_pos; apply Hn'.
          * apply Habs.
          * intros; split; apply Rlt_le; apply Hbnd; simpl; auto.
      - assert (HD : Rabs (1 + del) <= 1 + @default_rel t).
        { eapply Rle_trans; [apply Rabs_triang |].
          rewrite Rabs_R1; apply Rplus_le_compat_l.
          eapply Rle_trans; [apply Hd |]; nra. }
        apply HD. 
        } 
        apply He.
    (* Final algebraic inequality using fun_bnd structure *)
    rewrite sqrt_def.
    { unfold fun_bnd.
      replace (length (a :: l)) with (S n) by (simpl; lia).
      set (x := (@g t (S n - 1) + 1)).
      set (y := (1 + INR (S n) * x)).
      set (z := @g1 t (S n) (S n - 1)).
      set (u := ((fmax - @default_abs t) / (1 + @default_rel t) - z) * (1 / y)).
      rewrite <- !Rplus_assoc.
      replace (u + (@g t n + 1) * (INR (length l) * u))
        with (u * (1 + (@g t n + 1) * INR (length l))) by nra.
      apply Rcomplements.Rlt_minus_r.
      apply Rcomplements.Rlt_div_r;
        [apply Rlt_gt; apply default_rel_plus_1_gt_0 |].
      apply Rcomplements.Rlt_minus_r.
      assert (Hpos_n : 0 < 1 + (@g t n + 1) * INR (length l)).
      { apply Rplus_lt_le_0_compat; try nra.
        apply Rmult_le_pos;
          [ apply Rplus_le_le_0_compat; try nra; apply g_pos
          | apply pos_INR ]. }
      apply Rcomplements.Rlt_div_r; auto.
      assert (Hpos_y : 0 < 1 / (1 + INR (S (length l)) *
                                    (@g t (S (length l) - 1) + 1))).
      { apply Rcomplements.Rdiv_lt_0_compat; try nra.
        apply Rplus_lt_le_0_compat; try nra.
        apply Rmult_le_pos;
          [ apply pos_INR
          | apply Rplus_le_le_0_compat; try nra; apply g_pos ]. }
      assert (Hpos_Sn : 0 < 1 + INR (S n) * (@g t (S n - 1) + 1)).
      { apply Rplus_lt_le_0_compat; try nra.
        apply Rmult_le_pos;
          [ apply pos_INR
          | apply Rplus_le_le_0_compat; try nra; apply g_pos ]. }
      rewrite rdiv_mult_eq; try nra.
      unfold u, z, y, x.
      apply Rmult_lt_compat;
        [apply fun_bnd_pos_1; auto | apply Rlt_le; auto | |].
      { unfold fmax.
        apply Rminus_lt_minus.
        replace n with (length l) by (subst n; auto).
        assert (Hl : l = [] \/ l <> []).
        { destruct l; [left; auto | right].
          eapply hd_error_some_nil; simpl; auto. }
        destruct Hl as [Hl | Hl].
        - subst; simpl; unfold g1, g; field_simplify; simpl;
            field_simplify; apply default_abs_gt_0.
        - apply size_not_empty_nat in Hl.
          change @length with @size in *.
          replace (S (size l) - 1)%nat with (S (size l - 1))%nat by lia.
          apply g1n_lt_g1Sn; auto; lia. }
      { apply Rcomplements.Rlt_div_r.
        - apply Rlt_gt.
          replace (/ (1 + INR (S n) * (@g t (S n - 1) + 1)))
            with (1 / (1 + INR (S n) * (@g t (S n - 1) + 1))) by nra.
          apply Rdiv_lt_0_compat; try nra.
        - field_simplify; try nra.
          apply Rcomplements.Rlt_div_r; try nra.
          rewrite Rmult_1_l.
          apply Rplus_lt_le_compat; try nra.
          apply Rplus_le_lt_compat.
          + rewrite Rmult_comm.
            apply Rmult_le_compat;
              [ apply pos_INR
              | apply g_pos
              | apply le_INR; lia
              | replace (S n - 1)%nat with n%nat by lia; nra ].
          + unfold n; apply lt_INR; lia. } }
    apply fun_bound_pos; auto. }
Qed.

End NAN.