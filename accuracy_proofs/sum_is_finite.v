(** * Finite Sum Boundedness

    This file establishes conditions under which floating-point summation
    remains finite (non-infinite, non-NaN). The central contributions are:

    - [is_finite_sum_no_overflow']: a helper lemma showing that the floating-point
      sum is finite whenever both summands are finite and no overflow occurs.

    - [fun_bnd]: a bound on individual list elements sufficient to guarantee
      that their floating-point sum does not overflow. This bound decreases
      monotonically as the list length grows, reflecting the accumulation of
      rounding error.

    - [fun_bnd_le]: monotonicity of [fun_bnd], showing that the per-element
      bound for a list of length S n is no greater than that for length n.

    - [finite_sum_from_bounded]: the main theorem. Given a list of finite
      floating-point values each bounded in absolute value, 
      the floating-point sum fs satisfying [sum_rel_Ft] is
      finite. The proof proceeds by induction on the list, using the
      [fun_bnd_le] monotonicity lemma to discharge the inductive hypothesis
      and explicit rounding-error arithmetic to close the overflow bound.
*)

From LAProof.accuracy_proofs Require Import
  preamble
  real_lemmas
  common
  dotprod_model
  sum_model
  float_acc_lems
  fma_dot_acc
  sum_acc.

Section NAN.

Variable NAN : FPCore.Nans.

(** ** Overflow-free addition preserves finiteness

    If x and y are finite floating-point numbers and their sum does
    not overflow (in the sense of [Bplus_no_overflow]), then their sum is
    is finite. *)
    
Lemma is_finite_sum_no_overflow' (t : type) :
  forall (x y : ftype t)
         (Hfinx : Binary.is_finite x = true)
         (Hfiny : Binary.is_finite y = true)
         (Hov   : @Bplus_no_overflow t (FT2R x) (FT2R y)),
    Binary.is_finite (BPLUS x y) = true.
Proof.
  intros x y Hfinx Hfiny Hov.
  pose proof (Binary.Bplus_correct
                (fprec t) (femax t)
                (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE x y Hfinx Hfiny) as Hcorrect.
  unfold Bplus_no_overflow, FT2R in Hov.
  apply Rlt_bool_true in Hov.
  rewrite Hov in Hcorrect.
  simpl in Hcorrect.
  destruct Hcorrect as (_ & HB & _).
  simpl; auto.
Qed.

(** ** Per-element bound for finite summation

    [fun_bnd t n] is the maximum absolute value that each element of an
    n-element list may have while still guaranteeing that the
    floating-point sum of the list is finite.  It is defined as

    <<fmax t / (1 + default_rel t)  *  1 / (1 + n * (g t (n-1) + 1))>>

    where the function g encodes the standard (1 + eps)^k - 1 rounding-error 
    growth factor. *)
    
Definition fun_bnd (t : type) (n : nat) :=
  (@fmax t) / (1 + @default_rel t) * 1 / (1 + INR n * (@g t (n - 1) + 1)).

(** ** Monotonicity of [fun_bnd]

    The per-element bound is non-increasing in the list length: a longer
    list requires each element to be smaller to keep the sum finite. *)
    
Lemma fun_bnd_le (t : type) (n : nat) :
  fun_bnd t (S n) <= fun_bnd t n.
Proof.
  unfold fun_bnd. 
  apply Rmult_le_compat_l.
  - rewrite Rmult_1_r.
    apply Rcomplements.Rdiv_le_0_compat.
    unfold fmax; apply bpow_ge_0.
    eapply Rlt_trans with 1; try nra.
    apply default_rel_plus_1_gt_1.
  - apply rdiv_le;  try (
    apply Rplus_lt_le_0_compat; try nra;
    apply Rmult_le_pos; [apply pos_INR| ];
    apply Rplus_le_le_0_compat; try nra;
    apply g_pos ).
    apply Rplus_le_compat_l.
    apply Rmult_le_compat; [apply pos_INR | | |].
    apply Rplus_le_le_0_compat; try nra; apply g_pos.
    apply le_INR; try lia.
    unfold g; field_simplify.
    apply Rle_pow.
    apply default_rel_plus_1_ge_1.
    simpl; lia.
Qed.

(** ** Main theorem: element-wise bound implies finite sum

    If every element of l is finite and sufficiently bounded
    then the floating-point sum fs satisfying [sum_rel_Ft l fs] is finite.

    The proof proceeds by induction on l, using [fun_bnd_le] to transfer
    the per-element bound to the tail, then closing the overflow condition
    via explicit rounding-error arithmetic and algebraic manipulation. *)
    
Lemma finite_sum_from_bounded :
  forall (t : type) (l : list (ftype t))
         (fs : ftype t)
         (Hfs : sum_rel_Ft l fs),
    (forall x, In x l ->
       Binary.is_finite x = true /\ Rabs (FT2R x) < fun_bnd t (length l)) ->
    Binary.is_finite fs = true.
Proof.
  intros t.
  induction l as [| a l IHl].
  - (* Base case: empty list *)
    intros fs Hfs _.
    inversion Hfs; subst; simpl; auto.
  - (* Inductive case: list is [a :: l] *)
    intros fs Hfs Hbnd.
    inversion Hfs; subst.

    (* Transfer the bound to the tail l using [fun_bnd_le]. *)
    assert (Hin : forall x : ftype t,
               In x l ->
               Binary.is_finite x = true /\
               Rabs (FT2R x) < fun_bnd t (length l)).
    { intros x Hx.
      split.
      - apply Hbnd; simpl; auto.
      - eapply Rlt_le_trans.
        + apply Hbnd; simpl; auto.
        + apply fun_bnd_le. }

   (* The head element a is finite since it is in the list *)
    assert (Hfina: Binary.is_finite a = true) by
      (exact (proj1 (Hbnd a (in_eq a l)))).
    fold (@sum_rel_Ft NAN t) in H2.

    (* Apply the inductive hypothesis to obtain finiteness of the partial sum s. *)
    specialize (IHl s H2 Hin).

    apply is_finite_sum_no_overflow'; auto.

    (* Establish the no-overflow condition for a + s. *)
    unfold Bplus_no_overflow.

    (* Generic format witnesses for FT2R a and FT2R s. *)
    assert (A : Generic_fmt.generic_format Zaux.radix2
              (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
              (FT2R a))
      by apply Binary.generic_format_B2R.
    assert (B : Generic_fmt.generic_format Zaux.radix2
              (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
              (FT2R s))
      by apply Binary.generic_format_B2R.

    (* Obtain rounding error factor << d >> satisfying
       round(a + s) = (a + s) * (1 + d) with |d| <= default_rel. *)
    destruct (Plus_error.FLT_plus_error_N_ex
                Zaux.radix2
                (SpecFloat.emin (fprec t) (femax t))
                (fprec t)
                (fun x0 : Z => negb (Z.even x0))
                (FT2R a) (FT2R s) A B)
      as (d & Hd & Hd').
    unfold Relative.u_ro in Hd.
    fold (@default_rel t) in Hd.

    (* Rewrite the rounding mode to match Hd'. *)
    assert (H1 : Generic_fmt.round Zaux.radix2
                   (SpecFloat.fexp (fprec t) (femax t))
                   (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
                   (FT2R a + FT2R s)
                 = Generic_fmt.round Zaux.radix2
                     (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
                     (Generic_fmt.Znearest (fun x0 : Z => negb (Z.even x0)))
                     (FT2R a + FT2R s))
      by auto.
    rewrite <- H1 in Hd'; clear H1.
    rewrite Hd'; clear Hd'.

    (* Witnesses for the real-valued sum and its absolute-value sum. *)
    destruct (sum_rel_R_exists l s H2)     as (rs     & Hrs).
    destruct (sum_rel_R_abs_exists l s H2) as (rs_abs & Habs).

    (* Use [fSUM] to bound |FT2R s| in terms of the rounding-error growth
       factor g applied to the absolute-value sum rs_abs. *)
    assert (H3' : s = sumF (rev l)).
    { apply (sum_rel_Ft_fold (rev l)). rewrite revK. exact H2. }
    assert (IHl' : Binary.is_finite (sumF (rev l))) by (rewrite <- H3'; auto).
    assert (Hrev1 : sumR (map FT2R (rev l)) = rs).
    { rewrite map_rev sumR_rev. symmetry. apply sum_rel_R_fold. exact Hrs. }
    assert (Hrev2 : sumR (map Rabs (map FT2R (rev l))) = rs_abs).
    { rewrite map_rev map_rev sumR_rev. symmetry. apply sum_rel_R_fold. exact Habs. }
    pose proof (@fSUM NAN t (rev l) IHl') as Hfsum.
    rewrite <- H3' in Hfsum.
    rewrite Hrev1 in Hfsum.
    rewrite Hrev2 in Hfsum.
    rewrite size_rev in Hfsum.
    rewrite Rabs_minus_sym in Hfsum.
    apply Rabs_le_minus in Hfsum.

    (* Bound |FT2R s| <= (g(n) + 1) * rs_abs. *)
    assert (Hs_abs : Rabs (FT2R s) <=
                       (@g t (length l) + 1) * rs_abs).
    { eapply Rle_trans; [apply Hfsum |].
      assert (Hrsle : Rabs rs <= rs_abs).
      { eapply Rle_trans.
        - eapply sum_rel_R_Rabs; [apply Hrs | apply Habs].
        - eapply Req_le; eapply sum_rel_R_Rabs_eq; apply Habs. }
      change @size with @length.
      ring_simplify.
      apply Rplus_le_compat_l; exact Hrsle. }

    (* Bound |1 + d| <= 1 + default_rel. *)
    assert (HD : Rabs (1 + d) <= 1 + @default_rel t).
    { eapply Rle_trans; [apply Rabs_triang |].
      rewrite Rabs_R1.
      apply Rplus_le_compat_l.
      eapply Rle_trans; [apply Hd |].
      apply Rdiv_le_left.
      - apply Fourier_util.Rlt_zero_pos_plus1, default_rel_gt_0.
      - eapply Rle_trans with (@default_rel t * 1); try nra. }

    (* Combine bounds: |(a + s)*(1+d)| <= (1 + default_rel) * (|a| + |s|)
       and then close using [fun_bnd] algebra. *)
    eapply Rle_lt_trans.
    { rewrite Rabs_mult.
      apply Rmult_le_compat; try apply Rabs_pos.
      - eapply Rle_trans; [apply Rabs_triang |].
        apply Rplus_le_compat.
        + apply Rlt_le, Hbnd; simpl; auto.
        + eapply Rle_trans; [apply Hs_abs |].
          apply Rmult_le_compat_l.
          * apply Rplus_le_le_0_compat; try nra; apply g_pos.
          * apply sum_rel_bound''.
            -- apply Habs.
            -- intros x Hx; apply Rlt_le, Hbnd; simpl; auto.
      - apply HD. }

    (* Pure algebraic closure: the accumulated bound fits within [fmax t]. *)
    unfold fun_bnd; rewrite Rmult_1_r.
    assert (Heq_sub : (length (a :: l) - 1)%nat = length l)
      by (simpl; rewrite subSS subn0; reflexivity).
    rewrite Heq_sub.
    set (x := @g t (length l) + 1).
    set (y := 1 + INR (length (a :: l)) * x).
    set (z := (@fmax t) / (1 + @default_rel t) / y).
    change @size with @length.

    replace (z + x * (INR (length l) * z))
      with  (z * (1 + x * INR (length l)))
      by nra.
    assert (Hy : 0 < y).
    { unfold y.
      apply Rplus_lt_le_0_compat; try nra.
      apply Rmult_le_pos; [apply pos_INR |].
      unfold x; apply Rplus_le_le_0_compat; try nra; apply g_pos. }
    assert (Hy' : y <> 0) by (apply Stdlib.Rlt_neq_sym; auto).

    (* Simplify (1 + default_rel) * z = fmax / y. *)
    assert (H0 : (1 + @default_rel t) * z = (@fmax t) / y).
    { unfold z; field_simplify; auto.
      split; auto.
      apply tech_Rplus; try nra.
      apply default_rel_gt_0. }

    (* 1 + x * INR (length l) < y. *)
    assert (Hineq : 1 + x * INR (length l) < y).
    { unfold y.
      apply Rplus_le_lt_compat; try nra.
      rewrite Rmult_comm.
      apply Rmult_lt_compat_r; [unfold x; apply Rle_lt_0_plus_1, g_pos |].
      apply lt_INR; simpl; lia. }

    (* Rewrite via H0: z*(1+M)*(1+D) = (fmax/y)*(1+M). *)
    replace (z * (1 + x * INR (length l)) * (1 + @default_rel t))
      with  ((@fmax t) / y * (1 + x * INR (length l)))
      by (rewrite <- H0; ring).
    unfold fmax.
    apply Rlt_le_trans with (bpow Zaux.radix2 (femax t) / y * y).
    { apply Rmult_lt_compat_l; [| exact Hineq].
      unfold Rdiv; apply Rmult_lt_0_compat; [apply bpow_gt_0 | apply Rinv_pos; exact Hy]. }
    unfold Rdiv; rewrite Rmult_assoc; rewrite Rinv_l; [lra | exact Hy'].
Qed.

End NAN.