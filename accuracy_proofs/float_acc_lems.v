(** * Floating-Point Operation Accuracy

    This file establishes accuracy lemmas for the basic floating-point
    operations [BPLUS], [BMINUS], [BMULT], and [BFMA] as defined in the
    VCFloat library. Each operation is analyzed in the
    _round-to-nearest-even_ (RNE) rounding mode.

    The central results take the form of the standard _rounding error model_: 
    given that a floating-point operation does not overflow, its result [fl(op)]
    satisfies a bound of the form

    %\[ \mathtt{fl}(a \mathbin{\mathrm{op}} b) = (a \mathbin{\mathrm{op}} b)(1 + \delta) + \varepsilon \]%
    #\[ \mathtt{fl}(a \mathbin{\mathrm{op}} b) = (a \mathbin{\mathrm{op}} b)(1 + \delta) + \varepsilon \]#

    where the relative error %$\delta$%#\(\delta\)# and absolute error %$\varepsilon$%#\(\varepsilon\)# satisfy

    %\[ |\delta| \leq \mathbf{u}, \qquad |\varepsilon| \leq \eta, \qquad \delta \cdot \varepsilon = 0 \]%
    #\[ |\delta| \leq \mathbf{u}, \qquad |\varepsilon| \leq \eta, \qquad \delta \cdot \varepsilon = 0 \]#

    and where %$\mathbf{u}$%#\(\mathbf{u}\)# denotes the _unit roundoff_ and %$\eta$%#\(\eta\)# denotes 
    the _underflow threshold_ for the given floating-point type << t >>.
    The mutual exclusion condition %$\delta \cdot \varepsilon = 0$%#\(\delta \cdot \varepsilon = 0\)# reflects
    the standard decomposition: in the normal range only relative error is incurred, while in the 
    subnormal range only absolute error is incurred.

    For [BPLUS] and [BMINUS] the error model simplifies to
    %$\mathtt{fl}(a \mathbin{\mathrm{op}} b) = (a \mathbin{\mathrm{op}} b)(1 + \delta)$%#\(\mathtt{fl}(a \mathbin{\mathrm{op}} b) = (a \mathbin{\mathrm{op}} b)(1 + \delta)\)#,
    since addition and subtraction on floating-point numbers that are
    already representable incur only relative error.

    ** Structure

    The file is organized as follows:

    - _Signed zero lemmas_: behavior of operations when one argument is zero.
    - _Signed zero facts_: [FT2R] evaluations at signed zeros. 
    - _No-overflow predicates_: [fma_no_overflow], [Bmult_no_overflow],
      [Bplus_no_overflow], [Bminus_no_overflow].
    - _Generic rounding lemma_: [generic_round_property], which extracts
      the %$(\delta, \varepsilon)$%#\((\delta, \varepsilon)\)# decomposition from the Flocq library for
      an arbitrary real number.
    - _Per-operation accuracy and finiteness lemmas_ for [BFMA], [BMULT],
      [BPLUS], and [BMINUS], each in two forms:
      - a form assuming a no-overflow hypothesis on real-valued arguments;
      - a primed form ([fma_accurate'], [BMULT_accurate'], etc.) assuming
        only that the _floating-point result_ is finite, from which the
        no-overflow condition is derived automatically.
    - _Correctness lemmas_ ([BFMA_correct], [BMULT_correct], [BPLUS_correct]):
      these combine the finiteness of inputs and the rounding identity into
      a single conclusion.
*)

From LAProof.accuracy_proofs Require Import preamble common.

Section GenFloat.

Context {NAN : FPCore.Nans} {t : type}.

(** ** Signed Zero Lemmas

    Behavior of [BMULT], [BPLUS], and [BFMA] when one operand evaluates
    to zero under [FT2R].  These are used in higher-level proofs to
    eliminate zero-valued terms from error bounds. *)

Lemma Bmult_0R (a f : ftype t) :
  Binary.is_finite (BMULT a f) ->
  FT2R a = 0 ->
  (BMULT a f) = neg_zero \/ (BMULT a f) = pos_zero.
Proof.
  rewrite /BMULT/BINOP //= /pos_zero/neg_zero/Binary.Bmult.
  destruct f, a, s, s0 => //=;
  move => FIN HA; try discriminate FIN; auto;
  try apply Float_prop.eq_0_F2R in HA;
  repeat (destruct m0; try discriminate HA).
Qed.

Lemma Bplus_0R (a f : ftype t) :
  Binary.is_finite (BPLUS a f) ->
  FT2R f = 0 ->
  FT2R (BPLUS a f) = FT2R a.
Proof.
  rewrite /BMULT/BINOP //=
    /pos_zero/neg_zero/Binary.Bmult.
  destruct f, a, s, s0 => //=;
  move => FIN HA; try discriminate FIN; auto;
  try apply Float_prop.eq_0_F2R in HA;
  repeat (destruct m0; try discriminate HA).
Qed.

Lemma Bfma_mult_0R (a f s : ftype t) :
  Binary.is_finite (BFMA a f s) ->
  FT2R a = 0 ->
  FT2R (BFMA a f s) = FT2R s.
Proof.
  rewrite /BMULT/BINOP //=.
  destruct f;
  destruct a;
  destruct s;
  destruct s0; destruct s1; destruct s => //=;
  move => FIN HA; try discriminate FIN; auto;
  try apply Float_prop.eq_0_F2R in HA;
  repeat (destruct m0; try discriminate HA).
Qed.

(** ** Signed Zero Values

    Signed zeros are finite, and their
    real-valued interpretations and that of [Zconst t 0] under [FT2R]
    are all zero.  These are used directly in arithmetic simplifications. *)

Fact neg_zero_is_finite :
  Binary.is_finite (@neg_zero t).
Proof. reflexivity. Qed.

Fact FT2R_neg_zero :
  FT2R (@neg_zero t) = 0.
Proof. reflexivity. Qed.

Fact FT2R_pos_zero :
  FT2R (@pos_zero t) = 0.
Proof. reflexivity. Qed.

Fact FT2R_Zconst_0 :
  FT2R (Zconst t 0) = 0.
Proof. reflexivity. Qed.

Notation fmax := (@fmax t).

(** ** No-Overflow Predicates

    Each predicate asserts that the RNE-rounded exact result of the
    corresponding operation has absolute value strictly less than
    [fmax], i.e., the result falls within the normal
    floating-point range.  These are the preconditions for the main
    accuracy lemmas and are derived automatically in the primed variants. *)

Definition fma_no_overflow (x y z : R) : Prop :=
  (Rabs (rounded t (x * y + z)) < fmax)%R.

Definition Bmult_no_overflow (x y : R) : Prop :=
  (Rabs (rounded t (x * y)) < fmax)%R.

Definition Bplus_no_overflow (x y : R) : Prop :=
  (Rabs (Generic_fmt.round Zaux.radix2
           (SpecFloat.fexp (fprec t) (femax t))
           (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
           (x + y)) < fmax)%R.

Definition Bminus_no_overflow (x y : R) : Prop :=
  (Rabs (Generic_fmt.round Zaux.radix2
           (SpecFloat.fexp (fprec t) (femax t))
           (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
           (x - y)) < fmax)%R.

Notation D := (@default_rel t).
Notation E := (@default_abs t).

(** ** Generic Rounding Error Decomposition

    The lemma below is the shared foundation for all per-operation accuracy
    results.  It packages the Flocq [error_N_FLT] theorem into the
    %$(\delta, \varepsilon)$%#\((\delta, \varepsilon)\)# form used throughout this library. *)

(** [generic_round_property] is the fundamental %$(\delta,\varepsilon)$%#\((\delta,\varepsilon)\)#
    decomposition of RNE rounding error in the Flocq FLT format.

    The condition %$\delta * \varepsilon = 0$%#\(\delta *  \varepsilon = 0\)# 
    asserts that exactly one of the two error terms is zero, reflecting the fact 
    that the two sources of rounding error are mutually exclusive:

    - In the _normal range_, error is purely relative: %$\varepsilon = 0$%#\(\varepsilon = 0\)#.

    - In the _subnormal range_, error
      is purely absolute: %$\delta = 0$%#\(\delta = 0\)#

    No rounding event can simultaneously be in both regimes, so the two
    error terms never both appear at once. *)

Lemma generic_round_property :
  forall (x : R),
  exists delta epsilon : R,
    delta * epsilon = 0 /\
    (Rabs delta <= D)%R /\
    (Rabs epsilon <= E)%R /\
    Generic_fmt.round Zaux.radix2
      (SpecFloat.fexp (fprec t) (femax t))
      (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
      x = (x * (1 + delta) + epsilon)%Re.
Proof.
  intros.
  destruct (Relative.error_N_FLT Zaux.radix2
              (SpecFloat.emin (fprec t) (femax t)) (fprec t)
              (fprec_gt_0 t) (fun x0 : Z => negb (Z.even x0)) x)
    as [delta [epsilon [? [? [? ?]]]]].
  exists delta, epsilon.
  repeat split; auto.
Qed.

(** ** Fused Multiply-Add *)

(** [fma_accurate] establishes the standard rounding error model for the
    fused multiply-add operation. *)

Lemma fma_accurate :
  forall (x : ftype t) (FINx : Binary.is_finite x)
         (y : ftype t) (FINy : Binary.is_finite y)
         (z : ftype t) (FINz : Binary.is_finite z)
         (FIN : fma_no_overflow (FT2R x) (FT2R y) (FT2R z)),
  exists delta, exists epsilon,
    delta * epsilon = 0 /\
    Rabs delta <= D /\
    Rabs epsilon <= E /\
    (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1 + delta) + epsilon)%Re.
Proof.
  move => x FINx y FINy z FINz FIN. 
  pose proof (Binary.Bfma_correct (fprec t) (femax t)
                (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.fma_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE x y z FINx FINy FINz).
  fold (@FT2R t) in H.
  fold (@BFMA NAN t) in H.
  cbv zeta in H.
  pose proof (
    Raux.Rlt_bool_spec
      (Rabs
         (Generic_fmt.round Zaux.radix2
            (SpecFloat.fexp (fprec t) (femax t))
            (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
            (FT2R x * FT2R y + FT2R z)))
      fmax).
  unfold fmax in *.
  destruct H0.
  - destruct H as [? _].
    rewrite H.
    apply generic_round_property.
  - red in FIN. unfold rounded in FIN.
    unfold fmax in *.
    Lra.lra.
Qed.

(** [is_finite_fma_no_overflow] shows that finiteness of the result of an FMA
    implies the no-overflow condition on the exact value %$x \cdot y + z$%#\(x \cdot y + z\)#.
    This allows the primed form [fma_accurate'] to work directly from
    a finiteness hypothesis. *)

Lemma is_finite_fma_no_overflow :
  forall (x y z : ftype t)
    (HFINb : Binary.is_finite (BFMA x y z)),
  fma_no_overflow (FT2R x) (FT2R y) (FT2R z).
Proof.
  intros.
  red. set (ov := bpow Zaux.radix2 (femax t)).
  pose proof Rle_or_lt ov (Rabs (rounded t (FT2R x * FT2R y + FT2R z))) as Hor;
    destruct Hor; auto.
  apply Rlt_bool_false in H.
  assert (HFIN : Binary.is_finite x /\
                 Binary.is_finite y /\
                 Binary.is_finite z)
    by (destruct x, y, z; destruct s; destruct s0; destruct s1;
          simpl in *; try discriminate; repeat split; auto).
  destruct HFIN as (A & B & C).
  unfold rounded, ov in H.
  pose proof (Binary.Bfma_correct (fprec t) (femax t)
                (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.fma_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE x y z A B C) as H1.
  simpl in H1, H.
  rewrite H in H1; clear H.
  fold (BFMA x y z) in *.
  destruct (BFMA x y z); discriminate.
Qed.

(** [BFMA_finite_e] extracts finiteness of each individual argument from
    finiteness of the FMA result.  This is a standard regularity
    property: the IEEE 754 FMA result is non-finite if any input is
    non-finite (with the exception of a zero-times-infinity addend, which
    produces a NaN). *)

Lemma BFMA_finite_e :
  forall (a f u : ftype t)
    (Hfin : Binary.is_finite (BFMA a f u)),
  Binary.is_finite a /\
  Binary.is_finite f /\
  Binary.is_finite u.
Proof.
  intros.
  repeat split;
  destruct a, f, u; destruct s; destruct s0; destruct s1;
    try discriminate; auto.
Qed.

(** [is_finite_fma_no_overflow']: If all three inputs to an FMA are finite 
    and no overflow occurs, then the FMA result is finite. *)
    
Lemma is_finite_fma_no_overflow' :
  forall (x y z : ftype t)
    (Hfinx : Binary.is_finite x = true)
    (Hfiny : Binary.is_finite y = true)
    (Hfinz : Binary.is_finite z = true)
    (Hov   : fma_no_overflow (FT2R x) (FT2R y) (FT2R z)),
    Binary.is_finite (BFMA x y z) = true.
Proof.
  intros x y z Hfinx Hfiny Hfinz Hov.
  pose proof (Binary.Bfma_correct
                (fprec t) (femax t)
                (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.fma_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE
                x y z Hfinx Hfiny Hfinz) as H.
  cbv zeta in H.
  rewrite Rlt_bool_true in H.
  - destruct H as [_ [HFIN _]]; exact HFIN.
  - move: Hov; by rewrite /fma_no_overflow /rounded.
Qed.


(** [fma_accurate'] is the _finiteness-hypothesis_ form of [fma_accurate]:
    it requires only that the result is finite, deriving the
    no-overflow condition and input finiteness internally. *)

Lemma fma_accurate' :
  forall (x y z : ftype t)
    (FIN : Binary.is_finite (BFMA x y z)),
  exists delta, exists epsilon,
    delta * epsilon = 0 /\
    Rabs delta <= @default_rel t /\
    Rabs epsilon <= @default_abs t /\
    (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1 + delta) + epsilon)%Re.
Proof.
  intros.
  pose proof (BFMA_finite_e _ _ _ FIN) as H;
    destruct H as (A & B & C).
  apply fma_accurate => //.
  apply is_finite_fma_no_overflow; auto.
Qed.

(** [BFMA_correct] combines [BFMA_finite_e] and [is_finite_fma_no_overflow]
    to give the full correctness statement: finiteness of the result
    implies finiteness of all inputs and a rounding identity. *)

Lemma BFMA_correct (a b s : ftype t) :
  Binary.is_finite (BFMA a b s) ->
  (Binary.is_finite a /\ Binary.is_finite b /\ Binary.is_finite s) /\
  FT2R (BFMA a b s) =
    Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
      (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
      (FT2R a * FT2R b + FT2R s).
Proof.
  intros * FIN.
  pose proof (is_finite_fma_no_overflow a b s FIN) as H4;
    apply Rlt_bool_true in H4;
    unfold common.rounded in H4.
  assert (H : Binary.is_finite a = true /\
              Binary.is_finite b = true /\
              Binary.is_finite s = true).
  { unfold BFMA, BINOP in FIN.
    destruct a, b, s; auto; destruct s0, s1, s; discriminate. }
  split; auto.
  destruct H as [? [? ?]].
  pose proof (Binary.Bfma_correct (fprec t) (femax t)
                (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.fma_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE
                a b s H H0 H1) as H3; cbv zeta in H3.
  fold (@FT2R t) in H3.
  rewrite {}H4 in H3.
  fold (BFMA a b s) in H3.
  apply H3.
Qed.

(** ** Floating-Point Multiplication *)

(** [BMULT_accurate] establishes the rounding error model for multiplication,
    which computes %$\mathtt{fl}(x \cdot y)$%#\(\mathtt{fl}(x \cdot y)\)# under RNE rounding. *)

Lemma BMULT_accurate :
  forall (x y : ftype t)
    (FIN : Bmult_no_overflow (FT2R x) (FT2R y)),
  exists delta, exists epsilon,
    delta * epsilon = 0 /\
    Rabs delta <= @default_rel t /\
    Rabs epsilon <= @default_abs t /\
    (FT2R (BMULT x y) = (FT2R x * FT2R y) * (1 + delta) + epsilon)%Re.
Proof.
  intros.
  pose proof (Binary.Bmult_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.mult_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE x y).
  cbv zeta in H.
  pose proof (
    Raux.Rlt_bool_spec
      (Rabs
         (Generic_fmt.round Zaux.radix2
            (SpecFloat.fexp (fprec t) (femax t))
            (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
            (Binary.B2R _ _ x * Binary.B2R _ _ y))) fmax).
  fold (@FT2R t) in H, H0.
  unfold fmax in *.
  destruct H0.
  - destruct H as [? _].
    unfold BMULT, BINOP.
    rewrite {}H.
    apply generic_round_property.
  - red in FIN. unfold rounded in FIN.
    unfold fmax in *.
    lra.
Qed.

(** [is_finite_BMULT_no_overflow] shows that finiteness of [BMULT x y]
    implies that the exact product %$x \cdot y$%#\(x \cdot y\)# does not overflow. *)

Lemma is_finite_BMULT_no_overflow :
  forall (x y : ftype t)
    (HFINb : Binary.is_finite (BMULT x y)),
  Bmult_no_overflow (FT2R x) (FT2R y).
Proof.
  intros.
  pose proof Rle_or_lt (bpow Zaux.radix2 (femax t))
    (Rabs (rounded t (FT2R x * FT2R y))) as Hor;
    destruct Hor; auto.
  apply Rlt_bool_false in H; red.
  unfold rounded in H.
  pose proof (Binary.Bmult_correct (fprec t) (femax t)
                (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.mult_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE x y) as H0.
  rewrite {}H in H0.
  unfold BMULT, BINOP in HFINb.
  destruct (Binary.Bmult _ _ _ _ _ _ x y);
    simpl; try discriminate.
Qed.

(** [BMULT_accurate'] is the _finiteness-hypothesis_ form of
    [BMULT_accurate]. *)

Lemma BMULT_accurate' :
  forall (x y : ftype t)
    (FIN : Binary.is_finite (BMULT x y)),
  exists delta, exists epsilon,
    delta * epsilon = 0 /\
    Rabs delta <= @default_rel t /\
    Rabs epsilon <= @default_abs t /\
    (FT2R (BMULT x y) = (FT2R x * FT2R y) * (1 + delta) + epsilon)%Re.
Proof.
  intros.
  pose proof BMULT_accurate x y (is_finite_BMULT_no_overflow x y FIN); auto.
Qed.

(** [BMULT_finite_e] extracts finiteness of each factor from finiteness
    of the product. *)

Lemma BMULT_finite_e :
  forall (a b : ftype t)
    (Hfin : Binary.is_finite (BMULT a b)),
  Binary.is_finite a /\ Binary.is_finite b.
Proof.
  unfold BMULT, BINOP; intros.
  destruct a, b; inversion Hfin; clear Hfin; subst; auto.
Qed.

(** [BMULT_correct] gives the full correctness statement for multiplication:
    finiteness of the result implies finiteness of the operands and a
    rounding identity. *)

Lemma BMULT_correct (a b : ftype t) :
  Binary.is_finite (BMULT a b) ->
  (Binary.is_finite a /\ Binary.is_finite b) /\
  FT2R (BMULT a b) =
    Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
      (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
      (FT2R a * FT2R b).
Proof.
  intros * FIN.
  pose proof (is_finite_BMULT_no_overflow a b FIN).
  apply Rlt_bool_true in H.
  assert (Binary.is_finite a = true /\ Binary.is_finite b = true)
    by (unfold is_true in *; unfold BMULT, BINOP in FIN;
        destruct a, b;
          simpl in FIN; split; try discriminate; auto;
            match goal with
            | H : Binary.is_finite
                    (Binary.Bplus _ _ _ _ _ _
                       (Binary.B754_infinity _ _ ?s)
                       (Binary.B754_infinity _ _ ?s0)) = _ |-
              Binary.is_finite _ = _ =>
              destruct s; destruct s0; try discriminate; auto
            end).
  split; auto.
  destruct H0.
  pose proof (Binary.Bmult_correct (fprec t) (femax t)
                (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.mult_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE a b).
  rewrite {}H in H2.
  apply H2.
Qed.

(** ** Floating-Point Addition *)

(** [BPLUS_B2R_zero] is a special case: adding the zero constant
    to a finite value returns a result with the same
    real value. *)

Lemma BPLUS_B2R_zero (a : ftype t) :
  Binary.is_finite a ->
  FT2R (BPLUS a (Zconst t 0)) = FT2R a.
Proof.
  unfold BPLUS, BINOP, Zconst; intros;
  destruct a;
  unfold neg_zero; simpl; try discriminate; auto.
  destruct s; simpl; auto.
Qed.

(** [BPLUS_accurate] establishes the standard relative rounding error
    model for floating-point addition [BPLUS x y]. *)

Lemma BPLUS_accurate :
  forall (x : ftype t) (FINx : Binary.is_finite x)
         (y : ftype t) (FINy : Binary.is_finite y)
         (FIN : Bplus_no_overflow (FT2R x) (FT2R y)),
  exists delta,
    Rabs delta <= @default_rel t /\
    (FT2R (BPLUS x y) = (FT2R x + FT2R y) * (1 + delta))%Re.
Proof.
  intros.
  pose proof (Binary.Bplus_correct (fprec t) (femax t) (fprec_gt_0 t)
                (fprec_lt_femax t)
                (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE x y FINx FINy).
  cbv zeta in H.
  pose proof (
    Raux.Rlt_bool_spec
      (Rabs
         (Generic_fmt.round Zaux.radix2
            (SpecFloat.fexp (fprec t) (femax t))
            (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
            (Binary.B2R _ _ x + Binary.B2R _ _ y)))
      (Raux.bpow Zaux.radix2 (femax t))).
  destruct H0.
  - destruct H as [? _].
    unfold BPLUS, BINOP.
    fold (@FT2R t) in *.
    rewrite {}H.
    assert (A : Generic_fmt.generic_format Zaux.radix2
                  (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
                  (FT2R x))
      by apply Binary.generic_format_B2R.
    assert (B : Generic_fmt.generic_format Zaux.radix2
                  (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
                  (FT2R y))
      by apply Binary.generic_format_B2R.
    assert (H1 := Plus_error.FLT_plus_error_N_ex Zaux.radix2
                    (SpecFloat.emin (fprec t) (femax t))
                    (fprec t) (fun x0 : Z => negb (Z.even x0))
                    (FT2R x) (FT2R y) A B).
    unfold Relative.u_ro in H1. fold (@default_rel t) in H1.
    destruct H1 as (d & Hd & Hd').
    assert (H1 : Generic_fmt.round Zaux.radix2
                   (SpecFloat.fexp (fprec t) (femax t))
                   (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
                   (FT2R x + FT2R y) =
                 Generic_fmt.round Zaux.radix2
                   (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
                   (Generic_fmt.Znearest (fun x0 : Z => negb (Z.even x0)))
                   (FT2R x + FT2R y)) by auto.
    rewrite <- H1 in Hd'. clear H1.
    rewrite {}Hd'.
    exists d; split; auto.
    eapply Rle_trans; [apply Hd |].
    apply Rdiv_le_left.
    apply Fourier_util.Rlt_zero_pos_plus1.
    apply default_rel_gt_0.
    eapply Rle_trans with (@default_rel t * 1); try nra.
  - red in FIN.
    fold (@FT2R t) in *.
    unfold fmax in *.
    lra.
Qed.

(** [is_finite_sum_no_overflow] shows that finiteness of the result
    implies the no-overflow condition on the exact sum %$x + y$%#\(x + y\)#. *)

Lemma is_finite_sum_no_overflow :
  forall (x y : ftype t)
    (HFINb : Binary.is_finite (BPLUS x y)),
  Bplus_no_overflow (FT2R x) (FT2R y).
Proof.
  intros.
  pose proof Rle_or_lt (bpow Zaux.radix2 (femax t))
    (Rabs (rounded t (FT2R x + FT2R y))) as Hor;
    destruct Hor; auto.
  apply Rlt_bool_false in H.
  assert (HFIN : Binary.is_finite x = true /\ Binary.is_finite y = true).
  { unfold BPLUS, BINOP in HFINb.
    destruct x, y;
      simpl in *; split; try discriminate; auto;
      destruct s; destruct s0; simpl in *; try discriminate; auto. }
  unfold rounded in H.
  destruct HFIN as (A & B).
  pose proof (Binary.Bplus_correct (fprec t) (femax t)
                (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE x y A B) as H0.
  rewrite H in H0;
  destruct H0 as (C & _).
  unfold BPLUS, BINOP in HFINb.
  destruct (Binary.Bplus (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t)
              (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t))
              BinarySingleNaN.mode_NE x y);
    simpl; try discriminate.
Qed.

(** [no_overflow_sum_is_finite] is the converse direction: if both
    summands are finite and the exact sum does not overflow, then
    the result is finite. *)

Lemma no_overflow_sum_is_finite :
  forall (x y : ftype t)
    (H1  : Binary.is_finite x)
    (H2  : Binary.is_finite y)
    (Hov : Bplus_no_overflow (FT2R x) (FT2R y)),
  Binary.is_finite (BPLUS x y).
Proof.
  unfold Bplus_no_overflow, BPLUS, BINOP; intros.
  pose proof (Binary.Bplus_correct (fprec t) (femax t)
                (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE x y H1 H2) as H0.
  remember (Rlt_bool _ _) as HB; destruct HB.
  - destruct H0 as (_ & HP & _); auto.
  - exfalso.
    fold (@FT2R t) in *.
    unfold Rlt_bool in HeqHB.
    remember (Rcompare _ _) as HR; destruct HR; try discriminate.
    + symmetry in HeqHR.
      apply Rcompare_Eq_inv in HeqHR.
      unfold fmax in *.
      nra.
    + symmetry in HeqHR.
      apply Rcompare_Gt_inv in HeqHR.
      unfold fmax in *.
      nra.
Qed.

(** [BPLUS_accurate'] is the _finiteness-hypothesis_ form of
    [BPLUS_accurate]. *)

Lemma BPLUS_accurate' :
  forall (x y : ftype t)
    (FIN : Binary.is_finite (BPLUS x y)),
  exists delta,
    Rabs delta <= @default_rel t /\
    (FT2R (BPLUS x y) = (FT2R x + FT2R y) * (1 + delta))%Re.
Proof.
  unfold BPLUS, BINOP.
  intros.
  eapply BPLUS_accurate.
  1, 2: destruct x, y; simpl; try discriminate; auto;
        destruct s; destruct s0; simpl; try discriminate; auto.
  apply is_finite_sum_no_overflow; auto.
Qed.

(** [BPLUS_finite_e] extracts finiteness of each summand from finiteness
    of the sum. *)

Lemma BPLUS_finite_e :
  forall (a b : ftype t)
    (Hfin : Binary.is_finite (BPLUS a b)),
  Binary.is_finite a /\ Binary.is_finite b.
Proof.
  unfold BPLUS, BINOP; intros.
  destruct a, b; inversion Hfin; clear Hfin; subst; simpl; auto.
  destruct s, s0; discriminate; auto.
Qed.

(** [BPLUS_correct] gives the full correctness statement for 
    floating-point addition:
    finiteness of the result implies finiteness of each summand and
    relates the floating-point result to the rounded real result. *)

Lemma BPLUS_correct (a b : ftype t) :
  Binary.is_finite (BPLUS a b) ->
  (Binary.is_finite a /\ Binary.is_finite b) /\
  FT2R (BPLUS a b) =
    Generic_fmt.round Zaux.radix2 (SpecFloat.fexp (fprec t) (femax t))
      (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
      (FT2R a + FT2R b).
Proof.
  intros * FIN.
  pose proof (is_finite_sum_no_overflow a b FIN).
  apply Rlt_bool_true in H.
  assert (Binary.is_finite a /\ Binary.is_finite b)
    by (unfold is_true in *; unfold BPLUS, BINOP in FIN;
        destruct a, b;
          simpl in FIN; split; try discriminate; auto;
            match goal with
            | H : Binary.is_finite
                    (Binary.Bplus _ _ _ _ _ _
                       (Binary.B754_infinity _ _ ?s)
                       (Binary.B754_infinity _ _ ?s0)) = _ |-
              Binary.is_finite _ = _ =>
              destruct s; destruct s0; try discriminate; auto
            end).
  split; auto.
  destruct H0.
  pose proof (Binary.Bplus_correct (fprec t) (femax t)
                (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE a b H0 H1) as H3.
  rewrite {}H in H3.
  apply H3.
Qed.

(** ** Floating-Point Subtraction *)

(** [BMINUS_accurate] establishes the pure relative rounding error model
    for floating-point subtraction. *)

Lemma BMINUS_accurate :
  forall (x : ftype t) (FINx : Binary.is_finite x)
         (y : ftype t) (FINy : Binary.is_finite y)
         (FIN : Bminus_no_overflow (FT2R x) (FT2R y)),
  exists delta,
    Rabs delta <= @default_rel t /\
    (FT2R (BMINUS x y) = (FT2R x - FT2R y) * (1 + delta))%Re.
Proof.
  intros.
  pose proof (Binary.Bminus_correct (fprec t) (femax t) (fprec_gt_0 t)
                (fprec_lt_femax t)
                (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE x y FINx FINy).
  cbv zeta in H.
  pose proof (
    Raux.Rlt_bool_spec
      (Rabs
         (Generic_fmt.round Zaux.radix2
            (SpecFloat.fexp (fprec t) (femax t))
            (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
            (Binary.B2R _ _ x - Binary.B2R _ _ y)))
      (Raux.bpow Zaux.radix2 (femax t))).
  fold (@FT2R t) in *.
  destruct H0.
  - destruct H as [? _].
    unfold BMINUS, BINOP.
    rewrite H.
    assert (A : Generic_fmt.generic_format Zaux.radix2
                  (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
                  (FT2R x))
      by apply Binary.generic_format_B2R.
    assert (B : Generic_fmt.generic_format Zaux.radix2
                  (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
                  (- FT2R y)).
    { apply Generic_fmt.generic_format_opp.
      apply Binary.generic_format_B2R. }
    pose proof Plus_error.FLT_plus_error_N_ex Zaux.radix2
                 (SpecFloat.emin (fprec t) (femax t))
                 (fprec t) (fun x0 : Z => negb (Z.even x0))
                 (FT2R x) (- FT2R y) A B.
    unfold Relative.u_ro in H1. fold (@default_rel t) in H1.
    destruct H1 as (d & Hd & Hd').
    assert (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
              (FT2R x - FT2R y) =
            Generic_fmt.round Zaux.radix2
              (FLT.FLT_exp (SpecFloat.emin (fprec t) (femax t)) (fprec t))
              (Generic_fmt.Znearest (fun x0 : Z => negb (Z.even x0)))
              (FT2R x - FT2R y)) by auto.
    replace (_ + - _) with (FT2R x - FT2R y) in Hd' by nra.
    rewrite <- H1 in Hd'. clear H1.
    rewrite {}Hd'.
    exists d; split; auto.
    eapply Rle_trans; [apply Hd |].
    apply Rdiv_le_left.
    apply Fourier_util.Rlt_zero_pos_plus1.
    apply default_rel_gt_0.
    eapply Rle_trans with (@default_rel t * 1); try nra.
  - red in FIN.
    unfold fmax in *.
    lra.
Qed.

(** [is_finite_minus_no_overflow] shows that finiteness of the floating-point 
    result implies that the exact difference does not overflow. *)

Lemma is_finite_minus_no_overflow :
  forall (x y : ftype t)
    (HFINb : Binary.is_finite (BMINUS x y)),
  Bminus_no_overflow (FT2R x) (FT2R y).
Proof.
  intros.
  pose proof Rle_or_lt (bpow Zaux.radix2 (femax t))
    (Rabs (rounded t (FT2R x - FT2R y))) as Hor;
    destruct Hor; auto.
  apply Rlt_bool_false in H.
  assert (HFIN : Binary.is_finite x = true /\ Binary.is_finite y = true).
  { unfold BMINUS, BINOP in HFINb.
    destruct x, y;
      simpl in *; split; try discriminate; auto;
      destruct s; destruct s0; simpl in *; try discriminate; auto. }
  destruct HFIN as (A & B).
  unfold rounded in H.
  pose proof (Binary.Bminus_correct (fprec t) (femax t)
                (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE x y A B) as H0.
  rewrite H in H0;
  destruct H0 as (C & _).
  unfold BMINUS, BINOP in HFINb.
  destruct (Binary.Bminus (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t)
              (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t))
              BinarySingleNaN.mode_NE x y);
    simpl; try discriminate.
Qed.

(** [no_overflow_minus_is_finite] is the converse direction for
    subtraction: if both operands are finite and the exact difference
    does not overflow, then the result is finite. *)

Lemma no_overflow_minus_is_finite :
  forall (x y : ftype t)
    (H1  : Binary.is_finite x)
    (H2  : Binary.is_finite y)
    (Hov : Bminus_no_overflow (FT2R x) (FT2R y)),
  Binary.is_finite (BMINUS x y).
Proof.
  unfold Bminus_no_overflow, BMINUS, BINOP; intros.
  pose proof (Binary.Bminus_correct (fprec t) (femax t)
                (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.plus_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE x y H1 H2) as H0.
  remember (Rlt_bool _ _) as HB; destruct HB.
  - destruct H0 as (_ & HP & _); auto.
  - exfalso.
    unfold Rlt_bool in HeqHB.
    fold (@FT2R t) in *.
    remember (Rcompare _ _) as HR; destruct HR; try discriminate.
    + symmetry in HeqHR.
      apply Rcompare_Eq_inv in HeqHR.
      unfold fmax in *.
      nra.
    + symmetry in HeqHR.
      apply Rcompare_Gt_inv in HeqHR.
      unfold fmax in *.
      nra.
Qed.

(** [BMINUS_accurate'] is the _finiteness-hypothesis_ form of
    [BMINUS_accurate]. *)

Lemma BMINUS_accurate' :
  forall (x y : ftype t)
    (FIN : Binary.is_finite (BMINUS x y)),
  exists delta,
    Rabs delta <= @default_rel t /\
    (FT2R (BMINUS x y) = (FT2R x - FT2R y) * (1 + delta))%Re.
Proof.
  intros.
  eapply BMINUS_accurate.
  1, 2: unfold BMINUS, BINOP in FIN;
        destruct x, y; simpl; try discriminate; auto;
        destruct s; destruct s0; simpl; try discriminate; auto.
  apply is_finite_minus_no_overflow; auto.
Qed.

(** [BMINUS_finite_sub] extracts finiteness of each operand from
    finiteness of the difference. *)

Lemma BMINUS_finite_sub :
  forall (a b : ftype t)
    (Hfin : Binary.is_finite (BMINUS a b)),
  Binary.is_finite a /\ Binary.is_finite b.
Proof.
  unfold BMINUS, BINOP; intros.
  destruct a, b; inversion Hfin; clear Hfin; subst; simpl; auto.
  destruct s, s0; discriminate; auto.
Qed.

End GenFloat.