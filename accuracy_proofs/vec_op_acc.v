(** * Mixed Error Bounds for Floating-Point Matrix-Vector Operations

    This file establishes mixed error bounds for scalar-matrix multiplication,
    entry-wise matrix addition, and general matrix-vector multiply-accumulate
    (GEMV), computed in floating-point arithmetic. Each result decomposes
    the floating-point output into its exact real counterpart plus structured
    entry-wise error terms.

    ** Main Results

    - [Fscalemx_mixed_error]: Shows that the floating-point scalar-matrix
      product can be expressed as an exact scaled sum where each matrix entry
      carries a relative error bounded by the unit roundoff and an absolute
      error bounded by the underflow threshold.

    - [Faddmx_mixed_error]: Shows that the floating-point entry-wise matrix
      sum can be expressed as an exact sum of two componentwise-perturbed
      matrices, where each perturbation is relative and bounded by the unit
      roundoff.

    - [Smat_sumF_mixed_error]: Shows that the floating-point scaled matrix
      sum can be expressed as a sum of two perturbed scaled matrices, by
      composing [Fscalemx_mixed_error] and [Faddmx_mixed_error].

    - [Smat_vec_mul_mixed_error]: Shows that the floating-point scaled
      matrix-vector product can be expressed as an exact scaled result with
      a forward error on the inner matrix-vector multiply and a mixed error
      from the outer scalar multiplication.

    - [gemv_error]: Shows that the floating-point GEMV operation
      %$s_1 A x + s_2 y$%#\(s_1 A x + s_2 y\)# can be expressed as an exact
      result plus structured error matrices, combining the bounds from all
      preceding lemmas.

    ** Dependencies

    This file relies on:
    - [preamble], [common]: basic setup and shared definitions
    - [dotprod_model], [sum_model]: relational models of dot product and summation
    - [dot_acc], [float_acc_lems]: accuracy lemmas
    - [mv_mathcomp]: floating-point matrix/vector operations
    - [gemv_acc]: forward error bound for floating-point matrix-vector multiplication
*)

From LAProof.accuracy_proofs Require Import preamble common
     dotprod_model sum_model dot_acc float_acc_lems mv_mathcomp gemv_acc.

Section WithNans.

Context {NAN : FPCore.Nans} {t : FPStdLib.type}.

Notation g  := (@common.g t).
Notation g1 := (@common.g1 t).

(** ** Scalar-Matrix Multiplication: Mixed Error Bound *)

(** [Fscalemx_mixed_error] shows that the floating-point scalar-matrix product
    equals an exact scaled sum of perturbed matrix entries plus an absolute
    residual, with each entry carrying a relative perturbation bounded by
    the unit roundoff and an absolute error bounded by the underflow threshold. *)

Lemma Fscalemx_mixed_error :
  forall [m n] (a : ftype t) (v : 'M[ftype t]_(m, n))
    (Hfin : F.finitemx (F.scalemx a v)),
  let vr := map_mx FT2R v in
  exists (e eta : 'M[R]_(m, n)),
    map_mx FT2R (F.scalemx a v) = (scalemx (FT2R a) (vr + e) + eta)%Ri
    /\ (forall i j, exists d,
          e i j = vr i j * d /\ Rabs d <= @default_rel t)
    /\ (forall i j, Rabs (eta i j) <= @default_abs t).
Proof.
  intros m n a v Hfin vr.
  unfold F.scalemx.
  (* Define a pointwise property F capturing the per-entry error decomposition. *)
  pose F (i : 'I_m) (j : 'I_n) (x : R * R) :=
    let '(e, eta) := x in
    FT2R (@BMULT NAN _ a (v i j)) = FT2R a * (FT2R (v i j) + e) + eta
    /\ (exists d : R, e = vr i j * d /\ Rabs d <= @default_rel t)
    /\ Rabs eta <= @default_abs t.
  (* Establish the per-entry error decomposition using BMULT_accurate. *)
  assert (Hentry : forall i j, exists e eta, F i j (e, eta)). {
    intros i j.
    subst F vr; simpl.
    rewrite !mxE.
    specialize (Hfin i j); rewrite mxE in Hfin.
    set (x := fun_of_matrix v i j) in Hfin |- *; clearbody x.
    destruct (BMULT_accurate a x) as (del & eps & HD & HE & HF & Heq).
    { by apply is_finite_BMULT_no_overflow. }
    rewrite {}Heq.
    (* Fold the relative error as d := FT2R x * del. *)
    remember (FT2R x * del)%Re as d.
    exists d, eps.
    repeat split.
    - (* Algebraic rearrangement: a*(x*(1+del)) + eps = a*(x+d) + eps *)
      change (FT2R a * FT2R x * (1 + del) + eps
              = FT2R a * (FT2R x + d) + eps)%Re.
      nra.
    - exists del; split; [auto | apply /RleP; auto].
    - apply /RleP; auto.
  }
  (* Lift the pointwise existentials to matrix existentials. *)
  destruct (exists_mx F) as [x H0].
  { intros i j.
    destruct (Hentry i j) as [e [eta H']].
    exists (e, eta); auto. }
  exists (map_mx fst x), (map_mx snd x).
  subst F vr.
  repeat split.
  - (* Prove the matrix equality entry-wise. *)
    apply matrixP; intros i j.
    specialize (H0 i j); simpl in H0.
    rewrite !mxE in H0 |- *.
    destruct (fun_of_matrix x i j) as [e eta]; simpl.
    exact (proj1 H0).
  - (* Prove the relative error bound on e. *)
    intros i j.
    specialize (H0 i j); simpl in H0.
    rewrite !mxE in H0 |- *.
    destruct (fun_of_matrix x i j); simpl.
    exact (proj1 (proj2 H0)).
  - (* Prove the absolute error bound on eta. *)
    intros i j.
    specialize (H0 i j); simpl in H0.
    rewrite !mxE in H0 |- *.
    destruct (fun_of_matrix x i j); simpl.
    exact (proj2 (proj2 H0)).
Qed.

(** ** Entry-wise Matrix Addition: Mixed Error Bound *)

(** [Faddmx_mixed_error] shows that the floating-point entry-wise matrix sum
    can be expressed as an exact sum of two componentwise-perturbed matrices,
    where each perturbation is a relative error bounded by the unit roundoff. *)

Lemma Faddmx_mixed_error :
  forall [m n] (A B : 'M[ftype t]_(m, n))
    (Hfin : F.finitemx (F.addmx A B)),
  let Ar := map_mx FT2R A in
  let Br := map_mx FT2R B in
  exists (e1 e2 : 'M[R]_(m, n)),
    map_mx FT2R (F.addmx A B) = ((Ar + e1) + (Br + e2))%Ri
    /\ (forall i j, exists d, e1 i j = Ar i j * d /\ Rabs d <= @default_rel t)
    /\ (forall i j, exists d, e2 i j = Br i j * d /\ Rabs d <= @default_rel t).
Proof.
  intros m n A B Hfin Ar Br.
  (* Define a pointwise property capturing the per-entry error decomposition. *)
  pose F (i : 'I_m) (j : 'I_n) (e12 : R * R) :=
    let '(e1, e2) := e12 in
    FT2R (@BPLUS NAN t (A i j) (B i j)) = ((Ar i j + e1) + (Br i j + e2))
    /\ (exists d, e1 = Ar i j * d /\ Rabs d <= @default_rel t)
    /\ (exists d, e2 = Br i j * d /\ Rabs d <= @default_rel t).
  (* Establish the per-entry error decomposition using BPLUS_accurate'. *)
  assert (Hentry : forall i j, exists e1 e2, F i j (e1, e2)). {
    intros i j.
    subst F Ar Br; simpl.
    specialize (Hfin i j); rewrite !mxE in Hfin |- *.
    set (a := A i j) in Hfin |- *; clearbody a.
    set (b := B i j) in Hfin |- *; clearbody b.
    destruct (BPLUS_finite_e _ _ Hfin) as [Ha Hb].
    destruct (BPLUS_accurate' _ _ Hfin) as (del & HD & Heq).
    rewrite {}Heq.
    exists (FT2R a * del), (FT2R b * del).
    repeat split.
    - (* Both summands are perturbed by the same factor del. *)
      change ((FT2R a + FT2R b) * (1 + del)
              = FT2R a + FT2R a * del + (FT2R b + FT2R b * del))%Re.
      lra.
    - exists del; split; [auto | apply /RleP; auto].
    - exists del; split; [auto | apply /RleP; auto].
  }
  (* Lift pointwise existentials to matrix existentials. *)
  destruct (exists_mx F) as [x H0].
  { intros i j.
    destruct (Hentry i j) as [e1 [e2 H']].
    exists (e1, e2); auto. }
  exists (map_mx fst x), (map_mx snd x).
  subst F.
  repeat split.
  - (* Matrix equality entry-wise. *)
    apply matrixP; intros i j.
    specialize (H0 i j); simpl in H0.
    rewrite !mxE in H0 |- *.
    destruct (fun_of_matrix x i j) as [e1 e2]; simpl.
    exact (proj1 H0).
  - (* Relative error bound on e1. *)
    intros i j.
    specialize (H0 i j); simpl in H0.
    rewrite !mxE in H0 |- *.
    destruct (fun_of_matrix x i j); simpl.
    exact (proj1 (proj2 H0)).
  - (* Relative error bound on e2. *)
    intros i j.
    specialize (H0 i j); simpl in H0.
    rewrite !mxE in H0 |- *.
    destruct (fun_of_matrix x i j); simpl.
    exact (proj2 (proj2 H0)).
Qed.

(** ** Scaled Matrix Sum: Mixed Error Bound *)

(** [Smat_sumF_mixed_error] shows that the floating-point scaled matrix sum
    can be expressed as a sum of two perturbed scaled matrices, by composing
    [Fscalemx_mixed_error] and [Faddmx_mixed_error]. Each scaling step
    contributes a relative and an absolute error; the outer addition
    contributes an additional relative error per summand. *)

Lemma Smat_sumF_mixed_error :
  forall [m n] (u v : 'M[ftype t]_(m, n)) (a b : ftype t)
    (Hfin : F.finitemx (F.addmx (F.scalemx a u) (F.scalemx b v))),
  let vr := map_mx FT2R v in
  let ur := map_mx FT2R u in
  exists (e1 e2 e3 e4 e5 e6 : 'M[R]_(m, n)),
    map_mx FT2R (F.addmx (F.scalemx a u) (F.scalemx b v)) =
      ((scalemx (FT2R a) (ur + e1) + e2 + e3) +
       (scalemx (FT2R b) (vr + e4) + e5 + e6))%Ri
    /\ (forall i j, exists d,
          e1 i j = ur i j * d /\ Rabs d <= @default_rel t)
    /\ (forall i j, exists d,
          e4 i j = vr i j * d /\ Rabs d <= @default_rel t)
    /\ (forall i j, exists d,
          e3 i j = (scalemx (FT2R a) (ur + e1) + e2) i j * d
          /\ Rabs d <= @default_rel t)%Ri
    /\ (forall i j, exists d,
          e6 i j = (scalemx (FT2R b) (vr + e4) + e5) i j * d
          /\ Rabs d <= @default_rel t)%Ri
    /\ (forall i j, Rabs (e5 i j) <= @default_abs t)
    /\ (forall i j, Rabs (e2 i j) <= @default_abs t).
Proof.
  intros m n u v a b Hfin vr ur.
  simpl.
  (* Decompose finiteness of the sum into finiteness of each scaled term. *)
  destruct (F.finitemx_addmx_e _ _ Hfin) as [HfinA HfinB].
  (* Apply the addition mixed error bound to the outer sum. *)
  destruct (Faddmx_mixed_error _ _ Hfin) as (Du & Dv & Heq & HDu & HDv).
  rewrite {}Heq.
  (* Apply the scalar multiplication mixed error bound to each term. *)
  destruct (Fscalemx_mixed_error a u HfinA) as (ae & aeta & Heqa & Hea & Haeta).
  destruct (Fscalemx_mixed_error b v HfinB) as (be & beta & Heqb & Heb & Hbeta).
  (* Substitute the scale decompositions into the addition error terms. *)
  move : HDu HDv; rewrite {}Heqa {}Heqb => HDu HDv.
  exists ae, aeta, Du, be, beta, Dv.
  repeat split => //.
Qed.

(** ** Scaled Matrix-Vector Product: Mixed Error Bound *)

(** [Smat_vec_mul_mixed_error] shows that the floating-point scaled
    matrix-vector product can be expressed as an exact scaled result with
    a forward error on the inner matrix-vector multiply (bounded in terms of
    %$g(n)$%#\(g(n)\)#) and a mixed error from the outer scalar multiplication. *)

Lemma Smat_vec_mul_mixed_error :
  forall [m n] (b : ftype t) (A : 'M[ftype t]_(m, n)) (B : 'M[ftype t]_(n, 1))
    (Hfin : F.finitemx (F.scalemx b (F.mulmx A B))),
  exists (E : 'M[R]_(m, n)) (e eta1 eta2 : 'M[R]_(m, 1)),
    map_mx FT2R (F.scalemx b (F.mulmx A B)) =
      (scalemx (FT2R b)
         ((map_mx FT2R A + E) *m map_mx FT2R B + eta1 + e) + eta2)%Ri
    /\ (forall i j, Rabs (E i j) <= g n * Rabs (map_mx FT2R A i j))
    /\ (forall i j, Rabs (eta2 i j) <= @default_abs t)
    /\ (forall i j, exists d,
          e i j = FT2R (F.mulmx A B i j) * d /\ Rabs d <= @default_rel t)
    /\ (forall i j, Rabs (eta1 i j) <= g1 n n).
Proof.
  intros m n b A B Hfin.
  (* Apply the scalar multiply mixed error bound to b * (A*x). *)
  destruct (Fscalemx_mixed_error _ _ Hfin) as (e & eta & Heq & Hea & Hetaa).
  rewrite {}Heq in Hea |- *.
  (* Apply the forward error bound for floating-point matrix-vector multiply. *)
  destruct (mat_vec_mul_mixed_error A B) as (E & eta1 & Heq1 & He1 & Heta1).
  { apply (F.finitemx_scalemx_e _ _ Hfin). }
  rewrite {}Heq1.
  exists E, e, eta1, eta.
  repeat split => //.
  (* Rewrite the relative error on e in terms of the mulmx entry. *)
  intros i j.
  destruct (Hea i j) as [d H2].
  exists d.
  rewrite !mxE; rewrite mxE in H2.
  unfold F.mulmx in H2.
  rewrite mxE in H2.
  exact H2.
Qed.

(** ** General Matrix-Vector Multiply-Accumulate (GEMV): Mixed Error Bound *)

(** [gemv_error] is the central result of this file. It shows that the
    floating-point GEMV operation %$s_1 A x + s_2 y$%#\(s_1 A x + s_2 y\)#
    can be expressed as an exact result plus structured error matrices,
    combining the bounds from [Smat_sumF_mixed_error] and
    [mat_vec_mul_mixed_error]. *)

Lemma gemv_error :
  forall [m n] (A : 'M[ftype t]_(m, n)) (x : 'cV[ftype t]_n)
               (y : 'cV[ftype t]_m) (s1 s2 : ftype t)
    (Hfin : F.finitemx
              (F.addmx (F.scalemx s1 (F.mulmx A x)) (F.scalemx s2 y))),
  exists e1 e2 e3 e4 e5 e6 e7 e8,
    map_mx FT2R (F.addmx (F.scalemx s1 (F.mulmx A x)) (F.scalemx s2 y)) =
      ((scalemx (FT2R s1)
          ((((map_mx FT2R A + e1) *m map_mx FT2R x) + e2) + e3) + e4) + e5) +
      ((scalemx (FT2R s2) (map_mx FT2R y + e6) + e7) + e8)
    /\ (forall i j, Rabs (e1 i j) <= g n * Rabs (map_mx FT2R A i j))
    /\ (forall i j, Rabs (e2 i j) <= g1 n n)
    /\ (forall i j, exists d,
          e3 i j =
            (((map_mx FT2R A + e1) *m map_mx FT2R x) + e2)%Ri i j * d
          /\ Rabs d <= @default_rel t)
    /\ (forall i j, exists d,
          e6 i j = map_mx FT2R y i j * d /\ Rabs d <= @default_rel t)
    /\ (forall i j, exists d,
          e5 i j =
            (scalemx (FT2R s1)
              ((((map_mx FT2R A + e1) *m map_mx FT2R x) + e2) + e3) + e4) i j * d
          /\ Rabs d <= @default_rel t)
    /\ (forall i j, exists d,
          e8 i j =
            (scalemx (FT2R s2) (map_mx FT2R y + e6) + e7) i j * d
          /\ Rabs d <= @default_rel t)
    /\ (forall i j, Rabs (e7 i j) <= @default_abs t)
    /\ (forall i j, Rabs (e4 i j) <= @default_abs t).
Proof.
  intros m n A x y s1 s2 Hfin.
  (* Decompose s1*(A*x) + s2*y into scaled-sum error components.
     This yields error matrices e3..e8 covering the two scalings and
     the outer vector addition. *)
  destruct (Smat_sumF_mixed_error (F.mulmx A x) y s1 s2 Hfin)
    as (e3 & e4 & e5 & e6 & e7 & e8
        & Heq1 & He3 & He6 & He5 & He8 & He7 & He4).
  rewrite {}Heq1.
  (* Extract finiteness of A*x from the finiteness of s1*(A*x) + s2*y,
     which is needed to apply the matrix-vector multiply error bound. *)
  have HfinAx : F.finitemx (F.mulmx A x).
  { apply F.finitemx_addmx_e in Hfin.
    destruct Hfin as [HfinL _].
    exact: (F.finitemx_scalemx_e _ _ HfinL). }
  (* Apply the mixed error bound for floating-point matrix-vector multiply.
     This yields error matrices e1 (componentwise relative on A) and
     e2 (absolute, from accumulated dot product rounding). *)
  destruct (mat_vec_mul_mixed_error A x HfinAx)
    as (e1 & e2 & Heq2 & He1 & He2).
  (* Rewrite the mat-vec result in He3, He5, and the goal simultaneously.
     He5 references map_mx FT2R (F.mulmx A x) inside the scalemx term,
     so it must be rewritten alongside He3 and the main goal. *)
  rewrite {}Heq2 in He3 He5 |- *.
  exists e1, e2, e3, e4, e5, e6, e7, e8.
  repeat split => /= //.
Qed.
  
End WithNans.