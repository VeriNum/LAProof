(** * Matrix Multiplication Forward and Mixed Error Analysis

    This module establishes rigorous rounding error bounds for floating-point
    matrix operations, including matrix multiplication, scalar-matrix
    multiplication, matrix addition, and the general matrix multiply-accumulate
    (GEMM) operation.

    ** Error Factors

    Throughout, the accumulated relative error factor is
    %$g(n) = (1 + \mathbf{u})^n - 1$%#\(g(n) = (1 + \mathbf{u})^n - 1\)# and
    the mixed absolute error factor is
    %$g_1(n_1, n_2) = n_1 \cdot \eta \cdot (1 + g(n_2))$%#\(g_1(n_1, n_2) = n_1 \cdot \eta \cdot (1 + g(n_2))\)#,
    where %$\mathbf{u}$%#\(\mathbf{u}\)# is the unit roundoff and
    %$\eta$%#\(\eta\)# is the underflow threshold for the given type.
    Both are defined in [common].

    ** Error Bound Taxonomy

    The theorems in this file fall into three categories:

    _Pure forward error bounds_ characterize the absolute difference between
    the computed result and the exact result in terms of the input data.
    No reference is made to a nearby exact problem.

    _Mixed forward-backward error bounds_ express the computed result as the
    exact result of a slightly perturbed input (backward component), where the
    perturbation is bounded in terms of the original input data (forward
    component). The perturbation appears as an additive error matrix
    satisfying entry-wise bounds.

    _Pure backward error bounds_ express the computed result as the exact
    result of a perturbed input problem, with no forward error term.

    ** Key Results

    - [MMC_error] _(mixed)_: Shows that the floating-point matrix product
      %$\mathtt{fl}(AB)$%#\(\mathtt{fl}(AB)\)# equals the exact product of slightly perturbed
      columns plus a small entry-wise absolute error. The column perturbation
      is bounded column-wise by %$g(n)$%#\(g(n)\)# relative to the input, and the
      absolute residual by %$g_1(n,n)$%#\(g_1(n,n)\)# per entry.

    - [scaleM_error] _(mixed)_: Shows that floating-point scalar-matrix
      multiplication equals exact scaling of a slightly perturbed matrix plus
      a small entry-wise absolute error. The relative perturbation is bounded
      by %$\mathbf{u}$%#\(\mathbf{u}\)# and the absolute residual by %$\eta$%#\(\eta\)#.

    - [sMMC_error] _(mixed)_: Composes [MMC_error] and [scaleM_error] to give
      a structured decomposition of %$\mathtt{fl}(x \cdot (AB))$%#\(\mathtt{fl}(x \cdot (AB))\)#
      with backward perturbations from both the matrix product and the scaling
      step, together with forward absolute errors from each.

    - [mat_sum_error] _(pure backward)_: Shows that floating-point matrix
      addition equals the exact sum of two slightly perturbed matrices, with
      each entry perturbed by a relative factor bounded by %$\mathbf{u}$%#\(\mathbf{u}\)#.
      No forward error term appears.

    - [mat_axpby_error] _(mixed)_: Bounds %$\mathtt{fl}(xA + yB)$%#\(\mathtt{fl}(xA + yB)\)# by
      combining mixed errors from each scaling step with a backward error from
      the floating-point addition, yielding relative perturbations of the
      inputs and small absolute forward errors.

    - [GEMM_error] _(mixed)_: Master theorem for
      %$\mathtt{fl}(s_1(AB) + s_2 Y)$%#\(\mathtt{fl}(s_1(AB) + s_2 Y)\)#. Decomposes the
      full GEMM result into backward perturbation components and forward
      absolute errors from matrix multiplication, scalar scaling, and
      matrix addition.
*)

From LAProof.accuracy_proofs Require Import
  preamble common dotprod_model sum_model dot_acc
  float_acc_lems mv_mathcomp gemv_acc vec_op_acc.

Section MMERROR.

(** We work in an abstract floating-point context [NAN] (specifying NaN
    behavior) and over an abstract floating-point type << t >>. *)
    
Context {NAN : FPCore.Nans} {t : FPStdLib.type}.

Notation g  := (@common.g  t).
Notation g1 := (@common.g1 t).

(** ** Matrix Multiplication Error

    [MMC_error] establishes that the floating-point matrix product equals the
    exact product plus a column-wise backward perturbation and a small
    entry-wise absolute offset. The relative column perturbation is bounded
    by %$g(n)$%#\(g(n)\)# and the absolute residual by %$g_1(n,n)$%#\(g_1(n,n)\)# per entry,
    where %$n$%#\(n\)# is the inner dimension. *)
    
Theorem MMC_error :
  forall m n p
    (A : 'M[ftype t]_(m, n))
    (B : 'M[ftype t]_(n, p))
    (Hfin : F.finitemx (F.mulmx A B)),
  exists (E eta : 'M[R]_(m, p)),
       map_mx FT2R (F.mulmx A B)
     = (map_mx FT2R A *m map_mx FT2R B + E + eta)%Ri
  /\ (forall k : 'I_p,
        exists E0 : 'M[R]_(m, n),
             col k E = E0 *m col k (map_mx FT2R B)
          /\ (forall i j,
                Rabs (E0 i j) <= g n * Rabs (map_mx FT2R A i j)))
  /\ (forall i j, Rabs (eta i j) <= g1 n n).
Proof.
  move => m n p.
  elim: p.
  - (** Base case: p = 0 columns; all column index types are empty. *)
    move => A B Hfin.
    exists (const_mx 0), (const_mx 0).
    repeat split.
    + apply /matrixP => i j; destruct j; lia.
    + move => k; destruct k; lia.
    + move => i j; destruct j; lia.
  - (** Inductive step: split B into its leftmost column-block and the
        remaining columns, apply the induction hypothesis to the right block,
        and apply [mat_vec_mul_mixed_error] to the left block. *)
    move => p IH A B Hfin.
    change (p.+1) with (1 + p)%nat in *.
    rewrite -(hsubmxK B) F.mulmx_row map_row_mx.

    (** Apply the induction hypothesis to the right submatrix of B. *)
    destruct (IH A (rsubmx B)) as [E [eta [Heq [HE Heta]]]]. {
      move => i j.
      move : (Hfin i (rshift 1 j)).
      rewrite /F.mulmx !mxE col_rsubmx //.
    }
    clear IH.
    rewrite {}Heq.

    (** Apply the matrix-vector mixed error lemma to the left submatrix. *)
    destruct (mat_vec_mul_mixed_error A (lsubmx B))
      as [E1 [eta1 [Heq1 [HE1 Heta1]]]]. {
      move => i j.
      move : (Hfin i (lshift p j)).
      rewrite /F.mulmx !mxE col_lsubmx //.
    }
    rewrite {}Heq1.

    exists (row_mx (E1 *m map_mx FT2R (lsubmx B)) E),
           (row_mx eta1 eta).
    repeat split.
    + (** Reassemble the block-column equation. *)
      rewrite map_lsubmx map_rsubmx hsubmxK
              -add_row_mx mulmxDl -add_row_mx.
      f_equal; f_equal.
      rewrite -mul_mx_row hsubmxK //.
    + (** Column-wise backward error bound for E. *)
      move => k.
      case_splitP k.
      * exists E1; split => //.
        rewrite colKl map_row_mx colKl !col_id //.
      * destruct (HE k) as (E0 & Heq2 & HE0).
        exists E0; split => //.
        rewrite colKr map_row_mx colKr //.
    + (** Entry-wise forward absolute error bound for eta. *)
      move => i j.
      case_splitP j.
      * rewrite row_mxEl //.
      * rewrite row_mxEr //.
Qed.

(** ** Scalar-Matrix Multiplication Error

    [scaleM_error] establishes that floating-point scalar-matrix
    multiplication %$\mathtt{fl}(x \cdot A)$%#\(\mathtt{fl}(x \cdot A)\)# equals exact scaling of
    a slightly perturbed matrix plus a small entry-wise absolute offset.
    The relative perturbation is bounded entry-wise by the unit roundoff
    %$\mathbf{u}$%#\(\mathbf{u}\)# and the absolute residual by the underflow threshold
    %$\eta$%#\(\eta\)#. *)
    
Theorem scaleM_error :
  forall m n
    (A   : 'M[ftype t]_(m, n))
    (x   : ftype t)
    (Hfin : F.finitemx (F.scalemx x A)),
  exists (E eta : 'M[R]_(m, n)),
       map_mx FT2R (F.scalemx x A)
     = scalemx (FT2R x) (map_mx FT2R A + E) + eta
  /\ (forall i j,
        Rabs (E   i j) <= @default_rel t * Rabs (map_mx FT2R A i j))
  /\ (forall i j,
        Rabs (eta i j) <= @default_abs t).
Proof.
  intros m n A x Hfin.
  apply Fscalemx_mixed_error in Hfin.
  destruct Hfin as [e [eta [Heq [He Heta]]]].
  exists e, eta.
  split; auto.
  split; intros i j; auto.
  destruct (He i j) as [d [Hd Hbd]].
  rewrite Hd Rabs_mult Rmult_comm.
  apply /RleP.
  apply Rmult_le_compat_r.
  - apply Rabs_pos.
  - apply /RleP; auto.
Qed.

(** ** Scaled Matrix Product Error

    [sMMC_error] composes [MMC_error] and [scaleM_error] to give a
    structured decomposition of
    %$\mathtt{fl}(x \cdot (AB))$%#\(\mathtt{fl}(x \cdot (AB))\)#. The result carries
    backward perturbations from the matrix product (bounded by %$g(n)$%#\(g(n)\)#
    column-wise) and from the scaling step (bounded by %$\mathbf{u}$%#\(\mathbf{u}\)#
    entry-wise), together with forward absolute errors from each, bounded by
    %$g_1(n,n)$%#\(g_1(n,n)\)# and %$\eta$%#\(\eta\)# respectively. *)
    
Theorem sMMC_error :
  forall m n p
    (A    : 'M[ftype t]_(m, n))
    (B    : 'M[ftype t]_(n, p))
    (x    : ftype t)
    (Hfin : F.finitemx (F.scalemx x (F.mulmx A B))),
  exists E1 E eta1 eta : 'M[R]_(m, p),
       map_mx FT2R (F.scalemx x (F.mulmx A B))
     = scalemx (FT2R x)
         (((map_mx FT2R A *m map_mx FT2R B + E1) + eta1) + E) + eta
  /\ (forall k : 'I_p,
        exists E0,
             col k E1 = E0 *m col k (map_mx FT2R B)
          /\ (forall i j,
                Rabs (E0 i j) <= g n * Rabs (map_mx FT2R A i j)))
  /\ (forall i j, Rabs (eta1 i j) <= g1 n n)
  /\ (forall i j, Rabs (eta  i j) <= @default_abs t)
  /\ (forall i j,
        Rabs (E i j) <=
          @default_rel t *
          Rabs (((map_mx FT2R A *m map_mx FT2R B + E1) + eta1)%Ri i j)).
Proof.
  move => m n p A B x Hfin.

  (** Decompose the outer scaling error for x * (A*B). *)
  destruct (scaleM_error _ _ (F.mulmx A B) x Hfin)
    as (E & eta & Heq & HE & Heta).
  rewrite Heq.

  (** Decompose the matrix-multiplication error for A*B,
      propagating finiteness from [F.scalemx x (F.mulmx A B)]. *)
  destruct (MMC_error _ _ _ A B)
    as (E1 & eta1 & Heq1 & HE1 & Heta1). {
    apply (F.finitemx_scalemx_e _ _ Hfin).
  }
  rewrite Heq1.

  exists E1, E, eta1, eta.
  repeat split => //.
  move => i j.
  move : (HE i j).
  rewrite Heq1 //.
Qed.

(** ** Matrix Addition Error

    [mat_sum_error] establishes that floating-point matrix addition
    %$\mathtt{fl}(A + B)$%#\(\mathtt{fl}(A + B)\)# equals the exact sum of two slightly
    perturbed matrices. Each entry of both perturbation matrices is bounded
    in relative terms by the unit roundoff %$\mathbf{u}$%#\(\mathbf{u}\)#. This is a
    pure backward result: no forward error term appears. *)
    
Theorem mat_sum_error :
  forall m n
    (A B  : 'M[ftype t]_(m, n))
    (Hfin : F.finitemx (F.addmx A B)),
  exists EA EB : 'M[R]_(m, n),
       map_mx FT2R (F.addmx A B)
     = (map_mx FT2R A + EA) + (map_mx FT2R B + EB)
  /\ (forall i j, exists d,
        EA i j = map_mx FT2R A i j * d /\ Rabs d <= @default_rel t)
  /\ (forall i j, exists d,
        EB i j = map_mx FT2R B i j * d /\ Rabs d <= @default_rel t).
Proof.
  intros m n A B Hfin.
  destruct (Faddmx_mixed_error A B Hfin) as [EA [EB [Heq [HA HB]]]].
  exists EA, EB.
  repeat split; auto.
Qed.

(** ** Scaled Matrix Sum Error

    [mat_axpby_error] bounds the floating-point operation
    %$\mathtt{fl}(xA + yB)$%#\(\mathtt{fl}(xA + yB)\)# by combining the mixed errors from
    each scaling step with a backward error from the floating-point addition.
    The result decomposes into relative perturbations of %$A$%#\(A\)# and %$B$%#\(B\)#
    bounded by %$\mathbf{u}$%#\(\mathbf{u}\)# and irreducible absolute forward errors
    from each scaling, bounded by %$\eta$%#\(\eta\)#. *)
    
Theorem mat_axpby_error :
  forall [m n]
    (A B  : 'M[ftype t]_(m, n))
    (x y  : ftype t)
    (Hfin : F.finitemx
              (F.addmx (F.scalemx x A) (F.scalemx y B))),
  exists EA EB ea eb eta1 eta2 : 'M[R]_(m, n),
       map_mx FT2R (F.addmx (F.scalemx x A) (F.scalemx y B))
     =   scalemx (FT2R x) (map_mx FT2R A + EA) + eta1 + ea
       + scalemx (FT2R y) (map_mx FT2R B + EB) + eta2 + eb
  /\ (forall i j,
        Rabs (EA i j) <= @default_rel t * Rabs (map_mx FT2R A i j))
  /\ (forall i j,
        Rabs (EB i j) <= @default_rel t * Rabs (map_mx FT2R B i j))
  /\ (forall i j, exists d,
          ea i j
        = (scalemx (FT2R x) (map_mx FT2R A + EA) + eta1) i j * d
       /\ Rabs d <= @default_rel t)
  /\ (forall i j, exists d,
          eb i j
        = (scalemx (FT2R y) (map_mx FT2R B + EB) + eta2) i j * d
       /\ Rabs d <= @default_rel t)
  /\ (forall i j, Rabs (eta1 i j) <= @default_abs t)
  /\ (forall i j, Rabs (eta2 i j) <= @default_abs t).
Proof.
  move => m n A B x y Hfin.

  (** Decompose the outer addition as a pure backward error. *)
  destruct (mat_sum_error _ _ (F.scalemx x A) (F.scalemx y B))
    as (ea & eb & HEQ & H1 & H2) => //.

  (** Decompose the mixed error for the scaling x * A. *)
  destruct (scaleM_error _ _ A x)
    as (EA & eta1 & Heqx & H6 & H7). {
    apply (F.finitemx_addmx_e _ _ Hfin).
  }

  (** Decompose the mixed error for the scaling y * B. *)
  destruct (scaleM_error _ _ B y)
    as (EB & eta2 & Heqy & H12 & H13). {
    apply (F.finitemx_addmx_e _ _ Hfin).
  }

  rewrite {}HEQ {}Heqx in H1 |- *.
  rewrite {}Heqy in H2 |- *.
  exists EA, EB, ea, eb, eta1, eta2.
  repeat split => //.
  rewrite !addrA //.
Qed.

(** ** General GEMM Error

    [GEMM_error] is the master error theorem for the floating-point GEMM
    operation %$\mathtt{fl}(s_1(AB) + s_2 Y)$%#\(\mathtt{fl}(s_1(AB) + s_2 Y)\)#. It
    decomposes the result into backward perturbation components and forward
    absolute errors arising from matrix multiplication (bounded by %$g(n)$%#\(g(n)\)#
    and %$g_1(n,n)$%#\(g_1(n,n)\)#), scalar scaling (bounded by %$\mathbf{u}$%#\(\mathbf{u}\)# and
    %$\eta$%#\(\eta\)#), and matrix addition (backward, bounded by %$\mathbf{u}$%#\(\mathbf{u}\)#).
    The proof composes [mat_axpby_error] and [MMC_error]. *)
    
Theorem GEMM_error :
  forall [m n p]
    (A  : 'M[ftype t]_(m, n))
    (B  : 'M[ftype t]_(n, p))
    (Y  : 'M[ftype t]_(m, p))
    (s1 s2 : ftype t)
    (Hfin : F.finitemx
              (F.addmx (F.scalemx s1 (F.mulmx A B)) (F.scalemx s2 Y))),
  exists ab1 ab2 ab3 ab4 ab5 y1 y2 y3 : 'M[R]_(m, p),
       map_mx FT2R
         (F.addmx (F.scalemx s1 (F.mulmx A B)) (F.scalemx s2 Y))
     =   (scalemx (FT2R s1)
            ((((map_mx FT2R A *m map_mx FT2R B) + ab1) + ab2) + ab3)
          + ab4) + ab5
       + ((scalemx (FT2R s2) (map_mx FT2R Y + y1) + y2) + y3)
  /\ (forall k : 'I_p,
        exists E0,
             col k ab1 = E0 *m col k (map_mx FT2R B)
          /\ (forall i j,
                Rabs (E0 i j) <= g n * Rabs (map_mx FT2R A i j)))
  /\ (forall i j, Rabs (ab2 i j) <= g1 n n)
  /\ (forall i j,
        Rabs (ab3 i j) <=
          @default_rel t *
          Rabs ((((map_mx FT2R A *m map_mx FT2R B) + ab1) + ab2)%Ri i j))
  /\ (forall i j,
        Rabs (y1 i j) <= @default_rel t * Rabs (map_mx FT2R Y i j))
  /\ (forall i j, exists d,
          ab5 i j
        = (scalemx (FT2R s1)
             ((((map_mx FT2R A *m map_mx FT2R B) + ab1) + ab2) + ab3)
           + ab4) i j * d
       /\ Rabs d <= @default_rel t)
  /\ (forall i j, exists d,
          y3 i j
        = (scalemx (FT2R s2) (map_mx FT2R Y + y1) + y2) i j * d
       /\ Rabs d <= @default_rel t)
  /\ (forall i j, Rabs (ab4 i j) <= @default_abs t)
  /\ (forall i j, Rabs (y2 i j) <= @default_abs t).
Proof.
  intros m n p A B Y s1 s2 Hfin.

  (** Decompose the axpby structure for s1*(A*B) + s2*Y, obtaining
      backward addition errors ab5, y3 and forward scaling errors
      ab4, y2, together with backward scaling perturbations ab3, y1. *)
  destruct (mat_axpby_error (F.mulmx A B) Y s1 s2)
    as (ab3 & y1 & ab5 & y3 & ab4 & y2
        & Heq1 & Hab3 & Hy1 & Hab5 & Hy3 & Hab4 & Hy2) => //.

  (** Decompose the matrix-multiplication error for A*B, propagating
      finiteness from the s1*(A*B) factor of Hfin. *)
  destruct (MMC_error _ _ _ A B)
    as (ab1 & ab2 & Heq2 & Hab1 & Hab2). {
    apply F.finitemx_addmx_e in Hfin.
    destruct Hfin as [Hfin _].
    apply (F.finitemx_scalemx_e _ _ Hfin).
  }

  rewrite {}Heq1 {}Heq2 in Hab5, Hab3 |- *.
  exists ab1, ab2, ab3, ab4, ab5, y1, y2, y3.
  repeat split => //.
  rewrite !addrA //.
Qed.

End MMERROR.