(** * Matrix-Vector Multiplication Error Bounds

    This file establishes mixed and forward error bounds for floating-point
    matrix-vector multiplication, building on the dot product and summation
    accuracy results.

    ** Error Factors

    Throughout, the accumulated relative error factor is
    %$g(n) = (1 + \mathbf{u})^n - 1$%#\(g(n) = (1 + \mathbf{u})^n - 1\)# and
    the mixed absolute error factor is
    %$g_1(n_1, n_2) = n_1 \cdot \eta \cdot (1 + g(n_2))$%#\(g_1(n_1, n_2) = n_1 \cdot \eta \cdot (1 + g(n_2))\)#,
    where %$\mathbf{u}$%#\(\mathbf{u}\)# is the unit roundoff and
    %$\eta$%#\(\eta\)# is the underflow threshold for the given type.
    Both are defined in [common].

    ** Main Results

    - [vec_vec_mul_mixed_error]: Shows that the floating-point row-times-column
      dot product can be expressed as an exact product of a componentwise-perturbed
      row vector with the exact column vector, plus a small absolute residual.

    - [mat_vec_mul_mixed_error]: Shows that the floating-point matrix-vector
      product can be expressed as an exact product of a componentwise-perturbed
      matrix with the exact input vector, plus a small absolute residual.
      Proved by applying [vec_vec_mul_mixed_error] row by row.

    - [mat_vec_mul_forward_error]: Bounds the absolute forward error of the
      floating-point matrix-vector product in the vector max-norm by
      %$g(n) \cdot \|A\| \cdot \|B\| + g_1(n, n)$%#\(g(n) \cdot \|A\| \cdot \|B\| + g_1(n,n)\)#,
      where %$\|A\|$%#\(\|A\|\)# is the matrix infinity norm and
      %$\|B\|$%#\(\|B\|\)# is the vector max-norm.

    ** Dependencies

    This file relies on:
    - [preamble], [common]: basic setup and shared definitions
    - [dotprod_model], [sum_model]: relational models of dot product and summation
    - [dot_acc], [float_acc_lems]: accuracy lemmas
    - [mv_mathcomp]: floating-point matrix/vector operations and norm definitions
*)

From LAProof.accuracy_proofs Require Import preamble common
                                             dotprod_model sum_model
                                             dot_acc float_acc_lems mv_mathcomp.

From mathcomp.algebra_tactics Require Import ring.

Section WithNAN.

Context {NAN : FPCore.Nans} {t : type}.

Notation g  := (@common.g t).
Notation g1 := (@common.g1 t).

(** ** Row-Vector Times Column-Vector: Mixed Error Bound *)

(** [vec_vec_mul_mixed_error] shows that the floating-point row-times-column
    dot product can be expressed as an exact product of a componentwise-perturbed
    row vector with the exact column vector, plus a small absolute residual. *)
    
Lemma vec_vec_mul_mixed_error :
  forall [n] (A : 'M[ftype t]_(1,n)) (B : 'M[ftype t]_(n,1))
    (Hfin : F.finitemx (F.mulmx A B)),
  exists (E : 'M[R]_(1,n)) (eta : 'M[R]_(1,1)),
      map_mx FT2R (F.mulmx A B)
        = ((map_mx FT2R A + E) *m (map_mx FT2R B) + eta)%Ri
    /\ (forall i j, Rabs (E i j) <= g n * Rabs (map_mx FT2R A i j))
    /\ (forall i j, Rabs (eta i j) <= g1 n n).
Proof.
  intros *.
  rewrite F.mulmx_dotprodF.
  move => Hfin.
  specialize (Hfin ord0 ord0). rewrite mxE in Hfin.
  assert (Hlen : size (seq_of_rV A) = size (seq_of_rV B^T)).
  { unfold seq_of_rV. rewrite !size_map size_ord_enum //. }
  destruct (dotprod_mixed_error (seq_of_rV A) (seq_of_rV (trmx B)) Hlen Hfin)
    as [u [eta [Hu [Heq [HD Heta]]]]].
  exists ((\row_j nth R0 u j) - map_mx FT2R A)%Ri, (const_mx eta).
  repeat split.
  - rewrite map_const_mx.
    rewrite {}Heq.
    rewrite (addrC (map_mx _ _)) subrK.
    apply /matrixP. intros i j. rewrite !ord1. clear i j.
    rewrite !mxE.
    change (GRing.add ?A ?B) with (Rplus A B).
    f_equal.
    rewrite index_ord_enum.
    rewrite (unlock (bigop_unlock)).
    unfold reducebig, comp, applybig.
    unfold dotprodR, dotprod.
    rewrite foldl_foldr.
    2, 3: compute; intros; lra.
    unfold seq_of_rV.
    rewrite -!map_comp.
    rewrite /seq_of_rV size_map size_ord_enum in Hu.
    move :(nth_ord_enum_lemma R0 u). rewrite Hu => Hu'.
    rewrite {1}Hu'. clear Hu'.
    rewrite zip_map -map_comp foldr_map.
    simpl.
    f_equal.
    apply FunctionalExtensionality.functional_extensionality; intro i.
    apply FunctionalExtensionality.functional_extensionality; intro x.
    rewrite flip_Rplus.
    rewrite !mxE.
    reflexivity.
  - intros i j. rewrite ord1; clear i.
    destruct (HD j) as [d [Hval Hbd]].
    { unfold seq_of_rV. rewrite size_map size_ord_enum.
      pose proof (ltn_ord j). lia. }
    rewrite !mxE.
    rewrite {}Hval.
    unfold seq_of_rV in Hbd |- *.
    rewrite size_map size_ord_enum in Hbd.
    rewrite (nth_map j).
    2: { rewrite size_ord_enum; pose proof (ltn_ord j); lia. }
    rewrite nth_ord_enum'.
    change (A 0 j)%Ri with (A ord0 j).
    set Aj := FT2R (A ord0 j).
    change ((Aj * (1 + d))%Re - Aj)%Ri with ((Aj * (1 + d)) - Aj)%Ri.
    replace (Aj * (1 + d) - Aj)%Ri with (Aj * d)%Ri by ring.
    rewrite mulrC.
    rewrite Rabs_mult.
    apply /RleP.
    apply Rmult_le_compat_r; auto.
    apply Rabs_pos.
  - move => i j; rewrite !ord1 mxE; clear i j.
    move :Heta; rewrite /seq_of_rV size_map size_ord_enum //.
    move => Heta; apply /RleP; auto.
Qed.

(** ** General Matrix-Vector Product: Mixed Error Bound *)

(** [mat_vec_mul_mixed_error] shows that the floating-point matrix-vector
    product can be expressed as an exact product of a componentwise-perturbed
    matrix with the exact input vector, plus a small absolute residual.
    Proved by applying [vec_vec_mul_mixed_error] row by row. *)
    
Lemma mat_vec_mul_mixed_error :
  forall [m n] (A : 'M[ftype t]_(m,n)) (B : 'M[ftype t]_(n,1))
    (Hfin : F.finitemx (F.mulmx A B)),
  exists (E : 'M[R]_(m,n)) (eta : 'M[R]_(m,1)),
      map_mx FT2R (F.mulmx A B)
        = ((map_mx FT2R A + E) *m (map_mx FT2R B) + eta)%Ri
    /\ (forall i j, Rabs (E i j) <= g n * Rabs (map_mx FT2R A i j))
    /\ (forall i j, Rabs (eta i j) <= g1 n n).
Proof.
  intros.
  revert m A Hfin.
  induction m; intros.
  - exists (const_mx R0), (const_mx R0).
    split; [apply matrixP | split]; intros i j; destruct i; lia.
  - change (m.+1) with (1 + m)%nat in A, Hfin |- *.
    destruct (IHm (dsubmx A)) as [E2 [eta2 [HE2 [HB2 Heta2]]]].
    { move => i j. specialize (Hfin (rshift 1 i) j).
      unfold F.mulmx in Hfin |- *.
      rewrite mxE in Hfin. rewrite mxE row_dsubmx //. }
    clear IHm.
    destruct (vec_vec_mul_mixed_error (usubmx A) B) as [E1 [eta1 [HE1 [HB1 Heta1]]]].
    { move => i j. specialize (Hfin (lshift m i) j).
      unfold F.mulmx in Hfin |- *.
      rewrite mxE in Hfin. rewrite mxE row_usubmx //. }
    exists (col_mx E1 E2), (col_mx eta1 eta2).
    split; [ | split].
    + replace (F.mulmx A B)
        with (col_mx (F.mulmx (usubmx A) B) (F.mulmx (dsubmx A) B)).
      2: { clear.
           unfold F.mulmx. apply /matrixP. move => i j.
           destruct (splitP i) as [i'|i'];
             [ replace i with (@lshift 1 m i');
               [ | apply ord_inj; simpl; auto]
             | replace i with (@rshift 1 m i');
               [ | apply ord_inj; simpl; lia]].
           rewrite col_mxEu !mxE row_usubmx //.
           rewrite col_mxEd !mxE row_dsubmx //. }
      rewrite map_col_mx {}HE1 {}HE2 map_usubmx map_dsubmx.
      set A' := map_mx FT2R A.
      set B' := map_mx FT2R B.
      rewrite !mulmxDl.
      rewrite -!add_col_mx.
      f_equal.
      f_equal.
      rewrite mul_usub_mx mul_dsub_mx vsubmxK //.
      rewrite mul_col_mx //.
    + move => i j.
      rewrite -(vsubmxK A) map_col_mx.
      destruct (splitP i) as [i'|i'];
        [ replace i with (@lshift 1 m i');
          [ | apply ord_inj; simpl; auto]
        | replace i with (@rshift 1 m i');
          [ | apply ord_inj; simpl; lia]].
      move :(HB1 i' j). rewrite !col_mxEu !mxE //.
      move :(HB2 i' j). rewrite !col_mxEd !mxE //.
    + move => i j.
      destruct (splitP i) as [i'|i'];
        [ replace i with (@lshift 1 m i');
          [ | apply ord_inj; simpl; auto]
        | replace i with (@rshift 1 m i');
          [ | apply ord_inj; simpl; lia]].
      move :(Heta1 i' j). rewrite !col_mxEu //.
      move :(Heta2 i' j). rewrite !col_mxEd //.
Qed.

(** ** Matrix-Vector Product: Forward Error Bound *)

(** [mat_vec_mul_forward_error] bounds the absolute forward error of the
    floating-point matrix-vector product in the vector max-norm by
    %$g(n) \cdot \|A\|_M \cdot \|B\| + g_1(n, n)$%#\(g(n) \cdot \|A\|_M \cdot \|B\| + g_1(n,n)\)#,
    where [normM] is the matrix infinity norm and [normv] is the vector max-norm. *)

Theorem mat_vec_mul_forward_error :
  forall [m n] (A : 'M[ftype t]_(m,n)) (B : 'M[ftype t]_(n,1))
    (Hfin : F.finitemx (F.mulmx A B)),
    normv (map_mx FT2R (F.mulmx A B) - (map_mx FT2R A *m map_mx FT2R B))
      <= (g n * normM (map_mx FT2R A) * normv (map_mx FT2R B)) + g1 n n.
Proof.
  intros.
  destruct (mat_vec_mul_mixed_error _ _ Hfin) as (E & eta & HE & H1 & H2).
  rewrite {}HE mulmxDl.
  set Ar := map_mx FT2R A.
  set Br := map_mx FT2R B.
  have H0 : (Ar *m Br + E *m Br + eta - Ar *m Br = E *m Br + eta)%Ri.
  { rewrite -!addrA addrC addrA -addrA addNr addr0 //. }
  rewrite {}H0.
  eapply (le_trans (normv_triang _ _ _)).
  apply lerD.
  eapply (le_trans (subMultNorm _ _ _ _)).
  apply ler_pM => //.
  apply normM_pos.
  apply normv_pos.
  rewrite /normM mulrC big_max_mul.
  apply: le_bigmax2 => i0 _.
  rewrite /sum_abs.
  rewrite big_mul => [ | i b | ]; [ | ring | ].
  - apply ler_sum => i _.
    rewrite mulrC -/Ar //.
  - apply /RleP; auto with commonDB.
  - apply /RleP; auto with commonDB.
  - rewrite /normv.
    apply bigmax_le => [| i _].
    apply /RleP; auto with commonDB.
    auto.
Qed.

End WithNAN.