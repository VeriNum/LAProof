From LAProof.accuracy_proofs Require Import preamble common 
                                                 dotprod_model sum_model
                                                dot_acc float_acc_lems (*list_lemmas
                                                              gem_defs*) mv_mathcomp.

From mathcomp.algebra_tactics Require Import ring.


Section WithNAN. 
(* mixed error bounds over lists *)
Context {NAN: FPCore.Nans} {t : type}.


Definition mc_dotprodF [n: nat] (x: 'rV[ftype t]_n) (y: 'cV[ftype t]_n) : ftype t :=
   \big[BPLUS / pos_zero]_i (BMULT (x ord0 (rev_ord i)) (y (rev_ord i) ord0)).

Definition matrix_mulF [m n p] (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,p)) :=
 \matrix_(i,k) mc_dotprodF (row i A) (col k B).

Definition seq_of_rV {T}[n] (x: 'rV[T]_n) := map (x ord0) (ord_enum n).

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).


Lemma matrix_mulF_dotprodF:
  forall [n] (A: 'M[ftype t]_(1,n)) (B: 'M[ftype t]_(n,1)),
 matrix_mulF A B = const_mx (dotprodF (seq_of_rV A) (seq_of_rV (trmx B))).
Proof.
intros.
 unfold matrix_mulF. apply /matrixP. move => i k. rewrite !mxE.
 unfold seq_of_rV.
 rewrite !ord1. clear i k.
 unfold dotprodF, dotprod.
 unfold mc_dotprodF.
 rewrite (unlock (bigop_unlock)).
 unfold reducebig, comp, applybig.
 rewrite -(revK (map (uncurry _) _)).
 rewrite foldl_rev.
 simpl.
 rewrite index_ord_enum.
 rewrite zip_map -map_comp.
 rewrite -map_rev rev_ord_enum -map_comp.
 rewrite foldr_map.
 f_equal.
 simpl.
 apply FunctionalExtensionality.functional_extensionality; intro i.
 apply FunctionalExtensionality.functional_extensionality; intro x.
 rewrite !mxE. reflexivity.
Qed.

Lemma vec_vec_mul_mixed_error:
  forall [n] (A: 'M[ftype t]_(1,n)) (B: 'M[ftype t]_(n,1))
  (Hfin: forall i j, Binary.is_finite (matrix_mulF A B i j)),
  exists (E : 'M[R]_(1,n)) (eta : 'M[R]_(1,1)),
    map_mx FT2R (matrix_mulF A B) = ((map_mx FT2R A + E) *m (map_mx FT2R B) + eta)%Ri
    /\ (forall i j, Rabs (E i j) <= g n * Rabs (map_mx FT2R A i j))
    /\ (forall i j, Rabs (eta i j) <= g1 n n).
Proof.
intros *.
rewrite matrix_mulF_dotprodF.
move => Hfin.
specialize (Hfin ord0 ord0). rewrite mxE in Hfin.
assert (Hlen: size (seq_of_rV A) = size (seq_of_rV B^T)).
unfold seq_of_rV. rewrite !size_map size_ord_enum //.
destruct (dotprod_mixed_error (seq_of_rV A) (seq_of_rV (trmx B)) Hlen Hfin)
 as [u [eta [ Hu [Heq [HD ?]]]]].
exists ((\row_j nth R0 u j) - map_mx FT2R A)%Ri, (const_mx eta).
repeat split.
-
rewrite map_const_mx.
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
-
intros i j. rewrite ord1; clear i.
destruct (HD j).
unfold seq_of_rV. rewrite size_map size_ord_enum. pose proof (ltn_ord j). lia.
rewrite !mxE.
destruct H0.
rewrite {}H0.
unfold seq_of_rV in H1|-*.
rewrite size_map size_ord_enum in H1.
rewrite (nth_map j).
2: rewrite size_ord_enum; pose proof (ltn_ord j); lia.
rewrite nth_ord_enum'.
change (A 0 j)%Ri with (A ord0 j).
set Aj := FT2R (A ord0 j).
change ((Aj * (1 + x))%Re - Aj)%Ri with ((Aj * (1 + x)) - Aj)%Ri.
replace (Aj * (1 + x) - Aj)%Ri  with (Aj*x)%Ri by ring.
rewrite mulrC.
rewrite Rabs_mult.
apply /RleP.
apply Rmult_le_compat_r; auto.
apply Rabs_pos.
-
move => i j; rewrite !ord1 mxE; clear i j. 
move :H; rewrite /seq_of_rV size_map size_ord_enum //.
move => H; apply /RleP; auto.
Qed.

Lemma mat_vec_mul_mixed_error:
  forall [m n] (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,1))
  (Hfin: forall i j, Binary.is_finite (matrix_mulF A B i j)),
  exists (E : 'M[R]_(m,n)) (eta : 'M[R]_(m,1)),
    map_mx FT2R (matrix_mulF A B) = ((map_mx FT2R A + E) *m (map_mx FT2R B) + eta)%Ri
    /\ (forall i j, Rabs (E i j) <= g n * Rabs (map_mx FT2R A i j))
    /\ (forall i j, Rabs (eta i j) <= g1 n n).
Proof.
intros.
revert m A Hfin.
induction m; intros.
-
exists (const_mx R0), (const_mx R0).
split; [apply matrixP | split];  intros i j; destruct i; lia.
-
change (m.+1) with (1+m)%nat in A,Hfin|-*.
destruct (IHm (dsubmx A)) as [E2 [eta2 [? [? ?]]]]. {
   move => i j. specialize (Hfin (rshift 1 i) j).
   unfold matrix_mulF in Hfin|-*.
   rewrite mxE in Hfin. rewrite mxE row_dsubmx //.
}
clear IHm.
destruct (vec_vec_mul_mixed_error (usubmx A) B) as [E1 [eta1 [? [? ?]]]]. {
   move => i j. specialize (Hfin (lshift m i) j).
   unfold matrix_mulF in Hfin|-*.
   rewrite mxE in Hfin. rewrite mxE row_usubmx //.
}
exists (col_mx E1 E2), (col_mx eta1 eta2).
split; [ | split].
+
replace (matrix_mulF A B) with (col_mx (matrix_mulF (usubmx A) B) (matrix_mulF (dsubmx A) B)). 2:{
    clear.
   unfold matrix_mulF. apply /matrixP. move => i j. 
destruct (splitP i) as [i'|i'];
 [replace i with (@lshift 1 m i'); [  | apply ord_inj; simpl; auto]
 |replace i with (@rshift 1 m i'); [ | apply ord_inj; simpl; lia]].
 rewrite col_mxEu !mxE row_usubmx //.
 rewrite col_mxEd !mxE row_dsubmx //.
}
rewrite map_col_mx {}H {}H2 map_usubmx map_dsubmx.
set A' := map_mx FT2R A.
set B' := map_mx FT2R B.
rewrite !mulmxDl.
rewrite -!add_col_mx.
f_equal.
f_equal.
rewrite mul_usub_mx mul_dsub_mx vsubmxK //.
rewrite mul_col_mx //.
+
move => i j.
rewrite -(vsubmxK A) map_col_mx.
destruct (splitP i) as [i'|i'];
 [replace i with (@lshift 1 m i'); [  | apply ord_inj; simpl; auto]
 |replace i with (@rshift 1 m i'); [ | apply ord_inj; simpl; lia]].
 move :(H3 i' j).  rewrite !col_mxEu !mxE //.
 move :(H0 i' j).  rewrite !col_mxEd !mxE //.
+
move => i j.
destruct (splitP i) as [i'|i'];
 [replace i with (@lshift 1 m i'); [  | apply ord_inj; simpl; auto]
 |replace i with (@rshift 1 m i'); [ | apply ord_inj; simpl; lia]].
 move :(H4 i' j).  rewrite !col_mxEu  //.
 move :(H1 i' j).  rewrite !col_mxEd //.
Qed. 


Theorem forward_error :
 forall [m n] (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,1))
  (Hfin: forall i j, Binary.is_finite (matrix_mulF A B i j)),
  normv (map_mx FT2R (matrix_mulF A B) - (map_mx FT2R A *m map_mx FT2R B))
    <= (g n * normM (map_mx FT2R A) * normv (map_mx FT2R B)) + g1 n n.
Proof.
intros.
destruct (mat_vec_mul_mixed_error _ _ Hfin) as (E & eta & HE & H1 & H2).
rewrite {}HE mulmxDl.
set Ar := map_mx FT2R A.
set Br := map_mx FT2R B.
have H0: (Ar *m Br + E *m Br + eta - Ar *m Br = E *m Br + eta)%Ri.
rewrite -!addrA addrC addrA -addrA addNr addr0 //.
rewrite {}H0.
eapply (le_trans  (normv_triang _ _ _)).
apply lerD.
eapply (le_trans (subMultNorm _ _ _ _ )).
apply ler_pM => //. 
apply normM_pos.
apply normv_pos.
rewrite /normM mulrC big_max_mul.
apply: le_bigmax2 => i0 _.
rewrite /sum_abs.
rewrite big_mul =>  [ | i b | ]; [ | ring | ].
-
apply ler_sum => i _.
rewrite mulrC -/Ar //.
-
apply /RleP; auto with commonDB.
-
apply /RleP; auto with commonDB.
-
rewrite /normv.
apply bigmax_le => [|i _].  
apply /RleP; auto with commonDB.
auto.
Qed.

End WithNAN.

