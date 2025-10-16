From LAProof.accuracy_proofs Require Import preamble common 
       dotprod_model sum_model dot_acc float_acc_lems list_lemmas
         (*gem_defs*) mv_mathcomp gemv_acc vec_op_acc.

Section MMERROR. 
(* forward error matrix multiplication *)
Context {NAN: FPCore.Nans} {t : FPStdLib.type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).



Ltac case_splitP j :=
  first [is_var j | fail 1 "case_splitP requires a variable, but got" j];
 match type of j with 'I_(addn ?a ?b) =>
  let i := fresh "j" in let H := fresh in 
  destruct (splitP j) as [i H | i H];
 [replace j with (@lshift a b i); [ | apply ord_inj; simpl; lia]
 |replace j with (@rshift a b i); [ | apply ord_inj; simpl; lia]];
 clear j H; rename i into j
 end.

Local Remark mul_mx_row': 
 forall [R : GRing.SemiRing.type] m n p1 p2 
    (A: 'M[R]_(m,n)) (Bl: 'M[R]_(n,p1)) (Br: 'M[R]_(n,p2)),
  A *m row_mx Bl Br = row_mx (A *m Bl) (A *m Br).
Proof.
move => R m n p1 p2 A Bl Br.
apply /matrixP => i j.
case_splitP j.
rewrite row_mxEl !mxE . apply eq_bigr. move => k _;  rewrite row_mxEl//.
rewrite row_mxEr !mxE . apply eq_bigr. move => k _;  rewrite row_mxEr//.
Qed.

Lemma matrix_mulF_row:
 forall m n p1 p2 (A: 'M[ftype t]_(m,n)) (Bl: 'M_(n,p1)) (Br: 'M_(n,p2)),
  matrix_mulF A (row_mx Bl Br) = row_mx (matrix_mulF A Bl) (matrix_mulF A Br).
Proof.
intros.
apply /matrixP => i j.
case_splitP j.
 rewrite row_mxEl !mxE -col_lsubmx row_mxKl //.
 rewrite row_mxEr !mxE -col_rsubmx row_mxKr //.
Qed.

Theorem MMC_error:
  forall m n p (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,p))
 (Hfin: forall i j, Binary.is_finite (matrix_mulF A B i j)),
  exists (E eta: 'M[R]_(m,p)),
     map_mx FT2R (matrix_mulF A B) = (map_mx FT2R A *m map_mx FT2R B + E + eta)%Ri
  /\ (forall k: 'I_p, 
       exists E0: 'M[R]_(m,n), 
         col k E = E0 *m col k (map_mx FT2R B) /\
         (forall i j, Rabs (E0 i j) <= g n * Rabs (map_mx FT2R A i j)))
  /\ forall i j, Rabs (eta i j) <= g1 n n.
Proof.
move => m n p.
elim: p.
- move => A B Hfin.
exists (const_mx 0), (const_mx 0).
repeat split.
+ apply /matrixP. move => i j. destruct j; lia.
+ move => k; destruct k; lia.
+ move => i j; destruct j; lia.
- move => p IH A B Hfin.
change (p.+1) with (1+p)%nat in *.
rewrite -(hsubmxK B) matrix_mulF_row map_row_mx.
destruct (IH A (rsubmx B)) as [E [eta [Heq [HE Heta]]]]. {
  move => i j. move :(Hfin i (rshift 1 j)). rewrite /matrix_mulF !mxE col_rsubmx //.
}
clear IH. rewrite  {}Heq.
destruct (mat_vec_mul_mixed_error A (lsubmx B)) as [E1 [eta1 [Heq1 [HE1 Heta1]]]]. {
 move => i j. move :(Hfin i (lshift p j)). rewrite /matrix_mulF !mxE col_lsubmx //.
}
rewrite {}Heq1.
exists (row_mx (E1 *m map_mx FT2R (lsubmx B)) E), (row_mx eta1 eta).
repeat split.
+
rewrite map_lsubmx map_rsubmx hsubmxK -add_row_mx mulmxDl -add_row_mx.
f_equal.
f_equal.
rewrite -mul_mx_row hsubmxK //.
+
move => k.
case_splitP k.
* exists E1. split => //.
 rewrite colKl map_row_mx colKl !col_id //.
* destruct (HE k) as (E0 & Heq2 & HE0).
 exists E0; split => //.
 rewrite colKr map_row_mx colKr //.
+
move => i j.
case_splitP j.
rewrite row_mxEl //.
rewrite row_mxEr //.
Qed.

Theorem scaleM_error:
  forall m  n (A: 'M[ftype t]_(m,n)) (x: ftype t)
  (Hfin: forall i j, Binary.is_finite (matrix_scaleF x A i j)),
  exists (E eta: 'M[R]_(m,n)),
     map_mx FT2R (matrix_scaleF x A) = 
     scalemx (FT2R x) (map_mx FT2R A + E) + eta
    /\ (forall i j,  Rabs (E i j) <= @default_rel t * Rabs (map_mx FT2R A i j)) 
    /\ (forall i j,  Rabs (eta i j) <= @default_abs t).
Proof.
intros.
apply matrix_scaleF_mixed_error in Hfin.
destruct Hfin as [e [eta [? [? ?]]]].
exists e, eta; split; auto. split; intros; auto.
destruct (H0 i j) as [d [? ?]].
rewrite H2 Rabs_mult Rmult_comm.
apply /RleP; apply  Rmult_le_compat_r.
apply Rabs_pos.
apply /RleP; auto.
Qed.

Theorem sMMC_error:
 forall m n p (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,p)) (x: ftype t)
 (Hfin: forall i j, Binary.is_finite (matrix_scaleF x (matrix_mulF A B) i j)),
  exists E1 E eta1 eta: 'M[R]_(m,p),
     map_mx FT2R (matrix_scaleF x (matrix_mulF A B)) = 
      scalemx (FT2R x) (((map_mx FT2R A *m map_mx FT2R B + E1) + eta1) + E) + eta
 /\ (forall k: 'I_p, exists E0,
       col k E1 = E0 *m (col k (map_mx FT2R B)) /\
       (forall i j, Rabs (E0 i j) <= g n * Rabs (map_mx FT2R A i j)))
 /\ (forall i j, Rabs (eta1 i j) <= g1 n n)
 /\ (forall i j, Rabs (eta i j) <= @default_abs t)
 /\ (forall i j, Rabs (E i j) <= @default_rel t * Rabs (((map_mx FT2R A *m map_mx FT2R B + E1) + eta1)%Ri i j)).
Proof.
move => m n p A B x Hfin.
destruct (scaleM_error _ _ (matrix_mulF A B) x Hfin)
  as (E & eta & Heq & HE & Heta).
rewrite Heq.
destruct (MMC_error _ _ _ A B)
  as (E1 & eta1 & Heq1 & HE1 & Heta1). {
  move => i j. move :(Hfin i j). clear.
  rewrite /matrix_scaleF mxE => Hfin.
  apply BMULT_finite_e in Hfin; apply Hfin.
}
rewrite Heq1.
exists E1, E, eta1, eta; repeat split =>  //.
move => i j.
move :(HE i j).
rewrite Heq1 //.
Qed.

Theorem mat_sum_error:
  forall m n (A B: 'M[ftype t]_(m,n))
 (Hfin: forall i j, Binary.is_finite (matrix_sumF A B i j)),
  exists EA EB: 'M[R]_(m,n),
     map_mx FT2R (matrix_sumF A B) = 
      (map_mx FT2R A + EA) + (map_mx FT2R B + EB)
  /\ (forall i j, exists d, EA i j = map_mx FT2R A i j * d /\ Rabs d <= @default_rel t)
  /\ (forall i j, exists d, EB i j = map_mx FT2R B i j * d /\ Rabs d <= @default_rel t).
Proof.
intros.
destruct (matrix_sumF_mixed_error A B Hfin) as [EA [EB [Heq [HA HB]]]].
exists EA, EB; repeat split; auto.
Qed.

Theorem mat_axpby_error:
 forall [m n] (A B: 'M[ftype t]_(m,n)) (x y: ftype t)
 (Hfin: forall i j, Binary.is_finite (matrix_sumF (matrix_scaleF x A) (matrix_scaleF y B) i j)),
 exists EA EB ea eb eta1 eta2: 'M[R]_(m,n),
     map_mx FT2R (matrix_sumF (matrix_scaleF x A) (matrix_scaleF y B)) = 
     scalemx (FT2R x) (map_mx FT2R A + EA) + eta1 + ea
     + scalemx (FT2R y) (map_mx FT2R B + EB) + eta2 + eb
    /\ (forall i j, Rabs (EA i j) <= @default_rel t * Rabs (map_mx FT2R A i j))
    /\ (forall i j, Rabs (EB i j) <= @default_rel t * Rabs (map_mx FT2R B i j))
    /\ (forall i j, exists d, ea i j = (scalemx (FT2R x) (map_mx FT2R A + EA) + eta1) i j * d
                /\ Rabs d <= @default_rel t)
    /\ (forall i j, exists d, eb i j = (scalemx (FT2R y) (map_mx FT2R B + EB) + eta2) i j * d
                /\ Rabs d <= @default_rel t)
    /\ (forall i j, Rabs (eta1 i j) <= @default_abs t)
    /\ (forall i j, Rabs (eta2 i j) <= @default_abs t).
Proof.
move => m n A B x y Hfin.
destruct (mat_sum_error _ _ (matrix_scaleF x A) (matrix_scaleF y B))  
  as (ea & eb & HEQ & H1 & H2) => //.
destruct (scaleM_error _ _ A x) as
  (EA & eta1 & Heqx & H6 & H7) => //.
{ move => i j; move :(Hfin i j); clear. rewrite /matrix_sumF mxE => Hfin.
  apply BPLUS_finite_e in Hfin; apply Hfin.
}
destruct (scaleM_error _ _ B y) as
  (EB & eta2 & Heqy & H12 & H13) => //.
{ move => i j; move :(Hfin i j); clear. rewrite /matrix_sumF mxE => Hfin.
  apply BPLUS_finite_e in Hfin; apply Hfin.
}
rewrite {}HEQ.
rewrite {}Heqx in H1|-*.
rewrite {}Heqy in H2|-*.
exists EA, EB, ea, eb, eta1, eta2;
  repeat split => //.
rewrite !addrA //.
Qed.


Theorem GEMM_error:
  forall [m n p] (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,p)) (Y: 'M[ftype t]_(m,p))
        (s1 s2: ftype t)
  (Hfin: forall i j, Binary.is_finite (matrix_sumF (matrix_scaleF s1 (matrix_mulF A B)) (matrix_scaleF s2 Y) i j)),
  exists ab1 ab2 ab3 ab4 ab5 y1 y2 y3: 'M[R]_(m,p),
    map_mx FT2R (matrix_sumF (matrix_scaleF s1 (matrix_mulF A B)) (matrix_scaleF s2 Y)) =
    (scalemx (FT2R s1) ((((map_mx FT2R A *m map_mx FT2R B)+ ab1) + ab2) + ab3) + ab4) + ab5 +
   ((scalemx (FT2R s2) (map_mx FT2R Y + y1) + y2) + y3)
 /\ (forall k: 'I_p, exists E0, 
        col k ab1 = E0 *m col k (map_mx FT2R B) /\ 
        (forall i j, Rabs (E0 i j) <= g n * Rabs (map_mx FT2R A i j)))
 /\ (forall i j, Rabs (ab2 i j) <= g1 n n)
 /\ (forall i j, Rabs (ab3 i j) <= @default_rel t * Rabs ((((map_mx FT2R A *m map_mx FT2R B) + ab1) + ab2)%Ri i j))
 /\ (forall i j, Rabs (y1 i j) <= @default_rel t * Rabs (map_mx FT2R Y i j))
 /\ (forall i j, exists d, ab5 i j = (scalemx (FT2R s1) ((((map_mx FT2R A *m map_mx FT2R B) + ab1) + ab2) + ab3 )+ ab4) i j * d
              /\ Rabs d <= @default_rel t)
 /\ (forall i j, exists d, y3 i j = (scalemx (FT2R s2) (map_mx FT2R Y + y1) + y2) i j * d 
             /\ Rabs d <= @default_rel t)
 /\ (forall i j, Rabs (ab4 i j) <= @default_abs t)
 /\ (forall i j, Rabs (y2 i j) <= @default_abs t).
Proof.
intros.
(* compose errors from axpby and MMC *)
destruct (mat_axpby_error (matrix_mulF A B) Y s1 s2)  
  as (ab3 & y1 & ab5 & y3 & ab4 & y2 & Heq1 & Hab3 & Hy1 & Hab5 & Hy3 & Hab4 & Hy2) => //.
destruct (MMC_error _ _ _ A B)  
  as (ab1 & ab2 & Heq2 & Hab1 & Hab2) => //. 
{ clear - Hfin. move => i j. move :(Hfin i j). rewrite /matrix_sumF mxE => H.
  apply BPLUS_finite_e in H. destruct H as [H _].
  rewrite /matrix_scaleF mxE in H.
  apply BMULT_finite_e in H; apply H.
}
rewrite {}Heq1.
rewrite {}Heq2 in Hab5,Hab3|-*.
exists ab1, ab2, ab3, ab4, ab5, y1, y2, y3; repeat split => //.
repeat split => //.
- rewrite !addrA //.
Qed.

End MMERROR.



