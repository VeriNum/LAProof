From LAProof.accuracy_proofs Require Import preamble common
      dotprod_model sum_model dot_acc float_acc_lems mv_mathcomp gemv_acc.

Section WithNans.
Context {NAN: FPCore.Nans} {t : FPStdLib.type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Definition matrix_scaleF [m n] (a: ftype t) (M: 'M[ftype t]_(m,n)) :=
  map_mx (BMULT a) M.

Lemma matrix_scaleF_mixed_error:
 forall [m n] (a: ftype t) (v: 'M[ftype t]_(m,n))
   (Hfin: forall i j, Binary.is_finite (matrix_scaleF a v i j)),
    let vr:= map_mx FT2R v in
  exists (e eta: 'M[R]_(m,n)),
   map_mx FT2R (matrix_scaleF a v) = (scalemx (FT2R a) (vr + e) + eta)%Ri
  /\ (forall i j, exists d, e i j = vr i j * d /\ Rabs d <= @default_rel t)
  /\ (forall i j, Rabs (eta i j) <= @default_abs t).
Proof.
intros.
unfold matrix_scaleF.
pose F (i: 'I_m) (j: 'I_n) (x: R*R) :=
  let '(e,eta) := x in
  FT2R (@BMULT NAN _ a (v i j)) = FT2R a * (FT2R (v i j) + e) + eta /\
  (exists d:R, e = vr i j * d /\ Rabs d <= @default_rel t) /\
  Rabs eta <= @default_abs t.
assert (forall i j, exists e eta, F i j (e,eta)). {
 intros i j.
 subst F. simpl.
 subst vr.
 rewrite !mxE.
 specialize (Hfin i j). rewrite mxE in Hfin.
 set (x := fun_of_matrix v i j) in Hfin|-*. simpl in x. clearbody x.
 destruct (BMULT_accurate a x) as (del & eps & HD & HE & HF & Heq).
 by apply is_finite_BMULT_no_overflow.
rewrite {}Heq.
remember ((FT2R x) * del)%Re as d.
 exists d, eps.
 repeat split.
 change  (FT2R a * FT2R x * (1 + del) + eps = FT2R a * (FT2R x + d) + eps)%Re.
 nra.
 exists del; split; auto.
 apply /RleP; auto.
 apply /RleP; auto.
}
destruct (exists_mx F).
intros; destruct (H i j) as [e [eta H']]. exists (e,eta); auto.
exists (map_mx fst x), (map_mx snd x).
subst F. subst vr.
repeat split.
-
apply matrixP; intros i j; specialize (H0 i j); simpl in H0.
rewrite !mxE in H0|-*.
destruct (fun_of_matrix x i j); simpl.
destruct H0 as [? [? ?]].
apply H0.
-
intros i j; specialize (H0 i j); simpl in H0.
rewrite !mxE in H0|-*.
destruct (fun_of_matrix x i j); simpl.
destruct H0 as [? [? ?]].
auto.
-
intros i j; specialize (H0 i j); simpl in H0.
rewrite !mxE in H0|-*.
destruct (fun_of_matrix x i j); simpl.
destruct H0 as [? [? ?]].
auto.
Qed.

Definition matrix_sumF [m n] (A B: 'M[ftype t]_(m,n)) : 'M[ftype t]_(m,n) :=
  \matrix_(i,j) BPLUS (A i j) (B i j).

Lemma matrix_sumF_mixed_error :
  forall [m n] (A B: 'M[ftype t]_(m,n))
    (Hfin: forall i j, Binary.is_finite (matrix_sumF A B i j)),
    let Ar:= map_mx FT2R A in
    let Br:= map_mx FT2R B in
  exists (e1 e2 : 'M[R]_(m,n)),
   map_mx FT2R (matrix_sumF A B) = ((Ar + e1) + (Br + e2))%Ri
 /\ (forall i j, exists d, e1 i j = Ar i j * d /\ Rabs d <= @default_rel t)
 /\ (forall i j, exists d, e2 i j = Br i j * d /\ Rabs d <= @default_rel t).
Proof.
intros.
pose F (i: 'I_m) (j: 'I_n) (e12: R*R) :=
 let '(e1,e2) := e12 in
 FT2R (@BPLUS NAN t (A i j) (B i j)) = ((Ar i j + e1) + (Br i j + e2))
 /\ (exists d, e1 = Ar i j * d /\ Rabs d <= @default_rel t)
 /\ (exists d, e2 = Br i j * d /\ Rabs d <= @default_rel t).

assert (forall i j, exists e1 e2, F i j (e1,e2)). {
subst F.
intros i j. simpl. specialize (Hfin i j). subst Ar. rewrite !mxE. rewrite mxE in Hfin.
set (a := A  i j) in Hfin|-*. clearbody a.
set (b := B  i j) in Hfin|-*. clearbody b.
destruct (BPLUS_finite_e _ _ Hfin) as [Ha Hb].
destruct (BPLUS_accurate' _ _ Hfin) as (del & HD &  Heq).
rewrite {}Heq.
exists (FT2R a * del), (FT2R b * del).
repeat split.
change ((FT2R a + FT2R b) * (1 + del) =
              FT2R a + FT2R a * del + (FT2R b + FT2R b * del))%Re.
lra.
exists del; split; auto.
apply /RleP; auto.
exists del; split; auto.
apply /RleP; auto.
}
destruct (exists_mx F).
intros; destruct (H i j) as [e1 [e2 H']]. exists (e1,e2); auto.
exists (map_mx fst x), (map_mx snd x).
subst F.
repeat split.
-
apply matrixP; intros i j; specialize (H0 i j); simpl in H0.
rewrite !mxE in H0|-*.
destruct (fun_of_matrix x i j); simpl.
destruct H0 as [? [? ?]].
apply H0.
-
intros i j; specialize (H0 i j); simpl in H0.
rewrite !mxE in H0|-*.
destruct (fun_of_matrix x i j); simpl.
destruct H0 as [? [? ?]].
auto.
-
intros i j; specialize (H0 i j); simpl in H0.
rewrite !mxE in H0|-*.
destruct (fun_of_matrix x i j); simpl.
destruct H0 as [? [? ?]].
auto.
Qed.


Lemma Smat_sumF_mixed_error :
  forall [m n] (u v: 'M[ftype t]_(m,n)) (a b : ftype t)
    (Hfin : forall i j, Binary.is_finite (matrix_sumF (matrix_scaleF a u) (matrix_scaleF b v) i j)),
    let vr:= map_mx FT2R v in
    let ur:= map_mx FT2R u in
  exists (e1 e2 e3 e4 e5 e6: 'M[R]_(m,n)),
  map_mx FT2R (matrix_sumF (matrix_scaleF a u) (matrix_scaleF b v)) = 
             ((scalemx (FT2R a) (ur + e1) + e2 + e3) +
             (scalemx (FT2R b) (vr + e4) + e5 + e6))%Ri
  /\ (forall i j, exists d, e1 i j = ur i j * d /\ Rabs d <= @default_rel t)
  /\ (forall i j, exists d, e4 i j = vr i j * d /\ Rabs d <= @default_rel t)
  /\ (forall i j, exists d, e3 i j = (scalemx (FT2R a) (ur + e1) + e2) i j * d /\ Rabs d <= @default_rel t)%Ri
  /\ (forall i j, exists d, e6 i j = (scalemx (FT2R b) (vr + e4) + e5) i j * d /\ Rabs d <= @default_rel t)%Ri
  /\ (forall i j, Rabs (e5 i j) <= @default_abs t)
  /\ (forall i j, Rabs (e2 i j) <= @default_abs t).
Proof.
intros.
simpl.
destruct (matrix_sumF_mixed_error _ _ Hfin) as (Du & Dv & Heq & HD).
rewrite {}Heq.
destruct (matrix_scaleF_mixed_error a u) as (ae & aeta & Heqa & Hea & Haeta).
intros. specialize (Hfin i j); rewrite mxE in Hfin. destruct (BPLUS_finite_e _ _ Hfin); auto.
destruct (matrix_scaleF_mixed_error b v) as [be [beta [Heqb [Heb Hbeta]]]].
intros. specialize (Hfin i j); rewrite mxE in Hfin. destruct (BPLUS_finite_e _ _ Hfin); auto.
move :HD; rewrite {}Heqa {}Heqb => HD.
destruct HD as [HDu HDv].
exists ae, aeta ,Du, be, beta, Dv.
repeat split => //.
Qed.

Definition mc_dotprodF [n: nat] (x: 'rV[ftype t]_n) (y: 'cV[ftype t]_n) : ftype t :=
   \big[BPLUS / pos_zero]_i (BMULT (x ord0 (rev_ord i)) (y (rev_ord i) ord0)).

Definition matrix_mulF [m n p] (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,p)) :=
 \matrix_(i,k) mc_dotprodF (row i A) (col k B).

Lemma Smat_vec_mul_mixed_error:
  forall [m n] (b: ftype t) (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,1))
  (Hfin: forall i j, Binary.is_finite (matrix_scaleF b (matrix_mulF A B) i j)),
  exists (E : 'M[R]_(m,n)) (e eta1 eta2 : 'M[R]_(m,1)),
    map_mx FT2R (matrix_scaleF b (matrix_mulF A B)) =
     (scalemx (FT2R b) ((map_mx FT2R A + E)  *m (map_mx FT2R B) + eta1 + e) + eta2 )%Ri
    /\ (forall i j, Rabs (E i j) <= g n * Rabs (map_mx FT2R A i j))
    /\ (forall i j, Rabs (eta2 i j) <= @default_abs t)
    /\ (forall i j, exists d,  e i j = FT2R (matrix_mulF A B i j) * d /\ Rabs d <= @default_rel t)
    /\ (forall i j, Rabs (eta1 i j) <= g1 n n). 
Proof.
intros.
destruct (matrix_scaleF_mixed_error _ _ Hfin) as (e & eta & Heq & Hea & Hetaa).
rewrite {}Heq in Hea|-*.
destruct (mat_vec_mul_mixed_error A B)
  as (E & eta1 & Heq1 & H1).
{ clear - Hfin. move => i j. move :(Hfin i j). rewrite !mxE => H.
 apply BMULT_finite_e in H. apply H.
}
rewrite {}Heq1.
destruct H1 as [H0 H1].
exists E, e, eta1, eta; repeat split => //.
simpl.
move => i j. destruct (Hea i j) as [d H2].
exists d.
rewrite !mxE. rewrite mxE in H2.
unfold matrix_mulF in H2.
rewrite mxE in H2.
auto.
Qed.


Lemma gemv_error:
 forall [m n] (A: 'M[ftype t]_(m,n)) (x: 'cV[ftype t]_n) (y: 'cV[ftype t]_m) (s1 s2: ftype t)
 (Hfin:  forall i j, Binary.is_finite (matrix_sumF (matrix_scaleF s1 (matrix_mulF A x)) (matrix_scaleF s2 y) i j)),
  exists e1 e2 e3 e4 e5 e6 e7 e8,
    map_mx FT2R (matrix_sumF (matrix_scaleF s1 (matrix_mulF A x)) (matrix_scaleF s2 y)) =  
  ((scalemx (FT2R s1) ((((map_mx FT2R A + e1) *m (map_mx FT2R x)) + e2) + e3) + e4) + e5) +
  ((scalemx (FT2R s2) (map_mx FT2R y + e6) + e7) + e8)
  /\ (forall i j, Rabs (e1 i j) <= g n * Rabs (map_mx FT2R A i j))
  /\ (forall i j, Rabs (e2 i j) <= g1 n n)
  /\ (forall i j, exists d, e3 i j = (((map_mx FT2R A + e1) *m map_mx FT2R x) + e2)%Ri  i j * d /\ Rabs d <= @default_rel t)
  /\ (forall i j, exists d, e6 i j = map_mx FT2R y i j * d /\ Rabs d <= @default_rel t)
  /\ (forall i j, exists d, e5 i j = (scalemx (FT2R s1) ((((map_mx FT2R A + e1) *m map_mx FT2R x) + e2) + e3) + e4) i j * d
           /\ Rabs d <= @default_rel t)
  /\ (forall i j, exists d, e8 i j = (scalemx (FT2R s2) (map_mx FT2R y + e6) + e7) i j * d /\ Rabs d <= @default_rel t)
  /\ (forall i j, Rabs (e7 i j) <= @default_abs t)
  /\ (forall i j, Rabs (e4 i j) <= @default_abs t).
Proof.
intros.
(* proof follows from previous bounds for axpby and mul *)
destruct (Smat_sumF_mixed_error (matrix_mulF A x) y s1 s2)
  as (e3 & e4 & e5 & e6 & e7 & e8 & Heq1 & H1) => //.
rewrite {}Heq1.
destruct (mat_vec_mul_mixed_error A x)
  as (e1 & e2 & Heq2 & H2).
{ move => i j. move :(Hfin i j). rewrite !mxE => H.
  apply BPLUS_finite_e in H.  destruct H. 
  apply BMULT_finite_e in H. apply H.
}
rewrite {}Heq2 in H1|-*. 
destruct H2 as (He1 & He2).
destruct H1 as (He3 & He6 & He5 & He4 & He7 & He8).
simpl in *.
exists e1, e2, e3, e4, e5, e6, e7, e8; repeat split => /= //.
Qed.

End WithNans.




