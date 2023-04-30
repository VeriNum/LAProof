Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common op_defs dotprod_model sum_model.
Require Import dot_acc float_acc_lems list_lemmas.
Require Import gem_defs mv_mathcomp gemv_acc vec_op_acc.

From mathcomp.analysis Require Import Rstruct.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
Require Import mc_extra2.

From Coq Require Import ZArith Reals Psatz.
From Coq Require Import Arith.Arith.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Section MMERROR. 
(* forward error matrix multiplication *)
Context {NAN: Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A B: @matrix (ftype t)) (n : nat).

Notation Ar := (map_mat FT2R A).
Notation Br := (map_mat FT2R B).
Notation m := (length A). (* m x n row matrix*)
Notation p := (length B). (* n x p col matrix*)

Hypothesis Hn : forall x, In x A -> length x = n.
Hypothesis Hp : forall x, In x B -> length x = n.
Hypothesis Hfin: is_finite_mat (MMCF A B).

Theorem MMC_error:
  exists (E eta: matrix),
     map_mat FT2R (MMCF A B) = MMCR Ar Br +m E +m eta
    /\ (forall k , (k < p)%nat-> 
      exists (E0 : matrix) ,
      (* the p elements of E are cols of length m *)
      List.nth k E [] = E0 *r (List.nth k Br []) /\ 
      (* the m elements of E0 are rows of length n *)
      (forall i j, (i < m)%nat -> (j < n)%nat ->
      Rabs (E0 _(i,j)) <= g n * Rabs (Ar _(i,j))))
    /\ (forall i j, (i < p)%nat -> (j < m)%nat -> 
      Rabs (eta _(i,j)) <= g1 n n) 
    /\ size_col E m p
    /\ size_col eta m p.
Proof.
revert Hfin Hn Hp. revert A n.  
elim: B.
{ rewrite /MMCF/MMCR/MMC/MV. 
exists [],[]. repeat split => //=. }
clear B. move => b B IH A. intros => /=.
destruct (mat_vec_mul_mixed_error A b) as
  (E & eta & Heq1 & HE & Heta & H1 & H2).
{ apply is_finite_mat_cons in Hfin; by destruct Hfin. }
{ move => row Hr. rewrite Hn => //=.
by rewrite Hp => //=; left. }
rewrite Heq1.
rewrite CommonSSR.map_map_equiv.
rewrite MVR_dist. 
destruct (IH A n) as 
  (E' & eta' & Heq & HE' & Heta' & H3 & H4).
{ apply is_finite_mat_cons in Hfin; by destruct Hfin. }
{ move => x Hx. 
by apply Hn. } 
{ move => x Hx. 
by apply Hp; right. }
rewrite Heq. clear IH.
have Hb : length b = n.
rewrite Hp => //=; by left.
destruct H1; destruct H3; destruct H4.
exists 
  ((E *r List.map FT2R b) :: E'), (eta :: eta');
repeat split => /=; try lia.
{ intros. rewrite /matrix_index.
destruct k => //=.
exists E ; split => //.
rewrite Hb in HE. by apply HE. 
have Hk : is_true (k < p)%nat by lia.
destruct (HE' k Hk) as (E0 & Heq2 & HE0). 
exists E0; split => //. }
{ intros. rewrite /matrix_index.
destruct i => /=. 
rewrite Hb in Heta. 
apply Heta.
apply nth_In;
 rewrite H2 => //; lia.
apply Heta' => //. }
{ move => x [|] Hx. 
rewrite -Hx. 
by rewrite !map_length.
by apply H3. } 
{ move => x [|] Hx. 
by rewrite -Hx. 
by apply H5. } 
move => a b0 Ha Hb0.
destruct H1.
apply in_map_iff in Ha. 
destruct Ha as (x & Hx &Hx').
rewrite -Hx map_length.
symmetry; apply  (H0 b0 x Hb0 Hx').
Qed.

End MMERROR.


Section SCALE_M_ERROR.
(* mixed error matrix scaling *)
Context {NAN: Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A : @matrix (ftype t)).
Variable (x : ftype t) (n: nat).

Notation m := (length A).
Hypothesis Hp : forall x, In x A -> length x = n. (* A is (m x n) *)
Hypothesis Hfin: is_finite_mat (scaleMF x A).

Notation Ar := (map_mat FT2R A).

Theorem scaleM_error:
  exists (E eta: matrix),
     map_mat FT2R (scaleMF x A) = scaleMR (FT2R x) (Ar +m E) +m eta
    /\ (forall i j, (i < m)%nat -> (j < n)%nat -> 
      Rabs (E _(i,j)) <= g n * Rabs (Ar _(i,j))) 
    /\ (forall i j, (i < m)%nat -> (j < n)%nat -> 
      Rabs (eta _(i,j)) <= g1 n n) 
    /\ eq_size E A 
    /\ eq_size eta A.
Proof.
revert Hfin Hp. revert x n.
elim: A => /=.
{ intros. exists [], [] => //. }
clear A.  move => a A IH; intros.
destruct (IH x n) as (E & eta & Heq & IH'); clear IH.
{ move: Hfin. apply is_finite_mat_cons. } 
{ by intros; apply Hp; right. }
rewrite Heq. clear Heq. 
destruct (scaleV_mixed_error a x) as 
  (e & eta1 & Heq & HE & HF).
{ move: Hfin. apply is_finite_mat_cons. } 
rewrite !CommonSSR.map_map_equiv/= in Heq.
rewrite Heq; clear Heq.
have Ha : length a = n by apply Hp; left.
destruct IH' as (IH1 & IH2).
destruct IH2 as (IH2 & IH3 & IH4).
exists (e :: E), (eta1 :: eta);
  repeat split => //. 
{  intros. rewrite /matrix_index.
destruct i => /=.
destruct (HE j) as (del & Heq & HE').
rewrite Ha. lia.
rewrite Heq !CommonSSR.map_map_equiv.
rewrite Rabs_mult Rmult_comm -Ha. 
apply ler_pmul => //; apply /RleP; try apply Rabs_pos.
apply IH1; lia.  } 
{ intros. rewrite /matrix_index.
destruct i => /=.
rewrite -Ha. 
destruct HF as (HF & HF1& HF2).
apply (HF (List.nth j eta1 0%Re)).
apply nth_In. rewrite HF2 Ha; lia.
apply IH2; lia. } 
{ rewrite /eq_size in IH3. 
destruct IH3 as ( H & _).
simpl; by rewrite H. } 
{ move => x0 y0 [|]Hx [|]Hy. 
rewrite -Hx -Hy. 
destruct HF as (_ & HF & _) => //.
rewrite -Hx. rewrite Hp.
destruct HF as (_ & HF & _); lia. 
by right. rewrite -Hy.
destruct IH3. 
destruct E => //.
have Hz : (0 < m)%coq_nat by (simpl in H; lia).
rewrite (H0 x0 (List.nth 0 A [])). 
rewrite Hp => //. right.
apply nth_In; apply Hz. 
apply Hx.
by apply nth_In.
destruct IH3 as (_ & IH3). 
apply IH3 => //. } 
{ simpl. destruct IH4 as (IH4 & _); lia. }
{ move => x0 y0 [|]Hx [|]Hy. 
rewrite -Hx -Hy. 
destruct HF as (_ & _ & HF) => //.
rewrite -Hx. rewrite Hp.
destruct HF as (_ & _ & HF); lia. 
by right. rewrite -Hy.
destruct IH4. 
destruct eta => //.
have Hz : (0 < m)%coq_nat by (simpl in H; lia).
rewrite (H0 x0 (List.nth 0 A [])). 
rewrite Hp => //. right.
by apply nth_In. apply Hx.
apply nth_In; apply Hz.
destruct IH4 as (_ & IH4). 
apply IH4 => //. }
Qed.

End SCALE_M_ERROR.


Section SMMERROR. 
(* forward error matrix multiplication *)
Context {NAN: Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A B: @matrix (ftype t)) (n : nat) (x: ftype t).

Notation Ar := (map_mat FT2R A).
Notation Br := (map_mat FT2R B).
Notation xr := (FT2R x).
Notation m := (length A). (* m x n row matrix*)
Notation p := (length B). (* n x p col matrix*)

Hypothesis Hn : forall x, In x A -> length x = n.
Hypothesis Hp : forall x, In x B -> length x = n.
Hypothesis Hfin: is_finite_mat (scaleMF x (MMCF A B)).

Theorem sMMC_error:
  exists (E1 E eta1 eta: matrix),
     map_mat FT2R (scaleMF x (MMCF A B)) = 
       scaleMR xr (((MMCR Ar Br +m E1) +m eta1) +m E) +m eta
    /\ (forall k , (k < p)%nat-> 
      exists (E0 : matrix) ,
      (* the p elements of E are cols of length m *)
      List.nth k E1 [] = E0 *r (List.nth k Br []) /\ 
      (* the m elements of E0 are rows of length n *)
      (forall i j, (i < m)%nat -> (j < n)%nat ->
      Rabs (E0 _(i,j)) <= g n * Rabs (Ar _(i,j))))
    /\ (forall i j, (i < p)%nat -> (j < m)%nat -> 
      Rabs (eta1 _(i,j)) <= g1 n n) 
    /\ forall i j : nat,(i < p)%nat -> (j < m)%nat -> 
       Rabs (matrix_index eta1 i j 0%Re) <= g1 n n
    /\ forall i j : nat, (i < p)%nat -> (j < m)%nat ->
      Rabs (matrix_index E i j 0%Re) <=
     g m * Rabs (matrix_index ((MMCR Ar Br +m E1) +m eta1) i j 0%Re)
    /\ size_col E1 m p
    /\ size_col eta1 m p
    /\ eq_size E (MMCF A B)
    /\ eq_size eta (MMCF A B).
Proof.
destruct (scaleM_error (MMCF A B) x m)
  as (E & eta & Heq & HE & Heta & H1 & H2).
apply in_MMC_length => //.
apply Hfin.
rewrite Heq.
destruct (MMC_error A B n)
  as (E1 & eta1 & Heq1 & HE1 & Heta1 & H3 & H4).
by intros; apply Hn. 
by intros; apply Hp. 
by apply (is_finite_scaleM x).
rewrite Heq1.
exists E1, E, eta1, eta; split =>  //.
split =>  //.
split =>  //.
split =>  //.
apply Heta1 => //.
split =>  //.
rewrite !map_length in HE.
rewrite Heq1 in HE.
apply HE => //. 
Qed.

End SMMERROR.

Section MATADDERROR.

(* mixed error matrix addition *)
Context {NAN: Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A B: @matrix (ftype t)).
Variable (n : nat).

Notation m := (length A).
Hypothesis Hn : forall x, In x A -> length x = n. (* A is (m x n) *)
Hypothesis HA : eq_size A B.
Hypothesis Hfin: is_finite_mat (mat_sumF A B).

Notation Ar := (map_mat FT2R A).
Notation Br := (map_mat FT2R B).

Theorem mat_sum_error:
  exists (EA EB: matrix),
     map_mat FT2R (mat_sumF A B) = mat_sumR (Ar +m EA) (Br +m EB)
    /\ (forall i j, (i < m)%nat -> (j < n)%nat -> 
        exists d,  (EA _(i,j)) =  (Ar _(i,j)) *  d /\
         Rabs d <= @default_rel t) 
    /\ (forall i j, (i < m)%nat -> (j < n)%nat -> 
       exists d,  (EB _(i,j)) =  (Br _(i,j)) *  d /\
         Rabs d <= @default_rel t)
    /\ eq_size EA A 
    /\ eq_size EB A .
Proof.
revert HA Hfin Hn. revert n B.
elim : A. 
{ intros. exists [], [] => //=. }
clear A; move => a A IH n B.
case: B => //.
{ by intros; destruct HA. }
clear B. move => b B. intros.
destruct (IH n B) as 
  (EA & EB & HEQ & IH1 & IH2 & IH3 & IH4);
  clear IH.
{ by apply (eq_size_cons a b). } 
{ move : Hfin. 
rewrite /mat_sumF/mat_sum/map2/=.
apply is_finite_mat_cons. }
{ intros; apply Hn => /=; by right. }
simpl.  rewrite HEQ.  clear HEQ.
destruct (vec_sumF_mixed_error a b)
  as (e1 & e2 & Heq & He1 & He2 & He).
{ move : Hfin. 
rewrite /mat_sumF/mat_sum/map2/=.
apply is_finite_mat_cons. }
{ by apply (eq_size_cons a b A B). } 
have Hb : length b = n.
{ apply eq_size_cons in HA.
destruct HA as (_ & HA').
rewrite -HA'. apply Hn => /=. by left. }
rewrite !CommonSSR.map_map_equiv in Heq.
rewrite Heq. clear Heq.
exists (e1 :: EA), (e2 :: EB);
  repeat split => //=.
{  intros. rewrite /matrix_index.
destruct i => /=.
destruct (He1 j) as (del & Heq & HE').
rewrite Hb. lia.
rewrite Heq !CommonSSR.map_map_equiv.
by exists del; split. 
apply IH1; lia.  } 
{  intros. rewrite /matrix_index.
destruct i => /=.
destruct (He2 j) as (del & Heq & HE').
rewrite Hb. lia.
rewrite Heq !CommonSSR.map_map_equiv.
exists del => //.
apply IH2; lia. }
(* remaining is reasoning about lengths *)
{ rewrite /eq_size in IH3. 
destruct IH3 as ( H & _).
simpl; by rewrite H. } 
{ move => x0 y0 [|]Hx [|]Hy. 
rewrite -Hx -Hy. 
destruct He  => //.
rewrite -Hx. rewrite Hn.
destruct He as (He & _); 
  rewrite He. apply Hn => /=; 
by left.  
by simpl; right.
rewrite -Hy. rewrite Hn.
destruct IH3. 
destruct EA => //.
have Hz : (0 < m)%coq_nat by (simpl in H; lia).
rewrite (H0 x0 (List.nth 0 A [])). 
rewrite Hn => //. right.
apply nth_In; apply Hz. 
apply Hx.
by apply nth_In. simpl; by left.
destruct IH3 as (_ & IH3). 
apply IH3 => //. } 
{ simpl. destruct IH4 as (IH4 & _); lia. }
{ move => x0 y0 [|]Hx [|]Hy. 
rewrite -Hx -Hy. 
destruct He => //.
rewrite H0. rewrite Hb.
symmetry; apply Hn => /=. by left.
rewrite -Hx. rewrite Hn.
destruct He; lia.
simpl; by right.
rewrite -Hy.
destruct IH4. 
destruct EB => //.
have Hz : (0 < m)%coq_nat by (simpl in H; lia).
rewrite (H0 x0 (List.nth 0 A [])) => //. 
rewrite Hn => //.
symmetry; apply Hn.
simpl; by left.
simpl; right.
by apply nth_In.
by apply nth_In.
destruct IH4 as (_ & IH4).
apply IH4 => //. } 
Qed.


End MATADDERROR.


Section SMATADDERROR.

Context {NAN: Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A B: @matrix (ftype t)).
Variables (x y : ftype t).
Variable (n : nat).

Notation m := (length A).
Hypothesis Hn : forall x, In x A -> length x = n. (* A is (m x n) *)
Hypothesis Hn2 : forall x, In x B -> length x = n. (* B is (m x n) *)
Hypothesis HA : eq_size A B.
Hypothesis Hfin: is_finite_mat (mat_sumF (scaleMF x A) (scaleMF y B)).

Notation Ar := (map_mat FT2R A).
Notation Br := (map_mat FT2R B).

Theorem Smat_sum_error:
  exists (EA EB ea eb eta1 eta2: matrix),
     map_mat FT2R (mat_sumF (scaleMF x A) (scaleMF y B)) = 
     mat_sumR (scaleMR (FT2R x) (Ar +m EA) +m eta1 +m ea) 
          (scaleMR (FT2R y) (Br +m EB) +m eta2 +m eb)
    /\ (forall i j : nat, (i < m)%nat -> (j < n)%nat ->
      Rabs (matrix_index EA i j 0%R) <=
      g n * Rabs (matrix_index Ar i j 0%R))
    /\ (forall i j : nat, (i < m)%nat -> (j < n)%nat ->
     Rabs (matrix_index EB i j 0%R) <=
     g n * Rabs (matrix_index Br i j 0%R))
    /\ (forall i j : nat, (i < m)%nat -> (j < n)%nat ->
       exists d,
       matrix_index ea i j 0%R =
       matrix_index (scaleMR (FT2R x) (Ar +m EA) +m eta1) i j 0%R * d 
        /\ Rabs d <= @default_rel t)
    /\ (forall i j : nat, (i < m)%nat -> (j < n)%nat ->
       exists d,
       matrix_index eb i j 0%R =
       matrix_index (scaleMR (FT2R y) (Br +m EB) +m eta2) i j 0%R * d
        /\ Rabs d <= @default_rel t)
    /\ forall i j : nat, (i < m)%nat -> (j < n)%nat ->
      Rabs (matrix_index eta1 i j 0%Re) <= g1 n n
    /\ forall i j : nat, (i < m)%nat -> (j < n)%nat ->
      Rabs (matrix_index eta2 i j 0%Re) <= g1 n n
    /\ eq_size EA A 
    /\ eq_size EB A 
    /\ eq_size ea A 
    /\ eq_size eb A 
    /\ eq_size eta1 A 
    /\ eq_size eta2 A .
Proof.
destruct (mat_sum_error (scaleMF x A) (scaleMF y B) n)  
  as (ea & eb & HEQ & H1 & H2 & H3 & H4) => //.
{ apply scaleM_length => //. } 
{ rewrite /eq_size; split. 
rewrite !map_length. by destruct HA.
destruct HA; intros.
rewrite (scaleM_length x A n (@BMULT NAN t)) => //.
symmetry. pose proof (scaleM_length y B n (@BMULT NAN t)) => //.
rewrite H3 => //. }  
have HB: length B = m. destruct HA; lia.
rewrite HEQ.
apply is_finite_mat_sum in Hfin. destruct Hfin.
destruct (scaleM_error A x n) as
  (EA & eta1 & Heqx & H6 & H7 & H8 & H9 & H10) => //. 
destruct (scaleM_error B y n) as
  (EB & eta2 & Heqy & H12 & H13 & H14 & H15) => //.
rewrite Heqx Heqy. 
rewrite Heqx in H1.
rewrite Heqy in H2.
exists EA, EB, ea, eb, eta1, eta2;
  split => //.
  split => //.
  split => //. 
{ intros; apply H12 => //; lia. }
  split => //.
{ rewrite !map_length in H1.
intros. destruct (H1 i j) => //.
exists x0. apply H16. } 
  split => //. 
{ rewrite !map_length in H2.
intros. destruct (H2 i j) => //.
exists x0. apply H16. } 
  split => //.
{ by apply  H7 . }
  split => //.
{ apply H13; lia. } 
  split => //.
  split => //.
{ apply (eq_size_trans EB B A) => //.
by apply eq_size_symm. }
  split => //.
{ apply (eq_size_trans ea (scaleMF x A) A) => //.
  apply (eq_size_scale x A (@BMULT NAN t) n).
  intros; by apply Hn. } 
  split => //.
{ apply (eq_size_trans eb (scaleMF x A) A) => //.
  apply (eq_size_scale x A (@BMULT NAN t) n).
  intros; by apply Hn. } 
split.
rewrite /eq_size; split => //.
{ apply (eq_size_trans eta2 B A) => //.
by apply eq_size_symm. }
apply (eq_size_trans (scaleMF x A) A (scaleMF y B)) => //.
  apply (eq_size_scale x A (@BMULT NAN t) n).
  intros; by apply Hn. 
apply (eq_size_trans A B (scaleMF y B)) => //.
  apply eq_size_symm.
  apply (eq_size_scale y B (@BMULT NAN t) n).
  intros; by apply Hn2. 
Qed.
 

End SMATADDERROR.



