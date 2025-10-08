From LAProof.accuracy_proofs Require Import preamble common 
       dotprod_model sum_model dot_acc float_acc_lems list_lemmas
         gem_defs mv_mathcomp gemv_acc vec_op_acc.

Section MMERROR. 
(* forward error matrix multiplication *)
Context {NAN: FPCore.Nans} {t : FPStdLib.type}.

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
change @map with @List.map.
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
by rewrite !length_map.
by apply H3. } 
{ move => x [|] Hx. 
by rewrite -Hx. 
by apply H5. } 
move => a b0 Ha Hb0.
destruct H1.
apply in_map_iff in Ha. 
destruct Ha as (x & Hx &Hx').
rewrite -Hx length_map.
symmetry; apply  (H0 b0 x Hb0 Hx').
Qed.

End MMERROR.


Section SCALE_M_ERROR.
(* mixed error matrix scaling *)
Context {NAN: FPCore.Nans} {t : FPStdLib.type}.

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
rewrite Heq.
change @map with @List.map.
rewrite Rabs_mult Rmult_comm -Ha.
apply /RleP. 
apply ler_pM => //; apply /RleP; auto; apply Rabs_pos.
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
Context {NAN: FPCore.Nans} {t : FPStdLib.type}.

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
       Rabs (matrix_index 0%Re eta1 i j) <= g1 n n
    /\ forall i j : nat, (i < p)%nat -> (j < m)%nat ->
      Rabs (matrix_index 0%Re E i j) <=
     g m * Rabs (matrix_index 0%Re ((MMCR Ar Br +m E1) +m eta1) i j)
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
rewrite !length_map in HE.
rewrite Heq1 in HE.
apply HE => //. 
Qed.

End SMMERROR.

Section MATADDERROR.

(* mixed error matrix addition *)
Context {NAN: FPCore.Nans} {t : FPStdLib.type}.

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
rewrite Heq. clear Heq.
exists (e1 :: EA), (e2 :: EB);
  repeat split => //=.
{  intros. rewrite /matrix_index.
destruct i => /=.
destruct (He1 j) as (del & Heq & HE').
rewrite Hb. lia.
rewrite Heq.
change @map with @List.map.
by exists del; split. 
apply IH1; lia.  } 
{  intros. rewrite /matrix_index.
destruct i => /=.
destruct (He2 j) as (del & Heq & HE').
rewrite Hb. lia.
rewrite Heq.
change @map with @List.map.
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


Section MATAXPBY.

Context {NAN: FPCore.Nans} {t : FPStdLib.type}.

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

Theorem mat_axpby_error:
  exists (EA EB ea eb eta1 eta2: matrix),
     map_mat FT2R (mat_sumF (scaleMF x A) (scaleMF y B)) = 
     mat_sumR (scaleMR (FT2R x) (Ar +m EA) +m eta1 +m ea) 
          (scaleMR (FT2R y) (Br +m EB) +m eta2 +m eb)
    /\ (forall i j : nat, (i < m)%nat -> (j < n)%nat ->
      Rabs (matrix_index 0%R EA i j) <=
      g n * Rabs (matrix_index 0%R Ar i j))
    /\ (forall i j : nat, (i < m)%nat -> (j < n)%nat ->
     Rabs (matrix_index 0%R EB i j) <=
     g n * Rabs (matrix_index 0%R Br i j))
    /\ (forall i j : nat, (i < m)%nat -> (j < n)%nat ->
       exists d,
       matrix_index 0%R ea i j =
       matrix_index 0%R (scaleMR (FT2R x) (Ar +m EA) +m eta1) i j * d 
        /\ Rabs d <= @default_rel t)
    /\ (forall i j : nat, (i < m)%nat -> (j < n)%nat ->
       exists d,
       matrix_index 0%R eb i j =
       matrix_index 0%R (scaleMR (FT2R y) (Br +m EB) +m eta2) i j * d
        /\ Rabs d <= @default_rel t)
    /\ (forall i j : nat, (i < m)%nat -> (j < n)%nat ->
      Rabs (matrix_index 0%Re eta1 i j) <= g1 n n)
    /\ (forall i j : nat, (i < m)%nat -> (j < n)%nat ->
      Rabs (matrix_index 0%Re eta2 i j) <= g1 n n)
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
rewrite !length_map. by destruct HA.
destruct HA; intros.
rewrite (scaleM_length x A n BMULT) => //.
symmetry. pose proof (scaleM_length y B n BMULT) => //.
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
{ rewrite !length_map in H1.
intros. destruct (H1 i j) => //.
exists x0. apply H16. } 
  split => //. 
{ rewrite !length_map in H2.
intros. destruct (H2 i j) => //.
exists x0. apply H16. } 
  split => //.
  split => //.
{ rewrite HB in H13. by apply  H13 . }
  split => //.
  split => //.
{ apply (eq_size_trans EB B A) => //.
by apply eq_size_symm. }
  split => //.
{ apply (eq_size_trans ea (scaleMF x A) A) => //.
  apply (eq_size_scale x A BMULT n).
  intros; by apply Hn. } 
  split => //.
{ apply (eq_size_trans eb (scaleMF x A) A) => //.
  apply (eq_size_scale x A BMULT n).
  intros; by apply Hn. } 
split.
rewrite /eq_size; split => //.
{ apply (eq_size_trans eta2 B A) => //.
by apply eq_size_symm. }
apply (eq_size_trans (scaleMF x A) A (scaleMF y B)) => //.
  apply (eq_size_scale x A BMULT n).
  intros; by apply Hn. 
apply (eq_size_trans A B (scaleMF y B)) => //.
  apply eq_size_symm.
  apply (eq_size_scale y B BMULT n).
  intros; by apply Hn2. 
Qed.
 

End MATAXPBY.

Section GEMM.
Context {NAN: FPCore.Nans} {t : FPStdLib.type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A B Y: @matrix (ftype t)).
Variables (s1 s2 : ftype t).
Variable (n : nat).

Notation m := (length A). (* m x n row matrix*)
Notation p := (length B). (* n x p col matrix*)
Hypothesis Hn : forall x, In x A -> length x = n. (* A is (m x n) *)
Hypothesis Hp : forall x, In x B -> length x = n. (* B is (n x p) *)
Hypothesis HY : size_col Y m p. (* Y is (m x p) *)
Hypothesis Hfin: is_finite_mat (mat_sumF (scaleMF s1 (MMCF A B)) (scaleMF s2 Y)).

Notation Ar := (map_mat FT2R A).
Notation Br := (map_mat FT2R B).
Notation Yr := (map_mat FT2R Y).

Theorem GEMM_error:
  exists (ab1 ab2 ab3 ab4 ab5 y1 y2 y3: matrix),
     map_mat FT2R (mat_sumF (scaleMF s1 (MMCF A B)) (scaleMF s2 Y)) = 
  ((scaleMR (FT2R s1) (((MMCR Ar Br +m ab1) +m ab2) +m ab3) +m ab4) +m ab5) +m
  ((scaleMR (FT2R s2) (Yr +m y1) +m y2) +m y3)
  /\ (forall k : nat,(k < p)%nat ->
      exists E0 : matrix,
        List.nth k ab1 [::] = E0 *r List.nth k Br [] /\
        (forall i j : nat, (i < m)%nat -> (j < n)%nat ->
         Rabs (matrix_index 0%Re E0 i j) <= g n * Rabs (matrix_index 0%Re Ar i j))) 
  /\ (forall i j : nat, (i < p)%nat -> (j < m)%nat ->
      Rabs (matrix_index 0%Re ab2 i j) <= g1 n n)
  /\ (forall i j : nat, (i < p)%nat -> (j < m)%nat ->
      Rabs (matrix_index 0%Re ab3 i j) <= 
        g m * Rabs (matrix_index 0%Re ((MMCR Ar Br +m ab1) +m ab2) i j)) 
  /\ (forall i j : nat,
      (i < p)%nat -> (j < m)%nat ->
     Rabs (matrix_index 0%Re y1 i j) <=
        g m * Rabs (matrix_index 0%Re Yr i j)) 
  /\ (forall i j : nat, (i < p)%nat -> (j < m)%nat ->
        exists d,
        matrix_index 0%Re ab5 i j =
        matrix_index 0%Re
          (scaleMR (FT2R s1)
             (((MMCR Ar Br +m ab1) +m ab2) +m ab3) +m ab4) i j * d 
          /\ Rabs d <= @default_rel t) 
  /\ (forall i j : nat, (i < p)%nat -> (j < m)%nat ->
      exists d ,
        matrix_index 0%Re y3 i j =
        matrix_index 0%Re
          (scaleMR (FT2R s2) (Yr +m y1) +m y2) i j * d 
          /\ Rabs d <= @default_rel t)
  /\ (forall i j : nat,
      (i < p)%nat -> (j < m)%nat ->
      Rabs (matrix_index 0%Re ab4 i j) <= g1 m m)
  /\ (forall i0 j0 : nat, (i0 < p)%nat -> (j0 < m)%nat ->
       Rabs (matrix_index 0%Re y2 i0 j0) <= g1 m m).
Proof.
(* len hyps for composing errors *)
have Hlen1 : forall v : seq (ftype t),
    In v (MMCF A B) -> length v = m.
{ by apply (in_MMC_length A B BPLUS
  BMULT m (Zconst t 0)). }
have Hleny : forall a : seq (ftype t), In a Y -> length a = m.
{ move : HY. rewrite /size_col; move => HY1; destruct HY1; intros.
by apply H0. } 
have Hlen2 :  eq_size (MMCF A B) Y.
{ move : HY. rewrite /size_col /eq_size; move => HY1; destruct HY1;
  split. by rewrite H !length_map.
intros. symmetry; rewrite H0 => //. by symmetry; apply Hlen1. }
have Hsz : eq_size (scaleMF s1 (MMCF A B)) (scaleMF s2 Y).
{ apply (eq_size_trans (scaleMF s1 (MMCF A B)) (MMCF A B) (scaleMF s2 Y)).
apply (eq_size_scale  s1 (MMCF A B) BMULT m) => //.
apply (eq_size_trans (MMCF A B) Y (scaleMF s2 Y)) => //.
apply eq_size_symm. apply (eq_size_scale  s2 Y BMULT m) => //. } 
(* compose errors from axpby and MMC *)
destruct (mat_axpby_error (MMCF A B) Y s1 s2 m)  
  as (ab3 & y1 & ab5 & y3 & ab4 & y2 & Heq1 & H1) => //.
destruct (MMC_error A B n)  
  as (ab1 & ab2 & Heq2 & H2) => //. 
{ clear H1. apply is_finite_mat_sum in Hfin => //; destruct Hfin.
by apply is_finite_scaleM in H => //. } 
(* invoke errors *)
rewrite Heq2 in H1. rewrite Heq1 Heq2.
rewrite !length_map in H1.
clear Heq1 Heq2.
exists ab1, ab2, ab3, ab4, ab5, y1, y2, y3; split => //.
destruct H2 as (Hab1 & Hab2 & _).
destruct H1 as (Hab3 & Hy1 & Hab5 & Hy3 & Hab4 & Hy2 & _); repeat
split => //.
(* we don't keep lengths for gemm error, but could *)
Qed.

End GEMM.



