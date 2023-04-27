Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common op_defs dotprod_model sum_model.
Require Import dot_acc float_acc_lems list_lemmas.
Require Import gem_defs mv_mathcomp gemv_acc.

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

Section DEFS.
(* TODO : PUT THESE IN GEM_DEFS *)
Definition size_col {T} (A : list (list T)) m n :=
  length A = n /\
  forall a, In a A -> length a = m.

Definition size_row {T} (A : list (list T)) m n :=
  length A = m /\
  forall a, In a A -> length a = n.

End DEFS.

Section LEMS. 
(* TODO : PUT THESE IN GEM_DEFS *)
Context {NAN: Nans} {t : type}.

Lemma dotprodR_dist a b v : 
length a = length b -> 
dotprodR (a +v b) v = (dotprodR a v + dotprodR b v).
Proof.
move: a b.
elim : v => //=.
{ intros.
rewrite! dotprodR_nil_r -!RplusE; nra. } 
move => v0 v IH a. 
case : a => //=.
{ intros. 
symmetry in H.
rewrite length_zero_iff_nil in H.
rewrite H. rewrite !dotprodR_nil_l -!RplusE; nra. } 
move => a0 a b. case b => //=.
intros. 
rewrite /dotprodR. simpl. 
rewrite !fold_left_Rplus_Rplus -RplusE.
specialize (IH a l).
rewrite /dotprodR/vec_sumR/vec_sum/map2 in IH.
rewrite IH; [|lia].  rewrite -!RplusE; nra.
Qed.

Lemma MVR_dist A B v : 
forall (Hlen : forall a b, In a A -> In b B -> 
  length a = length b),  
(A +m B) *r v = (A *r v) +v (B *r v).
Proof.
move : A v.
elim: B => //=.
{intros; rewrite /vec_sumR/vec_sum/map2/= 
  combine_nil map_nil /mat_sumR mat_sum_nil
  /mvR/MV//=. } 
move => b B IH A.
case : A => //=.
move => a A v H.
rewrite IH. clear IH.
rewrite /vec_sumR vec_sum_cons. 
f_equal.
set (y:= vec_sumR a b).
fold (vec_sum Rplus a b).
fold (vec_sumR a b).
apply dotprodR_dist.
apply H; by left.
move => a0 b0 H1 H2.
apply H; by right.
Qed.

Lemma GEMM_nilC {T} (dot : vector -> vector -> T) 
  (sum mul : T -> T -> T) (A B : @gem_defs.matrix T) (x y : T) : 
  GEMM dot sum mul A B [] x y = [].
Proof. by rewrite /GEMM/scaleM mat_sum_nil. Qed.

Lemma GEMM_nilB {T} (dot : vector -> vector -> T) 
  (sum mul : T -> T -> T) (A C : @gem_defs.matrix T) (x y : T) : 
  GEMM dot sum mul A [] C x y = [].
Proof. by rewrite /GEMM/scaleM/MMC/=mat_sum_nil_l. Qed.

Lemma GEMM_cons {T} (dot : vector -> vector -> T) 
  (sum mul : T -> T -> T) 
  (A B C : @gem_defs.matrix T) b c (x y : T) :
let hd := vec_sum sum (scaleV mul x (MV dot A b)) (scaleV mul y c) in
GEMM dot sum mul A (b :: B) (c :: C) x y =  
  hd :: GEMM dot sum mul A B C x y.
Proof. rewrite /GEMM/mat_sum -(vec_sum_cons) /vec_sum /scaleM//=. Qed.

Lemma scaleMR_cons y d D :
scaleMR y (d :: D) = ((scaleVR y d) :: scaleMR y D).
Proof. by []. Qed.


Lemma GEMMR_distC  (A B C D: gem_defs.matrix ) (x y : R) :
(forall c, In c C -> length c = length A) -> 
length C = length B ->
eq_size C D -> 
GEMMR A B (C +m D) x y = (GEMMR A B C x y) +m (scaleMR y D).
Proof.
move : A B C.
elim: D.
{ intros. rewrite /scaleMR/scaleM/=.
by rewrite /mat_sumR !mat_sum_nil/GEMMR GEMM_nilC. } 
move => d D IH A B C. 
case: C => //. 
{ intros. destruct H1 => //. }  
move => c C. 
case: B => //.
move => b B. intros. 
simpl in H0. 
rewrite mat_sumR_cons => //; try lia.
rewrite /GEMMR !GEMM_cons.
fold GEMMR vec_sumR scaleVR.
rewrite IH; try lia. rewrite scaleMR_cons mat_sumR_cons. 
rewrite !(vec_sumR_assoc). 
f_equal. f_equal. 
by rewrite -scaleVR_dist.
rewrite !map_length;
symmetry. by apply H; left. 
rewrite !map_length. 
destruct H1;
by symmetry ;apply H2 => /=; left.
rewrite !map_length combine_length !map_length.
have HB : length B = length C by lia.
have HC : length C = length D .
destruct H1; simpl in H1. lia.
rewrite HB HC. apply Nat.min_id.
intros; apply H => /=; by right.
destruct H1. simpl in H1.
rewrite /eq_size; split; try lia.
intros; apply H2 => /=; by right.
destruct H1; simpl in H1; lia.
Qed.

(* END TODO *)

End LEMS.

Section MMERROR. 
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

Section SCALEERROR.
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
     map_mat FT2R (scaleMF x A) = scaleMR (FT2R x) (Ar +m E)
    /\ (forall i j, (i < m)%nat -> (j < n)%nat -> 
      Rabs (E _(i,j)) <= g n * Rabs (Ar _(i,j))) 
    /\ (forall i j, (i < m)%nat -> (j < n)%nat -> 
      Rabs (eta _(i,j)) <= g1 n n) 
    /\ eq_size E A 
    /\ eq_size eta A.
Proof.
Admitted.

End SCALEERROR.

Section MATADDERROR.
Context {NAN: Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A B: @matrix (ftype t)).
Variable (m n p: nat).

Hypothesis HA : size_row A m n.
Hypothesis HB : size_row B n p.
Hypothesis Hfin: is_finite_mat (mat_sumF A B).

Notation Ar := (map_mat FT2R A).
Notation Br := (map_mat FT2R B).

Theorem mat_sum_error:
  exists (EA EB eta: matrix),
     map_mat FT2R (mat_sumF A B) = (mat_sumR (Ar +m EA) (Br +m EB)) +m eta
    /\ (forall i j, (i < m)%nat -> (j < n)%nat -> 
      Rabs (EA _(i,j)) <= g n * Rabs (Ar _(i,j))) 
   /\ (forall i j, (i < m)%nat -> (j < n)%nat -> 
      Rabs (EB _(i,j)) <= g n * Rabs (Br _(i,j))) 
    /\ (forall i j, (i < m)%nat -> (j < n)%nat -> 
      Rabs (eta _(i,j)) <= g1 n n) 
    /\ eq_size EA A 
    /\ eq_size EB A 
    /\ eq_size eta A.
Proof.

Admitted.

End MATADDERROR.

Section VECSUMERROR.
Context {NAN: Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Lemma vec_sumF_mixed_error :
  forall (u v: @vector (ftype t))
    (Hfinv : is_finite_vec (vec_sumF u v))
    (Hlen : length u = length v),
    let vr:= map FT2R v in
    let ur:= map FT2R u in
    let m := length v in
  exists (e1 e2 : vector),
  map FT2R (vec_sumF u v) = vec_sumR (ur +v e1) (vr +v e2)
  /\ (forall i, (i < m)%nat -> exists d,
      List.nth i e1 0 = (List.nth i ur 0%R) * d
        /\ Rabs d <= g m)
  /\ (forall i, (i < m)%nat -> exists d,
      List.nth i e2 0 = (List.nth i vr 0%R) * d
        /\ Rabs d <= g m)
  /\ length e1   = length u
  /\ length e2   = length v.
Proof.
move => u. 
(* main induction on right vector *)
elim u. 
{ move => v /=; intros. 
exists [], [] => /=; repeat split => //=.
rewrite -Hlen. intros => //.
rewrite -Hlen. intros => //. }  
clear u; move => u0 u IH v.
(* main induction *)
case: v => //. 
move => v0 v. intros. 
rewrite /vec_sumF vec_sum_cons.
have Hfin:  is_finite_vec (vec_sum BPLUS u v) /\
  (Binary.is_finite  _ _ (BPLUS u0 v0) = true).
simpl in Hfinv. rewrite /vec_sumF vec_sum_cons in Hfinv.  
apply is_finite_vec_cons in Hfinv.
destruct Hfinv => //.
destruct Hfin as (H1f & H2f).
rewrite /vec_sumF in IH. 
destruct (IH v) as (e1 & e2 & Heq & H) => //; clear IH.
simpl in Hlen; lia.
simpl; rewrite Heq.
destruct (BPLUS_accurate' u0 v0) as (del & Hd & H1) => //.
rewrite H1; clear H1.
rewrite !CommonSSR.map_map_equiv/=.
exists (((FT2R u0) * del) :: e1), (((FT2R v0) * del) :: e2);
  repeat split. 
{ rewrite /ur/vr/=/vec_sumR !vec_sum_cons.
f_equal. 
rewrite -!RmultE; nra. }
{ move => i Hi; destruct i => /=.
exists del; split => //=.
apply /RleP. 
eapply Rle_trans. 
apply Hd. apply d_le_g_1; lia. 
destruct H as (H & H1).
elim: (H i). 
clear H; move => d' Hd'.
destruct Hd' as (Hd' & Hd'').
exists d'; split => //=.
eapply le_trans. apply Hd''.
unfold m => //=. apply /RleP; auto with commonDB.
unfold m in Hi; simpl in Hi; lia. } 
{ move => i Hi; destruct i => /=.
exists del; split => //=.
apply /RleP. 
eapply Rle_trans. 
apply Hd. apply d_le_g_1; lia. 
destruct H as (_ & H1 & _).
elim: (H1 i). 
clear H1; move => d' Hd'.
destruct Hd' as (Hd' & Hd'').
exists d'; split => //=.
eapply le_trans. apply Hd''.
unfold m => //=. apply /RleP; auto with commonDB.
unfold m in Hi; simpl in Hi; lia. } 
all : simpl; lia. 
Qed.

End VECSUMERROR.

Section SCALEVERROR.
Context {NAN: Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Lemma scaleV_mixed_error :
  forall (v: @vector (ftype t)) (a : ftype t)
    (Hfinv : is_finite_vec (scaleVF a v)),
    let vr:= map FT2R v in
    let m := length v in
  exists (e eta: vector),
  map FT2R (scaleVF a v) =  scaleVR (FT2R a) (vr +v e) +v eta
  /\ (forall i, (i < m)%nat -> exists d,
      List.nth i e 0 = (List.nth i vr 0%R) * d
        /\ Rabs d <= g m) 
  /\ (forall e0, In e0 eta -> Rabs e0 <= g1 m m) 
  /\ length e   = length v
  /\ length eta = length v .
Proof.
move => v.
elim: v => /= [a _|].
{ rewrite /vec_sumR/vec_sum/map2/=. 
  by exists [], []. }
move => v0 v IH. intros. 
have Hfin':  is_finite_vec (scaleVF a v) /\
Binary.is_finite _ _ (BMULT a v0).
  by apply is_finite_vec_cons in Hfinv.
case Hfin' =>  HA HB.
destruct (IH a) as 
  (e & eta & Heq & He & Heta) => //.
clear IH. rewrite Heq. clear Heq.
destruct (BMULT_accurate a v0) as 
  (del & eps & HD & HE & HF & Heq).
by apply is_finite_BMULT_no_overflow.
rewrite Heq. clear Heq.
remember ((FT2R v0) * del) as d.
exists (d :: e), (eps :: eta); repeat split.
{ rewrite /scaleVR/vec_sumR/vec_sum/map2/= Heqd -RmultE;
f_equal; nra. }
{ move => i Hi. rewrite Heqd.
destruct i => /=.
exists del; split; [nra|].
apply /RleP. eapply Rle_trans.
apply HE => /=. rewrite -Nat.add_1_r;
auto with commonDB. 
have Hi': (i < length v)%nat by lia.
destruct (He i Hi') as (x & He' & Hx).
rewrite He'. 
exists x; split => //=. 
eapply le_trans. apply Hx. 
apply /RleP; auto with commonDB. }
move => e0 [Hin| Hin].
{ rewrite -Hin. apply /RleP.
  eapply Rle_trans; [apply HF|].
  apply e_le_g1; lia. }
eapply le_trans. apply Heta => //.
apply /RleP. apply g1n_le_g1Sn'.
all: simpl; lia.
Qed.

End SCALEVERROR.

Section GEMMERROR.
Context {NAN: Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A B C : @matrix (ftype t)).
Variable (x y : ftype t).
Variable (m n p : nat).

Notation Ar := (map_mat FT2R A).
Notation Br := (map_mat FT2R B).
Notation Cr := (map_mat FT2R C).

Hypothesis Hn : forall x, In x A -> length x = n.
Hypothesis Hp : forall x, In x B -> length x = n.
Hypothesis Hfin: is_finite_mat (GEMMF A B C x y).
Hypothesis HA : size_row A m n.
Hypothesis HB : size_col B n p.
Hypothesis HC : size_col C m p.

Theorem GEMM_error:
  exists (EC E eta: matrix),
     map_mat FT2R (GEMMF A B C x y) = 
          (GEMMR Ar Br (Cr +m EC) (FT2R x) (FT2R y)) +m E +m eta
    /\ (forall k , (k < p)%nat-> 
      exists (E0 : matrix) ,
      (* the p elements of E are cols of length m *)
      List.nth k E [] = E0 *r (List.nth k Br []) /\ 
      (* the m elements of E0 are rows of length n *)
      (forall i j, (i < m)%nat -> (j < n)%nat ->
      Rabs (E0 _(i,j)) <= g n * Rabs (Ar _(i,j))))
    /\ (forall i j, (i < p)%nat -> (j < m)%nat -> 
      Rabs (eta _(i,j)) <= g1 n n) 
    /\ eq_size EC C
    /\ size_col E m p
    /\ size_col eta m p.
Proof.
revert Hn HA HB HC Hp Hfin.
revert A C x y m n p.
elim : B. clear B.
{ intros. exists [], [], [].
rewrite /GEMMF/GEMMR GEMM_nilB /mat_sumR/=. 
rewrite GEMM_nilB. rewrite mat_sum_nil; repeat split => //=.
{ intros. exists []; split. 
rewrite /mvR/MV/=. destruct k => //.
intros. rewrite /matrix_index/=.
destruct i; destruct j => //=;
rewrite Rabs_R0 -RmultE; apply mulr_ge0; apply /RleP;
  auto with commonDB; apply Rabs_pos. }
intros. rewrite /matrix_index/=.
destruct i; destruct j => //=;
rewrite Rabs_R0; apply /RleP;
auto with commonDB.
all : (destruct HC; destruct HB; 
simpl in H1; lia). } 
clear B. move => b B IH A C. 
elim: C => //.
{ exists [], [], []. 
rewrite /GEMMF GEMM_nilC/=. admit. }
clear C. move => c C. intros => /=.
destruct HB as (HB1 & HB2). 
clear HB; destruct p => //; clear p.
destruct (IH A C x y m n n0) as
  (E1 & E2 & E3 & Heq & H4) => //;
clear H.
(* IH conds *)
{ rewrite /size_col; split.
simpl in HB1; lia.
by intros; apply HB2 => /=; right. }
{ rewrite /size_col; split; destruct HC.
simpl in H; lia.
by intros; apply H0; right. } 
{by intros; apply Hp; right. }
{ move: Hfin. rewrite /GEMMF GEMM_cons.
apply is_finite_mat_cons. } 
(* main *)
rewrite Heq. clear Heq IH.
remember (List.map (BMULT x) (MV dotprodF A b))
  as U.
remember (List.map (BMULT y) c) as V.
(* apply vector sum mixed error *)
destruct (vec_sumF_mixed_error U V)
 as (e1 & e2 & Heq1 & He).
admit. admit.
rewrite !CommonSSR.map_map_equiv in Heq1.
rewrite Heq1.
(* apply vec scale mixed error *)
destruct (scaleV_mixed_error (MV dotprodF A b) x) as
  (e3 & eta3 & Heq3 & H3).
admit. 
rewrite !CommonSSR.map_map_equiv in Heq3.
subst U. rewrite Heq3; clear Heq3.
destruct (scaleV_mixed_error c y) as
  (e4 & eta4 & Heq4 & H4').
admit. 
rewrite !CommonSSR.map_map_equiv in Heq4.
subst V. rewrite Heq4; clear Heq4.
(* apply matrix vector mized error *)
destruct (mat_vec_mul_mixed_error A b)
  as (E & eta & HeqE & H5).
admit.
admit.
rewrite !CommonSSR.map_map_equiv in HeqE.
rewrite HeqE. clear HeqE.
rewrite  MVR_dist.
rewrite GEMMR_distC.
Admitted.

End GEMMERROR.

