Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common op_defs dotprod_model sum_model.
Require Import dot_acc float_acc_lems list_lemmas.
Require Import gem_defs mv_mathcomp.

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

From mathcomp.algebra_tactics Require Import ring.

Section MixedErrorList. 
(* mixed error bounds over lists *)
Context {NAN: Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A: @matrix (ftype t)).
Variable (v: @vector (ftype t)).

Notation n := (length v).
Notation m := (length A).
Notation Ar := (map_mat FT2R A).
Notation vr := (map FT2R v).

Hypothesis Hfin : is_finite_vec (A *f v).
Hypothesis Hlen: forall row, In row A -> length row = length v.

Lemma mat_vec_mul_mixed_error:
  exists (E : matrix) (eta : vector),
    A *fr v =  (Ar +m E) *r vr +v eta 
    /\ (forall i j, (i < m)%nat -> (j < n)%nat -> 
      Rabs (E _(i,j)) <= g n * Rabs (Ar _(i,j))) 
    /\ (forall k, In k eta -> Rabs k <= g1 n n) 
    /\ eq_size E A 
    /\ length eta = m.
Proof.
revert Hfin Hlen. 
elim: A => /= [ Hfin Hlen | a l IH Hfin' Hlen].
(*case A is nil*)
{ exists (zero_matrix 0 0 0%R), []; repeat split => /= //. }
have Hfin2 : is_finite_vec (l *f v).  
  revert Hfin'. rewrite /is_finite_vec => Hf x Hin'. 
  apply Hf; right => //.
have Hin2  : (forall row : list (ftype t), In row l -> length row = length v) by  
  move => row Hrow; apply Hlen; right => //.
destruct (IH Hfin2 Hin2) as (E & eta & IH1 & IH2 & IH3 & IH4 & IH5); 
  clear IH; rewrite IH1; clear IH1.
have Hlen': length a = n by apply Hlen; left => //. 
have Hfin1 : Binary.is_finite (fprec t) (femax t) (dotprodF a v) = true by 
  revert Hfin'; rewrite /is_finite_vec => Hfin'; apply Hfin'; left => /= //.
destruct (dotprod_mixed_error a v Hlen' Hfin1) as (u & ueta & X & Y & Z1 & Z2).
set (A':= (map FT2R a :: map_mat FT2R l) : matrix).
have Ha: (length u = length (map FT2R a)) by rewrite map_length; lia.
have : (length l = 0)%nat \/ (0 < length l)%nat by lia. move => [Hl | Hl].
{  apply length_zero_iff_nil in Hl; subst => /=.
exists (vec_sum u (map FT2R a) Rminus :: []) , ([ueta]); repeat split.
{ rewrite Y => /=. 
rewrite !CommonSSR.map_map_equiv.
rewrite CommonSSR.map_map_equiv map_length in Ha.
suff Hs: map2 Rplus (List.map FT2R a)
         (u -v List.map FT2R a) = u.
rewrite Hs vec_sumR_bounds => /= //.
fold (@vec_sum R (List.map FT2R a) (u -v List.map FT2R a) Rplus).
fold (vec_sumR (List.map FT2R a) (u -v List.map FT2R a)).
rewrite vec_sumR_comm. rewrite vec_sumR_opp => //.
fold (@vec_sumR u (List.map Ropp (List.map FT2R a))).
rewrite vec_sumR_assoc. rewrite vec_sumR_minus.
rewrite /vec_sumR map_length -Ha vec_sum_zeroR => //.
1, 2, 3 : by rewrite !map_length => //.
rewrite /vec_sum/map2 !map_length 
  combine_length map_length Ha; lia. }
{ move =>  i j Hi Hj.
rewrite !CommonSSR.map_map_equiv; rewrite /vec_sum/map2 /= in IH2.
assert (i = 0)%nat by lia; subst.
subst A'. rewrite /matrix_index => /=.
rewrite nth_vec_sum => /= //; [|nra].
have Hj' : (j < n)%coq_nat by lia.
destruct (Z1 j Hj') as (x & HB & HC); rewrite HB.
have H1 : (FT2R (List.nth j a neg_zero) = List.nth j (List.map FT2R a) 0%R) by
pose proof @map_nth (ftype t) R (FT2R) a neg_zero j. 
rewrite H1; apply /RleP; field_simplify_Rabs.
rewrite Rabs_mult Rmult_comm.
by apply Rmult_le_compat_r => //; apply Rabs_pos => /= . }
move => k /= [H | H] //. subst; apply /RleP => //. 
rewrite !CommonSSR.map_map_equiv => /=.
move => x y [Hx|Hx] [Hy|Hy]; subst => //.
rewrite /vec_sum/map2 map_length combine_length Ha 
  CommonSSR.map_map_equiv map_length; lia. }
exists (vec_sum u (map FT2R a) Rminus :: E) , (ueta::eta); repeat split.
{
rewrite CommonSSR.map_map_equiv map_length in Ha.
 rewrite Y; clear Y => /=.
rewrite !CommonSSR.map_map_equiv => /=.
suff: map2 Rplus (List.map FT2R a) (u -v List.map FT2R a) =  u.
move => Hs. rewrite Hs vec_sumR_bounds => //.
fold (@vec_sum R (List.map FT2R a) (u -v List.map FT2R a) Rplus).
fold (vec_sumR (List.map FT2R a) (u -v List.map FT2R a)).
rewrite vec_sumR_comm. rewrite vec_sumR_opp => //.
fold (@vec_sumR u (List.map Ropp (List.map FT2R a))).
rewrite vec_sumR_assoc. rewrite vec_sumR_minus.
rewrite map_length -Ha /vec_sumR vec_sum_zeroR => //.
1, 2, 3: rewrite !map_length => //.
rewrite /vec_sum/map2 !map_length 
  combine_length map_length Ha; lia. }
{ revert Ha. rewrite CommonSSR.map_map_equiv map_length. 
destruct u => /=. 
{ move => Ha i j Hi Hj; symmetry in Ha; rewrite length_zero_iff_nil in Ha; 
subst => /=; rewrite /matrix_index => /=.
destruct i; destruct j => /= //. 
1, 2: rewrite Rabs_R0 -RmultE Rmult_0_r; apply /RleP; nra.
1, 2: apply IH2; lia. }
{ move => Ha i j Hi Hj. revert Ha.
rewrite vec_sumR_opp. destruct a => /= //.
subst A' => /= Ha.
have H1 : (j < n)%coq_nat by lia.
destruct (Z1 j H1) as (d & Hd1 & Hd2).
destruct i; rewrite /matrix_index; destruct j => /= //.
revert Hd1 => /= Hd1; rewrite Hd1. 
  apply /RleP; field_simplify_Rabs; rewrite Rabs_mult Rmult_comm.
  apply Rmult_le_compat; 
  [ apply Rabs_pos | apply Rabs_pos | | apply Req_le ] => //.
{ fold (map2 Rplus u (List.map Ropp (List.map FT2R a))).
fold (vec_sum u (List.map Ropp (List.map FT2R a)) Rplus).
fold (vec_sumR u (List.map Ropp (List.map FT2R a))).
rewrite /vec_sumR -(vec_sumR_opp) => //.
rewrite -(vec_sumR_nth); revert Hd1 => /= Hd1. rewrite Hd1.
suff: List.nth j (List.map FT2R a) 0 =
 (List.nth j (List.map FT2R a) (@FT2R t neg_zero)).
move => Hs; rewrite Hs map_nth; apply /RleP; field_simplify_Rabs. 
rewrite Rabs_mult Rmult_comm; apply Rmult_le_compat; 
  [ apply Rabs_pos | apply Rabs_pos | apply Hd2 | apply Req_le; auto].
f_equal.  
1, 2 : rewrite map_length; simpl in Ha; lia. }
1, 2 : by unfold matrix_index in IH2; apply IH2.
rewrite X map_length. lia. } } 
move => k /=. move => [Hk | Hk]. 
  subst. apply /RleP; apply Z2.
  apply IH3 => //.
by rewrite CommonSSR.map_map_equiv /vec_sum /=;
  destruct IH4; lia.
move => x y /=. 
  rewrite CommonSSR.map_map_equiv. move => [Hx | Hx] [Hy | Hy] /= .
  subst; rewrite /vec_sum/map2 map_length combine_length.
  rewrite CommonSSR.map_map_equiv in Ha. rewrite Ha map_length; lia.
  subst; rewrite /vec_sum/map2 map_length combine_length.
  rewrite CommonSSR.map_map_equiv in Ha. rewrite Ha map_length.
  rewrite (Hin2 y) => //; rewrite Hlen' ; lia.
  destruct IH4. rewrite (Hlen y); [|left] => //.
set (l0 := List.nth 0 l [neg_zero]).
assert (In l0 l). apply nth_In; lia.
specialize (H0 x l0 Hx H1). rewrite H0.
apply Hin2 => //.
destruct IH4.
specialize (H0 x y Hx Hy). rewrite H0 => //.
simpl; lia.
Qed.

End MixedErrorList.

Section MixedErrorMath.  

From mathcomp Require Import matrix all_algebra bigop.

Require Import VST.floyd.functional_base.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Context {NAN: Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A: @gem_defs.matrix (ftype t)).
Variable (v: @gem_defs.vector (ftype t)).

Hypothesis Hlenv : ( 0 < length v)%nat.
Hypothesis HlenA : ( 0 < length A)%nat.
Let m := (length A - 1)%nat.
Let n := (length v - 1)%nat.

Notation Ar := (matrix_to_mx (m.+1) (n.+1) (map_mat FT2R A)).
Notation vr := (vector_to_vc (n.+1) (map FT2R v)).

Hypothesis Hfin : is_finite_vec (A *f v).
Hypothesis Hlen : forall x, In x A -> length x = n.+1.

Notation " i ' " := (Ordinal i) (at level 40).

From mathcomp.algebra_tactics Require Import ring.

Notation Av := (vector_to_vc (m.+1) (A *fr v)).

Lemma mat_vec_mul_mixed_error':
  exists (E : 'M[R]_(m.+1,n.+1)) (eta : 'cV[R]_m.+1),
    Av =  (Ar + E) *m vr + eta 
    /\ (forall i j (Hi : (i < m.+1)%nat) (Hj : (j < n.+1)%nat), 
      Rabs (E  (Hi ') (Hj ')) <= g n.+1 * Rabs (Ar  (Hi ') (Hj ')))
    /\ forall i (Hi: (i < m.+1)%nat), Rabs (eta (Hi ')  0) <= g1 n.+1 n.+1 .
Proof.
have Hlen' : forall x : seq.seq (ftype t), In x A -> Datatypes.length x = length v.
  move => x Hin. rewrite Hlen => //. lia. 
destruct (mat_vec_mul_mixed_error A v Hfin Hlen') as 
  (E & eta & H1 & H2 & H3 & H4 & H5).
exists (matrix_to_mx m.+1 n.+1 E), (vector_to_vc m.+1 eta); 
  split. rewrite H1.
have He : (m.+1 = Datatypes.length eta) by lia.
pose proof @vector_to_vc_plus' ((map_mat FT2R A +m E) *r map FT2R v) eta (m.+1) He.
  rewrite H5 in H. rewrite H. clear H.
f_equal.
have Hlen2: length (map_mat FT2R A +m E) = length A.
  destruct H4.
  rewrite /map_mat map_length combine_length H !map_length; lia.
have Hin1 : 
(forall x : seq.seq R,
      In x (map_mat FT2R A +m E) -> Datatypes.length x = Datatypes.length (List.map FT2R v)). 
apply matrix_sum_preserves_length'.
destruct H4. intros.
rewrite map_length.
set (y := nth 0 A []).
have Hy : In y A. subst y; apply nth_In; lia.
specialize (H0 x y H4 Hy); rewrite H0.
apply Hlen'; auto.
move => x Hx. 
apply list_in_map_inv in Hx.
destruct Hx as (x0 & Hx0 & Hx0').
subst.
rewrite !map_length.
apply Hlen'; auto.
have HlenA1 : m.+1 = length (map_mat FT2R A +m E) by (subst m; lia).
have Hlen1 : n.+1 = length (map FT2R v) by 
  (subst n; rewrite !map_length; lia).
rewrite -Hlen1 in Hin1.
pose proof vector_to_vc_mulmx_m HlenA1 Hlen1 Hin1.
rewrite H. clear H.
f_equal.
have HlenA2 : m.+1 = Datatypes.length (map_mat FT2R A) by 
  (subst m;rewrite !map_length; lia).
pose proof @matrix_to_mx_plus_m (map_mat FT2R A) E (m.+1) (n.+1) HlenA2.
unfold map_mat in H. rewrite map_length in H.
rewrite H. clear H. f_equal.
destruct H4; lia.
move => a e Ha Hep; split. 
apply list_in_map_inv in Ha.
destruct Ha as (x0 & Hx0 & Hx0').
subst. rewrite map_length. apply Hlen; auto.
destruct H4.
apply list_in_map_inv in Ha.
destruct Ha as (x0 & Hx0 & Hx0').
subst. pose proof (H4 e x0 Hep Hx0').
rewrite H6. apply Hlen; auto.
destruct H4.
rewrite /map_mat/mat_sumR/mat_sum/map2 !map_length combine_length
  map_length; lia.
split.
{ move => i j Hi Hj.
 rewrite -(matrix_to_mx_index E Hi Hj).
 rewrite -(matrix_to_mx_index (map_mat FT2R A) Hi Hj).
have HA : (length A = m.+1) by (subst m; lia).
have Hv : (length v = n.+1) by (subst m; lia).
rewrite HA Hv in H2. 
specialize (H2 i j Hi Hj).
subst n => /= //. }
move => i Hi.
rewrite vector_to_vc_index => /= //.
have Hv : (length v = n.+1) by (subst m; lia).
rewrite Hv in H3.
apply H3. apply nth_In. lia.
Qed.

End MixedErrorMath.

Section ForwardError.
From mathcomp Require Import matrix .

Context {NAN: Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A: @gem_defs.matrix (ftype t)).
Variable (v: @gem_defs.vector (ftype t)).

Hypothesis Hlenv : ( 0 < length v)%nat.
Hypothesis HlenA : ( 0 < length A)%nat.
Let m := (length A - 1)%nat.
Hypothesis Hlenv1: (length v - 1)%nat = m.

Notation Ar := (matrix_to_mx m.+1 m.+1 (map_mat FT2R A)).
Notation vr := (vector_to_vc m.+1 (map FT2R v)).

Hypothesis Hfin : is_finite_vec (A *f v).
Hypothesis Hlen : forall x, In x A -> length x = m.+1.

Notation " i ' " := (Ordinal i) (at level 40).

Notation Av' := (vector_to_vc m.+1 (map FT2R (mvF A v))).

Notation "| u |" := (normv u) (at level 40).

Theorem forward_error :
 |Av' - (Ar *m vr)| <= (g m.+1 * normM Ar * |vr|) + g1 m.+1 m.+1.
Proof.
destruct (mat_vec_mul_mixed_error' A v) as (E & eta & HE & H1 & H2) => //.
rewrite Hlenv1 => //.
rewrite HE mulmxDl. fold m. clear HE.  
have Hvr : vector_to_vc m.+1 (List.map FT2R v) = vr => //=.
move: H1. move: E. rewrite Hlenv1 Hvr. move => E H1.
have H0 : Ar *m vr + E *m vr + eta - Ar *m vr = E *m vr + eta. 
remember (Ar *m vr) as y. remember (E *m vr) as x. subst m. 
apply /matrixP => i j; do ![rewrite mxE | ] => /=; ring.
rewrite H0. clear H0. fold m in H1, H2.
eapply (le_trans (normv_triang _ _ )). 
apply ler_add.
eapply (le_trans (subMultNorm _ _ )).
apply ler_pmul => //. 
apply normM_pos.
apply normv_pos.
rewrite /normM mulrC big_max_mul.
apply le_bigmax2 => i0 _. 
rewrite /sum_abs.
rewrite big_mul =>  [ | i b | ]; try ring.
apply ler_sum => i _.
rewrite mulrC.
  destruct i0. destruct i. apply H1.
apply /RleP; auto with commonDB.
apply /RleP; auto with commonDB.
rewrite /normv.
apply bigmax_le => [|i _].  
apply /RleP; auto with commonDB.
destruct i. 
rewrite Hlenv1 in H2.
apply H2.
Qed.

End ForwardError. 