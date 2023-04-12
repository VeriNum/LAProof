(* This file contatins lemmas for the accuracy of the fma and non-fma dot products.
  These lemmas are used to prove the main accuracy theorems in dot_acc.v and fma_dot_acc.v.
  The theorems use the inductive definitions R_dot_prod_rel and dot_prod_rel,
  which are a bit easier (for me) to work with at a low level then dotprodF and dotprodR. *) 

Require Import vcfloat.VCFloat.
Require Import List.
Import ListNotations.
Require Import common dotprod_model float_acc_lems op_defs list_lemmas.

Require Import Reals.
Open Scope R.

Section ForwardErrorRel1.
(* forward error bound for non-fma dot product using inductive rels *) 
Context {NAN: Nans} {t : type}.

Variables (vF : list (ftype t * ftype t)).
Notation vR  := (map FR2 vF).
Notation vR' := (map Rabsp (map FR2 vF)).

Variable (fp : ftype t).
Hypothesis Hfp : dot_prod_rel vF fp.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) fp = true.

Variable (rp rp_abs : R).
Hypothesis Hrp  : R_dot_prod_rel vR rp.
Hypothesis Hra : R_dot_prod_rel vR' rp_abs.

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).
Notation E := (@default_abs t).

Lemma dotprod_forward_error_rel:
  Rabs (FT2R fp - rp) <=  g (length vF) * rp_abs + g1 (length vF) (length vF - 1).
Proof.
revert Hfp Hrp Hra Hfin. revert fp rp rp_abs.
induction vF.
{
intros;
inversion Hrp;
inversion Hfp;
inversion Hra;
subst.
unfold g, g1; simpl;
rewrite Rminus_eq_0;
rewrite Rabs_R0;
field_simplify; try apply default_rel_sep_0;
  try apply Stdlib.Rdiv_pos_compat; try nra;
apply default_rel_gt_0.
}
intros.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* list (a0 :: a :: l) *)
(* case empty l *)
{
subst; simpl.
rewrite (R_dot_prod_rel_single rp (FR2 a)); auto.
inversion Hfp. inversion H2. subst.
assert ( HFINa:
      (Binary.is_finite (fprec t) (femax t) (BMULT (fst a) (snd a)) = true /\
      Binary.is_finite (fprec t) (femax t) (Zconst t 0) = true)).
  { destruct (BMULT (fst a) (snd a)); unfold pos_zero; simpl; auto. }
  destruct HFINa as (A & C).
rewrite BPLUS_B2R_zero_r; auto.
pose proof BMULT_accurate'  (fst a) (snd a) A as Hmula.
destruct Hmula as (d' & e' & Hed' & Hd' & He' & B); rewrite B; clear B.
unfold g1, g; simpl.
inversion Hra. inversion H3; subst.
rewrite Rmult_1_r. rewrite !Rplus_0_r.
replace (1 + D - 1) with (D) by nra. field_simplify;
field_simplify_Rabs.  unfold FR2. destruct a; simpl.
eapply Rle_trans. apply Rabs_triang. rewrite Rabs_mult.
eapply Rle_trans.
apply Rplus_le_compat. apply Rmult_le_compat; try apply Rabs_pos.
apply Rle_refl. apply Hd'. apply He'.
rewrite Rmult_comm.
apply Rplus_le_compat; try nra.
rewrite Rmult_assoc.
rewrite <- Rabs_mult. try nra.
}
(* non-empty l *)
intros; inversion Hfp;
inversion Hrp; inversion Hra; subst.
(destruct (BPLUS_finite_e _ _ Hfin) as (A & B)).
(* IHl *)
specialize (IHl s s0 s1 H3 H7 H11 B).
destruct (BPLUS_accurate'  (BMULT (fst a) (snd a)) s Hfin) as (d' & Hd'& Hplus);
rewrite Hplus; clear Hplus.
destruct (BMULT_accurate'  (fst a) (snd a) A) as (d & e & Hed & Hd& He& Hmul); 
rewrite Hmul; clear Hmul.
(* algebra *)
apply length_not_empty_nat in H.
destruct a; cbv [ FR2 Rabsp fst snd].
simpl.
set (n:= length l) in *.
set (F:= FT2R f * FT2R f0).
field_simplify_Rabs.
replace (F * d * d' + F * d + F * d' + e * d' + e + FT2R s * d' + FT2R s - s0) with
((F * d * d' + F * d + F * d' + FT2R s * d') + (FT2R s - s0) + (1 + d') * e) by nra.
eapply Rle_trans;
  [ apply Rabs_triang | ].
eapply Rle_trans;
  [  apply Rplus_le_compat; [eapply Rle_trans;
  [ apply Rabs_triang | ] |]  | ].
apply Rplus_le_compat_l; apply IHl .
rewrite Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos | apply He].
rewrite  Rplus_assoc.
eapply Rle_trans;
  [  apply Rplus_le_compat_r ; eapply Rle_trans; [ apply Rabs_triang | ] | ].
apply Rplus_le_compat_l; rewrite Rabs_mult; rewrite Rmult_comm;
  apply Rmult_le_compat; [ apply Rabs_pos| apply Rabs_pos| apply Hd' | ].
{ apply Rabs_le_minus in IHl. assert (Hs: Rabs (FT2R s) <=
      g (length l) * s1 + g1 (length l) (length l - 1) + s1).
{ eapply Rle_trans. apply IHl. apply Rplus_le_compat_l.
rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 l) s1); auto.
apply (dot_prod_sum_rel_R_Rabs (map FR2 l)); auto. }
apply Hs. }
field_simplify.
fold D E n.
rewrite !Rplus_assoc. 
replace (Rabs (F * d * d' + (F * d + F * d')) +
(D * g n *  s1 +
 (D *  s1 +
  (D * g1 n (n - 1) +
   ( s1 * g n + (g1 n (n - 1) + Rabs (1 + d') * E)))))) with
(Rabs (F * d * d' + (F * d + F * d')) + ((1+ D) * g n *  s1 + D *  s1) +
 (D * g1 n (n - 1) + (g1 n (n - 1) + Rabs (1 + d') * E))) by nra.
replace (s1 * g (S n) + (g (S n) * Rabs (FT2R f) * Rabs (FT2R f0) + g1 (S n) (n - 0)))
with (g (S n) * Rabs (FT2R f * FT2R f0) + s1 * g (S n) + g1 (S n) (n - 0)) by
(rewrite Rmult_assoc, <- Rabs_mult; nra).
apply Rplus_le_compat.
apply Rplus_le_compat.
eapply Rle_trans;
  [ apply Rabs_triang | ].
eapply Rle_trans;
  [ apply Rplus_le_compat; [rewrite !Rabs_mult| eapply Rle_trans; [apply Rabs_triang| ]] | ].
apply Rmult_le_compat; [rewrite <- Rabs_mult; apply Rabs_pos | apply Rabs_pos|  |  apply Hd'].
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd ].
apply Rplus_le_compat; rewrite Rabs_mult.
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd ].
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd' ].
fold D F. replace (Rabs F * D * D + (Rabs F * D + Rabs F * D)) with
  ( ((1 + D)*(1+D) - 1) * Rabs F ) by nra.
apply Rmult_le_compat_r; try apply Rabs_pos; unfold D, g.
apply Rplus_le_compat; try nra.
rewrite <- tech_pow_Rmult.
apply Rmult_le_compat_l.
eapply Rle_trans with 1; try nra; apply default_rel_plus_1_ge_1.
eapply Rle_trans with ((1 + D)^1); try nra.
fold D; nra.
apply Rle_pow; auto with commonDB.
apply Req_le; rewrite one_plus_d_mul_g.
rewrite Rmult_comm.
repeat f_equal;  try lia.
rewrite <- Rplus_assoc.
eapply Rle_trans; [apply Rplus_le_compat_l; 
  apply Rmult_le_compat_r; [ unfold E; apply default_abs_ge_0| eapply Rle_trans] | ].
apply Rabs_triang. rewrite Rabs_R1. 
apply  Rplus_le_compat_l; apply Hd'.
rewrite !Rmult_plus_distr_r. rewrite Rmult_1_l.
rewrite <- !Rplus_assoc.
replace (D * g1 n (n - 1) + g1 n (n - 1)) with (g1 n (n-1) * (1+D)) by nra;
rewrite one_plus_d_mul_g1; auto.
rewrite Rplus_assoc.
replace (E + D * E) with 
  ((1+D) * E) by nra.
eapply Rle_trans; [apply plus_d_e_g1_le; auto| apply Req_le; f_equal;lia].
Qed.

End ForwardErrorRel1. 

Section ForwardErrorRel2.
(* forward error bound for fma dot product using inductive rels *) 
Context {NAN: Nans} {t : type}.

Variable (vF : list (ftype t * ftype t)).
Notation vR  := (map FR2 vF).
Notation vR' := (map Rabsp (map FR2 vF)).

Variable (fp : ftype t).
Hypothesis Hfp : fma_dot_prod_rel vF fp.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) fp = true.

Variable (rp rp_abs : R).
Hypothesis Hrp  : R_dot_prod_rel vR rp.
Hypothesis Hra : R_dot_prod_rel vR' rp_abs.

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).
Notation E := (@default_abs t).

Lemma fma_dotprod_forward_error_rel:
  Rabs (FT2R fp - rp) <=  g (length vF) * rp_abs + g1 (length vF) (length vF - 1).
Proof.
revert Hfp Hrp Hra Hfin. revert fp rp rp_abs.
induction vF.
{
intros;
inversion Hrp;
inversion Hfp;
inversion Hra;
subst.
unfold g, g1; simpl;
rewrite Rminus_eq_0;
rewrite Rabs_R0;
field_simplify; try apply default_rel_sep_0;
  try apply Stdlib.Rdiv_pos_compat; try nra;
apply default_rel_gt_0.
}
intros.
assert (Hl: l = [] \/ l <> []).
destruct l; auto.
right.
eapply hd_error_some_nil; simpl; auto.
destruct Hl.
(* list (a0 :: a :: l) *)
(* case empty l *)
{
subst; simpl.
rewrite (R_dot_prod_rel_single rp (FR2 a)).
inversion Hfp. inversion H2. subst.
pose proof fma_accurate' (fst a) (snd a) (Zconst t 0) Hfin as Hacc.
destruct Hacc as (e & d & Hz & He & Hd & A). rewrite A; clear A.
inversion Hra; inversion H3; subst.
unfold g1, g; simpl.
rewrite Rmult_1_r. rewrite !Rplus_0_r.
replace (1 + @default_rel t - 1) with (@default_rel t) by nra.
field_simplify_Rabs. destruct a; simpl.
eapply Rle_trans. apply Rabs_triang. rewrite Rabs_mult.
rewrite Rmult_plus_distr_l. rewrite Rmult_comm.
apply Rplus_le_compat; try nra.
  apply Rmult_le_compat; try apply Rabs_pos; try apply Rle_refl;
  try apply Rabs_pos; auto.
rewrite <- Rabs_mult; apply Req_le; nra.
simpl in Hrp; auto.
}
(* non-empty l *)
intros; inversion Hfp;
inversion Hrp; inversion Hra; subst.
(destruct (BMFA_finite_e _ _ _ Hfin) as (A & B & C)).
(* IHl *)
specialize (IHl s s0 s1 H3 H7 H11 C).
pose proof (fma_accurate' (fst a) (snd a) s Hfin) as Hplus.
destruct Hplus as (d' & e'& Hz & Hd'& He'& Hplus); rewrite Hplus;
  clear Hplus.
(* algebra *)
destruct a; cbv [ FR2 Rabsp fst snd].
simpl.
set (n:= length l).
field_simplify_Rabs.
replace (FT2R f * FT2R f0 * d' + FT2R s * d' + FT2R s + e' - s0) with
   (d' * (FT2R f * FT2R f0) + d' * FT2R s + (FT2R s - s0) + e') by nra.
eapply Rle_trans;
  [ apply Rabs_triang | eapply Rle_trans; [ apply Rplus_le_compat_r; apply Rabs_triang
    | ] ].
eapply Rle_trans;
  [  apply Rplus_le_compat_r | ].
apply Rplus_le_compat_r.
apply Rabs_triang.
eapply Rle_trans;
  [apply Rplus_le_compat_r; apply Rplus_le_compat_l | ].
apply IHl.
eapply Rle_trans;
  [apply Rplus_le_compat; [apply Rplus_le_compat_r| apply He' ] | ].
apply Rplus_le_compat.
rewrite Rabs_mult;
apply Rmult_le_compat_r; try apply Rabs_pos;
apply Hd'.
rewrite Rabs_mult;
apply Rmult_le_compat; try apply Rabs_pos.
apply Hd'.
apply Rabs_le_minus in IHl.
assert (Hs: Rabs (FT2R s) <=
      g (length l) * s1 + g1 (length l) (length l - 1) + s1).
{ eapply Rle_trans. apply IHl. 
apply Rplus_le_compat_l.
rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 l) s1); auto. 
apply (dot_prod_sum_rel_R_Rabs (map FR2 l)); auto. }
apply Hs.
fold n.
set (F:=Rabs (FT2R f * FT2R f0)).
rewrite !Rmult_plus_distr_l.
replace (D * F + (D * (g  n * s1) + D * g1 n (n - 1) + D * s1) +
(g n * s1 + g1  n (n - 1)) + E) with
(D * F + ((1 + D) * g  n * s1 + D * s1) + g1 n (n - 1) * (1 + D) + E) by nra.
rewrite one_plus_d_mul_g. rewrite one_plus_d_mul_g1.
rewrite Rplus_assoc.
apply Rplus_le_compat.
apply Rplus_le_compat.
rewrite <- Rabs_mult. fold F.
apply Rmult_le_compat_r.
unfold F; apply Rabs_pos.
apply d_le_g_1; lia.
apply Rmult_le_compat_r.
rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 l) s1); auto. apply Rabs_pos.
apply Req_le; f_equal; auto; lia.
unfold E; rewrite Nat.sub_0_r. apply plus_e_g1_le.
unfold n; apply length_not_empty in H; auto.
Qed.

End ForwardErrorRel2.

Section MixedErrorRel1. 
(* mixed error bound for non-fma dot product using inductive rels *) 
Context {NAN: Nans} {t : type}.

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).
Notation E := (@default_abs t).

Variables (v1 v2 : list (ftype t)).
Hypothesis Hlen : length v1 = length v2.
Notation vF  := (combine v1 v2).

Variable (fp : ftype t).
Hypothesis Hfp : dot_prod_rel vF fp.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) fp = true.

(* mixed error bound *)
Lemma dotprod_mixed_error_rel:
  exists (u : list R) (eta : R),
    length u = length v2 /\
    R_dot_prod_rel (combine u (map FT2R v2)) (FT2R fp - eta) /\
    (forall n, (n < length v2)%nat -> exists delta,
      nth n u 0 = FT2R (nth n v1 neg_zero) * (1 + delta) /\ Rabs delta <= g (length v2))  /\
    Rabs eta <= g1 (length v2) (length v2).
Proof.
revert Hfp Hfin Hlen. revert fp v1.
induction v2.
{ simpl; intros.   replace v1 with (@nil (ftype t)) in * by (symmetry; apply length_zero_iff_nil; auto). 
  exists [], 0; repeat split; 
  [inversion Hfp; subst; rewrite Rminus_0_r; simpl; auto;
  apply R_dot_prod_rel_nil  | | rewrite Rabs_R0; unfold g1, g; simpl; nra ]. 
  intros; exists 0; split; 
  [ assert (n = 0)%nat by lia; subst; simpl; nra | rewrite Rabs_R0; unfold g; nra].
}
intros.
  destruct v1; intros.
  { simpl in Hlen. pose proof Nat.neq_0_succ (length l); try contradiction. }
    assert (Hv1: l = [] \/ l <> []).
    destruct l; auto. right.
    eapply hd_error_some_nil; simpl; auto.
    assert (Hlen1: length l0 = length l) by (simpl in Hlen; auto).
    destruct Hv1.
    assert (l0 = []). { simpl in Hlen; apply length_zero_iff_nil;  
          apply length_zero_iff_nil in H; rewrite H in Hlen1; auto. }
    subst; clear Hlen1.
{ (* case singleton lists *)
clear IHl. inversion Hfp; subst. 
inversion H2; subst; clear H2.
 simpl in  Hfp, Hfin; unfold fst, snd.
assert (FINmul: Binary.is_finite (fprec t) (femax t) (BMULT f a) = true).
{ destruct (BMULT f a); unfold neg_zero in *; simpl; try discriminate; auto. }
rewrite BPLUS_B2R_zero_r in *; auto.
pose proof BMULT_accurate' f a FINmul as Hacc.
destruct Hacc as (d & e & Hed & Hd & He & Hacc).
exists [FT2R f * (1  +d)], e; repeat split.
{ simpl. rewrite Hacc. replace (FT2R f * FT2R a * (1 + d) + e - e) with
  (FT2R f * (1 + d) * FT2R a + 0) by (simpl; nra).
apply R_dot_prod_rel_cons; apply R_dot_prod_rel_nil. }
{ intros; exists d; split; auto. simpl in H. 
  destruct n. { simpl; auto. } 
  apply le_S_n in H; apply Nat.le_0_r in H; rewrite H; simpl; nra.
eapply Rle_trans; [apply Hd| apply d_le_g_1; simpl; auto].
}
eapply Rle_trans; [apply He|]. apply e_le_g1; simpl in *; auto.
} 
(* case cons lists*)
(* apply IH *)
pose proof (length_not_empty l H) as Hlen3.
inversion Hfp;  subst.
unfold fst, snd in Hfin, Hfp; unfold fst, snd.
destruct (BPLUS_finite_e _ _ Hfin) as (A & B).
destruct (BMULT_finite_e _ _ A) as (C & _).
(* IHl *)
specialize (IHl s l0 H3 B Hlen1).
(* construct u *)
destruct (BPLUS_accurate' (BMULT f a) s Hfin) as (d' & Hd'& Hplus); 
rewrite Hplus; clear Hplus.
destruct (BMULT_accurate' f a A) as (d & e & Hed & Hd& He& Hmul); 
rewrite Hmul; clear Hmul.
destruct IHl as (u & eta & Hlenu & Hurel & Hun & Heta).
exists (FT2R f * (1+d) * (1 + d') :: map (Rmult (1+d')) u), 
  (e * (1 + d') + eta * (1 + d')).
repeat split.
{ simpl. rewrite map_length; auto. }
{ pose proof dot_prod_combine_map_Rmult (1+d') u (map FT2R l) (FT2R s - eta).
rewrite map_length in H0. specialize (H0 Hlenu Hurel); simpl.
replace
 ((FT2R f * FT2R a * (1 + d) + e + FT2R s) * (1 + d') -
   (e * (1 + d') + eta * (1 + d')))
with
 (FT2R f * (1 + d) * (1 + d') * FT2R a  + (FT2R s - eta) * (1 + d')) by nra.
apply R_dot_prod_rel_cons; rewrite Rmult_comm; auto. }
{ intros. destruct n. simpl.
{ simpl. exists ((1 + d) * (1 + d') -1); split.
  { field_simplify; nra. } 
  { field_simplify_Rabs. eapply Rle_trans; [apply Rabs_triang|].
    eapply Rle_trans; [apply Rplus_le_compat; [apply Rabs_triang | apply Hd' ] |].
    eapply Rle_trans; [apply Rplus_le_compat_r; apply Rplus_le_compat; [|apply Hd] |  ].
    rewrite Rabs_mult. apply Rmult_le_compat; 
        [apply Rabs_pos | apply Rabs_pos | apply Hd | apply Hd'].
    eapply Rle_trans with ((1 + D) * (1 + D) - 1); try nra.
    unfold g. apply Rplus_le_compat; try nra. 
    rewrite <- tech_pow_Rmult; apply Rmult_le_compat; try nra; try
    (eapply Rle_trans with 1; try nra; apply (default_rel_plus_1_ge_1)).
    eapply Rle_trans with ((1 + D) ^ 1); try nra.
    apply Rle_pow; try
    (eapply Rle_trans with 1; try nra; apply (default_rel_plus_1_ge_1)).
     rewrite <- Hlen1; auto. lia. }
}
simpl in H0; assert (Hn: (n < length l)%nat) by lia.
specialize (Hun n Hn);
   destruct Hun as (delta & Hun & Hdelta). simpl;
replace 0 with (Rmult  (1+d') 0) by nra. rewrite map_nth.
rewrite Hun.
exists ( (1+d') * (1+delta) -1).
split; [nra | ].
field_simplify_Rabs.
eapply Rle_trans; [apply Rabs_triang | ].
eapply Rle_trans; [apply Rplus_le_compat; [ apply Rabs_triang | apply Hdelta] | ].
eapply Rle_trans; [apply Rplus_le_compat_r; [rewrite Rabs_mult] | ].
apply Rplus_le_compat; [apply Rmult_le_compat;  try apply Rabs_pos | ].
apply Hd'.
apply Hdelta.
apply Hd'.
replace (D * g (length l) + D + g (length l)) with
((1 + D) * g (length l) *1 + D *1) by nra.
rewrite one_plus_d_mul_g.
rewrite Rmult_1_r.
apply Req_le; f_equal; lia.
}
simpl.
eapply Rle_trans; [apply Rabs_triang| ].
eapply Rle_trans; [apply Rplus_le_compat; [rewrite Rabs_mult| rewrite Rabs_mult] | ].
eapply Rmult_le_compat; try apply Rabs_pos.
apply He.
eapply Rle_trans; [apply Rabs_triang | rewrite Rabs_R1; apply Rplus_le_compat_l; apply Hd'].
eapply Rmult_le_compat; try apply Rabs_pos.
apply Heta.
eapply Rle_trans; [apply Rabs_triang | rewrite Rabs_R1; apply Rplus_le_compat_l; apply Hd'].
rewrite Rplus_comm. rewrite one_plus_d_mul_g1'.
assert (Hp: (1 <= S (length l))%nat) by lia.
pose proof @plus_d_e_g1_le' t (length l) (S (length l)) Hlen3 Hp as HYP; clear Hp.
eapply Rle_trans; [| apply HYP]; apply Req_le; nra.
Qed.

End MixedErrorRel1.

Section MixedErrorRel2.

Context {NAN: Nans} {t : type}.

Notation g := (@g t).
Notation g1 := (@g1 t).
Notation D := (@default_rel t).
Notation E := (@default_abs t).

Variables (v1 v2 : list (ftype t)).
Hypothesis Hlen : length v1 = length v2.
Notation vF  := (combine v1 v2).

Variable (fp : ftype t).
Hypothesis Hfp : fma_dot_prod_rel vF fp.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) fp = true.

(* mixed error bounds *)
Lemma fma_dotprod_mixed_error_rel:
  exists (u : list R) (eta : R),
    length u = length v1 /\
    R_dot_prod_rel (List.combine u (map FT2R v2)) (FT2R fp - eta) /\
    (forall n, (n < length v2)%nat -> exists delta,
      nth n u 0 = FT2R (nth n v1 neg_zero) * (1 + delta) /\ Rabs delta <= g (length v2))  /\
    Rabs eta <= g1 (length v2) (length v2 - 1).
Proof.
revert Hfp Hfin Hlen. revert fp v1.
induction v2.
{ simpl; intros.   replace v1 with (@nil (ftype t)) in * by (symmetry; apply length_zero_iff_nil; auto). 
  exists [], 0; repeat split; 
  [inversion Hfp; subst; rewrite Rminus_0_r; simpl; auto;
  apply R_dot_prod_rel_nil  | | rewrite Rabs_R0; unfold g1, g; simpl; nra ]. 
  intros; exists 0; split; 
  [ assert (n = 0)%nat by lia; subst; simpl; nra | rewrite Rabs_R0; unfold g; nra].
}
intros.
  destruct v1; intros.
  { simpl in Hlen. pose proof Nat.neq_0_succ (length l); try contradiction. }
    assert (Hv1: l = [] \/ l <> []).
    destruct l; auto. right.
    eapply hd_error_some_nil; simpl; auto.
    assert (Hlen1: length l0 = length l) by (simpl in Hlen; auto).
    destruct Hv1.
    assert (l0 = []). { simpl in Hlen; apply length_zero_iff_nil;  
          apply length_zero_iff_nil in H; rewrite H in Hlen1; auto. }
    subst; clear Hlen1.
{
inversion Hfp; subst. 
inversion H2; subst; clear H2.
simpl in Hfp, Hfin.
pose proof fma_accurate' f a (Zconst t 0) Hfin as Hacc.
destruct Hacc as (d & e & Hde & Hd & He& Hacc).
exists [FT2R f * (1  +d)], e; repeat split.
{ simpl. rewrite Hacc. replace ((FT2R f * FT2R a + FT2R (Zconst t 0)) * (1 + d) + e - e) with
  (FT2R f * (1 + d) * FT2R a + 0) by (simpl; nra).
apply R_dot_prod_rel_cons; apply R_dot_prod_rel_nil. }
{ intros; exists d; split; auto. simpl in H. 
  destruct n. { simpl; auto. } 
  apply le_S_n in H; apply Nat.le_0_r in H; rewrite H; simpl; nra.
eapply Rle_trans; [apply Hd| apply d_le_g_1; simpl; auto].
}
eapply Rle_trans; [apply He|]. unfold g1, g; simpl; nra.
}
 (* apply IH *)
pose proof (length_not_empty l H) as Hlen3. 
inversion Hfp; subst.
(destruct (BMFA_finite_e _ _ _ Hfin) as (A' & B' & C')).
specialize (IHl s l0).
destruct IHl as (u & eta & Hlenu & A & B & C ); auto.
(* construct u0 *)
simpl in Hfin.
pose proof fma_accurate'   f a s Hfin as Hacc;
destruct Hacc as (d & e & Hz & Hd & He & Hacc). 
unfold fst, snd; rewrite Hacc.
exists (FT2R f * (1+d) :: map (Rmult (1+d)) u), (e + eta * (1 + d)).
repeat split.
{ simpl. rewrite map_length; auto. }
{ pose proof dot_prod_combine_map_Rmult (1+d) u (map FT2R l) (FT2R s - eta).
rewrite map_length in H0. 
rewrite Hlen1 in Hlenu.
specialize (H0 Hlenu A); simpl.
replace  ((FT2R f * FT2R a + FT2R s) * (1 + d) + e - (e + eta * (1 + d))) with
(FT2R f * (1 + d) * FT2R a + (FT2R s - eta)*(1+d)) by nra.
apply R_dot_prod_rel_cons. rewrite Rmult_comm; auto. }
{ intros. destruct n. simpl.
{ simpl. exists d; split; auto. eapply Rle_trans; [apply Hd| ]. apply d_le_g_1. apply le_n_S; lia. }
assert (n<length l)%nat by (simpl in H0; lia); clear H0.
specialize (B n H1); destruct B as (delta & B & HB); simpl.
replace 0 with (Rmult (1 + d) 0) by nra. rewrite map_nth.
rewrite B.
exists ( (1+d) * (1+delta) -1).
split; [nra | ].
field_simplify_Rabs.
eapply Rle_trans; [apply Rabs_triang | ].
eapply Rle_trans; [apply Rplus_le_compat; [ apply Rabs_triang | apply HB] | ].
eapply Rle_trans; [apply Rplus_le_compat_r; [rewrite Rabs_mult] | ].
apply Rplus_le_compat; [apply Rmult_le_compat;  try apply Rabs_pos | ].
apply Hd.
apply HB.
apply Hd.
replace (D * g  (length l) + D + g (length l)) with
((1 + D ) * g  (length l) *1 + D *1) by nra.
rewrite one_plus_d_mul_g.
rewrite Rmult_1_r.
apply Req_le; f_equal; lia.
}
simpl.
eapply Rle_trans; [apply Rabs_triang| ].
eapply Rle_trans; [apply Rplus_le_compat; [apply He| rewrite Rabs_mult] | ].
eapply Rmult_le_compat; try apply Rabs_pos.
apply C.
eapply Rle_trans; [apply Rabs_triang| ].
rewrite Rabs_R1.
eapply Rle_trans; [apply Rplus_le_compat_l; apply Hd| apply Rle_refl ].
rewrite one_plus_d_mul_g1; try lia.
unfold g1; field_simplify.
rewrite Rplus_assoc.
eapply Rplus_le_compat.
eapply Rmult_le_compat; try apply g_pos.
apply Rmult_le_pos; [apply default_abs_ge_0| apply pos_INR ].
eapply Rmult_le_compat; try apply default_abs_ge_0; try  apply pos_INR.
apply Req_le; auto.
apply le_INR; lia.
apply Req_le; f_equal; auto; lia.
set (n:= length l).
replace (INR (S n)) with (INR n + 1)%R. 
apply Req_le; nra.
apply transitivity with (INR (n + 1)).
rewrite plus_INR; simpl; auto. f_equal; simpl; lia.
Qed.

End MixedErrorRel2.


Section SparseErrorRel1. 
(* sparse forward error bound for non-fma dot product using inductive rels *) 
Context {NAN: Nans} {t : type}.

Variables (v1 v2 : list (ftype t)).
Hypothesis (Hlen : length v1 = length v2).

Variable (fp : ftype t).
Hypothesis Hfp : dot_prod_rel (combine v1 v2) fp.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) fp = true.

Notation v1R := (map FT2R v1).

Variable (rp rp_abs : R).
Hypothesis Hrp  : R_dot_prod_rel (map FR2 (combine v1 v2)) rp.
Hypothesis Hra : R_dot_prod_rel (map Rabsp (map FR2 (combine v1 v2))) rp_abs.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).
Notation nnzR := (nnzR v1R).

Lemma sparse_dotprod_forward_error_rel:
  Rabs (FT2R fp - rp) <=  g nnzR * rp_abs + g1 nnzR (nnzR - 1).
Proof.
revert Hlen Hfp Hfin Hrp Hra.
revert rp rp_abs fp v2.
unfold nnz.
induction v1; intros.
{ simpl in Hlen; symmetry in Hlen; apply length_zero_iff_nil in Hlen; subst. 
inversion Hfp; inversion Hrp; subst; simpl; field_simplify_Rabs. 
  rewrite Rabs_R0. 
  apply Rplus_le_le_0_compat; auto with commonDB.
  apply Rmult_le_pos;  auto with commonDB.
 rewrite <- (R_dot_prod_rel_Rabs_eq [] rp_abs); auto;
  apply Rabs_pos. }
destruct v2; try discriminate.
assert (Hlen1 : length l = length l0) by (simpl; auto).
set (n2:= (common.nnzR (map FT2R l))%nat) in *.
inversion Hrp. inversion Hfp. inversion Hra; subst. 
assert (HFIN: Binary.is_finite (fprec t) (femax t) s0 = true).
{ simpl in Hfin. destruct (BMULT a f); destruct s0;
   try discriminate; simpl in *; auto;
  destruct s0; destruct s2; try discriminate; auto. }
assert (HFIN2: Binary.is_finite (fprec t) (femax t) (BMULT a f) = true).
{ simpl in Hfin. destruct (BMULT a f); destruct s0;
   try discriminate; simpl in *; auto. } simpl. 
specialize (IHl s s1 s0 l0 Hlen1 H6 HFIN H2 H10).
(* reason by cases on the head of the list *) 
destruct (Req_EM_T (FT2R a) 0%R). 
(* start  head of list is zero *)
{ rewrite e. unfold common.nnzR; rewrite nnz_cons.
replace (FT2R (BPLUS (BMULT a f) s0)) with (FT2R s0).
field_simplify_Rabs. 
eapply Rle_trans; [apply IHl|]. 
apply Req_le; f_equal; try nra. unfold n2, common.nnzR. 
rewrite Rabs_R0, Rmult_0_l,  Rplus_0_l; nra.
pose proof Bmult_0R a f HFIN2 as H; destruct H; auto; rewrite H;
try rewrite Bplus_neg_zero; try rewrite Bplus_neg_zero; auto;
repeat (destruct s0; simpl; auto). } (* end head of list is zero *) 
(* start head of list is non-zero *)
unfold common.nnzR, nnz. rewrite !count_occ_cons_neq; auto.
set (l1:= (map FT2R l)) in *.
set (n1:= (length (FT2R a :: l1) - @count_occ R Req_EM_T l1 0%R)%nat).
assert (n1 = S n2).
{ unfold n1, n2. pose proof @count_occ_bound R Req_EM_T 0%R l1.
  unfold common.nnzR, nnz.
  destruct (count_occ Req_EM_T l1 0%R); unfold l1 in *; simpl; try lia. }
(* start case on nnz = case on nnz in tail *)
assert (H0: (n2 = 0)%nat \/ (1<=n2)%nat) by lia; destruct H0. 
(* tail all zeros *)
{ rewrite H0 in *. rewrite H.
pose proof R_dot_prod_rel_nnzR l l0 Hlen1 s H2 H0; subst.
pose proof dot_prod_rel_nnzR l l0 Hlen1 s0 H6 HFIN H0.
pose proof R_dot_prod_rel_nnzR_abs l l0 Hlen1 s1 H10 H0; subst.
rewrite Bplus_0R; auto.
destruct (@BMULT_accurate' t NAN a f HFIN2)
  as (d' & e' & Hed' & Hd' & He' & Hacc).
rewrite Hacc; clear Hacc.
unfold g1, g.
simpl; field_simplify; 
field_simplify_Rabs. 
eapply  Rle_trans; [apply Rabs_triang | ].
apply Rplus_le_compat.
rewrite Rabs_mult.
rewrite Rmult_comm.
rewrite Rabs_mult. rewrite Rmult_assoc.
apply Rmult_le_compat_r; auto with commonDB.
rewrite <- Rabs_mult; apply  Rabs_pos.
eapply Rle_trans; [apply He'| ]; auto with commonDB; nra.
}
(* tail not all zeros *)
destruct (@BPLUS_accurate' t NAN (BMULT a f) s0 Hfin)
  as (d' & Hd' & Hacc).
rewrite Hacc; clear Hacc.
destruct (@BMULT_accurate' t NAN a f HFIN2)
  as (d & e & Hed & Hd & He & Hacc).
rewrite Hacc; clear Hacc. 
set (F:= FT2R a * FT2R f ).
field_simplify_Rabs.
replace (F * d * d' + F * d + F * d' + e * d' + e + FT2R s0 * d' + FT2R s0 - s) with
((F * d * d' + F * d + F * d' + FT2R s0 * d') + (FT2R s0 - s) + (1 + d') * e) by nra.
eapply Rle_trans;
  [ apply Rabs_triang | ].
eapply Rle_trans;
  [  apply Rplus_le_compat; [eapply Rle_trans;
  [ apply Rabs_triang | ] |]  | ].
apply Rplus_le_compat_l; apply IHl .
rewrite Rabs_mult; apply Rmult_le_compat_l; [apply Rabs_pos | apply He].
rewrite  Rplus_assoc.
eapply Rle_trans;
  [  apply Rplus_le_compat_r ; eapply Rle_trans; [ apply Rabs_triang | ] | ].
apply Rplus_le_compat_l; rewrite Rabs_mult; rewrite Rmult_comm;
  apply Rmult_le_compat; [ apply Rabs_pos| apply Rabs_pos| apply Hd' | ].
{ apply Rabs_le_minus in IHl. 
  assert (Hs: Rabs (FT2R s0) <=
        g n2 * s1 + g1 n2 (n2 - 1) + s1).
  { eapply Rle_trans. apply IHl. 
  apply Rplus_le_compat.
  apply Rplus_le_compat.
  apply Rmult_le_compat; auto with commonDB; try apply Rle_refl.
  rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 (combine l l0)) s1); auto;
  apply Rabs_pos. 
  apply Rle_refl.
  rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 (combine l l0)) s1); auto;
  apply (dot_prod_sum_rel_R_Rabs (map FR2 (combine l l0))); auto. }
apply Hs. }
field_simplify.
unfold g1, g in IHl. 
field_simplify in IHl.
set (D:= default_rel).
set (E:= default_abs).
rewrite !Rplus_assoc.
rewrite H.
match goal with |-context[?A<= ?B] =>
replace A with (Rabs (F * d * d' + (F * d + F * d')) + ((1+ D) * g n2 *  s1 + D *  s1) +
 (D * g1 n2 (n2 - 1) + (g1 n2 (n2 -1) + Rabs (1 + d') * E))) by nra;
replace B with 
(g (S n2) * Rabs F + s1 * g (S n2) + g1 (S n2) (S n2 - 1) ) by
(rewrite Rmult_assoc, <-Rabs_mult; fold F; nra)
end.
apply Rplus_le_compat.
apply Rplus_le_compat.
unfold g.
eapply Rle_trans;
  [ apply Rabs_triang | ].
eapply Rle_trans;
  [ apply Rplus_le_compat; [rewrite !Rabs_mult| eapply Rle_trans; [apply Rabs_triang| ]] | ].
apply Rmult_le_compat; [rewrite <- Rabs_mult; apply Rabs_pos | apply Rabs_pos|  |  apply Hd'].
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd ].
apply Rplus_le_compat; rewrite Rabs_mult.
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd ].
apply Rmult_le_compat_l; [apply Rabs_pos  | apply Hd' ].
fold D. replace (Rabs F * D * D + (Rabs F * D + Rabs F * D)) with
  ( ((1 + D)*(1+D) - 1) * Rabs F ) by nra.
apply Rmult_le_compat_r; try apply Rabs_pos; unfold D, g.
apply Rplus_le_compat; try nra.
rewrite <- tech_pow_Rmult.
apply Rmult_le_compat_l; auto with commonDB.
eapply Rle_trans with ((1 + D)^1); try nra.
fold D; nra.
apply Rle_pow; auto with commonDB. 
apply Req_le. unfold D,E. rewrite one_plus_d_mul_g.
rewrite Rmult_comm.
repeat f_equal;  try lia.
rewrite <- !Rplus_assoc.
replace (D * g1 n2 (n2 - 1) + g1 n2 (n2 - 1)) with (g1 n2 (n2-1) * (1+D)) by nra.
unfold D.
rewrite one_plus_d_mul_g1; auto.
eapply Rle_trans; [apply Rplus_le_compat_l |].
apply Rmult_le_compat_r; unfold E; auto with commonDB.
assert (Rabs (1 + d') <= 1 + D).
eapply Rle_trans; [apply Rabs_triang| rewrite Rabs_R1].
apply Rplus_le_compat_l; apply Hd'.
apply H1.
eapply Rle_trans; [apply plus_d_e_g1_le; auto| apply Req_le; f_equal;lia].
Qed.

End SparseErrorRel1.

Section SparseErrorRel2. 
(* sparse forward error bound for fma dot product using inductive rels *) 
Context {NAN: Nans} {t : type}.

Variables (v1 v2 : list (ftype t)).
Hypothesis (Hlen : length v1 = length v2).

Variable (fp : ftype t).
Hypothesis Hfp : fma_dot_prod_rel (combine v1 v2) fp.
Hypothesis Hfin: Binary.is_finite (fprec t) (femax t) fp = true.

Notation v1R := (map FT2R v1).
Notation vR  := (map FR2 (combine v1 v2)).
Notation vR' := (map Rabsp (map FR2 (combine v1 v2))).

Variable (rp rp_abs : R).
Hypothesis Hrp  : R_dot_prod_rel vR rp.
Hypothesis Hra : R_dot_prod_rel vR' rp_abs.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).
Notation D := (@default_rel t).
Notation E := (@default_abs t).
Notation nnzR := (nnzR v1R).

Lemma sparse_fma_dotprod_forward_error:
  Rabs (FT2R fp - rp) <=  g nnzR * rp_abs + g1 nnzR (nnzR - 1).
Proof.
revert Hlen Hfp Hfin Hrp Hra.
revert rp rp_abs fp v2.
unfold nnz.
induction v1; intros.
{ simpl in Hlen; symmetry in Hlen; apply length_zero_iff_nil in Hlen; subst. 
inversion Hfp; inversion Hrp; subst; simpl; field_simplify_Rabs. 
  rewrite Rabs_R0. 
  apply Rplus_le_le_0_compat; auto with commonDB.
  apply Rmult_le_pos;  auto with commonDB.
 rewrite <- (R_dot_prod_rel_Rabs_eq [] rp_abs); auto;
  apply Rabs_pos. }
destruct v2; try discriminate.
assert (Hlen1 : length l = length l0) by (simpl; auto).
set (n2:= (common.nnzR (map FT2R l))%nat) in *.
inversion Hrp. inversion Hfp. inversion Hra; subst. 
assert (HFIN: Binary.is_finite (fprec t) (femax t) s0 = true).
{ simpl in Hfin. destruct a; destruct f; destruct s0;
   try discriminate; simpl in *; auto;
  destruct s0; destruct s2; destruct s3; try discriminate; auto. }
simpl. 
specialize (IHl s s1 s0 l0 Hlen1 H6 HFIN H2 H10).
(* reason by cases on the head of the list *) 
destruct (Req_EM_T (FT2R a) 0%R). 
(* start  head of list is zero *)
{ rewrite e. unfold common.nnzR; rewrite nnz_cons.
replace (FT2R (BFMA a f s0)) with (FT2R s0).
field_simplify_Rabs. 
eapply Rle_trans; [apply IHl|]. 
apply Req_le; f_equal; try nra. unfold n2, common.nnzR. 
rewrite Rabs_R0, Rmult_0_l,  Rplus_0_l; nra.
pose proof Bfma_mult_0R a f s0 Hfin as H; destruct H; auto; rewrite H;
try rewrite Bplus_neg_zero; try rewrite Bplus_neg_zero; auto;
repeat (destruct s0; simpl; auto). } (* end head of list is zero *) 
(* start head of list is non-zero *)
unfold common.nnzR, nnz. rewrite !count_occ_cons_neq; auto.
set (l1:= (map FT2R l)) in *.
set (n1:= (length (FT2R a :: l1) - @count_occ R Req_EM_T l1 0%R)%nat).
assert (n1 = S n2).
{ unfold n1, n2. pose proof @count_occ_bound R Req_EM_T 0%R l1.
  unfold common.nnzR, nnz.
  destruct (count_occ Req_EM_T l1 0%R); unfold l1 in *; simpl; try lia. }
(* start case on nnz = case on nnz in tail *)
assert (H0: (n2 = 0)%nat \/ (1<=n2)%nat) by lia; destruct H0. 
(* tail all zeros *)
{ rewrite H0 in *. rewrite H.
pose proof R_dot_prod_rel_nnzR l l0 Hlen1 s H2 H0; subst.
pose proof fma_dot_prod_rel_nnzR l l0 Hlen1 s0 H6 HFIN H0.
pose proof R_dot_prod_rel_nnzR_abs l l0 Hlen1 s1 H10 H0; subst.
destruct (fma_accurate' a f s0 Hfin) as (e & d & ed & He & Hd & Hacc).
rewrite Hacc; clear Hacc. 
rewrite H1.
unfold g1, g.
simpl; field_simplify; 
field_simplify_Rabs. 
eapply  Rle_trans; [apply Rabs_triang | ].
apply Rplus_le_compat.
rewrite Rabs_mult.
rewrite Rmult_comm.
rewrite Rabs_mult. rewrite Rmult_assoc.
apply Rmult_le_compat_r; auto with commonDB.
rewrite <- Rabs_mult; apply  Rabs_pos.
eapply Rle_trans; [apply Hd| ]; auto with commonDB; nra.
}
pose proof (fma_accurate' a f s0 Hfin) as Hplus.
destruct Hplus as (d' & e'& Hz & Hd'& He'& Hplus); rewrite Hplus;
  clear Hplus.
(* algebra *)
field_simplify_Rabs.
replace (FT2R a * FT2R f * d' + FT2R s0 * d' + FT2R s0 + e' - s) with
   (d' * (FT2R a * FT2R f) + d' * FT2R s0 + (FT2R s0 - s) + e') by nra.
eapply Rle_trans;
  [ apply Rabs_triang | eapply Rle_trans; [ apply Rplus_le_compat_r; apply Rabs_triang
    | ] ].
eapply Rle_trans;
  [  apply Rplus_le_compat_r | ].
apply Rplus_le_compat_r.
apply Rabs_triang.
eapply Rle_trans;
  [apply Rplus_le_compat_r; apply Rplus_le_compat_l | ].
apply IHl.
eapply Rle_trans;
  [apply Rplus_le_compat; [apply Rplus_le_compat_r| apply He' ] | ].
apply Rplus_le_compat.
rewrite Rabs_mult;
apply Rmult_le_compat_r; try apply Rabs_pos;
apply Hd'.
rewrite Rabs_mult;
apply Rmult_le_compat; try apply Rabs_pos.
apply Hd'.
apply Rabs_le_minus in IHl.
assert (Hs: Rabs (FT2R s0) <=
      g n2 * s1 + g1 n2 (n2  - 1) + s1).
{ eapply Rle_trans. apply IHl. 
apply Rplus_le_compat_l.
rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 (combine l l0)) s1); auto. 
apply (dot_prod_sum_rel_R_Rabs (map FR2 (combine l l0))); auto. }
apply Hs.
set (F:=Rabs (FT2R a * FT2R f)).
rewrite !Rmult_plus_distr_l.
replace (D * F + (D * (g  n2 * s1) + D * g1 n2 (n2 - 1) + D * s1) +
(g n2 * s1 + g1  n2 (n2 - 1)) + E) with
(D * F + ((1 + D) * g  n2 * s1 + D * s1) + g1 n2 (n2 - 1) * (1 + D) + E) by nra.
rewrite one_plus_d_mul_g. rewrite one_plus_d_mul_g1; auto.
rewrite Rplus_assoc.
apply Rplus_le_compat.
apply Rplus_le_compat.
rewrite <- Rabs_mult. fold F.
apply Rmult_le_compat_r.
unfold F; apply Rabs_pos.
apply d_le_g_1; lia.
apply Rmult_le_compat_r.
rewrite <- (R_dot_prod_rel_Rabs_eq (map FR2 (combine l l0)) s1); auto. apply Rabs_pos.
apply Req_le; f_equal; auto; lia.
rewrite H.
eapply Rle_trans.
apply plus_e_g1_le; auto.
rewrite <- H.
replace n2 with (n1 - 1)%nat; try nra; lia.
Qed.

End SparseErrorRel2.
