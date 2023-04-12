Require Import vcfloat.VCFloat.
Require Import List.
Require Import common op_defs list_lemmas float_acc_lems.
Require Import FunctionalExtensionality.

Require Import Reals.
Open Scope R.

Import ListNotations.

Section DotProdGeneric.


Definition dotprod {A} (mult plus: A -> A -> A) (zero : A) (v1 v2: list A):=
  fold_left (fun s x12 => plus (mult (fst x12) (snd x12)) s) 
                (combine v1 v2) zero.

Lemma dotprod_nil_l :
  forall A (l : list A)
  (mult plus : A -> A -> A) (zero : A), dotprod mult plus zero nil l = zero.
Proof. intros; induction l; simpl; auto. Qed.

Lemma dotprod_nil_r :
  forall A (l : list A)
  (mult plus : A -> A -> A) (zero : A), dotprod mult plus zero l nil = zero.
Proof. intros; induction l; simpl; auto. Qed.

Lemma dotprod_single :
  forall A (l : list A) 
  (mult plus : A -> A -> A) (zero a2: A) 
  (Hpz : forall y, plus y zero = y)
  (Hmz : forall y, mult zero y = zero), 
let a1 := nth 0 l zero in 
dotprod mult plus zero l [a2] = mult a1 a2.
Proof. intros; simpl; destruct l.
rewrite dotprod_nil_l. subst a1. simpl; auto.
unfold dotprod. rewrite combine_firstn_r. simpl; auto.
Qed.

End DotProdGeneric.

Section DotProdFloat.
Context {NAN : Nans} {t : type}.

Definition dotprodF : list (ftype t) -> list (ftype t) -> ftype t := 
  dotprod BMULT BPLUS (Zconst t 0).

Inductive dot_prod_rel : 
            list (ftype t * ftype t) -> ftype t -> Prop :=
| dot_prod_rel_nil  : dot_prod_rel  nil (Zconst t 0)
| dot_prod_rel_cons : forall l (xy : ftype t * ftype t) s,
    dot_prod_rel  l s ->
    dot_prod_rel  (xy::l) (BPLUS (BMULT  (fst xy) (snd xy)) s).

Lemma dotprodF_rel_fold_right :
forall (v1 v2: list (ftype t)), 
    dot_prod_rel (rev (List.combine v1 v2)) (dotprodF v1 v2).
Proof.
intros v1 v2. unfold dotprodF, dotprod; rewrite <- fold_left_rev_right. 
induction (rev (List.combine v1 v2)).
{ simpl; auto. apply dot_prod_rel_nil. }
simpl. apply dot_prod_rel_cons. auto.
Qed.

End DotProdFloat.

Section DotProdFMA.
Context {NAN : Nans} {t : type}.

(* FMA dot-product *)
Definition fma_dotprod (v1 v2: list (ftype t)) : ftype t :=
  fold_left (fun s x12 => BFMA (fst x12) (snd x12) s) 
                (List.combine v1 v2) (Zconst t 0).

Inductive fma_dot_prod_rel : 
            list (ftype t * ftype t) -> ftype t -> Prop :=
| fma_dot_prod_rel_nil  : fma_dot_prod_rel nil (Zconst t 0)
| fma_dot_prod_rel_cons : forall l (xy : ftype t * ftype t) s,
    fma_dot_prod_rel  l s ->
    fma_dot_prod_rel  (xy::l) (BFMA (fst xy) (snd xy) s).


Lemma fma_dot_prod_rel_fold_right  :
forall (v1 v2: list (ftype t)), 
    fma_dot_prod_rel (rev (List.combine v1 v2)) (fma_dotprod v1 v2).
Proof.
intros v1 v2. 
 unfold fma_dotprod; rewrite <- fold_left_rev_right. 
induction (rev (List.combine v1 v2)).
{ simpl; auto. apply fma_dot_prod_rel_nil. }
simpl. apply fma_dot_prod_rel_cons. auto.
Qed.

End DotProdFMA.

Section RealDotProd.

Definition dotprodR l1 l2 : R := 
  fold_left Rplus (map (uncurry Rmult) (List.combine l1 l2)) 0%R.

Inductive R_dot_prod_rel : 
            list (R * R) -> R -> Prop :=
| R_dot_prod_rel_nil  : R_dot_prod_rel  nil 0%R
| R_dot_prod_rel_cons : forall l xy s,
    R_dot_prod_rel  l s ->
    R_dot_prod_rel  (xy::l)  (fst xy * snd xy + s).

Lemma R_dot_prod_rel_eq :
  forall l a b 
  (Ha: R_dot_prod_rel l a)
  (Hb: R_dot_prod_rel l b), a = b.
Proof.
induction l.
{ intros; inversion Ha; inversion Hb; auto. }
intros; inversion Ha; inversion Hb; subst; f_equal. 
apply IHl; auto.
Qed.

Definition Rabsp p : R * R := (Rabs (fst p), Rabs (snd p)).

Definition FR2 {t: type} (x12: ftype t * ftype t) := (FT2R (fst x12), FT2R (snd x12)).

Lemma FT2R_FR2 t : 
  (forall a a0 : ftype t, (FT2R a, FT2R a0) = FR2 (a, a0)) .
Proof. intros. unfold FR2; simpl; auto. Qed.

Definition sum_fold: list R -> R := fold_right Rplus 0%R.

Lemma dotprodR_nil_l u:
dotprodR nil u = 0%R. 
Proof. simpl; auto. Qed.

Lemma dotprodR_nil_r u:
dotprodR u nil = 0%R. 
Proof. 
unfold dotprodR, dotprod; rewrite combine_nil; simpl; auto. 
Qed.


Lemma sum_rev l:
sum_fold l = sum_fold (rev l).
Proof.
unfold sum_fold. 
rewrite fold_left_rev_right.
replace (fun x y : R => y + x) with Rplus
 by (do 2 (apply FunctionalExtensionality.functional_extensionality; intro); lra).
induction l; simpl; auto.
rewrite IHl.
rewrite <- fold_left_Rplus_0; f_equal; nra.
Qed.

Lemma Rplus_rewrite :
(fun x y  => x + y) = Rplus.
Proof. (do 2 (apply functional_extensionality; intro); lra).
Qed.

Lemma dotprodR_rel :
forall (v1 v2: list R) , 
    R_dot_prod_rel ((List.combine v1 v2)) (dotprodR v1 v2).
Proof.
intros; unfold dotprodR;
induction (((combine v1 v2))).
{ simpl. apply R_dot_prod_rel_nil. }
destruct a; simpl. 
unfold dotprodR. simpl.
rewrite fold_left_Rplus_Rplus.
apply R_dot_prod_rel_cons; auto.
Qed.

Lemma dotprodR_rev : forall (v1 v2: list R) , 
  length v1 = length v2 -> 
  dotprodR v1 (rev v2) = dotprodR (rev v1) v2.
Proof.
intros; unfold dotprodR.
replace (combine v1 (rev v2)) with
  (rev (combine (rev v1) v2)).
rewrite <- fold_left_rev_right.
replace (fun x y : R => y + x) with Rplus
 by (do 2 (apply functional_extensionality; intro); lra).
symmetry.
induction (combine (rev v1) v2).
simpl; auto.
match goal with |- context [?A = ?B] =>
set (y:= B)
end. 
simpl. subst y.
rewrite fold_left_Rplus_Rplus.
rewrite IHl.
rewrite !map_rev, !rev_involutive.
simpl; auto.
rewrite <- combine_rev, rev_involutive; auto.
rewrite rev_length; auto.
Qed.

Lemma R_dot_prod_rel_fold_right t :
forall (v1 v2: list (ftype t)) , 
   let prods := map (uncurry Rmult) (map FR2 (List.combine v1 v2)) in
    R_dot_prod_rel (rev (map FR2 (List.combine v1 v2))) (sum_fold prods).
Proof.
intros. subst prods. rewrite sum_rev. rewrite <- !map_rev.
induction (map FR2 (rev (combine v1 v2))).
{ simpl. apply R_dot_prod_rel_nil. }
destruct a; simpl. apply R_dot_prod_rel_cons; auto.
Qed.

Lemma R_dot_prod_rel_fold_right' t :
forall (v1 v2: list (ftype t)) , 
   let prods := map (uncurry Rmult) (map FR2 (List.combine v1 v2)) in
    R_dot_prod_rel (rev (map FR2 (List.combine v1 v2))) (dotprodR (map FT2R v1) (map FT2R v2)).
Proof.
intros. subst prods. unfold dotprodR. rewrite <- !map_rev.
rewrite (combine_map _ _ _ FR2); auto. 
rewrite <- (rev_involutive (combine v1 v2)) at 2.
rewrite <- fold_left_rev_right.
rewrite (rev_involutive (combine v1 v2)) .
rewrite <- !map_rev. 
induction (map FR2 (rev (combine v1 v2))).
{ simpl. apply R_dot_prod_rel_nil. }
destruct a; simpl. rewrite Rplus_comm. apply R_dot_prod_rel_cons; auto.
Qed.

Lemma R_dot_prod_rel_fold_right_Rabs t :
forall (v1 v2: list (ftype t)) , 
   let prods := map (uncurry Rmult) (map Rabsp (map FR2 (List.combine v1 v2))) in
    R_dot_prod_rel (rev (map Rabsp (map FR2 (List.combine v1 v2)))) (sum_fold prods).
Proof.
intros. subst prods. rewrite sum_rev. rewrite <- !map_rev.
induction (map Rabsp (map FR2 (rev (combine v1 v2)))).
{ simpl. apply R_dot_prod_rel_nil. }
destruct a; simpl. apply R_dot_prod_rel_cons; auto.
Qed.

Lemma R_dot_prod_rel_fold_right_Rabs' t :
forall (v1 v2: list (ftype t)) , 
   let prods := map (uncurry Rmult) (map Rabsp (map FR2 (List.combine v1 v2))) in
   R_dot_prod_rel (rev (map Rabsp (map FR2 (List.combine v1 v2)))) (dotprodR (map Rabs (map FT2R v1)) (map Rabs (map FT2R v2))).
Proof.
intros. subst prods. unfold dotprodR. rewrite <- !map_rev.
rewrite (combine_map _ _ _ Rabsp); auto. 
rewrite (combine_map _ _ _ FR2); auto. 
rewrite <- (rev_involutive (combine v1 v2)) at 2.
rewrite <- fold_left_rev_right.
rewrite (rev_involutive (combine v1 v2)) .
rewrite <- !map_rev. 
induction (map Rabsp (map FR2 (rev (combine v1 v2)))).
{ simpl. apply R_dot_prod_rel_nil. }
destruct a; simpl. rewrite Rplus_comm. apply R_dot_prod_rel_cons; auto.
Qed.

Lemma R_dot_prod_rel_single rs a:
R_dot_prod_rel [a] rs -> rs = (fst a * snd a).
Proof.
intros.
inversion H.
inversion H3; subst; nra.
Qed.

Lemma R_dot_prod_rel_single' a:
R_dot_prod_rel [a] (fst a * snd a).
Proof.
replace (fst a * snd a) with (fst a * snd a + 0) by nra.
apply R_dot_prod_rel_cons; apply R_dot_prod_rel_nil.
Qed.

Lemma R_dot_prod_rel_Rabs_eq :
forall l s,
R_dot_prod_rel (map Rabsp l) s -> Rabs s = s.
Proof.
induction  l.
{ intros.
inversion H.
rewrite Rabs_R0.
nra. }
intros.
inversion H; subst; clear H.
unfold Rabsp. destruct a; simpl.
replace (Rabs(Rabs r * Rabs r0 + s0)) with 
  (Rabs r * Rabs r0 + s0); try nra.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos;
apply Rabs_pos.
rewrite <- IHl; try apply Rabs_pos; auto.
Qed.

Lemma dot_prod_sum_rel_R_Rabs :
forall l s1 s2,
R_dot_prod_rel l s1 -> R_dot_prod_rel (map Rabsp l) s2 -> Rabs s1 <= Rabs s2.
Proof.
induction l.
{ intros.
inversion H.
inversion H0.
nra. }
intros.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
unfold Rabsp; destruct a; simpl.
eapply Rle_trans; [
apply Rabs_triang |].
replace (Rabs (Rabs r * Rabs r0 + s0)) with 
  (Rabs r * Rabs r0 + s0).
eapply Rplus_le_compat; try nra.
rewrite Rabs_mult; nra.
rewrite <- (R_dot_prod_rel_Rabs_eq l); auto.
symmetry.
rewrite Rabs_pos_eq; try nra.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos;
apply Rabs_pos.
rewrite <- (R_dot_prod_rel_Rabs_eq l); auto.
apply Rabs_pos.
Qed.

Lemma dot_prod_combine_map_Rmult a u v r:
length u = length v ->
R_dot_prod_rel (combine u v) r -> 
R_dot_prod_rel (combine (map (Rmult a) u) v) (a * r). 
Proof. revert u r. induction v.
{ intros. rewrite !combine_nil in *.  
  inversion H0; subst; rewrite Rmult_0_r; apply R_dot_prod_rel_nil. }
destruct u.
  { intros; pose proof Nat.neq_0_succ (length v); try contradiction. }
  intros.   inversion H0. assert (Hlen: length u = length v) by (simpl in H; lia).
  specialize (IHv u s Hlen H4).
  simpl. replace (a * (r * a0 + s)) with 
    (a * r * a0 + a * s) by nra. apply R_dot_prod_rel_cons; auto.
Qed.

Lemma dotprod_rel_R_exists {NAN: Nans}:
  forall (t : type) (l : list (ftype t * ftype t)) (fp : ftype t)
  (Hfp : dot_prod_rel l fp),
  exists rp, R_dot_prod_rel (map FR2 l) rp.
Proof.
intros ?. induction l.
{ simpl; exists 0. apply R_dot_prod_rel_nil. }
intros. inversion Hfp; subst. 
destruct (IHl s H2) as (rs & Hrs); clear IHl.
exists (FT2R (fst a) * FT2R (snd a) + rs); simpl. 
apply R_dot_prod_rel_cons; auto.
Qed.

Lemma dotprod_rel_R_exists_fma {NAN: Nans}:
  forall (t : type) (l : list (ftype t * ftype t)) (fp : ftype t)
  (Hfp : fma_dot_prod_rel l fp),
  exists rp, R_dot_prod_rel (map FR2 l) rp.
Proof.
intros ?. induction l.
{ simpl; exists 0. apply R_dot_prod_rel_nil. }
intros. inversion Hfp; subst. 
destruct (IHl s H2) as (rs & Hrs); clear IHl.
exists (FT2R (fst a) * FT2R (snd a) + rs); simpl. 
apply R_dot_prod_rel_cons; auto.
Qed.

Lemma sum_rel_R_abs_exists_fma {NAN: Nans}:
  forall (t : type) (l : list (ftype t * ftype t)) (fp : ftype t)
  (Hfp : fma_dot_prod_rel l fp),
  exists rp, R_dot_prod_rel (map Rabsp (map FR2 l)) rp.
Proof.
intros ?. induction l.
{ simpl; exists 0. apply R_dot_prod_rel_nil. }
intros. inversion Hfp; subst. 
destruct (IHl s H2) as (rs & Hrs); clear IHl.
exists (Rabs (FT2R (fst a)) * Rabs (FT2R (snd a)) + rs); simpl. 
apply R_dot_prod_rel_cons; auto.
Qed.

Lemma dotprodR_rel_bound'  :
  forall (t : type) (l : list (ftype t * ftype t)) (rp a: R)
  (Ha : 0 <= a)
  (Hrp : R_dot_prod_rel (map FR2 l) rp)
  (Hin : forall x, In x l -> Rabs (FT2R (fst x)) <= sqrt a /\ Rabs (FT2R (snd x)) <= sqrt a),
  Rabs rp <= INR (length l) * a.
Proof.
induction l; intros.
{ inversion Hrp; subst; simpl; rewrite Rabs_R0; nra. }
  inversion Hrp; subst. 
  eapply Rle_trans; [apply Rabs_triang|].
  eapply Rle_trans; [apply Rplus_le_compat | ].
  rewrite Rabs_mult; apply Rmult_le_compat; try apply Rabs_pos.
  apply Hin; simpl; auto.
  apply Hin; simpl; auto.
  apply IHl; auto; [ apply Ha| intros; apply Hin; simpl; auto].
  rewrite sqrt_def; auto. apply Req_le;
  replace (length (a::l)) with ( S(length l)) by auto. 
  rewrite S_INR; nra.
Qed.

Lemma dotprodR_rel_bound''  :
  forall (t : type) (l : list (ftype t * ftype t)) (rs_abs a: R)
  (Ha : 0 <= a)
  (Hrp : R_dot_prod_rel (map Rabsp (map FR2 l)) rs_abs)
  (Hin : forall x, In x l -> Rabs (FT2R (fst x)) <= sqrt a /\ Rabs (FT2R (snd x)) <= sqrt a),
  rs_abs <= INR (length l) * a.
Proof.
induction l; intros.
{ inversion Hrp; subst; simpl; nra. }
  inversion Hrp; subst. 
  eapply Rle_trans; [ apply Rplus_le_compat | ].
  apply Rmult_le_compat; 
  [ destruct a; simpl; apply Rabs_pos | destruct a; simpl; apply Rabs_pos | | ].
  apply Hin; simpl; auto.
  apply Hin; simpl; auto.
  apply IHl; auto; [ apply Ha| intros; apply Hin; simpl; auto].
  rewrite sqrt_def; auto. apply Req_le;
  replace (length (a::l)) with ( S(length l)) by auto. 
  rewrite S_INR; nra.
Qed.


End RealDotProd.


Section NonZeroDP.
Context {NAN: Nans} {t : type}.

Variables (v1 v2 : list (ftype t)).
Hypothesis (Hlen : length v1 = length v2).

Notation v1R := (map FT2R v1).

Lemma dot_prod_rel_nnzR :
forall 
(fp : ftype t)
(Hfp : dot_prod_rel (combine v1 v2) fp)
(Hfin: Binary.is_finite (fprec t) (femax t) fp = true),
nnzR v1R = 0%nat -> FT2R fp = 0.
Proof.
intros.
pose proof nnz_lemma _ _ v1R _ H.
revert H0 H Hfp Hlen Hfin. revert v2 fp.
induction v1; intros.
simpl in *; inversion Hfp; auto.
destruct v2; try discriminate; auto.
inversion Hfp; subst.
unfold fst, snd.
assert (Hin: forall x : R, In x (map FT2R l) -> x = 0).
{ intros. apply H0; simpl; auto. }
assert (Hlen1:  length l = length l0) by (simpl; auto).
assert (HFIN: Binary.is_finite (fprec t) (femax t) s = true).
{ simpl in Hfin. destruct (BMULT a f); destruct s;
  destruct s0; try discriminate; simpl in *; auto; 
  destruct s; try discriminate; auto.
}
pose proof nnz_is_zero_cons _ (FT2R a) (map FT2R l) _ _ H as H1.
specialize (IHl l0 s Hin H1 H4 Hlen1 HFIN).
destruct (@BPLUS_accurate' t NAN (BMULT a f) s Hfin)
  as (d & _ & Hacc).
rewrite Hacc; clear Hacc.
rewrite IHl.
assert (HFIN2: Binary.is_finite (fprec t) (femax t) (BMULT a f) = true).
{ simpl in Hfin. destruct (BMULT a f); destruct s; try discriminate; auto. } 
assert (Ha: FT2R a = 0).
apply H0; simpl; auto.
pose proof Bmult_0R _ _ HFIN2 Ha as H2; destruct H2; rewrite H2;
simpl; nra.
Qed.

Lemma fma_dot_prod_rel_nnzR :
forall 
(fp : ftype t)
(Hfp : fma_dot_prod_rel (combine v1 v2) fp)
(Hfin: Binary.is_finite (fprec t) (femax t) fp = true),
nnzR v1R = 0%nat -> FT2R fp = 0.
Proof.
intros.
pose proof nnz_lemma _ _ v1R _ H.
revert H0 H Hfp Hlen Hfin. revert v2 fp.
induction v1; intros.
simpl in *; inversion Hfp; auto.
destruct v2; try discriminate; auto.
inversion Hfp; subst.
unfold fst, snd.
assert (Hin: forall x : R, In x (map FT2R l) -> x = 0).
{ intros. apply H0; simpl; auto. }
assert (Hlen1:  length l = length l0) by (simpl; auto).
assert (HFIN: Binary.is_finite (fprec t) (femax t) s = true).
{ simpl in Hfin. destruct a; destruct f; destruct s;
  destruct s0; destruct s1; destruct s; try discriminate; simpl in *; auto; 
  try discriminate; auto. }
pose proof nnz_is_zero_cons _ (FT2R a) (map FT2R l) _ _ H as H1.
specialize (IHl l0 s Hin H1 H4 Hlen1 HFIN).
assert (Ha: FT2R a = 0).
apply H0; simpl; auto.
rewrite (Bfma_mult_0R a f s  Hfin Ha).
rewrite IHl; auto.
Qed.


Lemma R_dot_prod_rel_nnzR :
forall 
(rp : R)
(Hrp  : R_dot_prod_rel (map FR2 (combine v1 v2)) rp),
nnzR v1R = 0%nat -> rp = 0.
Proof.
intros ? ? H.
pose proof nnz_lemma _ _ v1R _ H.
revert H0 H Hrp  Hlen. revert v2 rp.
induction v1; intros.
simpl in *; inversion Hrp; auto.
destruct v2; try discriminate; auto.
inversion Hrp; subst.
unfold FR2, fst, snd.
assert (Hin: forall x : R, In x (map FT2R l) -> x = 0).
{ intros. apply H0; simpl; auto. }
assert (Hlen1:  length l = length l0) by (simpl; auto).
pose proof nnz_is_zero_cons _ (FT2R a) (map FT2R l) _ _ H as H1.
specialize (IHl l0 s Hin H1 H4 Hlen1).
rewrite IHl.
specialize (H0 (FT2R a)).
rewrite H0; [|simpl;auto]; nra.
Qed.


Lemma R_dot_prod_rel_nnzR_abs :
forall 
(rp_abs : R) 
(Hra : R_dot_prod_rel (map Rabsp (map FR2 (combine v1 v2))) rp_abs),
nnzR v1R = 0%nat -> rp_abs = 0.
Proof.
intros ? ? H.
pose proof nnz_lemma _ _ v1R  _ H.
revert H0 H Hra  Hlen. revert v2 rp_abs .
induction v1; intros.
simpl in *. inversion Hra. auto.
destruct v2; try discriminate; auto.
inversion Hra; subst.
unfold FR2, Rabsp, fst, snd.
assert (Hin: forall x : R, In x (map FT2R l) -> x = 0).
{ intros. apply H0; simpl; auto. }
assert (Hlen1:  length l = length l0) by (simpl; auto).
pose proof nnz_is_zero_cons _ (FT2R a) (map FT2R l) _ _ H as H2.
specialize (IHl l0 s Hin H2 H4 Hlen1). 
rewrite IHl.
pose proof in_map Rabs (map FT2R (a::l)).
specialize (H0  (FT2R a)).
rewrite H0; [|simpl;auto]. rewrite Rabs_R0. nra.
Qed.


End NonZeroDP.