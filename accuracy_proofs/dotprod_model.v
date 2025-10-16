From LAProof.accuracy_proofs Require Import preamble common 
                                           list_lemmas
                                            float_acc_lems.
Require Import FunctionalExtensionality.

Section DotProdGeneric.

Definition dotprod {A} (mult plus: A -> A -> A) (zero : A) (v1 v2: list A):A :=
  foldl  (Basics.flip plus) zero (map (uncurry mult) (zip v1 v2)).

Lemma dotprod_nil_l :
  forall A (l : list A)
  (mult plus : A -> A -> A) (zero : A), dotprod mult plus zero nil l = zero.
Proof. destruct l; auto. Qed.

Lemma dotprod_nil_r :
  forall A (l : list A)
  (mult plus : A -> A -> A) (zero : A), dotprod mult plus zero l nil = zero.
Proof. destruct l; auto. Qed.

Lemma dotprod_single :
  forall A (l : list A) 
  (mult plus : A -> A -> A) (zero a2: A) 
  (Hpz : forall y, plus y zero = y)
  (Hmz : forall y, mult zero y = zero), 
let a1 := nth zero l 0 in 
dotprod mult plus zero l [a2] = mult a1 a2.
Proof.
intros; simpl; destruct l.
- rewrite dotprod_nil_l. subst a1. simpl; auto.
- unfold dotprod. rewrite /= {2}/Basics.flip Hpz. destruct l; auto.
Qed.

End DotProdGeneric.

Section DotProdFloat.
Context {NAN : FPCore.Nans} {t : type}.

Definition dotprodF : list (ftype t) -> list (ftype t) -> ftype t := 
  dotprod BMULT BPLUS pos_zero.

Inductive dot_prod_rel : 
            list (ftype t * ftype t) -> ftype t -> Prop :=
| dot_prod_rel_nil  : dot_prod_rel  nil pos_zero
| dot_prod_rel_cons : forall l (xy : ftype t * ftype t) s,
    dot_prod_rel  l s ->
    dot_prod_rel  (xy::l) (BPLUS (BMULT  (fst xy) (snd xy)) s).

Lemma dotprodF_rel_fold_right :
forall (v1 v2: list (ftype t)), 
    dot_prod_rel (rev (zip v1 v2)) (dotprodF v1 v2).
Proof.
intros v1 v2. unfold dotprodF, dotprod.
rewrite -(revK (map _ (zip v1 v2))) foldl_rev -map_rev.
induction (rev _) as [ | [x y] l]; constructor; auto.
Qed.

End DotProdFloat.

Section DotProdFMA.
Context {NAN : FPCore.Nans} {t : type}.

(* FMA dot-product *)
Definition fma_dotprod (v1 v2: list (ftype t)) : ftype t :=
  foldl (fun s x12 => BFMA (fst x12) (snd x12) s) pos_zero (zip v1 v2).

Inductive fma_dot_prod_rel : 
            list (ftype t * ftype t) -> ftype t -> Prop :=
| fma_dot_prod_rel_nil  : fma_dot_prod_rel nil (Zconst t 0)
| fma_dot_prod_rel_cons : forall l (xy : ftype t * ftype t) s,
    fma_dot_prod_rel  l s ->
    fma_dot_prod_rel  (xy::l) (BFMA (fst xy) (snd xy) s).


Lemma fma_dot_prod_rel_fold_right  :
forall (v1 v2: list (ftype t)), 
    fma_dot_prod_rel (rev (zip v1 v2)) (fma_dotprod v1 v2).
Proof.
intros v1 v2. 
 unfold fma_dotprod. 
rewrite -{2}(revK (zip v1 v2)) foldl_rev.
induction (rev _).
{ simpl; auto. apply fma_dot_prod_rel_nil. }
simpl. apply fma_dot_prod_rel_cons. auto.
Qed.

End DotProdFMA.


Section RealDotProd.

Definition dotprodR: forall l1 l2 : seq R, R:= 
  dotprod Rmult Rplus 0%R.

Inductive R_dot_prod_rel :   list (R * R) -> R -> Prop :=
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
  forall a a0 : ftype t, (FT2R a, FT2R a0) = FR2 (a, a0).
Proof. reflexivity. Qed.

Definition sum_fold: list R -> R := foldr Rplus 0%R.

Lemma dotprodR_nil_l u:
dotprodR nil u = 0. 
Proof. intros; apply dotprod_nil_l. Qed.

Lemma dotprodR_nil_r u:
dotprodR u nil = 0. 
Proof. intros; apply dotprod_nil_r. Qed.

Lemma flip_Rplus: Basics.flip Rplus = Rplus.
Proof. 
rewrite /Basics.flip;
do 2 (apply FunctionalExtensionality.functional_extensionality; intro); lra.
Qed.

Lemma Rplus_rewrite : (fun x y  => x + y)%Re = Rplus.
Proof. reflexivity. Qed.

Lemma sum_rev l:   sum_fold l = sum_fold (rev l).
Proof.
rewrite /sum_fold -foldl_rev foldl_foldr.
f_equal; do 2 (apply FunctionalExtensionality.functional_extensionality; intro); lra.
hnf; intros; lra.
hnf; intros; lra.
Qed.

Lemma dotprodR_rel :
forall (v1 v2: list R) , 
    R_dot_prod_rel (zip v1 v2) (dotprodR v1 v2).
Proof.
intros; unfold dotprodR, dotprod.
induction (zip v1 v2).
{ simpl. apply R_dot_prod_rel_nil. }
evar (z: R).
replace   (foldl _ _ _) with z.
apply R_dot_prod_rel_cons; apply IHl.
subst z.
clear.
rewrite !foldl_foldr;  [ | compute; intros; lra..].
destruct a as [x y]; simpl.
rewrite Rplus_comm //.
Qed.

Lemma dotprodR_rel_inj: forall l s1 s2, 
  R_dot_prod_rel l s1 -> R_dot_prod_rel l s2 -> s1=s2.
Proof.
induction l; intros; inversion H; clear H; inversion H0; clear H1; subst; f_equal; auto.
Qed.

Lemma dotprodR_rev : forall (v1 v2: list R) , 
  size v1 = size v2 -> 
  dotprodR v1 (rev v2) = dotprodR (rev v1) v2.
Proof.
intros.
rewrite /dotprodR /dotprod -{1}(revK v1) -rev_zip ?size_rev //.
rewrite {2}flip_Rplus map_rev foldl_rev foldl_foldr //; compute; intros; lra.
Qed.

Lemma map_FR2_zip: forall {t} (v1 v2: seq (ftype t)), 
  map FR2 (zip v1 v2) = zip (map FT2R v1) (map FT2R v2).
Proof.
induction v1; destruct v2; simpl; f_equal; auto.
Qed.

Lemma map_Rabsp_zip: forall (v1 v2: seq R), 
  map Rabsp (zip v1 v2) = zip (map Rabs v1) (map Rabs v2).
Proof.
induction v1; destruct v2; simpl; f_equal; auto.
Qed.

Lemma R_dot_prod_rel_fold_right t :
forall (v1 v2: list (ftype t)) , 
   size v1 = size v2 ->
   let prods := map (uncurry Rmult) (map FR2 (zip v1 v2)) in
    R_dot_prod_rel (rev (map FR2 (zip v1 v2))) (sum_fold prods).
Proof.
intros.
subst prods.
rewrite map_FR2_zip.
move :(dotprodR_rel (rev (map FT2R v1))  (rev (map FT2R v2))).
rewrite  dotprodR_rev ?size_rev ?size_map // revK /sum_fold /dotprodR /dotprod 
 foldl_foldr //.
2,3: compute; intros; lra.
rewrite -rev_zip ?size_map ?flip_Rplus //.
Qed.

Lemma R_dot_prod_rel_fold_right' t :
forall (v1 v2: list (ftype t)) , 
   size v1 = size v2 ->
   let prods := map (uncurry Rmult) (map FR2 (zip v1 v2)) in
    R_dot_prod_rel (rev (map FR2 (zip v1 v2))) (dotprodR (map FT2R v1) (map FT2R v2)).
Proof.
intros.
replace (dotprodR _ _) with (sum_fold prods).
apply R_dot_prod_rel_fold_right; auto.
rewrite sum_rev /sum_fold /dotprodR /dotprod -foldl_rev revK /prods map_FR2_zip //.
Qed.

Lemma R_dot_prod_rel_fold_right_Rabs t :
forall (v1 v2: list (ftype t)) , 
   size v1 = size v2 ->
   let prods := map (uncurry Rmult) (map Rabsp (map FR2 (zip v1 v2))) in
    R_dot_prod_rel (rev (map Rabsp (map FR2 (zip v1 v2)))) (sum_fold prods).
Proof.
intros.
subst prods.
rewrite map_FR2_zip map_Rabsp_zip.
move :(dotprodR_rel (rev (map Rabs (map FT2R v1)))  (rev (map Rabs (map FT2R v2)))).
rewrite  dotprodR_rev ?size_rev ?size_map // revK /sum_fold /dotprodR /dotprod 
 foldl_foldr //.
2,3: compute; intros; lra.
rewrite -rev_zip ?size_map ?flip_Rplus //.
Qed.

Lemma R_dot_prod_rel_fold_right_Rabs' t :
forall (v1 v2: list (ftype t)) , 
   size v1 = size v2 ->
   let prods := map (uncurry Rmult) (map Rabsp (map FR2 (zip v1 v2))) in
   R_dot_prod_rel (rev (map Rabsp (map FR2 (zip v1 v2)))) (dotprodR (map Rabs (map FT2R v1)) (map Rabs (map FT2R v2))).
Proof.
intros.
replace (dotprodR _ _) with (sum_fold prods).
apply R_dot_prod_rel_fold_right_Rabs; auto.
rewrite sum_rev /sum_fold /dotprodR /dotprod -foldl_rev revK /prods map_FR2_zip map_Rabsp_zip //.
Qed.

Lemma R_dot_prod_rel_single rs a:
R_dot_prod_rel [::a] rs -> rs = (fst a * snd a).
Proof.
intros.
inversion H.
inversion H3; subst.
apply Rplus_0_r.
Qed.

Lemma R_dot_prod_rel_single' a:
R_dot_prod_rel [::a] (fst a * snd a).
Proof.
replace (fst a * snd a)%Re with (fst a * snd a + 0)%Re by apply Rplus_0_r.
apply R_dot_prod_rel_cons; apply R_dot_prod_rel_nil.
Qed.

Lemma R_dot_prod_rel_Rabs_eq :
forall l s,
R_dot_prod_rel (map Rabsp l) s -> Rabs s = s.
Proof.
induction  l; intros; inversion H; clear H; subst.
apply Rabs_R0.
unfold Rabsp. destruct a; simpl.
replace (Rabs(Rabs r * Rabs r0 + s0))%Re with 
  (Rabs r * Rabs r0 + s0)%Re; try nra.
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
replace (Rabs (Rabs r * Rabs r0 + s0))%Re with 
  (Rabs r * Rabs r0 + s0)%Re.
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

Lemma dot_prod_zip_map_Rmult a u v r:
size u = size v ->
R_dot_prod_rel (zip u v) r -> 
R_dot_prod_rel (zip (map (Rmult a) u) v) (a * r). 
Proof.
intros.
move :(dotprodR_rel u v) => H1.
move :(dotprodR_rel_inj _ _ _ H0 H1) => H2.
subst r.
clear H0 H1.
move :(dotprodR_rel (map (Rmult a) u) v) => H3.
replace (Rmult a (dotprodR u v)) with (dotprodR (map (Rmult a) u) v); auto.
clear - H.
unfold dotprodR, dotprod.
rewrite !foldl_foldr.
2,3,4,5: compute; intros; lra.
revert v H; induction u; destruct v; intros; inversion H; clear H; subst; simpl.
compute; lra.
rewrite IHu; auto.
rewrite {1 3}/Basics.flip.
lra.
Qed.

Lemma dotprod_rel_R_exists {NAN : FPCore.Nans} {t : type} :
  forall (l : list (ftype t * ftype t)) (fp : ftype t)
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

Lemma dotprod_rel_R_exists_fma {NAN : FPCore.Nans} {t : type} :
  forall (l : list (ftype t * ftype t)) (fp : ftype t)
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

Lemma sum_rel_R_abs_exists_fma {NAN : FPCore.Nans} {t : type} :
  forall (l : list (ftype t * ftype t)) (fp : ftype t)
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
induction l; intros; inversion Hrp; clear Hrp; subst.
compute; nra.
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
Context {NAN: FPCore.Nans} {t : type}.

Variables (v1 v2 : list (ftype t)).
Hypothesis (Hlen : size v1 = size v2).

Notation v1R := (map FT2R v1).

Lemma Req_eq: forall x y, Req_bool x y = eq_op x y.
Proof.
intros.
destruct (Req_bool_spec x y); symmetry; apply /eqP ; auto.
Qed.

Lemma dot_prod_rel_nnzR :
forall 
(fp : ftype t)
(Hfp : dot_prod_rel (zip v1 v2) fp)
(Hfin: Binary.is_finite fp = true),
nnzR v1R == 0%nat -> FT2R fp = 0.
Proof.
intros.
rewrite nnzR_lemma in H.
revert H Hfp Hlen Hfin. revert v2 fp.
induction v1; intros. destruct v2; try discriminate; inversion Hfp; auto.
inversion Hfp; subst. 
rewrite /pos_zero /Zconst  => //=.
destruct xy => //=.
simpl BPLUS in Hfin, Hfp.
destruct v2 as [  | v2a v2r]; [discriminate |].
inversion H0; clear H0; subst.
move :H => /= /andP [H H0].
move : (BPLUS_correct _ _ Hfin) => [[H2 H3] H4].
rewrite {}H4.
have Hs: FT2R s = 0 by (apply (IHl v2r) => //; auto).
rewrite Hs Rplus_0_r.
have Ha:  FT2R a = 0 by move: H => /eqP //.
rewrite (proj2 (BMULT_correct _ _ H2)).
rewrite Ha Rmult_0_l !Generic_fmt.round_0 //. 
Qed.

Lemma fma_dot_prod_rel_nnzR :
forall 
(fp : ftype t)
(Hfp : fma_dot_prod_rel (zip v1 v2) fp)
(Hfin: Binary.is_finite fp = true),
nnzR v1R == 0%nat -> FT2R fp = 0.
Proof.
intros.
rewrite nnzR_lemma in H.
move : v2 fp H Hfp Hlen Hfin.
clear Hlen.
induction v1; destruct v0; intros; inversion Hlen; clear Hlen.
inversion Hfp; auto.
inversion Hfp; clear Hfp; subst.
rewrite  /Zconst  => //=.
move :H => /= /andP [H8 H9].
move : (BFMA_correct _ _ _ Hfin) => /= [[H2 [H3 H6]] H7].
rewrite H7.
rewrite (IHl _ _ H9 H4); auto.
move :H8 => /eqP => H8.
rewrite -H8.
rewrite Rplus_0_r Rmult_0_l  !Generic_fmt.round_0 //.
Qed.

Lemma R_dot_prod_rel_nnzR :
forall 
(rp : R)
(Hrp  : R_dot_prod_rel (map FR2 (zip v1 v2)) rp),
nnzR v1R == 0%nat -> rp = 0.
Proof.
intros ? ? H.
rewrite nnzR_lemma in H.
revert v2 rp H Hrp  Hlen.
induction v1; intros.
destruct v2; try discriminate; auto.
inversion Hrp; auto.
destruct v2; try discriminate; auto.
inversion Hrp; subst.
unfold FR2, fst, snd.
move :H => /= /andP [H H0].
move :H => /eqP H.
simpl in Hlen.
rewrite -H Rmult_0_l.
rewrite  (IHl _ _ H0 H3). lra. lia.
Qed.

Lemma R_dot_prod_rel_nnzR_abs :
forall 
(rp_abs : R) 
(Hra : R_dot_prod_rel (map Rabsp (map FR2 (zip v1 v2))) rp_abs),
nnzR v1R == 0%nat -> rp_abs = 0.
Proof.
intros ? ? H.
rewrite nnzR_lemma in H.
revert H Hra  Hlen. revert v2 rp_abs .
induction v1; intros.
simpl in *. inversion Hra. auto.
destruct v2; try discriminate; auto.
destruct v2; try discriminate.
inversion Hra; subst.
unfold FR2, Rabsp, fst, snd.
move :H => /= /andP [H H0].
move :H => /eqP H.
simpl in Hlen.
rewrite -H Rabs_R0 Rmult_0_l (IHl _ _ H0 H3).
lra. lia.
Qed.


End NonZeroDP.