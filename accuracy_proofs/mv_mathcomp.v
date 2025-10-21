(* This file contains theorems connecting MathComp operations on 
  matrices and vectors to operations on lists. *)


From LAProof.accuracy_proofs Require Import preamble common 
    dotprod_model sum_model dot_acc float_acc_lems.

From mathcomp.algebra_tactics Require Import ring.

Open Scope ring_scope.
Open Scope order_scope.

Definition sum_abs {m n} (A: 'M[R]_(m,n)) i : R:= \sum_j (Rabs (A i j)).
Definition normv   {m} (v: 'cV[R]_m)  : R:= \big[maxr/0]_(i < m) Rabs (v i 0%Ri).
Definition normM   {m n} (A: 'M[R]_(m,n))   : R:= \big[maxr/0]_i (sum_abs A i).
Definition seq_of_rV {T}[n] (x: 'rV[T]_n) := map (x ord0) (ord_enum n).

Ltac case_splitP j :=
  first [is_var j | fail 1 "case_splitP requires a variable, but got" j];
 match type of j with 'I_(addn ?a ?b) =>
  let i := fresh "j" in let H := fresh in 
  destruct (splitP j) as [i H | i H];
 [replace j with (@lshift a b i); [ | apply ord_inj; simpl; lia]
 |replace j with (@rshift a b i); [ | apply ord_inj; simpl; lia]];
 clear j H; rename i into j
 end.

(** Example of how to use case_splitP *)
Local Remark mul_mx_row' [R : GRing.SemiRing.type] m n p1 p2 
    (A: 'M[R]_(m,n)) (Bl: 'M[R]_(n,p1)) (Br: 'M[R]_(n,p2)):
  A *m row_mx Bl Br = row_mx (A *m Bl) (A *m Br).
Proof.
apply /matrixP => i j.
case_splitP j.
rewrite row_mxEl !mxE . apply eq_bigr. move => k _;  rewrite row_mxEl//.
rewrite row_mxEr !mxE . apply eq_bigr. move => k _;  rewrite row_mxEr//.
Qed.

(** Example of how the mathcomp experts do this another way, from mathcomp.algebra.matrix  *)
Local Remark mul_mx_row'' [R : GRing.SemiRing.type]  m n p1 p2 (A : 'M[R]_(m, n)) (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)) :
  A *m row_mx Bl Br = row_mx (A *m Bl) (A *m Br).
Proof.
apply/matrixP=> i k; rewrite !mxE.
by case defk: (split k) => /[!mxE]; under eq_bigr do rewrite mxE defk.
Qed.

Lemma nth_List_nth: forall {A: Type} (d: A) (l: seq.seq A) (n: nat),
  seq.nth d l n = List.nth n l d.
Proof.
  move => A d l. elim : l => [//= n | //= h t IH n].
  - by case : n.
  - case: n. by []. move => n. by rewrite /= IH.
Qed.

Lemma pred_lt: forall [n: nat], (0 < n -> n.-1 < n)%nat.
Proof.
  move => n Hn. by rewrite ltn_predL.
Qed.

Definition pred_ord [n: nat] (Hn: (0 < n)%nat) : 'I_n := Ordinal (pred_lt Hn).

Lemma ordinal_enum_size: forall n: nat,
  size (Finite.enum (ordinal n)) = n.
Proof.
  move => n. have: size ([seq val i | i <- enum 'I_n]) = n. rewrite val_enum_ord. by apply: size_iota.
  rewrite size_map. unfold enum. rewrite size_map //.
Qed.

Lemma size_ord_enum: forall n, size (ord_enum n) = n.
Proof.
  move => n. 
  have : size (ord_enum n) = size ([seq val i | i <- ord_enum n]) by rewrite size_map.
  by rewrite val_ord_enum size_iota.
Qed.

Lemma nth_index_enum: forall {n: nat} (x: 'I_n) y,
  seq.nth y (index_enum (ordinal n)) x = x.
Proof.
  move => n x y.
 have nth_ord := (@nth_ord_enum n y x). unfold enum in nth_ord. move: nth_ord.
  rewrite (@nth_map _ y) //. by rewrite ordinal_enum_size.
Qed. 

Lemma nth_ord_enum': forall n (i: 'I_n) x, seq.nth x (ord_enum n) i = i.
Proof.
  move => n i x. have Hv := val_ord_enum n.  have Hmap :=  @nth_map 'I_n x nat x val i (ord_enum n).
  move : Hmap. rewrite Hv size_ord_enum nth_iota =>[//=|//]. rewrite add0n. move => H.
  (*some annoying stuff about equality of ordinals vs nats*)
  have : nat_of_ord ( seq.nth x (ord_enum n) i) == nat_of_ord i.
 rewrite {2}H. by []. by [].
  move => Hnatord. have : seq.nth x (ord_enum n) i == i by []. 
  by move => /eqP Heq.
Qed.


Lemma index_ord_enum: forall (n: nat), (index_enum (ordinal n)) = ord_enum n.
Proof.
  move => n. have: (0 <= n)%nat by []. rewrite leq_eqVlt => /orP[/eqP Hn0 | Hnpos].
  - subst. rewrite /ord_enum /= /index_enum /=. apply size0nil. apply ordinal_enum_size.
  - apply (eq_from_nth (x0:=pred_ord Hnpos)).
    + rewrite ordinal_enum_size size_ord_enum //.
    + move => i. rewrite ordinal_enum_size => Hi.
      have->: i = nat_of_ord (Ordinal Hi) by [].
     rewrite nth_index_enum nth_ord_enum' //.
Qed.

(* generally useful lemmmas for max operator *)
Lemma maxrC : @commutative R R maxr. 
  Proof. rewrite /commutative => x y.
  rewrite -!RmaxE. apply Rmax_comm. Qed.

Lemma maxrA : @associative R  maxr. 
  Proof. rewrite /associative => x y z.
  rewrite -!RmaxE. apply Rmax_assoc. Qed. 

Lemma big_mul {n:nat} (F : ordinal n -> R) op a:
(forall i b, op (F i) b * a = op (F i * a) (b * a)) -> 
R0 <= a -> \big[op/0]_(i0 < n) (F i0) * a = \big[op/0]_(i0 < n) (F i0 * a).
Proof. 
destruct n.
-
intros.
 rewrite (unlock (bigop_unlock)).
 unfold reducebig, comp, applybig. simpl. rewrite index_ord_enum. simpl.
 apply Rmult_0_l. 
-
revert F a. elim: n => /= // [F a Hc Ha| n0 IH F a Hc Ha].
rewrite !big_ord_recl !big_ord0/= //.
rewrite (Hc ord0 0)  mul0r //.
rewrite big_ord_recl => /= //. 
etransitivity.
2 : rewrite big_ord_recl => /= //.
rewrite Hc.
rewrite IH => //.
Qed.

Lemma big_max_mul {n:nat} (F : ordinal n -> R) a:
R0 <= a -> \big[maxr/0]_(i0 < n) (F i0) * a = \big[maxr/0]_(i0 < n) (F i0 * a).
Proof. 
move => Ha.
apply big_mul => //.
move => i  b.
change (maxr (F i) b * a = maxr (F i * a) (b * a))%Ri.
rewrite maxr_pMl //.
Qed.

(* Lemmas about norm defs *)


Lemma normv_pos {m} (v: 'cV[R]_m) : R0 <= normv v.
Proof.
rewrite /normr/normv. 
elim/big_ind: _ => //[x y Hx Hy| i _].
rewrite  -RmaxE. eapply le_trans; [apply Hy|].
apply /RleP; apply Rmax_r.
apply /RleP; apply Rabs_pos.
Qed.

Lemma normM_pos [m n] (A: 'M[R]_(m,n)) : R0 <= normM A.
Proof.
rewrite /normr/normM . 
elim/big_ind: _ => //[x y Hx Hy| i _].
rewrite  -RmaxE/Rmax. destruct Rle_dec => //.
rewrite /sum_abs. 
elim/big_ind: _ => //[x y Hx Hy| j _].
apply addr_ge0 => //.
apply /RleP; apply Rabs_pos.
Qed.

Lemma Rabs_sum (n:nat) : forall (F : ordinal n -> R),
Rabs (\sum_j F j) <= \sum_j Rabs (F j).
Proof.
destruct n.
- intros. 
 rewrite (unlock (bigop_unlock)).
 unfold reducebig, comp, applybig. simpl.
 rewrite index_ord_enum. simpl.  rewrite Rabs_R0. apply /RleP. reflexivity.
-
elim : n => [F | n IH F]. 
rewrite !big_ord_recr!big_ord0/=. 
  eapply le_trans ; [apply Rleb_norm_add| rewrite Rabs_R0; apply lerD => /= //].
eapply le_trans.
1, 2: rewrite big_ord_recr /=. apply Rleb_norm_add.
apply lerD => /= //.
Qed.


Lemma subMultNorm m n (A: 'M[R]_(m,n))  (u : 'cV_n) : 
  normv ( A *m u ) <= normM A * normv u.
Proof.
destruct m.
-
rewrite /normr /normM /normv.
 rewrite (unlock (bigop_unlock)).
 unfold reducebig, comp, applybig. simpl.
 rewrite index_ord_enum. simpl.
 set xx := foldr _ _ _. clearbody xx.
 apply /RleP. change (0 <= 0*xx)%Re. rewrite Rmult_0_l. reflexivity.
-
remember (normv u) as umax.
rewrite /normr /normM /normv /sum_abs /=  big_max_mul.
apply: le_bigmax2 => i0 _.
rewrite mxE => /=.
eapply le_trans.
apply Rabs_sum .
elim/big_rec2: _ =>  // [ |i1 y1 y2 _ Hy].
apply mulr_ge0 => //. 
rewrite Hequmax; apply normv_pos.
rewrite mulrDl.
apply lerD => //.
rewrite Rabs_mult.
apply ler_pM => //.
1,2: apply /RleP; apply Rabs_pos.
rewrite Hequmax/normv.
by apply /le_bigmax.
rewrite Hequmax.
 apply normv_pos.
Qed.

Lemma normv_triang m  (u v: 'cV_m) : 
  normv ( u + v ) <= normv u + normv v.
Proof.
rewrite {1}/normv.
apply: bigmax_le => [ | i _]. 
apply addr_ge0; apply normv_pos.
rewrite mxE => /=.
eapply le_trans.
apply Rleb_norm_add. apply lerD;
apply: le_bigmax => [ | i _]. 
Qed.


Local Definition crazy (T: Type): 'I_0 -> T.
intro. destruct X. lia.
Defined.

Lemma exists_mx: forall {T} [m n] (F: 'I_m -> 'I_n -> T -> Prop),
  (forall i j, exists x, F i j x) -> 
  exists A: 'M[T]_(m,n), forall i j, F i j (A i j).
Proof.
intros.
induction m.
-
exists (\matrix_(i,j) crazy T i). intros. destruct i. lia.
-
change (m.+1) with (1+m)%nat.
destruct (IHm (fun i j => F (rshift 1 i) j)).
intros. apply H.
assert (exists A1: 'M[T]_(1,n), forall j, F ord0 j (A1 ord0 j)). {
  clear IHm x H0.
  induction n. exists (\matrix_(i,j) crazy T j). intros. destruct j; lia.
  destruct (IHn (fun i j => F i (rshift 1 j))). intros. apply H. 
  destruct (H ord0 ord0).
  exists (row_mx (@const_mx _ 1 1 x0) x). 
  intros.
 change (n.+1) with (1 + n)%nat in j |-*.
 destruct (splitP j).
 replace j with (@lshift 1 n j0).
   2: apply ord_inj; simpl; auto.
 rewrite row_mxEl. rewrite mxE. 
 replace (lshift n j0) with (@ord0 n); auto.
 rewrite ord1; apply ord_inj; simpl; auto.
 replace j with (@rshift 1 n k). 
  2: apply ord_inj; simpl; lia.
 rewrite row_mxEr.
 apply H0.
}
destruct H1 as [A1 ?].
change (m.+1) with (1 + m)%nat.
exists (col_mx A1 x).
intros.
destruct (splitP i) as [i0|i0].
+
replace i with (@lshift 1 m i0).
 2: apply ord_inj; simpl; auto.
rewrite col_mxEu.
replace (lshift m i0) with (@ord0 m).
2: rewrite ord1; apply ord_inj; simpl; auto.
rewrite ord1.
apply H1.
+
replace i with (@rshift 1 m i0).
2: apply ord_inj; simpl; auto.
rewrite col_mxEd.
apply H0.
Qed.

Lemma rev_ord_enum: forall n, rev (ord_enum n) = map (@rev_ord n) (ord_enum n).
Proof.
intros.
assert (map (@nat_of_ord n) (rev (ord_enum n)) = map (@nat_of_ord n) (map (@rev_ord n) (ord_enum n))).
2:{
set a := rev (ord_enum n) in H|-*; clearbody a.
set b := map (@rev_ord _) _ in H|-*; clearbody b.
revert b H; induction a; destruct b; intros; try discriminate; simpl; auto.
inversion H; clear H; subst.
f_equal; auto.
apply ord_inj; auto.
}
rewrite -map_comp map_rev val_ord_enum.
transitivity (map (fun y => subn n (S y)) (map (@nat_of_ord n) (ord_enum n))).
2: rewrite -map_comp /comp //.
unfold ord_enum.
rewrite pmap_filter.
2: intro; simpl; unfold insub; destruct idP; simpl in *; auto.
transitivity (map (fun y => subn n (S y)) (iota 0 n)).
2:{
set u := O.
 f_equal. symmetry. apply /all_filterP.
replace (fun x: nat => isSome (insub x)) with (fun x => x<n+u)%N.
2:{ subst u; apply FunctionalExtensionality.functional_extensionality; intro x.
 rewrite addn0.
   unfold insub. destruct idP; auto.
}
clearbody u.
revert u; induction n; simpl; intros; auto.
apply /andP; split. lia. specialize (IHn (S u)).
replace (fun x : nat => leq (S x) (addn (S n) u)) with (fun x : nat => leq (S x) (addn n (S u))); auto.
apply FunctionalExtensionality.functional_extensionality; intro x; lia.
}
apply nth_ext with (d:=O) (d':=O); change @length with @size.
rewrite size_rev size_map //.
intros.
rewrite size_rev size_iota in H.
rewrite -!nth_List_nth.
rewrite nth_rev.
2: rewrite size_iota; lia.
rewrite size_iota.
rewrite nth_iota.
2: lia.
rewrite (nth_map O).
2: rewrite size_iota; lia.
rewrite nth_iota; try lia.
Qed.

Lemma nth_ord_enum_lemma:
 forall [T] (d: T) (u: seq T),
   u = map (nth d u \o @nat_of_ord (size u)) (ord_enum (size u)).
Proof.
intros.
rewrite map_comp val_ord_enum map_nth_iota0 // take_size //.
Qed.

Lemma sumR_sum: forall (x: seq R), sumR x = \sum_(i in 'I_(size x)) nth R0 x (nat_of_ord i).
Proof.
intros.
rewrite /sumR  (unlock bigop_unlock)
 /reducebig /comp /applybig /= index_ord_enum.
 rewrite {1}(nth_ord_enum_lemma R0 x).
 rewrite foldr_map //.
Qed.


Module F.  (* Floating-point math-comp matrix and vector operations *)

Section WithNAN. 
Context {NAN: FPCore.Nans} {t : type}.

Definition sum  [n: nat] (x: 'I_n -> ftype t) : ftype t :=
    \big[BPLUS / neg_zero]_i x (rev_ord i).

Definition dotprod [n: nat] (x: 'rV[ftype t]_n) (y: 'cV[ftype t]_n) : ftype t :=
   \big[BPLUS / pos_zero]_i (BMULT (x ord0 (rev_ord i)) (y (rev_ord i) ord0)).

Definition mulmx [m n p] (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,p)) :=
 \matrix_(i,k) dotprod (row i A) (col k B).

Definition scalemx [m n] (a: ftype t) (M: 'M[ftype t]_(m,n)) :=
  map_mx (BMULT a) M.

Definition addmx [m n] (A B: 'M[ftype t]_(m,n)) : 'M[ftype t]_(m,n) :=
  \matrix_(i,j) BPLUS (A i j) (B i j).

Lemma mulmx_row:
 forall m n p1 p2 (A: 'M[ftype t]_(m,n)) (Bl: 'M_(n,p1)) (Br: 'M_(n,p2)),
  mulmx A (row_mx Bl Br) = row_mx (mulmx A Bl) (mulmx A Br).
Proof.
intros.
apply /matrixP => i j.
case_splitP j.
 rewrite row_mxEl !mxE -col_lsubmx row_mxKl //.
 rewrite row_mxEr !mxE -col_rsubmx row_mxKr //.
Qed.

Lemma sum_sumF: forall [n] (x: 'I_n -> ftype t), sum x = sumF (map x (ord_enum n)).
Proof.
 intros.
 rewrite /sum /sumF (unlock bigop_unlock) /reducebig /comp /applybig
 -(revK (map x _)) foldl_rev -map_rev rev_ord_enum -map_comp foldr_map index_ord_enum //.
Qed.

Lemma dotprod_dotprodF:
  forall [n] (x: 'rV[ftype t]_n) (y: 'cV[ftype t]_n),
  dotprod x y = dotprodF (seq_of_rV x) (seq_of_rV (trmx y)).
Proof.
intros.
 rewrite /dotprod /seq_of_rV /dotprodF /dotprod_model.dotprod !ord1.
 rewrite (unlock bigop_unlock).
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
 apply FunctionalExtensionality.functional_extensionality; intro z.
 rewrite !mxE. reflexivity.
Qed.

Lemma mulmx_dotprodF:
  forall [n] (A: 'M[ftype t]_(1,n)) (B: 'M[ftype t]_(n,1)),
 mulmx A B = const_mx (dotprodF (seq_of_rV A) (seq_of_rV (trmx B))).
Proof.
intros.
 unfold mulmx. apply /matrixP. move => i k. rewrite !mxE row_id col_id.
 apply dotprod_dotprodF.
Qed.

Definition finitemx [m n] (A: 'M[ftype t]_(m,n)) : Prop := 
   (forall i j, Binary.is_finite (A i j)).

Lemma finitemx_addmx_e: forall [m n] (A B: 'M[ftype t]_(m,n)),
  finitemx (addmx A B) -> finitemx A /\ finitemx B.
Proof.
rewrite /addmx /finitemx => m n A B Hfin.
split =>  i j; specialize (Hfin i j); rewrite mxE in Hfin; apply BPLUS_finite_e in Hfin; apply Hfin.
Qed.

Lemma finitemx_scalemx_e: forall [m n] (c: ftype t) (A: 'M[ftype t]_(m,n)),
  finitemx (scalemx c A) -> finitemx A.
Proof.
rewrite /scalemx /finitemx => m n c A Hfin i j.
specialize (Hfin i j). rewrite mxE in Hfin. apply BMULT_finite_e in Hfin; apply Hfin.
Qed.

End WithNAN.

End F.

