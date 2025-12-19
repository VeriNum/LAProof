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

(** Given a variable [i] of type [Z] or [nat], replace it everywhere with a variable [i] of type ['I_n],
    appropriately coerced. *)
Ltac ordify n i :=
  let Hi := fresh "H" i in
  let Hj := fresh "H" i in 
  let j := fresh "i" in
  match type of i with ?t => let t' := eval hnf in t in match t' with
    | Z => assert (Hi: Datatypes.is_true (ssrnat.leq (S (Z.to_nat i)) n)) by lia;
               set (j := @Ordinal n (Z.to_nat i) Hi);
               assert (Hj : i = Z.of_nat (nat_of_ord j)) by (simpl; lia)
    | nat =>  assert (Hi: Datatypes.is_true (ssrnat.leq (S i) n)) by lia;
                  set (j := @Ordinal n i Hi);
                  assert (Hj : i = nat_of_ord j) by (simpl; lia)
   end end;
   clearbody j; clear Hi;
   subst i;
   rename j into i.

Ltac case_splitP j :=
  tryif clearbody j then fail "case_splitP requires a variable, but got  a local definition" j
  else tryif is_var j then idtac else fail "case_splitP requires a variable, but got" j;
 match type of j with 'I_(addn ?a ?b) =>
  let i := fresh "j" in let H := fresh in 
  destruct (splitP j) as [i H | i H];
 [replace j with (@lshift a b i); [ | apply ord_inj; simpl; lia]
 |replace j with (@rshift a b i); [ | apply ord_inj; simpl; lia]];
 clear j H; rename i into j
 end.

(** Example of how to use case_splitP *)
Local Remark mul_mx_row' [R : pzSemiRingType] m n p1 p2 
    (A: 'M[R]_(m,n)) (Bl: 'M[R]_(n,p1)) (Br: 'M[R]_(n,p2)):
  A *m row_mx Bl Br = row_mx (A *m Bl) (A *m Br).
Proof.
apply /matrixP => i j.
case_splitP j.
rewrite row_mxEl !mxE . apply eq_bigr. move => k _;  rewrite row_mxEl//.
rewrite row_mxEr !mxE . apply eq_bigr. move => k _;  rewrite row_mxEr//.
Qed.

(** Example of how the mathcomp experts do this another way, from mathcomp.algebra.matrix  *)
Local Remark mul_mx_row'' [R : pzSemiRingType]  m n p1 p2 (A : 'M[R]_(m, n)) (Bl : 'M_(n, p1)) (Br : 'M_(n, p2)) :
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


Lemma size_seq_of_rV : forall {T} [n] x, size (@seq_of_rV T n x) = n.
Proof.
intros.
rewrite /seq_of_rV size_map size_ord_enum //.
Qed.

Lemma nth_seq_of_rV: forall {T}[n](d: T)(x: 'rV[T]_n) (i: 'I_n), nth d (seq_of_rV x) i = x ord0 i.
Proof.
intros.
pose proof (ltn_ord i).
rewrite /seq_of_rV (nth_map i d) ?nth_ord_enum' // size_ord_enum //.
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

Definition FMA_dotprod [n: nat] (x: 'rV[ftype t]_n) (y: 'cV[ftype t]_n) : ftype t :=
   fma_dotprod (seq_of_rV x) (seq_of_rV y^T).

Definition mulmx [m n p] (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,p)) :=
 \matrix_(i,k) dotprod (row i A) (col k B).

Definition FMA_mulmx [m n p] (A: 'M[ftype t]_(m,n)) (B: 'M[ftype t]_(n,p)) :=
 \matrix_(i,k) FMA_dotprod (row i A) (col k B).

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

Lemma FMA_mulmx_row:
 forall m n p1 p2 (A: 'M[ftype t]_(m,n)) (Bl: 'M_(n,p1)) (Br: 'M_(n,p2)),
  FMA_mulmx A (row_mx Bl Br) = row_mx (FMA_mulmx A Bl) (FMA_mulmx A Br).
Proof.
intros.
apply /matrixP => i j.
case_splitP j.
 rewrite row_mxEl !mxE -col_lsubmx row_mxKl //.
 rewrite row_mxEr !mxE -col_rsubmx row_mxKr //.
Qed.

Lemma mulmx_col:
 forall m1 m2 n p (Au: 'M[ftype t]_(m1,n)) (Ad: 'M[ftype t]_(m2,n))  (B: 'M_(n,p)),
  mulmx (col_mx Au Ad) B = col_mx (mulmx Au B) (mulmx Ad B).
Proof.
intros.
apply /matrixP => i j.
case_splitP i.
 rewrite col_mxEu !mxE -row_usubmx col_mxKu //.
 rewrite col_mxEd !mxE -row_dsubmx col_mxKd //.
Qed.

Lemma FMA_mulmx_col:
 forall m1 m2 n p (Au: 'M[ftype t]_(m1,n)) (Ad: 'M[ftype t]_(m2,n))  (B: 'M_(n,p)),
  FMA_mulmx (col_mx Au Ad) B = col_mx (FMA_mulmx Au B) (FMA_mulmx Ad B).
Proof.
intros.
apply /matrixP => i j.
case_splitP i.
 rewrite col_mxEu !mxE -row_usubmx col_mxKu //.
 rewrite col_mxEd !mxE -row_dsubmx col_mxKd //.
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

Lemma FMA_mulmx_fma_dotprod:
  forall [n] (A: 'M[ftype t]_(1,n)) (B: 'M[ftype t]_(n,1)),
 FMA_mulmx A B = const_mx (fma_dotprod (seq_of_rV A) (seq_of_rV (trmx B))).
Proof.
intros.
 unfold mulmx. apply /matrixP. move => i k. rewrite !mxE row_id col_id //.
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

Definition listlist_of_mx {T}  [m n: nat] (A: 'M[T]_(m,n)) : list (list T) :=
  map (fun  i: 'I_m => map (A i) (ord_enum n)) (ord_enum m).

Definition list_of_cV {T} [n: nat] (V: 'cV[T]_n) : list T :=
   map (fun i => V i ord0) (ord_enum n).

Definition mx_of_listlist {T} {d: T} (rows cols: nat) (mval: list (list T)) : 'M[T]_(rows,  cols) :=
 \matrix_(i,j) seq.nth (d: T) (seq.nth nil mval i) j.

Definition cV_of_list {T} {d: T} (n: nat) (vval: list T) : 'cV[T]_n :=
  \matrix_(i,j) seq.nth (d:T) vval i.

Definition matrix_cols_nat {T} (m: list (list T)) (cols: nat) := 
    Forall (fun r => size r = cols) m.

Lemma listlist_of_mx_of_listlist:
  forall {t} {d} rows cols (mval: list (list (ftype t))),
   rows = Datatypes.length mval ->
   matrix_cols_nat mval cols ->
   listlist_of_mx (@mx_of_listlist _ d rows cols mval) = mval.
Proof.
intros.
unfold listlist_of_mx, mx_of_listlist.
eapply (nth_ext _ _ nil nil).
rewrite length_map -H. apply size_ord_enum.
intros i Hi.
rewrite -!nth_List_nth.
rewrite length_map in Hi.
change @length with @size in Hi,H.
rewrite size_ord_enum in Hi.
rewrite (nth_ord_enum_lemma nil mval) -H.
f_equal.
f_equal.
apply FunctionalExtensionality.functional_extensionality; intro j.
rewrite map_comp /comp.
rewrite val_ord_enum.
rewrite map_nth_iota. 2: lia.
rewrite drop0.
replace (take rows mval) with mval.
2: rewrite H take_size //.
rewrite (nth_ord_enum_lemma d (nth nil mval j)).
replace (size _) with cols.
2:{ clear i Hi.
    red in H0. rewrite Forall_nth in H0. specialize (H0 j nil). rewrite nth_List_nth. symmetry; apply H0.
   change @length with @size; rewrite -H. pose proof (ltn_ord j). lia.
}
f_equal.
simpl.
clear i Hi.
rename j into i.
apply FunctionalExtensionality.functional_extensionality; intro j.
rewrite mxE /comp //.
Qed.

Lemma mx_of_listlist_of_mx:
  forall {T} {d:T} rows cols (A: 'M[T]_(rows,cols)),
   @mx_of_listlist _ d rows cols (listlist_of_mx  A) = A.
Proof.
intros.
apply matrixP => i j.
rewrite /mx_of_listlist mxE /listlist_of_mx.
rewrite (nth_map i).
2: rewrite size_ord_enum; apply ltn_ord.
rewrite (nth_map j).
2: rewrite size_ord_enum; apply ltn_ord.
rewrite !nth_ord_enum'.
auto.
Qed.

Lemma list_of_cV_of_list:
  forall {T} {d:T} n (vval: list T),
   size vval = n ->
   list_of_cV (@cV_of_list _ d n vval) = vval.
Proof.
intros.
unfold list_of_cV, cV_of_list.
apply (nth_ext _ _ d d).
rewrite length_map -H. apply size_ord_enum.
intros i Hi.
rewrite -!nth_List_nth.
rewrite length_map in Hi.
change @length with @size in Hi,H.
rewrite size_ord_enum in Hi.
rewrite (nth_ord_enum_lemma d vval) -H.
f_equal.
f_equal.
(* apply FunctionalExtensionality.functional_extensionality; intro j. *)
rewrite map_comp /comp.
rewrite val_ord_enum.
rewrite map_nth_iota. 2: lia.
rewrite drop0 take_size.
apply FunctionalExtensionality.functional_extensionality; intro j.
rewrite mxE //.
Qed.

Lemma cV_of_list_of_cV:
  forall {T} `{d:T} n (x: 'cV[T]_n),
  @cV_of_list _ d n (list_of_cV x) = x.
Proof.
intros.
apply matrixP => i j.
rewrite /mx_of_listlist mxE /listlist_of_mx.
rewrite (nth_map i).
2: rewrite size_ord_enum; apply ltn_ord.
rewrite !ord1.
f_equal.
apply nth_ord_enum'.
Qed.

Lemma matrix_rows_listlist_of_mx: forall {T} [rows cols] (A: 'M[T]_(rows,cols)),
   size (listlist_of_mx A) = rows.
Proof.
intros.
unfold listlist_of_mx. rewrite size_map. apply size_ord_enum.
Qed.

Lemma matrix_cols_listlist_of_mx: forall {T} [rows cols] (A: 'M[T]_(rows,cols)),
  matrix_cols_nat (listlist_of_mx A) cols.
Proof.
intros.
unfold matrix_cols_nat, listlist_of_mx.
apply Forall_map, Forall_forall.
intros; simpl.
rewrite size_map. apply mv_mathcomp.size_ord_enum.
Qed.

Lemma size_list_of_cV: forall {T} [n] (vval: 'cV[T]_n),
  size (list_of_cV vval) = n.
Proof.
intros.
rewrite /list_of_cV size_map size_ord_enum //.
Qed.


Lemma nth_list_of_cV: 
  forall {T} {d:T} [n] (vval: 'cV[T]_n) (i: 'I_n), 
   nth d (list_of_cV vval) (nat_of_ord i) = vval i ord0.
Proof.
intros.
rewrite /list_of_cV (nth_map i) ?nth_ord_enum' // size_ord_enum.
apply ltn_ord.
Qed.

Definition list_dotprod {NAN: FPCore.Nans} {t: type} (v1 v2: list (ftype t)) : ftype t :=
  foldl (fun s x12 => BFMA (fst x12) (snd x12) s) (Zconst t 0) (zip v1 v2) .

Definition matrix_vector_mult {NAN: FPCore.Nans}{t: type} (m: list (list (ftype t))) (v: list (ftype t)) : list (ftype t) :=
      map (fun row => list_dotprod row v) m.

Lemma list_of_cV_col_mx: forall {T} n1 n2 (x: 'cV[T]_n1) (y: 'cV[T]_n2),
  list_of_cV (col_mx x y) = list_of_cV x ++ list_of_cV y.
Proof.
intros.
assert (n1 = O \/ 0< n1)%N by lia.
destruct H.
subst.
- rewrite /list_of_cV /col_mx. simpl.
  apply eq_in_map.
 red; simpl; intros.
 clear H.
 rewrite mxE. 
 change n2 with (addn O n2) in x0.
 case_splitP x0. destruct x0; lia.
 f_equal.
 apply ord_inj. simpl. reflexivity.
-
 assert (d: T). destruct n1; try lia; apply (x ord0 ord0).
 rewrite /list_of_cV /col_mx.
 apply eq_from_nth with d.
 rewrite size_cat !size_map !size_ord_enum //.
 intros i.
 rewrite size_map !size_ord_enum => Hi.
 rewrite nth_cat.
 rewrite size_map size_ord_enum.
 rewrite (nth_map (Ordinal Hi)) ?size_ord_enum // mxE.
 assert (nth (Ordinal Hi) (ord_enum (n1+n2)) i = Ordinal Hi).
 change i with (nat_of_ord (Ordinal Hi)).
 rewrite nth_ord_enum' //.
 rewrite H0.
 destruct (i<n1)%N eqn:?H.
+
unfold split. simpl. destruct (ltnP i n1); try lia.
rewrite (nth_map (Ordinal i0)).
2: rewrite size_ord_enum //.
change i with (nat_of_ord (Ordinal i0)).
rewrite nth_ord_enum' //.
+
unfold split. simpl. destruct (ltnP i n1); try lia.
assert (is_true (i-n1 < n2)%N) by lia.
rewrite (nth_map (Ordinal H2)).
2: rewrite size_ord_enum //.
change (i-n1)%nat with (nat_of_ord (Ordinal H2)).
rewrite nth_ord_enum' //.
f_equal.
apply ord_inj. simpl. auto.
Qed.

Lemma map_const_len: 
  forall {A B} (c: B) (al: list A), map (fun _ => c) al = repeat c (length al).
Proof.
induction al; simpl; intros; f_equal; auto.
Qed.

Lemma listlist_of_mx_col_mx: forall {T} n1 n2 m (A: 'M[T]_(n1,m)) (B: 'M[T]_(n2,m)),
  listlist_of_mx (col_mx A B) = listlist_of_mx A ++ listlist_of_mx B.
intros.
assert (m = 0 \/ 0 < m)%N by lia. destruct H as [Hm | Hm]. {
 subst m. rewrite /listlist_of_mx. change (ord_enum 0) with (@nil 'I_0). simpl.
 rewrite !map_const_len.
 change @length with @size. rewrite !size_ord_enum.
 rewrite repeat_app //.
}
assert (n1 = O \/ 0< n1)%N by lia.
destruct H as [Hn1 | Hn1].
subst.
- rewrite /list_of_cV /col_mx. simpl.
  apply eq_in_map; intros i _.
 apply eq_in_map; intros j _.
 rewrite mxE. 
 change n2 with (addn O n2) in i.
 simpl in *.
 case_splitP i. destruct i; lia.
 f_equal.
 apply ord_inj. simpl. reflexivity.
-
 assert (d: T). destruct n1,m; try lia; apply (A ord0 ord0).
 rewrite /list_of_cV /col_mx.
 apply eq_from_nth with nil.
 rewrite size_cat !size_map !size_ord_enum //.
 intros i.
 rewrite size_map !size_ord_enum => Hi.
 rewrite nth_cat.
 rewrite size_map size_ord_enum.
 rewrite (nth_map (Ordinal Hi)) ?size_ord_enum //.
 apply eq_from_nth with d. {
   rewrite size_map size_ord_enum.
  destruct (leq (S i) n1) eqn:?H.
  assert (HA := matrix_cols_listlist_of_mx A).
  red in HA. rewrite Forall_nth in HA. specialize (HA i nil).
  change @length with @size in HA.
 rewrite matrix_rows_listlist_of_mx in HA.
  specialize (HA ltac:(lia)).
  rewrite -nth_List_nth in HA. auto.
  assert (HB := matrix_cols_listlist_of_mx B).
  red in HB. rewrite Forall_nth in HB. specialize (HB (i-n1)%nat nil).
  change @length with @size in HB.
 rewrite matrix_rows_listlist_of_mx in HB.
  specialize (HB ltac:(lia)).
  rewrite -nth_List_nth in HB. auto.
 }
 rewrite size_map size_ord_enum => j Hj.
 rewrite (nth_map (Ordinal Hj)).
 2: rewrite size_ord_enum //.
 change j with (nat_of_ord (Ordinal Hj)).
 rewrite nth_ord_enum'.
 assert (nth (Ordinal Hi) (ord_enum (n1+n2)) i = Ordinal Hi).
 change i with (nat_of_ord (Ordinal Hi)).
 rewrite nth_ord_enum' //.
 rewrite H.
 rewrite mxE.
 destruct (i<n1)%N eqn:?H.
+
unfold split. simpl. destruct (ltnP i n1); try lia.
rewrite (nth_map (Ordinal i0)).
2: rewrite size_ord_enum //.
change i with (nat_of_ord (Ordinal i0)).
rewrite nth_ord_enum' //.
rewrite (nth_map (Ordinal Hj)).
2: rewrite size_ord_enum //.
change j with (nat_of_ord (Ordinal Hj)).
rewrite nth_ord_enum' //.
+
unfold split. simpl. destruct (ltnP i n1); try lia.
assert (is_true (i-n1 < n2)%N) by lia.
rewrite (nth_map (Ordinal H1)).
2: rewrite size_ord_enum //.
change (i-n1)%nat with (nat_of_ord (Ordinal H1)).
rewrite nth_ord_enum' //.
rewrite (nth_map (Ordinal Hj)).
2: rewrite size_ord_enum //.
f_equal.
apply ord_inj. simpl. auto.
change j with (nat_of_ord (Ordinal Hj)).
rewrite nth_ord_enum' //.
Qed.

Lemma listlist_of_mx_inj: forall {T} [m n] (A B: 'M[T]_(m,n)),
  listlist_of_mx A = listlist_of_mx B -> A=B.
Proof.
intros.
apply matrixP. intros i j.
assert (m=O \/ n = O \/ 0<m /\ 0<n)%N by lia.
destruct H0; [ | destruct H0].
subst. destruct i. lia.
subst; destruct j; lia.
assert (d: T) by (destruct m; destruct n; try lia; apply (A ord0 ord0)).
assert (nth d (nth nil (listlist_of_mx A) i) j = 
             nth d (nth nil (listlist_of_mx B) i) j).
  rewrite H; auto.
clear - H1.
rewrite /listlist_of_mx in H1.
pose proof (ltn_ord i).
pose proof (ltn_ord j).
rewrite !(nth_map i) in H1. 2,3: rewrite size_ord_enum; auto.
rewrite !(nth_map j) in H1. 2,3: rewrite size_ord_enum; auto.
rewrite !nth_ord_enum' in H1.
auto.
Qed.

Lemma Fmulmx_matrix_vector_mult:
 forall {NAN: FPCore.Nans}{t} rows cols (mval: list (list (ftype t))) (vval: list (ftype t)),
   rows = size mval ->
   cols = size vval ->
   matrix_cols_nat mval cols ->
   matrix_vector_mult mval vval = list_of_cV (F.FMA_mulmx (@mx_of_listlist _ (Zconst t 0) rows cols mval) 
                                                                                        (@cV_of_list _ (Zconst t 0) cols vval)).
Proof.
intros.
subst rows.
destruct (size vval) eqn:Hcols.
-
destruct cols; try discriminate.
destruct vval; try discriminate.
clear H0 Hcols.
assert (mval = List.repeat nil (size mval)).
induction H1; auto. simpl. f_equal; auto. destruct x; auto; discriminate.
rewrite H.
set n := size mval.
clearbody n. clear mval H H1.
change @size with @length. rewrite repeat_length.
induction n. reflexivity.
simpl.
rewrite {}IHn.
replace (mx_of_listlist (S n) 0 (cons nil (repeat nil n))) with
     (col_mx (@mx_of_listlist _ (Zconst t 0) 1 0 nil) (@mx_of_listlist _ (Zconst t 0) n 0 (repeat nil n))).
2: apply /matrixP => i j; destruct j; lia.
change (S n) with (addn 1 n).
rewrite F.FMA_mulmx_col.
set (u := F.FMA_mulmx _ _).
clearbody u.
rewrite /list_dotprod /=.
rewrite list_of_cV_col_mx.
rewrite {2}/list_of_cV.
set one := ord_enum 1. compute in one. destruct idP; try lia. subst one.
simpl.
f_equal.
rewrite /F.mulmx /mx_of_listlist /cV_of_list mxE //.
-
assert (0 < cols)%N by lia. rewrite -H0 in Hcols. clear n H0.
induction H1; [reflexivity | ].
simpl.
replace (mx_of_listlist (S (size l)) cols (cons x l))
  with (col_mx (@mx_of_listlist _ (Zconst t 0) 1 cols (cons x nil)) (@mx_of_listlist _ (Zconst t 0) (size l) cols l)).
+
change (S ?A) with (addn 1 A).
rewrite F.FMA_mulmx_col.
rewrite list_of_cV_col_mx.
replace (list_of_cV _) with [:: list_dotprod x vval].
simpl. f_equal.
apply IHForall.
rewrite /list_of_cV.
set one := ord_enum 1. compute in one. destruct idP; try lia. subst one.
simpl. f_equal.
rewrite mxE /F.FMA_mulmx /F.FMA_dotprod /fma_dotprod /list_dotprod.
f_equal. f_equal.
*  apply (@eq_from_nth _ pos_zero).
rewrite size_seq_of_rV //.
move => j Hj. rewrite H0 in Hj. ordify cols j.
rewrite nth_seq_of_rV !mxE //.
*  apply (@eq_from_nth _ pos_zero).
rewrite size_seq_of_rV //.
move => j Hj. rewrite Hcols in Hj. ordify cols j.
rewrite nth_seq_of_rV !mxE //.
+
change (S (size l)) with (addn 1 (size l)).
apply listlist_of_mx_inj.
rewrite listlist_of_mx_of_listlist.
2: simpl; change @length with @size; lia.
2: constructor; auto.
rewrite listlist_of_mx_col_mx.
rewrite !listlist_of_mx_of_listlist; auto.
constructor; auto.
Qed.


