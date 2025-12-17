(** * LAProof.accuracy_proofs.solve_model: models of Cholesky decomposition and triangular solve *)

From LAProof.accuracy_proofs Require Import preamble common float_acc_lems.
Require Import vcfloat.FPStdLib.
Require Import vcfloat.FPStdCompCert.
From LAProof Require Import accuracy_proofs.mv_mathcomp.


(** * MathComp matrices over a nonring *)

(** Most MathComp matrix operations, such as matrix multiplication, are parameterized
  over a Ring or Field structure.  When you do the dot-products in a matrix multiply, it
  doesn't matter what order you add up the element products, because addition in a Ring
  is associative-commutative.  But our functional models of matrix algorithms are in floating point,
  which is not a Ring or Field because (for example) addition is not associative.

  MathComp handles this by having some matrix operations (such as transpose [tr_mx]
  and the very definition of a  [@matrix _ _ _] (notated as ['M[_]_(_,_)]) be parameterized
  only over a [Type] when they don't need a Ring structure; it is only the operators whose
  natural mathematics need additional properties, that require a Ring or Field.

  That means we can use natural MathComp operations such as blocking and transpose
  on floating-point matrices ['M[ftype t]_(m,n)] but we cannot use MathComp's matrix multiply
   [mulmx].   Instead, if we multiply floating-point matrices, we must define it ourselves in
  a way that specifies exactly what order of operations is done, or (if a relation instead of a
  function) what order(s) are permitted.

  The definition [update_mx] is an example of an operation that naturally does not require
  a Ring structure.  The definition [subtract_loop], below, is an example of the other kind; 
  we can't use MathComp's dot-product to define it, so we write a definition that explicitly
  specifies the order of additions. 
 *)

Definition update_mx {T} [m n] (M: 'M[T]_(m,n)) (i: 'I_m) (j: 'I_n) (x: T) : 'M[T]_(m,n) :=
    \matrix_(i',j') if  andb (Nat.eq_dec i' i) (Nat.eq_dec j' j) then x else M i' j'.

(** * Functional model of Cholesky decomposition (jik algorithm) *)
(** The next three definitions, up to [cholesky_jik_spec], are adapted from
  similar definitions in coq-libvalidsdp by P. Roux et al. *)


Section WithNaN.

Context {NAN: FPCore.Nans} {t : type}.

Definition subtract_loop {t} (c: ftype t) (l: seq (ftype t * ftype t)) :=
  foldl BMINUS c (map (uncurry BMULT) l).

Definition subtract_loop_jik {t}  [n] (c: ftype t) (R: 'M[ftype t]_n) (i j k: 'I_n) : ftype t :=
   subtract_loop c (map (fun k' => (R k' i, R k' j)) (take k (ord_enum n))).

Definition cholesky_jik_ij {t} [n: nat] (A R: 'M[ftype t]_n) (i j: 'I_n) : Prop :=
     (forall Hij: (i<j)%N, R i j = BDIV (subtract_loop_jik (A i j) R i j i) (R i i))  
   /\ (forall Hij: i=j, R i j = BSQRT (subtract_loop_jik (A i j) R i j i)).

Definition cholesky_jik_spec {t} [n: nat] (A R: 'M[ftype t]_n) : Prop :=
  forall i j, cholesky_jik_ij A R i j.

(** When we have run the "Cholesky jik algorithm" only up to iteration (i,j),
   the matrix is only initialized above row i, and in row i up to column j, so we
  need this subrelation in our loop invariant. *)
Definition cholesky_jik_upto {t} [n] (imax: 'I_n) (jmax : 'I_n.+1) (A R : 'M[ftype t]_n) : Prop :=
  forall (i j: 'I_n),
      ((j<jmax)%N -> cholesky_jik_ij A R i j)
   /\ (nat_of_ord j = nat_of_ord jmax -> (i<imax)%N -> cholesky_jik_ij A R i j)
   /\ ((j>jmax)%N -> R i j = A i j)
   /\ (nat_of_ord j= nat_of_ord jmax -> (i>=imax)%N -> R i j = A i j).

Definition cholesky_success {t} [n: nat] (A R: 'M[ftype t]_n) : Prop :=
   cholesky_jik_spec A R /\
   forall i, Binary.is_finite_strict _ _ (R i i).


(* Test a Cholesky result for pos-def (1), pos-semidef (0), error(-1) *)
Definition Zcholesky_return {t} (x: ftype t) : Z :=
 match x with 
 | Binary.B754_zero _ _ _ => 0%Z
 | Binary.B754_finite _ _ _ _ _ _ => 1%Z
 | _ => -1%Z
 end.

Definition BFREXP [t] (x: ftype t): (ftype t * Z) :=
  Binary.Bfrexp (fprec t) (femax t) (fprec_gt_0 t) x.

Definition cholesky_return {t} [n] (R: 'M[ftype t]_n) : ftype t :=
     foldl (fun (x: ftype t) (i: 'I_n) => BMULT x (fst (BFREXP (R i i)))) (Zconst t 1) (ord_enum n).

(** Functional models of forward substitution and back substitution *)

Definition forward_subst_step {t: type} [n: nat] 
         (L: 'M[ftype t]_n) (x: 'cV[ftype t]_n) (i: 'I_n) 
     : 'cV_n  :=
   update_mx x i ord0
    (BDIV (subtract_loop (x i ord0) (map (fun j => (L i j, x j ord0)) (take i (ord_enum n))))
          (L i i)).

Definition forward_subst [t: type] [n]
         (L: 'M[ftype t]_n) (x: 'cV[ftype t]_n) : 'cV_n :=
  foldl (forward_subst_step L) x (ord_enum n).

Definition backward_subst_step {t: type} [n: nat]
         (U: 'M[ftype t]_n) (x: 'cV[ftype t]_n) (i: 'I_n) : 'cV_n :=
    update_mx x i ord0
      (BDIV (subtract_loop (x i ord0) (map (fun j => (U i j, x j ord0)) (drop (i+1) (ord_enum n))))
         (U i i)).

Definition backward_subst {t: type} [n: nat]
         (U: 'M[ftype t]_n) (x: 'cV[ftype t]_n) : 'cV[ftype t]_n :=
     foldl (backward_subst_step U) x (rev (ord_enum n)).

Lemma subtract_loop_finite_e: forall (c: ftype t) (al: seq (ftype t * ftype t)), 
  Binary.is_finite (subtract_loop c al) ->
  Binary.is_finite c /\ forallb (fun p => Binary.is_finite (fst p) && Binary.is_finite (snd p)) al.
Proof.
 intros c al; revert c; induction al as [ | [x y] al] ; intros.
 - split; auto.
 - unfold subtract_loop in H.  simpl in H. 
  apply IHal in H.
  destruct H.
  apply float_acc_lems.BMINUS_finite_sub in H. destruct H; auto.
  split; auto.
  simpl. apply BMULT_finite_e in H1. destruct H1. rewrite H1 H2. apply H0.
Qed.

(* move this to float_acc_lems *)
Lemma BSQRT_finite_e: forall (x: ftype t) (H: Binary.is_finite (BSQRT x)), Binary.is_finite x.
Proof.
intros.
destruct x; try destruct s; try discriminate; auto.
Qed.

Lemma diag_finite_R_finite:
 forall [n] (A R: 'M[ftype t]_n),
  A^T = A ->
  cholesky_jik_spec A R ->
  (forall i, Binary.is_finite (R i i)) ->
  forall i j, (nat_of_ord i <= nat_of_ord j)%N -> Binary.is_finite (R i j).
Proof.
intros n A R H H0 H1' i j H2.
pose proof I.
assert ((i<j) \/ (nat_of_ord i == nat_of_ord j))%N by lia.
destruct H3.
2: assert (i=j) by (apply ord_inj; lia); subst j; apply (H1' i).
destruct (H0 i j) as [? _].
specialize (H4 H3).
pose proof (H1' j).
pose proof (H0 j j).
destruct H6 as [_ ?].
rewrite H6 in H5; auto.
apply BSQRT_finite_e in H5.
unfold subtract_loop_jik in H5.
apply subtract_loop_finite_e in H5.
destruct H5 as [_ H5].
red in H5. rewrite -> forallb_forall in H5.
specialize (H5 (R i j, R i j)).
simpl in H5.
assert (Binary.is_finite (fun_of_matrix R i j) && Binary.is_finite (fun_of_matrix R i j) = true).
2: rewrite Bool.andb_true_iff in H7; destruct H7; auto.
apply H5.
clear - H3.
rewrite map_take.
set f := (fun k' : ordinal n => pair (fun_of_matrix R k' j) (fun_of_matrix R k' j)).
change (pair _ _) with (f i).
clearbody f.
pose proof (ltn_ord j).
replace (f i) with  (ListDef.nth (nat_of_ord i) (take (nat_of_ord j) (map f (ord_enum n))) (Zconst t 0, Zconst t 0)).
apply nth_In.
change @length with @size.
rewrite size_take.
rewrite size_map.
rewrite size_ord_enum.
rewrite H.
lia.
rewrite -nth_List_nth.
rewrite nth_take; auto.
rewrite (nth_map i).
rewrite nth_ord_enum' //.
rewrite size_ord_enum.
lia.
Qed.


Lemma last_R_finite:
 forall [n] (A R: 'M[ftype t]_n.+1),
  A^T = A ->
  cholesky_jik_spec A R ->
   Binary.is_finite (R (inord n) (inord n)) ->
  forall i j, (nat_of_ord i <= nat_of_ord j)%N -> Binary.is_finite (R i j).
Proof.
Abort.  (* Not true.  If one of the [R i i] is +infinity, then the calculation of the next row will divide by that value, yielding zeros. *)

Lemma cholesky_success_R_finite:
 forall [n] (A R: 'M[ftype t]_n),
  A^T = A ->
  cholesky_success A R ->
  forall i j, (nat_of_ord i <= nat_of_ord j)%N -> Binary.is_finite (R i j).
Proof.
intros.
destruct H0.
eapply diag_finite_R_finite; try eassumption.
clear i j H1; intro i.
apply is_finite_strict_finite; apply H2.
Qed.


Lemma rev_List_rev: forall t (al: list t), rev al = List.rev al.
Admitted.

Lemma BFREXP_finite_e: forall [t] (x: ftype t), Binary.is_finite (fst (BFREXP x)) -> Binary.is_finite x.
Admitted.

Lemma Bmult_R0 (f a: ftype t) :
Binary.is_finite (BMULT f a) ->
FT2R a = 0 -> 
(BMULT f a) = neg_zero \/ (BMULT f a) = pos_zero.
Proof.
  rewrite /BMULT/BINOP //= /pos_zero/neg_zero/Binary.Bmult.
  destruct f,a,s,s0 => //=; 
  move => FIN HA; try discriminate FIN; auto;
  try apply Float_prop.eq_0_F2R in HA;
  repeat (destruct m0; try discriminate HA).
Qed.

Lemma SQRT_nonneg: forall (x: ftype t),
 Binary.is_finite x -> BCMP Gt true (Zconst t 0) (BSQRT x) = false.
Proof.
  move => x H.
   destruct x; try destruct s; try reflexivity; try discriminate.
   unfold BSQRT, UNOP.
  destruct (Binary.Bsqrt_correct _ _ (fprec_gt_0 t) (fprec_lt_femax t)
                   (FPCore.sqrt_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE
                   (Binary.B754_finite (fprec t) (femax t) false m e e0))
   as [? [? ?]].
 set j := Binary.Bsqrt _ _ _ _ _ _ _ in H0,H1,H2|-*.
 simpl in H2.
 assert (Binary.Bsign _ _ j = false).
 apply H2. clear - H1; destruct j; auto.
 clear - H1 H3.
 destruct j; auto; try discriminate.
 simpl in H3.
  subst s; reflexivity.
Qed.

Lemma cholesky_return_success:
  (2 < femax t)%Z ->
  forall [n] (A R: 'M[ftype t]_n),
    cholesky_jik_spec A R ->
    Zcholesky_return (cholesky_return R) = 1%Z ->
    cholesky_success A R.
Proof.
intros Hemax2 n A R H H0.
split; auto.
unfold cholesky_return in H0.
pose isSqrt (x: ftype t) := Binary.is_finite x -> BCMP Gt true (Zconst t 0) x = false.
assert (Hpos: forall i, isSqrt (R i i)). {
  move => i. destruct (H i i) as [_ ?]. rewrite H1 //.
  set x := subtract_loop_jik _ _ _ _ _. clearbody x. clear.
   move => H.
  apply SQRT_nonneg; auto.
  apply BSQRT_finite_e in H; auto.
}
intro.
assert (Forall (fun i =>  Binary.is_finite_strict _ _ (R i i)) (ord_enum n)).
2:{
rewrite Forall_forall in H1. apply H1.
apply /Iter.In_mem.
apply mem_ord_enum.
}
rewrite -(revK (ord_enum n)) in H0|-*.
rewrite foldl_rev in H0.
set al := rev (ord_enum n) in H0|-*.
clearbody al.
set f := (fun x => _) in H0.
set z := foldr _ _ _ in H0.
assert (Binary.is_finite z /\ (FT2R z <> 0)%Re). {
  destruct z; try destruct s; try discriminate H0.
  simpl. split; auto.
  unfold Defs.F2R; simpl.
  intro Hx; apply Rmult_integral in Hx; destruct Hx. apply eq_IZR_R0 in H1. discriminate.
  pose proof (bpow_gt_0 Zaux.radix2 e); lra.
  split; auto. simpl.
  apply Rgt_not_eq.
  apply Rmult_pos_pos.
  unfold IZR.
  apply IPR_gt_0. apply bpow_gt_0.
}
clear - H1 Hpos Hemax2.
destruct H1; subst z.
rewrite rev_List_rev.
apply Forall_rev.
induction al; constructor.
-
simpl in H, H0.
rewrite {1}/f in H.
rewrite {1}/f in H0.
apply BMULT_finite_e in H. destruct H.
apply BFREXP_finite_e in H1.
destruct (R a a); try discriminate; auto.
destruct (Bmult_R0 (foldr f (Zconst t 1) al)  (BFREXP (Binary.B754_zero (fprec t) (femax t) s)).1).
destruct (BMULT _ _); simpl in H0; auto; try lra.
reflexivity.
rewrite H2 in H0. simpl in H0. lra.
rewrite H2 in H0; simpl in H0; lra.
-
apply IHal.
simpl in H.
apply BMULT_finite_e in H. destruct H; auto.
simpl in H0.
rewrite {1}/f in H0.
simpl in H.
set x := foldr _ _ _ in H,H0|-*.
specialize (Hpos a).
rewrite /f in H.
set y := R a a in Hpos,H0,H|-*.
clear - Hpos H0 H Hemax2.
red in Hpos.
apply BMULT_finite_e in H; destruct H.
specialize (Hpos (BFREXP_finite_e _ H1)).
destruct y; try destruct s; try discriminate.
set y := Binary.B754_zero (fprec t) (femax t) true in Hpos,H0,H1.
+
change (fst _) with y in H0.
destruct (Bmult_R0 x y).
destruct (BMULT x y); simpl in H0; try lra; reflexivity.
reflexivity.
rewrite H2 in H0; simpl in H0; lra.
rewrite H2 in H0; simpl in H0; lra.
+
destruct x; try destruct s; simpl in H0|-*; try discriminate; try lra.
+
clear H1 Hpos.
clearbody x.
clear - H0 H Hemax2.
rewrite /BFREXP in H0.
destruct (Binary.Bfrexp_correct _ _ _ Hemax2 (Binary.B754_finite (fprec t) (femax t) false m e e0) (Logic.eq_refl _))
  as [_ [? _]].
set y := Binary.B754_finite (fprec t) (femax t) false m e e0 in H0,H1.
set z := fst _ in H1,H0|-*.
clearbody z.
assert (0 < Binary.B2R _ _ y)%Re. {
  subst y; simpl. apply Float_prop.F2R_gt_0.  simpl.  lia.
}
rewrite H1 in H2.
assert (0 < bpow Zaux.radix2 (Binary.Bfrexp (fprec t) (femax t) (fprec_gt_0 t) y).2)%Re.
 apply bpow_gt_0. 
assert (0 < Binary.B2R _ _ z)%Re. nra.
assert (Binary.is_finite z).
  clear - H4; destruct z; try destruct s; simpl in H4; try lra; reflexivity.
clear - H0 H4 H H5.
unfold BMULT, BINOP in H0.
pose proof (Binary.Bmult_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t)
        (FPCore.mult_nan (fprec t) (femax t) (fprec_gt_one t)) BinarySingleNaN.mode_NE x z).
set u := Binary.Bmult _ _ _ _ _ _ _ _ in H0,H1.
clearbody u.
destruct (Rlt_bool _ _) in H1.
*
destruct H1 as [? [? ?]].
rewrite H H5 in H2. simpl in H2.
clear - H2 H0 H3 H4 H H1.
specialize (H3 ltac:(destruct u; try destruct s; try discriminate; auto)).
intro.
unfold FT2R in H5. rewrite H5 in H1.
rewrite Rmult_0_l in H1. simpl in H1.
rewrite Generic_fmt.round_0 in H1.
unfold FT2R in H0. rewrite H1 in H0. lra.
*
unfold Binary.binary_overflow, BinarySingleNaN.binary_overflow in H1.
simpl in H1.
destruct u; try destruct s; simpl in H0; try lra; try discriminate.
Qed.

End WithNaN.

