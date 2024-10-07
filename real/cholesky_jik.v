From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun bigop finset fingroup perm order.
From mathcomp Require Import div prime binomial ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
From mathcomp.algebra_tactics Require Import ring lra.
From mathcomp Require Import ssrnum reals interval classical_sets topology normedtype boolp.
Import Num.Theory Num.Def numFieldTopology.Exports numFieldNormedType.Exports.
Require Import LAProof.real.cholesky.
Unset Implicit Arguments.
(*Unset Strict Implicit.*)
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Import GroupScope.
Import GRing.Theory Order.POrderTheory.
Local Open Scope ring_scope.

Local Notation "A ^T" := (trmx A) : ring_scope.

(* Algorithm 10.2 from Higham *)

Section Cholesky_jik.

Variable F : realType.

Axiom proof_irr: forall (P: Prop) (H1 H2: P), H1=H2.

Lemma ordinal_eq: forall {n m1 m2} P1 P2, m1=m2 -> @Ordinal n m1 P1 = @Ordinal n m2 P2.
Proof.
intros; subst. f_equal. apply proof_irr.
Qed.

Definition widen_ik {n} (i: 'I_n) (k: 'I_i) : 'I_n := 
   widen_ord (ltnW (ltn_ord i)) k.

Definition widen_ik_subproof [n i: nat] (k: 'I_i) (H: (i<n.+1)%N) : (k < n.+1)%N := 
  widen_ord_proof k (ltnW (ltn_ord (Ordinal H))).

Lemma widen_ik_sub: 
  forall (n i: nat) (H: (i < n.+1)%N) (k: 'I_i),
   widen_ik (Sub i H) k = Sub (nat_of_ord k) (widen_ik_subproof k H).
Proof. reflexivity. Qed.

Lemma solve_LT_eq: forall [n] (L: 'M[F]_n.+1) (c: 'cV[F]_n.+1),
   let r := solve_LT L c in
     forall i: 'I_n.+1,
        r i 0 = (c i 0 - \sum_(k<i) (fun k' => L i k' * r k' 0) (widen_ik i k))/L i i.
Proof.
elim  => [ | n IH] L c r i.
- rewrite /r ord1 big_ord0 /= mxE mulrC subr0 //.
- simpl in r.
  set L': 'M_(1+n.+1) := L.
  set c': 'cV_(1+n.+1) := c.
  set c1 := dsubmx c' - dlsubmx L' *m ((L 0 0)^-1 *: usubmx c').
  specialize (IH (drsubmx L') c1).
  revert r.
  set r' := solve_LT (drsubmx L') c1 in IH *.
  move => r.
  cbv zeta in IH.
  clearbody r'.
  subst r.
  change 'I_(1+n.+1) in i.
  case: (split_ordP i) => i' Hi'; subst i. rewrite ord1; clear i'.
 + set x := _ *: _. simpl in x.
   rewrite -(vsubmxK c') !(col_mxEu _ _ (0:'I_1)).
   rewrite -(submxK L') (block_mxEul _ _ _ _ (0:'I_1) (0:'I_1)).
   change (_ *: _) with x in c1. simpl in c1.
   simpl. rewrite big_ord0 subr0 /x mxE mulrC /c' !mxE lshift0 //.
 + set x := _ *: _. simpl in x.
   rewrite -(vsubmxK c') (col_mxEd x) (col_mxEd (usubmx c')).
   rewrite -{2}(submxK L'). rewrite  (block_mxEdr (ulsubmx L')).
   rewrite (IH i') /c1 -/x. clear IH c1.
   f_equal.
   rewrite mxE -addrA.
   f_equal.
   rewrite big_split_ord /= big_ord1 mxE mxE.
   have ->: widen_ik (rshift 1 i') (lshift i' 0) = lshift n.+1 0.
     apply ordinal_eq; reflexivity.
   rewrite (col_mxEu x) big_ord1.
   have ->:  L' (rshift 1 i') (lshift n.+1 0) = dlsubmx L' i' 0.
      by rewrite -(submxK L') block_mxEdl block_mxKdl.
   move :(_ * _) => u.
   set a := bigop _ _ _. set b := bigop _ _ _.
   rewrite (_: a=b); first by field.
   apply eq_big; auto.
   move => i _.
   have ->: widen_ik (rshift 1 i') (rshift 1 i) = rshift 1 (widen_ik i' i)
       by apply ordinal_eq; reflexivity.
   f_equal.
   * rewrite -{2}(submxK L') (block_mxEdr (ulsubmx L')) //.
   *  rewrite (col_mxEd x) //.
Qed.

Definition sumR := List.fold_right GRing.add  (0:F).


Definition Mij {n} (A: 'M[F]_n.+1) (i j : nat) : F :=
 if insub i is Some i' then if insub j is Some j' then A i' j' else 0 else 0.

Definition Vi {n} (x: 'cV[F]_n.+1) (i: nat) : F :=
  if insub i is Some i' then x i' 0 else 0.
 

Lemma sum_nat_sumR: forall n (f: nat -> F),
  \sum_(0<= i < n) f i = sumR [seq f i | i <- index_iota 0 n].
Proof.
 intros i f.
  set lo := 0%nat.
  unfold index_iota.
  set n := (i-lo)%N. clearbody n.
  move :n lo.
  elim => [ | n Hn] lo. 
 + 
   have ->: iota lo 0 = index_iota lo 0. unfold index_iota. f_equal; lia.
   rewrite big_geq; auto.
 + transitivity (\sum_(k <- index_iota lo (lo+n).+1) f k).
   f_equal. unfold index_iota; f_equal; lia.
   rewrite big_nat_recl; last lia.
   simpl. rewrite -Hn. f_equal.
   have ->: iota lo.+1 n = index_iota lo.+1 ((n+lo).+1). unfold index_iota; f_equal; lia.
   rewrite big_add1.
   f_equal. f_equal. lia.
Qed.

Lemma iota_0_index_iota: forall i, iota 0 i = index_iota 0 i.
Proof.
move => i. rewrite /index_iota; f_equal; lia.
Qed.

Lemma solve_LT_eq': forall n (L: 'M[F]_n.+1) (c: 'cV[F]_n.+1),
   let r := solve_LT L c in
     forall i: nat,
        (i < n.+1)%N ->
        Vi r i = (Vi c i - sumR (map (fun k => Mij L i k * Vi r k) (iota 0 i))) / Mij L i i.
Proof.
move => n L c r i H.
have H0 := solve_LT_eq L c (Sub i H).
rewrite iota_0_index_iota.
rewrite -/r in H0. 
rewrite /Vi /Mij.
rewrite insubT.
rewrite {}H0.
f_equal. f_equal. f_equal.
transitivity (\sum_(0 <= k < i) Mij L i k * Vi r k).
-
  rewrite big_mkord.
  apply eq_bigr.
  move => k _.
  pose Hk := widen_ik_subproof k H.
  rewrite widen_ik_sub /Mij /Vi !insubT //.
- rewrite /Mij /Vi insubT sum_nat_sumR //.
Qed.

Definition cholesky_jik_spec {n} (A R: 'M[F]_(n.+1)) : Prop :=
  R = \matrix_(i,j) 
        if (i<j)%N then (A i j - \sum_(k<i) (R (widen_ik i k) i * R (widen_ik i k) j)) / R i i
        else if i==j then Num.sqrt(A j j - \sum_(k<i) (R (widen_ik i k) j ^+ 2))
        else 0.

Ltac if_lia b :=
 match goal with |- context[if ?A then _ else _] => 
    have ->: A=b by lia
 end.

Lemma cast_ord_inj': forall [n m: nat] (eq: n=m) x y, (cast_ord eq x == cast_ord eq y) = (x==y).
Proof.
intros.
have H := @cast_ord_inj _ _ eq x y.
apply /eqP.
destruct (@eqP _ x y).
f_equal; auto.
contradict n0; auto.
Qed.

Lemma cholesky_jik_spec_eqv: forall n (A: 'M[F]_n.+1),  cholesky_jik_spec A (cholesky A).
Proof.
elim => [ | n IH] A.
-
apply matrixP.
move => i j.
rewrite !ord1 !mxE.
if_lia false.
simpl.
rewrite big_ord0 subr0 //.
-
red.
rewrite -(castmxK add_two add_two A).
move :(castmx (add_two,add_two) A).
clear A.
move => A.
rewrite /cholesky castmxKV.
change (_ n (ulsubmx A)) with (cholesky (ulsubmx A)).
set A1 := ulsubmx A.
specialize (IH A1).
set R1 := cholesky A1 in IH *.
set c := ursubmx A.
have Hr:= solve_LT_eq R1^T c.
set r := solve_LT _ _ in Hr *.
clearbody r.
cbv zeta in Hr.
set α := drsubmx A.
rewrite IH.
set R := castmx _ (block_mx _ _ _ _).
apply matrixP.
move => i j.
rewrite !mxE.
rewrite -(cast_ordK add_two i) -(cast_ordK add_two j).
case: (split_ordP (cast_ord add_two i)) => i0 Hi; rewrite Hi; clear i Hi;
case: (split_ordP (cast_ord add_two j)) => j0 Hj; rewrite Hj; clear j Hj;
rewrite !castmxE !cast_ordK ?block_mxEul ?block_mxEdl ?block_mxEur ?block_mxEdr !mxE; simpl.
+
rewrite cast_ord_inj'.
rewrite eq_refl.
case: (i0 < j0)%N /ltP => Hij.
*
if_lia false.
f_equal.
f_equal.
f_equal.
--
apply eq_bigr. move => i _.
f_equal.
++
rewrite {}/R /widen_ik.
have Hi0n: (i0 <= n.+1)%N by clear - Hij;  destruct i0; simpl in *; lia.
have ->: (widen_ord (ltnW (ltn_ord (cast_ord (esym add_two) (lshift 1 i0)))) i) = 
          cast_ord (esym add_two) (lshift 1 (widen_ord (m:=n.+1) Hi0n i))
 by apply ordinal_eq; reflexivity.
rewrite !castmxE !cast_ordK block_mxEul.
red in IH. rewrite -IH.
f_equal. apply ordinal_eq; reflexivity.
++
rewrite {}/R /widen_ik.
have Hi0n: (i0 <= n.+1)%N by clear - Hij;  destruct i0; simpl in *; lia.
have ->: (widen_ord (ltnW (ltn_ord (cast_ord (esym add_two) (lshift 1 i0)))) i) = 
          cast_ord (esym add_two) (lshift 1 (widen_ord (m:=n.+1) Hi0n i)).
 compute. f_equal. apply proof_irr.
rewrite !castmxE !cast_ordK block_mxEul.
red in IH. rewrite -IH.
f_equal. apply ordinal_eq; reflexivity.
--
f_equal.
rewrite IH mxE.
if_lia false.
rewrite eq_refl.
f_equal.
rewrite /A1.
f_equal.
rewrite ulsubmxEsub mxE //.
f_equal.
rewrite -IH //.
*
case: (i0 == j0) /eqP => Hij'.
--
subst j0. clear Hij.
rewrite eq_refl.
f_equal.
f_equal.
f_equal.
apply eq_bigr. move => k _.
rewrite {}/R /widen_ik.
have ->: (widen_ord (ltnW (ltn_ord (cast_ord (esym add_two) (lshift 1 i0)))) k) = 
          cast_ord (esym add_two) (lshift 1 (widen_ord (m:=n.+1) (ltnW (ltn_ord i0)) k))
 by apply ordinal_eq; reflexivity. 
rewrite !castmxE !cast_ordK block_mxEul.
rewrite -IH //.
--
have ->:(lshift 1 i0 == lshift 1 j0)=false.
apply gtn_eqF. simpl.
have Hij'': nat_of_ord i0 <> nat_of_ord j0 
 by clear - Hij'; destruct i0,j0; contradict Hij'; simpl in *; subst; f_equal; auto.
lia. auto.
+
rewrite ord1 {}Hr. clear j0.
if_lia false.
rewrite addn0 ltn_ord eq_refl !mxE.
f_equal.
*
f_equal.
f_equal.
apply eq_bigr. move => k _.
rewrite {}/R /widen_ik mxE.
have ->: (widen_ord (ltnW (ltn_ord (cast_ord (esym add_two) (lshift 1 i0)))) k) = 
          cast_ord (esym add_two) (lshift 1 (widen_ord (m:=n.+1) (ltnW (ltn_ord i0)) k))
 by apply ordinal_eq; reflexivity.
rewrite !castmxE !cast_ordK block_mxEul block_mxEur.
f_equal.
rewrite -IH //.
*
f_equal.
clear R c r α.
have ->: A (lshift 1 i0) (lshift 1 i0) = A1 i0 i0.
  rewrite /A1 ulsubmxEsub mxE //.
clearbody A1. clear A.
rewrite {1}IH mxE.
if_lia false. rewrite eq_refl. done.
+
have ->: (n.+1+i0<j0)%N=false.
clear - i0 j0; destruct i0,j0; simpl in *; lia.
case: (cast_ord (esym add_two) (rshift n.+1 i0) ==
  cast_ord (esym add_two) (lshift 1 j0)) /eqP => Hij; auto.
apply cast_ord_inj in Hij.
have HH := eq_rlshift i0 j0. rewrite Hij in HH. rewrite eq_refl in HH. done.
+
rewrite !ord1. clear i0 j0.
if_lia false.
rewrite eq_refl.
f_equal.
f_equal.
f_equal.
set fi := widen_ik _.
simpl in fi.
transitivity (\sum_(k<n.+1) R (cast_ord (esym add_two) (lshift 1 k))
 (cast_ord (esym add_two) (rshift n.+1 0)) ^+ 2).
*
apply eq_bigr.
move => i _.
rewrite !mxE !castmxE esymK !cast_ordKV block_mxEur expr2 //.
*
clearbody R. clear.
rewrite (big_ord_widen_leq (n.+1+@nat_of_ord 1 0)); last lia.
apply eq_big.
--
move => i. destruct i; simpl in *. lia.
--
simpl.
move => i Hi.
f_equal.
f_equal.
rewrite {}/fi /widen_ik.
destruct i; simpl in*.
rewrite /widen_ord /cast_ord // /inord /insubd /odflt/oapp /insub.
destruct idP; last by lia.
apply ordinal_eq; reflexivity.
Qed.


End Cholesky_jik.

