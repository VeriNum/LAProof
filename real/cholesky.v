From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun bigop finset fingroup perm order.
From mathcomp Require Import div prime binomial ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Import GroupScope.
Import GRing.Theory.
Local Open Scope ring_scope.

Local Notation "A ^T" := (trmx A) : ring_scope.

Section SemiRing.

Variable F: semiRingType.

Lemma mulmx_castmx:
 forall m m' n n' p p' (eqm: m=m') (eqn: n=n') (eqp: p=p') (A: 'M[F]_(_,_))  B,
    castmx (eqm,eqn) A *m castmx (eqn,eqp) B = castmx (eqm,eqp) (A *m B).
Proof.
 intros.  subst. rewrite !castmx_id //.
Qed.

Definition symmetric {n} (A: 'M[F]_n) := A^T=A.

Definition symmetric_castmx {n n'} (eqn: n=n') (A: 'M_n) :
  symmetric (castmx (eqn,eqn) A) = symmetric A.
Proof. subst n'. by rewrite castmx_id. Qed.

Lemma symmetric_ulsubmx:
 forall {n} (A: 'M_(n+1)),
  symmetric A -> symmetric (ulsubmx A).
Proof.
move => n A H. rewrite /symmetric trmx_ulsub H //.
Qed.

Definition upper_triangular {n} (A: 'M[F]_n) :=
 (forall i j: 'I_n , (i>j)%N -> A i j = 0).

Lemma upper_triangular_is_trig: forall {n} (A: 'M[F]_n),
    upper_triangular A <-> is_trig_mx A^T.
Proof.
  rewrite /upper_triangular => n A. split => [ Hup | /is_trig_mxP Atrig].
  - apply /is_trig_mxP => i j lt_ij. by rewrite mxE (Hup j i lt_ij).
  - move => i j lt_ji. by rewrite - (Atrig j i lt_ji) mxE.
Qed.

Definition upper_triangular_castmx {n n'} (eqn: n=n') (A: 'M_n) :
  upper_triangular (castmx (eqn,eqn) A) = upper_triangular A.
Proof. subst n'. by rewrite castmx_id. Qed.

Definition diagonal_nonzero {n} (A: 'M[F]_n) :=
  forall i, A i i != 0.

End SemiRing.

Section Solve_LT.

Variable F : fieldType.

(*  let L be a nonsingular lower triangular matrix,
    let c be a column matrix,
    then solve_LT L c finds a column matrix x such that L x = c. *)
Fixpoint solve_LT {n} :  'M[F]_n.+1 -> 'M[F]_(n.+1,1) -> 'M[F]_(n.+1,1) :=
 match n with
 | 0 => fun L c => const_mx ((L 0 0)^-1 *  c 0 0 )
 | n'.+1 => fun L c =>
        let L' : 'M_(1 + n'.+1) := L in
        let c' : 'M_(1+n'.+1,1) := c in
        let x' := solve_LT (drsubmx L') (dsubmx c' - dlsubmx L' *m ((L 0 0)^-1 *: usubmx c')) in
         col_mx ( (L 0 0)^-1 *: usubmx c') x'
 end.

Lemma solve_LT_correct:
  forall n (L: 'M[F]_n.+1) (c: 'M[F]_(n.+1,1)),
    upper_triangular L^T ->
    diagonal_nonzero L ->
    L *m solve_LT L c = c.
Proof.
induction n.
- intros; simpl.
rewrite {1}(mx11_scalar L) mul_scalar_mx scalemx_const mulrA divrr ?unitfE //= mul1r.
apply matrixP => i j; rewrite !ord1 !mxE //=.
-
simpl.
rewrite -['M[F]_n.+2]/'M[F]_(1+n.+1) -['cV[F]_n.+2]/'cV[F]_(1+n.+1) => L c H H0.
set c' := (dsubmx c - _).
rewrite -{1}(submxK L) (mul_block_col (ulsubmx L)) (_: ursubmx L = 0).
2: rewrite -(trmxK L); move :(L^T) H => R H;
   apply matrixP => i j; rewrite !ord1 !mxE /=; by apply H.
rewrite mul0mx addr0 -!scalemxAr {}IHn.
2: rewrite trmx_drsub => i j LESS; move :(L^T) H => R H;
   rewrite !mxE; by apply H.
2: move => i; rewrite !mxE //.
subst c'.
rewrite -scalemxAr addrA (addrC _ (dsubmx c)) addrK scalemxAl (_: ulsubmx L = const_mx (L 0 0)).
2: apply matrixP => i j; by rewrite !ord1 !mxE !lshift0.
rewrite scalemx_const mulrC divrr ?unitfE //= (_: const_mx _ = 1).
2: apply matrixP => i j; by rewrite !ord1 !mxE.
by rewrite mulmxE mul1r vsubmxK.
Qed.

End Solve_LT.

Require Import mathcomp.algebra.ssrnum.

Section Cholesky.

Variable F : rcfType.  (* rcf = real closed field *)

Lemma add_two {n}: n.+2 = n.+1+1.
Proof. rewrite addrC //. Qed.

Fixpoint cholesky {n} : 'M[F]_n.+1 -> 'M[F]_n.+1 :=
  match n with
  | 0 => fun A => (Num.sqrt (A 0 0))%:M
  | n'.+1 => fun A =>
         let A' : 'M_(n'.+1+1):= castmx (add_two,add_two) A in
         let A1 := ulsubmx A' in
         let c := ursubmx A' in
         let α := drsubmx A' 0 0in
         let R1 := cholesky A1 in
         let r := solve_LT R1^T c in
         let β := Num.sqrt (α - ((r^T *m r) 0 0)) in
         castmx (esym add_two, esym add_two) (block_mx R1 r 0 β%:M)
  end.

Definition diagonal_positive {n} (A: 'M[F]_n) :=
  forall i, A i i > 0 :>F.

Definition posdef' {n} (A: 'M_n) :=
   forall x : 'cV_n, x != 0 -> (x^T *m A *m x) 0 0 > 0 :>F.

Definition positive_definite {n} (A: 'M_n) :=
  symmetric A /\ posdef' A.


Definition positive_definite_castmx {n n'} (eqn: n=n') (A: 'M_n) :
  positive_definite (castmx (eqn,eqn) A) = positive_definite A.
Proof. subst n'. by rewrite castmx_id. Qed.

Lemma positive_definite_ulsubmx:
 forall {n} (A: 'M_(n+1)),
  positive_definite A -> positive_definite (ulsubmx A).
Proof.
 move => n A [SYM H].
 split.
 by apply symmetric_ulsubmx.
 move => x H0.
 have H2: col_mx x 0%:M != 0. {
   move :H0; apply contra_neq => H0.
   rewrite -col_mx0 in H0.
   apply eq_col_mx in H0.
   apply H0.
 }
 move :(H (col_mx x 0%:M) H2).
 rewrite -{1}(submxK A) /block_mx (tr_col_mx x) (mul_row_col x^T).
 rewrite tr_scalar_mx mul_scalar_mx scale0r addr0 -mulmxA (mul_row_col (ulsubmx A)).
 rewrite scalar_mxC mul_scalar_mx scale0r addr0 mulmxA //.
Qed.

Lemma det_positive_definite: forall {n} (A: 'M[F]_(n.+1)),
  positive_definite A -> 0 < \det A .
Admitted.

Lemma block_decompose {n1 n2} {A: 'M[F]_n1} {B: 'M[F]_(n1, n2)}
  {C: 'M[F]_(n2, n1)} {D: 'M[F]_n2}:
  A \in unitmx ->
  block_mx A B C D = (block_mx 1%:M 0 (C *m invmx A) 1%:M) *m
                     (block_mx A 0 0 (D - C *m invmx A *m B)) *m
                     (block_mx 1%:M (invmx A *m B) 0 1%:M).
Proof.
  move => Ai. rewrite !mulmx_block !mulmx0 !mul0mx !mulmx1 !mul1mx !addr0 add0r (mulmxA A).
  by rewrite (mulmxV Ai) -(mulmxA C) (mulVmx Ai) !mulmx1 mul1mx mulmxA addrCA subrr addr0.
Qed.

Lemma det_block_mx {n1 n2} (A: 'M[F]_(n1+n2)):
  ulsubmx A \in unitmx ->
  \det A = \det (ulsubmx A) * \det (drsubmx A - dlsubmx A *m invmx (ulsubmx A) *m ursubmx A).
Proof.
  move => Ai. rewrite -{1}(submxK A) (block_decompose Ai) !det_mulmx !det_lblock det_ublock.
  by rewrite !det1 !mulr1 mul1r.
Qed.

Definition diagonal_of {n} (A: 'M[F]_n.+1) : 'rV[F]_n.+1 :=
  \row_i (A i i).

Lemma det_upper_triangular {n} (A: 'M[F]_n.+1) :
  upper_triangular A -> \det A = \det (diag_mx (diagonal_of A)).
Proof.
  rewrite upper_triangular_is_trig => Htrig.
  rewrite -det_tr (det_trig Htrig) det_diag /diagonal_of.
  apply: eq_bigr=> i _. by rewrite !mxE.
Qed.

Theorem cholesky_correct:
  forall n (A: 'M_n.+1),
    positive_definite A ->
    let R := cholesky A in
      upper_triangular R /\ diagonal_positive R /\ R^T * R = A.
Proof.
elim => [|n IHn].
-
 simpl.
 move => A [H H0].
 repeat split.
 + by move => i j; rewrite !ord1; move => K; inversion K.
 + move => i. rewrite !mxE eqxx /= mulr1n.
   move :(H0 1 ltac:(apply oner_neq0)).
   rewrite trmx1 mul1mx mulmx1 Num.Theory.sqrtr_gt0 //.
 + rewrite tr_scalar_mx -mulmxE  mul_scalar_mx scale_scalar_mx -expr2 Num.Theory.sqr_sqrtr
           -?mx11_scalar //=.
   move : (H0 1).
   rewrite !mulmxE trmx1 mulr1 mul1r.
   move => H1.
   apply Order.POrderTheory.ltW.
   apply H1, oner_neq0.
-
move => A.
rewrite -(castmxK add_two add_two A).
set A' : 'M_(n.+1 + 1) := castmx _ A.
rewrite positive_definite_castmx.
clearbody A'; clear A. move :A' => A PA.
rewrite /cholesky -/cholesky
   upper_triangular_castmx trmx_cast tr_block_mx -mulmxE mulmx_castmx castmxKV /=.
set A1 := ulsubmx A.
case: (IHn A1) => [ | UPPER [DP H1]] {IHn};
  first by apply positive_definite_ulsubmx.
move :(cholesky _) => R in UPPER DP H1 *.
set α := drsubmx A.
set c := ursubmx A.
have DN: diagonal_nonzero R.
  move => i. apply /negP => /eqP EQ. move :(DP i). rewrite EQ => GT.
  eapply Order.POrderTheory.lt_nsym; eassumption.
have H2 := @solve_LT_correct _ _ (R^T) c
               ltac:(by move => i j LESS; rewrite !mxE; apply UPPER)
               ltac:(by move => i; rewrite !mxE; apply DN).
move :(solve_LT _ _) => r in H2 *.
set β2 := (_ -  _).
set β : F := Num.sqrt β2.
have EQA: A = block_mx A1 c c^T α
    by rewrite -(submxK A) trmx_ursub (proj1 PA).
have Runit: R \in unitmx.
  {  rewrite unitmxE unitfE det_upper_triangular // det_diag.
     apply /prodf_neq0 => i _. by rewrite mxE.
  }
assert (POSβ: 0 < β2). {
 have Adet: 0 < \det A1
  by apply det_positive_definite, positive_definite_ulsubmx, PA.
 have A1unit: A1 \in unitmx
  by rewrite unitmxE unitfE; apply Num.Theory.lt0r_neq0, Adet.
 have HH := PA; apply det_positive_definite in HH; move :HH.
 rewrite (@det_block_mx _ _ A) // -/A1 -/c -/α EQA block_mxKdl -H2 trmx_mul trmxK
        mulmxA -!(mulmxA r^T) -{2}H1.
 rewrite -H1 in A1unit.
 move :(mulmxK A1unit (invmx R^T)).
 rewrite !(mulmxA (invmx _)) mulVmx ?unitmx_tr // mul1mx.
 move => GG. rewrite {}GG mulVmx ?unitmx_tr // mul1mx det_mx11 mxE /β2.
 move :(α 0 0) => a in β2 β *.
 move :(r^T *m r) => rr.
 rewrite mxE Num.Theory.pmulr_rgt0 //.
}
repeat split.
+ (* upper triangular *)
  move => i j LESS.
  rewrite !mxE /split; case: (ltnP i n.+1) => Hi;
  rewrite !mxE /split; case: (ltnP j n.+1) => Hj.
  by apply UPPER.
  by lia.
  by rewrite !mxE.
  by destruct i,j; simpl in *; lia.
+ (* diagonal_positive *)
  move => i. rewrite castmxE /= esymK.
  case: (split_ordP (cast_ord add_two i)) => i0 e.
  * rewrite e block_mxEul //.
  * rewrite e block_mxEdr ord1 mxE eqxx /= mulr1n /β Num.Theory.sqrtr_gt0 //.
+ (* R^T * R = A *)
f_equal.
rewrite mulmx_block !mulmx0 !addr0 !mulmxE !H1 !trmx0 !mul0mx !addr0
    -{2}(trmxK R) -trmx_mul H2 tr_scalar_mx EQA.
f_equal.
rewrite -mulmxE -scalar_mxM -expr2 Num.Theory.sqr_sqrtr;
 last by apply Order.POrderTheory.ltW.
rewrite (mx11_scalar (_ *m _)) addrC scalar_mx_is_additive
        -addrA addNr addr0 -mx11_scalar //.
Qed.

Fixpoint cholesky_LDL {n} : 'M[F]_n.+1 -> 'M[F]_n.+1 * 'rV[F]_n.+1 :=
  match n with
  | 0 => fun A => (1, (A 0 0)%:M)
  | n'.+1 => fun A =>
         let A' : 'M_((n'.+1)+1):= castmx (add_two,add_two) A in
         let A1 := ulsubmx A' in
         let c := ursubmx A' in
         let An := drsubmx A' in
         let: (L1,D1) := cholesky_LDL A1 in
         let r := solve_LT L1 c in
         let α := An 0 0 in
         let β2 := α - ((r^T *m r) 0 0) in
         let L' : 'M_((n'.+1)+1):= block_mx L1 0 r^T 1 in
         let D' : 'rV_((n'.+1)+1) := row_mx D1 (β2%:M) in
          (castmx (esym add_two, esym add_two) L',
           castmx (erefl _, esym add_two) D')
  end.

Lemma castmx_diag_mx: forall {n n'} (eqn: n=n') (D: 'rV[F]_n'),
 castmx (eqn,eqn) (diag_mx (castmx (erefl 1%N, esym eqn) D)) = diag_mx D.
Proof. intros. subst. rewrite !castmx_id //. Qed.

Lemma cholesky_LDL_eq: forall n (A: 'M[F]_n.+1),
   positive_definite A ->
   let R := cholesky A in
   let: (L,D) := cholesky_LDL A in
   L *m diag_mx (map_mx Num.sqrt D) = R^T.
Proof.
elim => [|n IHn] A PA.
-
rewrite /= mul1mx tr_scalar_mx.
apply matrixP. move => i j. rewrite !mxE ord1 eqxx //.
-
rewrite -(castmxK add_two add_two A).
set A' : 'M_(n.+1 + 1) := castmx _ A.
have PA1: positive_definite (ulsubmx A').
   apply positive_definite_ulsubmx.
   rewrite positive_definite_castmx //.
rewrite /cholesky -/cholesky /cholesky_LDL -/cholesky_LDL castmxKV.
move :(IHn (ulsubmx A') PA1). clear IHn.
move :(cholesky_correct PA1) => [UT [DN CORR]].
move :(cholesky _) => R1 in UT DN CORR *.
move :(cholesky_LDL _) => [L1 D1] /= => H.
rewrite trmx_cast tr_block_mx -{}H /=.
Abort.  (* continue this some other day *)


End Cholesky.
