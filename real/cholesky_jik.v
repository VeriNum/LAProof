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
      compute; f_equal; apply proof_irr.
   rewrite (col_mxEu x) big_ord1.
   have ->:  L' (rshift 1 i') (lshift n.+1 0) = dlsubmx L' i' 0.
      by rewrite -(submxK L') block_mxEdl block_mxKdl.
   move :(_ * _) => u.
   set a := bigop _ _ _. set b := bigop _ _ _.
   rewrite (_: a=b); first by field.
   apply eq_big; auto.
   move => i _.
   have ->: widen_ik (rshift 1 i') (rshift 1 i) = rshift 1 (widen_ik i' i)
       by compute; f_equal; apply proof_irr.
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

Fixpoint cholesky_jik_iloop (n: nat) (A: nat -> nat -> F) (d: nat) : nat -> nat -> F :=
 match d with
 | O => fun _ _ => 0
 | S d' => let R := cholesky_jik_iloop n A d' 
            in fun i j => 
              if (n.+1<=j)%N then 0
              else if j==d' 
              then if  (i<j)%N
                   then (A i j - \sum_(0<=k<i) (R k i * R k j)) / R i i
                   else if i==j
                        then Num.sqrt (A j j - \sum_(0<=k<j) (R k j ^+ 2))
                        else 0
              else R i j
  end.

Lemma insub_nat_of_ord: forall n (i: 'I_n),
   @insub nat (fun i => (i < n)%N) (fintype_ordinal__canonical__eqtype_SubType n) (@nat_of_ord n i) = Some i.
Proof.
intros.
unfold insub.
destruct idP. f_equal.
destruct i; compute; f_equal; apply proof_irr.
have H := @ltn_ord n i.
lia.
Qed.

Lemma cloop_i_ge_d: forall n A d i j, (i >= d)%N -> cholesky_jik_iloop n A d i j = 0.
Proof.
induction d; simpl; intros; auto.
case: (@ltP n j) => Hnj; auto.
case: (@eqP _ j d) => Hjd; auto.
subst j.
have -> :(i<d)%N=false by lia.
have -> :(i==d)=false by lia.
auto.
Qed.


Ltac if_lia b :=
 match goal with |- context[if ?A then _ else _] => 
    have ->: A=b by lia
 end.


Lemma cloop_inc:
 forall (n n' d1 d2 : nat) (A1 A2: nat -> nat -> F),
   (n <= n')%N -> (d1<=n)%N -> (d2<=n')%N ->
   (forall i j, i<n -> j<n -> A1 i j = A2 i j)%coq_nat ->
   (forall i j, i<n -> j<n -> 
Variable F : realType.
      cholesky_jik_iloop n A1 n i j = cholesky_jik_iloop n' A2 n' i j)%coq_nat.
Proof.
intros n n'; revert n.
induction n'; simpl; intros; try lia.
destruct n; simpl; try lia.
repeat if_lia false.
case: (@eqP _ j n) => Hjn; [ subst j | ].
-
case: (@ltP i n) => Hin.
+
case: (@eqP _ n n') => Hnn'.
*
subst n'.
f_equal.
--
f_equal; auto.
f_equal.
admit.
--
f_equal.
admit.  (* looks plausible *)
*
rewrite (IHn' n.+1).

destruct n'; try lia.
simpl.
repeat if_lia false.
case: (@eqP _ n n') => Hnn.
subst n'.
if_lia true.
f_equal.
--
f_equal; auto.
f_equal.
admit.
--
f_equal.

apply IHn'.

apply IHn'.

mpl.

apply IHn'.

*
f_equal.
destruct n; try lia.
simpl.
repeat if_lia false.
repeat if_lia true.
case: (@eqP _ i n) => Hin'; [ subst i | ].
f_equal.
f_equal.
auto.
f_equal.
admit.
apply IHn.

apply IHn.


-
case: (@ltP i d2) => Hid2.
+
destruct d2; try lia.
rewrite {3}/cholesky_jik_iloop -/cholesky_jik_iloop.
if_lia false.
if_lia false.
if_lia true.
case: (@eqP _ i d2) => Hid2'; [ subst i | ].

simpl.

if_lia false.
f_equal. f_equal. auto. f_equal. admit.
f_equal.
apply IHn.

simpl.
 apply IHn.




Lemma cloop_eqv1:
 forall (n n1 n2 d1 d2: nat) (A1 A2: nat -> nat -> F),
   (n <= n1)%coq_nat -> (n <= n2)%coq_nat ->
   (n <= d1)%coq_nat -> (d1 <= d2)%coq_nat ->
   (forall i j, i<n -> j<n -> A1 i j = A2 i j)%coq_nat ->
   (forall i j, i<n -> j<n -> 
      cholesky_jik_iloop n1 A1 d1 i j = cholesky_jik_iloop n2 A2 d2 i j)%coq_nat.
Proof.
intros ? ? ? d1 d2.
revert d2 n n1 n2.
induction d1; destruct d2; intros; simpl; auto; try lia.
have -> :(n1<j)%N=false by lia.
have -> :(n2<j)%N=false by lia.
case: (@eqP _ j d1) => Hjd1; [ subst d1 | ];
 (case: (@eqP _ j d2) => Hjd2; [ subst d2 | ]);
 (case: (@ltP i j) => Hij); try lia.
-
 f_equal; [f_equal | ].
 + apply H3; auto. 
 + f_equal. admit.
 + f_equal. destruct n as [|n]; [lia|]. apply IHd1 with n; try lia.
    intros; apply H3; lia.
- case: (@eqP _ i j) => Hij'; auto.
  subst j. f_equal. f_equal. apply H3; auto. f_equal.
  admit.
- assert (j.+1=n) by lia. subst n. assert (j<d2)%N by lia. 
  clear H5 H4 Hjd2 H2 H1. rename j into d1.
  (* Likely provable by induction on (d2-d1).  One step would look like: *)
  destruct d2. lia. simpl.
  have ->:(n2<d1)%N=false by lia.
  case: (@eqP _ d1 d2) => Hd12.
  + subst d2.
   have ->:(i<d1)%N=true by lia.
   f_equal. f_equal. apply H3; auto. f_equal.
   admit.
   f_equal. apply IHd1 with (n:=d1); try lia. intros; apply H3; lia.
  + admit.  (* see "Likely provable" above *)
- 
  case: (@eqP _ i j) => Hij'; try lia.
  subst j.
  have Hni: (n= S i)%coq_nat by lia. subst n. clear H5 H1.
  (* Likely provable by induction on (d2-d1).  One step would look like: *)
  destruct d2. lia. simpl.
  have ->:(n2<i)%N=false by lia.
  case: (@eqP _ i d2) => Hd12.
  + subst d2.
   have ->:(i<i)%N=false by lia.
   have ->:(i==i)%N=true by lia.
   f_equal. f_equal. auto. f_equal. admit.
  + admit.  (* see "Likely provable" above *)
-
  destruct n. lia. 
  apply IHd1 with n; auto; try lia.
Abort.

(** This lemma is very possibly true, but I am not at all sure
  that this is the right induction to prove it.  -- Andrew *)
Lemma cholesky_jik_correct:
  forall n (A: 'M[F]_n.+1),
    Mij (cholesky A) =2 cholesky_jik_iloop n (Mij A) n.+1.
Proof.
move => n A i j. rewrite {1}/Mij.
case: insubP => [ /= i' Hin Hi'| Hi /= ].
2:{case: (@ltP n j) => // Hj.
   case: (@eqP _ j n) => // Hjn. subst j. have -> :(i<n)%N=false by lia. 
   have -> :(i==n)=false by lia. auto.
   have Hn: (n>j)%coq_nat by lia. clear Hj Hjn.
   have Hin: (i>=n)%coq_nat by lia. clear Hi.
   move :n A i j Hn Hin; elim => [A i j Hn Hin| n IH A i j Hn Hin]; first lia.
   simpl. have -> :(n.+1<j)%N=false by lia.
   case: (@eqP _ j n) => Hjn.
   subst j. have -> :(i<n)%N=false by lia. have -> :(i==n)=false by lia. auto.
   specialize (IH (ulsubmx (castmx (add_two,add_two) A)) i j).
   symmetry; apply cloop_i_ge_d. lia.
}
case: insubP => [j' Hj Hj' | Hj ].
2: (have -> :(n<j)%N=true by lia); auto.
simpl in Hj', j'.
have -> :(n<j)%N=false by lia.
destruct i' as [i'' Oi], j' as [j'' Oj]. simpl in Hi',  Hj'. subst j'' i''.
clear Hin Hj.
revert i j Oi Oj; induction n;intros.
-
assert (i=0) by lia; subst i.
assert (j=0) by lia; subst j.
simpl.
unfold Mij.
rewrite insubT.
unfold Sub.
simpl.
rewrite subr0 mxE.
f_equal. f_equal.
f_equal.
apply proof_irr.
-
rewrite castmxE.
rewrite esymK.
case: (split_ordP (cast_ord add_two (Ordinal Oj))) => [j'' Hj'' | j'' Hj''].
+
destruct j'' as [j' Hj'].
inversion Hj''.
subst j'.
have -> :(j==n.+1)=false by lia.
rewrite /cholesky -/cholesky.
rewrite /cholesky_jik_iloop -/cholesky_jik_iloop.
have -> :(n.+1< j)%N=false by lia.
case: (@eqP _ j n) => // Hjn. 
*
subst j. rewrite Hj''.
case: (split_ordP (cast_ord add_two (Ordinal Oi))) => [i'' Hi'' | i'' Hi''].
--
destruct i'' as [i' Hi']. inversion Hi''. subst i'.
rewrite Hi''.  
rewrite block_mxEul.
rewrite (IHn (ulsubmx (castmx (add_two, add_two) A)) i n Hi' Hj').
clear IHn.
have -> :(n==n)=true by lia.
case: (@ltP i n) => Hin.
++
admit. (* plausible *)
++
have -> : (i==n) by lia.
f_equal.
admit. (* plausible *)
--
rewrite Hi''.
rewrite block_mxEdl.
inversion Hi''.
rewrite ord1 in H0 *. simpl in H0. assert (i=n.+1) by lia. subst i.
simpl.
have -> :(n.+1+0<n)%N=false by lia.
have -> :(n.+1+0==n)%N=false by lia.
rewrite mxE.
auto.
*
rewrite Hj''.
case: (split_ordP (cast_ord add_two (Ordinal Oi))) => [i'' Hi'' | i'' Hi''].
--
destruct i'' as [i' Hi']. inversion Hi''. subst i'.
rewrite Hi''.
rewrite block_mxEul.
rewrite (IHn (ulsubmx (castmx (add_two, add_two) A)) i j Hi' Hj').
have -> :(j==n)=false by lia.
admit. (* plausible *)
--
rewrite ord1 in Hi'' *. clear i''.
rewrite Hi''.
rewrite block_mxEdl.
clear IHn.
rewrite mxE.
inversion Hi''.
subst i.
admit. (* perhaps *)
+
rewrite ord1 in Hj'' *. clear j''.
inversion Hj''. rewrite Hj''.
have Hj: j=n.+1 by lia. subst j. clear Hj.
have -> : (n.+1+0 == n.+1)%N=true by lia.
case: (split_ordP (cast_ord add_two (Ordinal Oi))) => [i'' Hi'' | i'' Hi''].
*
rewrite -/cholesky.
destruct i'' as [i' Hi']. inversion Hi''. subst i'.
rewrite Hi''.
rewrite block_mxEur.
have -> :(i<n.+1+0)%N=true by lia.
rewrite (_: (n.+1+0)%N=n.+1); last by lia.
set R' := cholesky_jik_iloop n.+1 (Mij A) n.+1.
clear Oj Hj'' Oi Hi''.
set A1 := ulsubmx (castmx (add_two, add_two) A).
have Oj : is_true (0 < n.+1)%N by lia.
specialize (IHn A1 (*i 0 Hi' Oj*)).
set c := ursubmx (castmx (add_two, add_two) A).
(*rewrite (_: (i<0)%N=false) in IHn; last by lia.*)
set R := (cholesky A1) in IHn *.
set R'' := cholesky_jik_iloop n (Mij A1) n in IHn.




rewrite /solve_LT. cbv beta.
unfold solve_LT.
simpl in R'.
case: (@eqP _ 0 n) => H0n; auto.
--

have UT := cholesky_upper_triangular A1.
have Unit :  is_true ((cholesky A1)^T \in unitmx) by admit.
have SLT := solve_LT_correct c UT Unit.
set r := solve_LT _ _ in SLT *. clearbody r.
rewrite /c in SLT. clear c.
clearbody R.



subst c.


Search cholesky.


have -> :(n.+1<i)%N=false by lia.
have -> :(i<i)%N=false by lia.
have -> :(i==i)=true by lia.



Search (_ + 0 = _)%coq_nat.
rewrite PeanoNat.Nat.add_0_r in H0.
Search (_ + 0)%N.

simpl.



rewrite ord

simpl.

case (@eqP _ i n).

Search (Mij _ _ _ = Mij _ _ _).
f_equal.
f_equal.

Search Mij.
unfold Mij.
--


have -> :(i<n)%N=false by lia. 



 lia. subst j''.

Search lshift.
assert (j < n.+1)%N by lia.
Search cast_ord lshift.
simpl in Hj''.
Search block_mx lshift.
case: (@eqP _ j n.+1) => Hjn.
+
case: (@ltP i j) => Hij.
Search rshift.
Search cast_ord rshift.

Qed.
reflexivity.
Search map_mx.
rewrite mxE.
Search (_ - 0 = _).
rewrite sub_0_r.
lia.
simpl.

Search insub.
simpl.
Search (insub 0).

 simpl.
have -> :(j==0%N)=true by lia.
have -> :(i==0%N)=true by lia.

simpl.
         rewrite /cholesky_jik_iloop -/cholesky_jik_iloop.

Check ord_of_nat.
Search nat_of.
Search fun_of_matrix Mij.

subst j.

set (R := cholesky_jik_iloop n (Mij A) n).






   done.

elim => [ | n Hn] A i j.
-
rewrite {1}/Mij. simpl.
case: insubP => [ /= i'| Hi /= ].
 + rewrite ord1 /= => Hi Hi'. subst i. clear i' Hi.
   case: insubP => [j' Hj Hj' | Hj ].
   * subst j. clear Hj. rewrite ord1 {j'}.
     rewrite /= mxE subr0 /Mij insubT ord1 //.
   * by have -> : (0<j)%N by lia.
 + case: (@ltP 0 j) => // Hj.
   have -> :(j=0) by lia. rewrite eqxx.
   have -> :(i<0)%N=false  by lia.
   have -> :(i==0)=false by lia.
   done.
- rewrite {1}/Mij.
  set A1 := ulsubmx (castmx (add_two,add_two) A).
  specialize (Hn A1).
  case: insubP => [i' _ Hi | Hi]. 
  + simpl in i'. simpl in Hi. subst i.
    case: insubP => [ j' _ Hj | Hj ].
    * simpl in j'. simpl in Hj. subst j.
      rewrite /cholesky -/cholesky.
      rewrite castmxE esymK.
      rewrite -/A1.
      set i := cast_ord add_two i'.
      set j := cast_ord add_two j'.
      change (nat_of_ord i') with (nat_of_ord i).
      change (nat_of_ord j') with (nat_of_ord j).
      case: (split_ordP j) => [j'' Hj'' | j'' Hj'']; subst j.
      --
       subst i. rewrite Hj''. rewrite block_mxEh row_mxEl.
       case: (split_ordP (cast_ord add_two i')) => [i'' Hi'' | i'' Hi''];
       rewrite Hi''.
       ++ rewrite col_mxEu.
         match type of Hn with ?X =2 ?Y => 
           have Hn': X i'' j'' = Y i'' j'' by done end.
         rewrite {Hn}. rewrite {1}/Mij in Hn'.
         clear Hi'' Hj'' j' i'.
         move : Hn'.
         rewrite !insub_nat_of_ord.
         move => H; rewrite {}H.
       have cholesky_jik_iloop_lemma1:
         forall n A i j, (j<n.+1)%coq_nat ->
          cholesky_jik_iloop n (@Mij n (ulsubmx (castmx (add_two, add_two) A))) n.+1 i j = 
          cholesky_jik_iloop n.+1 (@Mij n.+1 A) n.+2 i j.
           clear. admit.
         apply cholesky_jik_iloop_lemma1.
         rewrite /lshift. simpl.
         pose proof (@ltn_ord _ j''); lia.  (* why doesn't "have" work? *)
       ++ rewrite col_mxEd.
         match type of Hn with ?X =2 ?Y => 
           have Hn': X i'' j'' = Y i'' j'' by done end.
         rewrite {Hn}. rewrite {1}/Mij in Hn'.
         clear Hi'' Hj'' j' i'.
         move : Hn'.
         rewrite !insub_nat_of_ord.
         rewrite ord1. clear i''. simpl nat_of_ord.
         rewrite insubT. unfold Sub. simpl isSub.Sub.
         have -> : @Ordinal n.+1 0 is_true_true  = GRing.zero.
         compute. f_equal. apply proof_irr.
         rewrite addn0.
         rewrite mxE => H.
         move :j'' => j in H *.
         rewrite /cholesky_jik_iloop -/cholesky_jik_iloop.
         rewrite (_ : (n.+1 <j)%N=false); last by (move :(leq_ord j); lia).
         rewrite (_ : (_ == _)=false); last by (move :(leq_ord j); lia).
         rewrite (_ : (_ == nat_of_ord j)=false); last by (move :(leq_ord j); lia).
         destruct (nat_of_ord j == n) eqn:H1; auto.
         have H2: (j<n)%N by move:(leq_ord j); lia.
         clear - H2.
         move :(Mij A) => B. clear A.
         set j' := nat_of_ord j in H2 *. clearbody j'. clear j.
         set k := (n.+1).
         have Hk: (n<k)%N by lia.
         move :j' H2 k Hk.
         elim n => j H2 k Hk.
         lia.
         move => j' H1 /=.
         rewrite (_: (_<_)%N = false); last by lia.
         destruct (k==j) eqn:H3.
         ** rewrite (_: (_==_)=false); last by lia. auto.
         ** apply H2. lia. lia.
     -- 
         rewrite /cholesky_jik_iloop -/cholesky_jik_iloop.
         simpl nat_of_ord.
         rewrite (_: (n.+1<nat_of_ord j')%N=false); last by (pose proof (leq_ord j'); lia).
         rewrite (_: (nat_of_ord i'< nat_of_ord i')%N = false); last by lia.
         set R := cholesky_jik_iloop n.+1 (Mij A) n.
         
         Search nat_of_ord cast_ord.
         
         

         Search ('I_ _) leq.
Abort.

End Cholesky_jik.

