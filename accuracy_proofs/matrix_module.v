From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval mathcomp_extra.
From mathcomp Require Import ereal reals signed topology prodnormedzmodule. 
From mathcomp Require Import normedtype sequences mxalgebra Rstruct.

Import Order.Theory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.
Import numFieldNormedType.Exports.
Import normedtype.NbhsNorm.

Import topology.numFieldTopology.Exports.
Import CompleteNormedModule.Exports.


Local Open Scope ring_scope.


Section Examples.

Variables (R: realType) (m n : nat).
(* test examples of sharing using norm properties from ssrnum*)

Lemma chasd  (A: 'M[R]_m.+1)  (u : 'cV_m.+1) :
\big[maxr/0]_ij `|(A *m u) ij.1 ij.2| / \big[maxr/0]_ij `|u ij.1 ij.2| <= 
\big[maxr/0]_ij  (`|(A *m u) ij.1 ij.2| / `|u ij.1 ij.2|)
.
Proof. Admitted.

Lemma subMultNorm (A: 'M[R]_m.+1) (u : 'cV_m.+1) : 
  `| A *m u | <= `|A| * `|u|.
Proof.
rewrite /normr /= !mx_normE.
rewrite -ler_pdivr_mulr.
eapply le_trans.
2: apply bigmax_geP.
apply chasd. 2: admit.  
apply bigmax_le. admit.
intros.
rewrite ler_pdivr_mulr.
rewrite mxE.
eapply le_trans.
apply checks.
rewrite -ler_pdivr_mulr.
assert (
(\sum_j `|A i.1 j * u j i.2|) / `|u i.1 i.2| <= (\sum_j `|A i.1 j * u j i.2 / u i.1 i.2|)
). admit.
eapply le_trans.
apply H0.
Admitted.


Example matrix_triangle  (M N : 'M[R]_(m.+1, n.+1)) :
  `|M + N| <= `|M| + `|N|.
Proof.  apply ler_norm_add. Qed.

Example matrix_norm_positive (A : 'M[R]_(m.+1, n.+1)) : 
        0 <= `|A|.
Proof. apply normr_ge0. Qed.

End Examples.

Section Inverse.

Variables (R: realType) (m n : nat).

Lemma eqmx_mulr (b a1 a2: 'M[R]_m.+1) :
        a1 = a2 -> a1 * b = a2 * b. 
Proof.
by move => H; rewrite H.
Qed.

Lemma mulr_eqmx : forall  (b a1 a2: 'M[R]_m.+1) ,
        b \is a GRing.unit -> a1 *m b = a2 *m b -> a1 = a2. 
Proof.
move => b a1 a2  H1 H2. 
have : a1 * b * b^-1 = a2 * b * b^-1 by apply eqmx_mulr; apply H2.
rewrite -!mulrA mulrV // !mulr1 //. 
Qed.

Lemma invmx_mul (A B: 'M[R]_m.+1) :
        A \in unitmx -> B \in unitmx ->
        invmx (A *m B) = invmx B *m invmx A.
Proof.
move => H1 H2.
have H3: A *m B \in unitmx by (rewrite unitmx_mul; apply/andP => //=).
have H4: invmx (A *m B) * (A *m B) = invmx B *m invmx A * (A *m B).
 rewrite -mulmxE (mulVmx H3) mulmxE mulrA -mulmxE.
 rewrite -!mulmxA [invmx A *m (A *m B)]mulmxA (mulVmx H1) mul1mx (mulVmx H2) //.
apply (mulr_eqmx _ _ _ H3 H4).
Qed.

Lemma invmx_pert (A E: 'M[R]_m.+1) :
        A \in unitmx -> 1 + invmx A * E \in unitmx ->
        invmx (A + E) = invmx (1 + invmx A * E) * invmx A.
Proof.
move => H1 H2.
have H3: invmx (A + E) = invmx (A * (1 + invmx A * E)).
rewrite mulrDr mulrA mulr1 -mulmxE (mulmxV H1) mul1mx //.
rewrite H3 (invmx_mul _ _ H1) //.
Qed.

End Inverse.


Section MatrixFacts.

Variables (m n : nat) (R: realType).

Variable g : {linear 'rV[R]_m.+1 -> 'rV[R]_n.+1}.

Lemma trmxeq (m' n' : nat) (A B : 'M[R]_(m',n')) : A = B -> A^T = B^T.
Proof. by move => H; rewrite H. Qed.

Lemma trmx_mul_rV_lin1 u : (u *m lin1_mx g)^T = (g u)^T.
Proof. by apply trmxeq; apply mul_rV_lin1. Qed.

Lemma trmxZ a (A : 'M[R]_n) : (a *: A)^T = a *: (A^T).
Proof.  by apply/matrixP =>  k i /[!mxE]. Qed.

End MatrixFacts. 


Section Maps.

(** Notes: 
 contractive maps are defined in sequences *)
Variables (m n : nat) (R: realType).
Variables (Sv : set 'cV[R]_(m.+1)).


Definition f_app (f : 'rV[R]_m -> 'rV[R]_m)
        (u: 'rV[R]_m)  := fun n => iter n f u.

Goal forall (f : 'rV[R]_m -> 'rV[R]_m) (u: 'rV[R]_m) ,
       f_app f u 1 = f u.
rewrite/f_app/iter //. Qed.

Goal forall (f : 'rV[R]_m -> 'rV[R]_m) (u: 'rV[R]_m) ,
       f_app f u 0 =  u.
rewrite/f_app/iter //. Qed.

Canonical mat_R_CompleteNormedModule (m' n' : nat) :=
  [completeNormedModType R of (matrix R m'.+1 n'.+1)].

Lemma Banach_test : forall (f' : {fun Sv >-> Sv}) ,
  is_contraction f' -> closed Sv -> (Sv !=set0)%classic ->
        exists2 x:'cV_m.+1, Sv x & x = f' x .
Proof.
move => f' A B C; apply banach_fixed_point => //.
Qed.

Definition lin2_mx {m' n' : nat} (f: 'cV[R]_n'.+1 -> 'cV[R]_m'.+1) : 
  'M[R]_(m'.+1, n'.+1) := \matrix[lin1_mx_key]_(j, i) f (delta_mx i 0) j 0.

Variable f : {linear 'cV[R]_n.+1 -> 'cV[R]_m.+1}.
Variable g : {linear 'rV[R]_m.+1 -> 'rV[R]_n.+1}.

Lemma mul_cV_lin2 (u : 'cV_n.+1): 
   lin2_mx f *m u = f u.
Proof.
by rewrite {2}[u]matrix_sum_delta linear_sum; apply/colP=> i;
rewrite mxE summxE; apply eq_bigr => j _; rewrite big_ord1 linearZ !mxE mulrC.
Qed.

Variable fs : {fun Sv >-> Sv}.
Axiom linear_fs : linear fs.

Canonical fs' := Linear linear_fs.

Lemma Banach_tests :
  is_contraction fs' -> closed Sv -> (Sv !=set0)%classic ->
        exists2 x:'cV_m.+1, Sv x & x = fs' x .
Proof.
move => A B C; apply banach_fixed_point => //.
Qed.


Lemma mul_cV_lin2'  (u : 'cV_m.+1): 
   lin2_mx fs *m u = fs' u.
Proof.
by rewrite {2}[u]matrix_sum_delta linear_sum; apply/colP=> i;
rewrite mxE summxE; apply eq_bigr => j _; rewrite big_ord1 linearZ !mxE mulrC.
Qed.

(* Search normr matrix_normedZmodType *)

Lemma linear_exists (m' n' : nat) (A: 'M[R]_(m'.+1,n'.+1)) : 
  exists f, forall u : 'cV_(n'.+1) , f u = A *m u /\ linear f.
Proof. 
Admitted.

Lemma subMultNorm (A: 'M[R]_m.+1) (u : 'cV_m.+1) : 
  `| A *m u | <= `|A| * `|u|.
Proof.
rewrite /normr /= !mx_normE.
Search normr.
Search BigOp.bigop normr.
Admitted.

Lemma mx_norm_is_klipschitz : 
  forall (k : R) (HBND: `|lin2_mx fs| <= k),   k.-lipschitz_Sv fs.
Proof.
move => k HBND. 
rewrite/dominated_by/globally /= => x Hx.
rewrite -linearB // .
rewrite -mul_cV_lin2'.
eapply le_trans => [ | ].
apply subMultNorm =>  //.
Admitted.

Lemma norm_lt_contraction: 
  `|lin2_mx fs| < 1 -> is_contraction fs.
Proof.
move => H.
exists `|lin2_mx fs|%:nng => // (* see signed.v; x%:nng explicitly casts x to {nonneg R} *).
unfold contraction; simpl.
split => [//|].
apply mx_norm_is_klipschitz => //.
Qed.


(* definition of the matrix condition number *)
Definition kappa (A : 'M[R]_m.+1) := `|(invmx A)| * `|A|.

Lemma Neumann_bound' (A : 'M[R]_m.+1):
        (1 - A) * \sum_(0 <= i < n.+1) A^i.
Proof.

Lemma Neumann_bound (F : 'M[R]_m.+1):
        `|invmx(1 - F)| <=  \sum_(0 <= i < n.+1) `|F|^i.
Proof.
unfold norm.



