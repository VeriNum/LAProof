(** * LAProof.accuracy_proofs.solve_model: models of Cholesky decomposition and triangular solve *)

From LAProof.accuracy_proofs Require Import preamble common float_acc_lems.
Require Import vcfloat.FPStdLib.
Require Import vcfloat.FPStdCompCert.



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
