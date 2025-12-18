(**  * LAProof.C.verif_densemat_mult: VST proofs dense matrix multiply functions *)
(** ** Corresponds to C program [densemat.c] *)

(** * Prologue. 

 For explanation see the prologue of [LAProof.C.spec_densemat] *)
From VST.floyd Require Import proofauto VSU.
From LAProof.accuracy_proofs Require Import solve_model.
From LAProof.C Require Import densemat spec_alloc spec_densemat floatlib matrix_model.
From vcfloat Require Import FPStdCompCert FPStdLib.
Require Import VSTlib.spec_math VSTlib.spec_malloc.
Require Import Coq.Classes.RelationClasses.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
Import fintype matrix mv_mathcomp dotprod_model.

Require Import LAProof.C.densemat_lemmas.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Local Definition upto_row_col {T} [m n] (A: 'M[T]_(m,n)) (i j: nat) : 'M[option T]_(m,n) :=
 \matrix_(i',j')
  if Nat.ltb i' i then Some (A i' j')
  else if Nat.ltb i i' then None
  else if Nat.ltb j' j then Some (A i' j')
  else None.

Local Ltac case_ltb := match goal with |- context [Nat.ltb ?a ?b] =>
    destruct (Nat.ltb_spec a b); try lia
 end.

Lemma body_densematn_mult: semax_body Vprog Gprog f_densematn_mult densematn_mult_spec.
Proof.
start_function.
assert_PROP (m <= Int.max_signed /\ n <= Int.max_signed /\ p <= Int.max_signed) by entailer!.
destruct H as [Hm [Hn Hp]].
forward_for_simple_bound (Z.of_nat m) 
  (EX i:Z, 
    PROP ( )
    LOCAL (temp _m (Vint (Int.repr (Z.of_nat m))); temp _n (Vint (Int.repr (Z.of_nat n)));
    temp _p (Vint (Int.repr (Z.of_nat p))); temp _x pA; temp _y pB; 
    temp _z pC)
    SEP (densematn shA (map_mx Some A) pA; densematn shB (map_mx Some B) pB;
              densematn shC (upto_row_col (F.mulmx A B) (Z.to_nat i) O) pC))%assert.
- entailer!!. unfold upto_row_col.
  apply derives_refl'; f_equal. apply matrixP. intros i' j'. unfold const_mx. rewrite !mxE.
  simpl.
  destruct (Nat.ltb _ _); auto.
- forward_for_simple_bound (Z.of_nat p) 
  (EX j:Z, 
    PROP ( )
    LOCAL (temp _i (Vint (Int.repr i)); temp _m (Vint (Int.repr (Z.of_nat m))); temp _n (Vint (Int.repr (Z.of_nat n)));
    temp _p (Vint (Int.repr (Z.of_nat p))); temp _x pA; temp _y pB; 
    temp _z pC)
    SEP (densematn shA (map_mx Some A) pA; densematn shB (map_mx Some B) pB;
              densematn shC (upto_row_col (F.mulmx A B) (Z.to_nat i) (Z.to_nat j)) pC))%assert.
+ entailer!!. apply derives_refl.
+ rename i0 into j. ordify m i. ordify p j.
   pose (X := existT _ m (existT _ n (existT _ p ((A,B),(i,j)))) :
        {m & {n & {p & ('M[ftype the_type]_(m,n) * 'M[ftype the_type]_(n,p)) * ('I_m * 'I_p)}}}%type).
   forward_call (shA, shB, X, pA, pB); clear X.
  set (C := upto_row_col _ _ _).
  set (z := spec_densemat.F.dotprod _ _).
  forward_densematn_set C i j pC shC z.
  entailer!!.
  apply derives_refl'; f_equal.
  subst C. unfold update_mx, upto_row_col.
  apply matrixP; intros i' j'.
  rewrite !mxE.
  simpl in *.
  rewrite !Nat2Z.id.
  destruct (Nat.eq_dec i' i).
 *
  assert (i'=i) by (apply ord_inj; auto). subst i'. simpl. clear e.
  destruct (Nat.eq_dec j' j).
  -- assert (j'=j) by (apply ord_inj; auto); subst j'; simpl; clear e.
    rewrite Nat.ltb_irrefl.
    destruct (Nat.ltb_spec (nat_of_ord j) (Z.to_nat (Z.add (Z.of_nat j) 1%Z))); [ | lia].
    f_equal. subst z.
    unfold F.mulmx; rewrite !mxE. reflexivity.
  -- simpl.
     rewrite Nat.ltb_irrefl.
     repeat case_ltb; auto.
 * simpl.
     repeat case_ltb; auto.
+ entailer!!.
   ordify m i.
   apply derives_refl'; f_equal.
   unfold upto_row_col.
   apply matrixP; intros i' j'; rewrite !mxE.
   rewrite !Nat2Z.id.
   repeat case_ltb; auto.
   pose proof (ltn_ord j'); lia.
- entailer!!.
   apply derives_refl'; f_equal.
   unfold upto_row_col, map_mx.
   apply matrixP; intros i' j'; rewrite !mxE.
   pose proof (ltn_ord i').
   rewrite !Nat2Z.id.
   repeat case_ltb; auto.
Qed.

Lemma body_densemat_mult: semax_body Vprog Gprog f_densemat_mult densemat_mult_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*.
Intros. 
forward.
forward.
forward.
pose (X := existT _ m (existT _ n (existT _ p (A,B))) :
            {m & {n & {p & 'M[ftype the_type]_(m,n) * 'M[ftype the_type]_(n,p)}}}%type).
forward_call (shA,shB,shC,X, 
                      offset_val densemat_data_offset pA, offset_val densemat_data_offset pB, offset_val densemat_data_offset pC).
entailer!!.
Qed.

Lemma body_densematn_dotprod: semax_body Vprog Gprog f_densematn_dotprod densematn_dotprod_spec.
Proof.
start_function.
forward.
assert_PROP (m <= Int.max_signed /\ n <= Int.max_signed /\ p <= Int.max_signed) by entailer!.
destruct H as [Hm [Hn Hp]].
pose (x := row i A).
pose (y := col j B).
forward_for_simple_bound (Z.of_nat n)
  (EX k:Z,  
    PROP ( )
    LOCAL (temp _s (Vfloat (dotprodF (seq.take (Z.to_nat k) (seq_of_rV x)) (seq.take (Z.to_nat k) (seq_of_rV (trmx y)))));
                  temp _m (Vint (Int.repr m));
                  temp _n (Vint (Int.repr n)); temp _p (Vint (Int.repr p)); temp _i (Vint (Int.repr i));
                  temp _j (Vint (Int.repr j)); temp _x pA; temp _y pB)
    SEP (densematn shA (map_mx Some A) pA; densematn shB (map_mx Some B) pB))%assert.
-
entailer!!. simpl. rewrite !seq.take0. reflexivity.
-
rename i0 into k.
ordify n  k.
forward_densematn_get (map_mx Some A) i k pA shA (A i k).
     unfold map_mx; rewrite mxE; auto.
forward_densematn_get (map_mx Some B) k j pB shB (B k j).
     unfold map_mx; rewrite mxE; auto.
forward.
entailer!!.
f_equal.
unfold dotprodF, dotprod.
replace (Z.to_nat (k+1)) with (S (Z.to_nat k)) by lia.
assert (d: ftype the_type) by apply common.pos_zero.
rewrite !(take_snoc d) by (rewrite size_seq_of_rV; lia).
rewrite seq.zip_cat by (rewrite !seq.size_take_min, !size_seq_of_rV; auto).
simpl.
rewrite seq.map_cat.
rewrite seq.foldl_cat.
simpl.
set (u := seq.foldl _ _ _). clearbody u.
unfold Basics.flip at 1.
change Float.add with (@BPLUS _ the_type).
f_equal.
rewrite Nat2Z.id.
rewrite !nth_seq_of_rV.
unfold trmx, x, y, row, col. rewrite !mxE.
reflexivity.
-
forward.
entailer!!.
f_equal.
rewrite Nat2Z.id.
rewrite !seq.take_oversize by (rewrite size_seq_of_rV; lia).
symmetry.
apply F.dotprod_dotprodF.
Qed.

Lemma body_densemat_dotprod: semax_body Vprog Gprog f_densemat_dotprod densemat_dotprod_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*.
Intros. 
forward.
forward.
forward.
pose (X := existT _ m (existT _ n (existT _ p ((A,B), (i,j)))) :
            {m & {n & {p & ('M[ftype the_type]_(m,n) * 'M[ftype the_type]_(n,p)) * ('I_m * 'I_p)}}}%type).
forward_call (shA,shB,X, offset_val densemat_data_offset pA, offset_val densemat_data_offset pB).
forward.
cancel.
Qed.

