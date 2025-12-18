(**  * LAProof.C.verif_densemat_cholesky: VST proofs of Cholesky functions on dense matrices. *)
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
Import fintype matrix.

Require Import LAProof.C.densemat_lemmas.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

(** * [densemat_cfactor] verification: Cholesky factorization *)

Definition cholesky_return' [n] (j: 'I_(S n)) (R: 'M[ftype the_type]_n) : ftype the_type := 
   seq.foldl BMULT (Zconst the_type 1) (map (fun k => fst (BFREXP (R k k))) (seq.take j (ord_enum n))).

Lemma cholesky_return'_e: forall n (R: 'M_n) (n': 'I_(S n)), 
     n = nat_of_ord n' -> cholesky_return' n' R = cholesky_return R.
Proof.
intros.
unfold cholesky_return', cholesky_return.
replace (nat_of_ord n') with (seq.size (ord_enum n)).
 2: rewrite size_ord_enum, <- H; auto.
rewrite seq.take_size.
clear n' H.
set (u := Zconst _ _). clearbody u.
revert u; induction (ord_enum n); simpl; intros; auto.
Qed.

Lemma body_densematn_cfactor: semax_body Vprog Gprog f_densematn_cfactor densematn_cfactor_spec.
Proof.
start_function.
subst MORE_COMMANDS; unfold abbreviate; canonicalize_float_constants.
rename X into M.
assert_PROP (0< n <= Int.max_signed) by entailer!.
pose (A := map_mx optfloat_to_float (mirror_UT M)).
assert (Datatypes.is_true (ssrnat.leq 1 n)) by lia.
pose (zero := @Ordinal n 0 H1).
forward.
forward_for_simple_bound (Z.of_nat n) 
  (EX j':Z, EX j: 'I_(S n), EX R: 'M[ftype the_type]_n,
      PROP(j'=j; cholesky_jik_upto zero j A R)
      LOCAL(temp _n (Vint (Int.repr n)); lvar _scratch tint v_scratch; temp _A p;
                   temp _err (Vfloat (cholesky_return' j R)))
      SEP(data_at_ Tsh tint v_scratch; densematn sh (joinLU M (map_mx Some R)) p))%assert.
- Exists (lshift1 zero) A.
  entailer!!; [ split | ].
 +  apply cholesky_jik_upto_zero; auto.
 + unfold cholesky_return'. simpl. rewrite seq.take0. simpl.
    f_equal. apply B754_finite_ext.
 +
  apply derives_refl'; f_equal.
  subst A.
  clear - H.
  apply matrixP.
  intros i j. unfold joinLU. rewrite mxE.
  destruct (ssrnat.leq _ _) eqn:?H; auto.
  unfold map_mx. rewrite !mxE.
  specialize (H i j).
  unfold mirror_UT, joinLU in *.
  rewrite mxE in *. rewrite H0 in *. destruct (M i j); try contradiction. auto.  
-
rename i into j'.
Intros. subst j'.
forward_for_simple_bound (Z.of_nat j) 
  (EX i':Z, EX i: 'I_n, EX R: 'M[ftype the_type]_n,
      PROP(i' = Z.of_nat i; cholesky_jik_upto i j A R)
      LOCAL(temp _j (Vint (Int.repr j)); temp _n (Vint (Int.repr n)); lvar _scratch tint v_scratch;  temp _A p; 
                    temp _err (Vfloat (cholesky_return' j R)))
      SEP(data_at_ Tsh tint v_scratch; densematn sh (joinLU M (map_mx Some R)) p))%assert.
 + Exists (@Ordinal n O ltac:(clear - H2; lia)) R.
   entailer!!.
 + clear H4 R.  rename R0 into R.
   Intros. subst i. rename i0 into i.
   assert (Datatypes.is_true (ssrnat.leq (S j) n)) by lia.
   pose (j' := @Ordinal n _ H4).
   assert (j = lshift1 j'). apply ord_inj. simpl. auto.
   rewrite H6 in *. clearbody j'. subst j. rename j' into j. simpl in H3.
  forward_densematn_get (joinLU M (map_mx Some R)) i j p sh (R i j).
   unfold joinLU, map_mx. rewrite !mxE. replace (ssrnat.leq _ _) with true by lia. auto.
   forward_for_simple_bound (Z.of_nat i)
     (EX k':Z, EX k:'I_n,
      PROP(k'=Z.of_nat k; cholesky_jik_upto i (lshift1 j) A R)
      LOCAL(temp _s (val_of_float (subtract_loop_jik (A i j) R i j k) );
            temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)); 
            temp _n (Vint (Int.repr n));  lvar _scratch tint v_scratch; temp _A p;
                    temp _err (Vfloat (cholesky_return' (lshift1 j) R)))
      SEP(data_at_ Tsh tint v_scratch; densematn sh (joinLU M (map_mx Some R)) p))%assert.
    pose proof (ltn_ord i); lia.
  * Exists zero. entailer!!. f_equal. unfold subtract_loop_jik. simpl. rewrite seq.take0.
    destruct (H5 i j) as [_ [_ [_ H8]]]. rewrite H8; auto.
  * Intros. subst i0.
    assert (Hi := ltn_ord i).
    forward_densematn_get  (joinLU M (map_mx Some R)) k i p sh (R k i).
    unfold joinLU, map_mx. rewrite !mxE. simpl. replace (ssrnat.leq _ _) with true by lia. auto.
    forward_densematn_get  (joinLU M (map_mx Some R)) k j p sh (R k j).
    unfold joinLU, map_mx. rewrite !mxE. simpl. replace (ssrnat.leq _ _) with true by lia. auto.
    forward.
    assert (Datatypes.is_true (ssrnat.leq (S (S k)) n)) by lia.
    pose (Sk := @Ordinal n _ H7).
    Exists Sk. 
    change (Vfloat
            (Float.sub (subtract_loop_jik (A i j) R i j k)
               (Float.mul (R k i) (R k j))))
    with (val_of_float (BMINUS (subtract_loop_jik (A i j) R i j k) (BMULT (R k i) (R k j)))).
    entailer!!. split. simpl; lia.
     f_equal.
     unfold subtract_loop_jik, subtract_loop.
     simpl nat_of_ord. rewrite (take_snoc k) by (rewrite size_ord_enum; lia). 
     rewrite !seq.map_cat, seq.foldl_cat.
     simpl. rewrite !nth_ord_enum'.  reflexivity.
    *
    Intros k'.
    assert (i=k')%nat by (apply ord_inj; lia). subst k'.
    forward_densematn_get  (joinLU M (map_mx Some R)) i i p sh (R i i).
    unfold joinLU, map_mx. rewrite !mxE. simpl. replace (ssrnat.leq _ _) with true by lia. auto.
    pose (X := existT _ (n,n) (joinLU M (map_mx Some R),(i,j)) 
          : {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
    forward_call (X,p,sh, BDIV (subtract_loop_jik (A i j) R i j i) (R i i)); clear X.
    set (rij := BDIV _ _).
    assert (Datatypes.is_true (ssrnat.leq (S (S i)) n)) by (pose proof ltn_ord j; lia).
    pose (i1 := @Ordinal n _ H7).
    Exists i1 (update_mx R i j rij).
    entailer!!. split3. subst i1. simpl.  lia.
    apply update_i_lt_j; auto. lia.
    f_equal. unfold cholesky_return'. f_equal.
    f_equal; extensionality k; unfold update_mx; rewrite mxE; repeat destruct (Nat.eq_dec _ _); auto; lia.
    apply derives_refl'. f_equal.
     apply matrixP. intros i' j'.
     unfold update_mx, joinLU, map_mx.
     rewrite !mxE. simpl in i',j'.
     do 2 destruct (Nat.eq_dec _ _); auto. simpl in *.
     replace (ssrnat.leq _ _) with true; auto. lia.
  + clear R H4. Intros i R.
    assert (j = lshift1 i) by (apply ord_inj; simpl; lia).
    subst j.
    forward_densematn_set  (joinLU M (map_mx Some R)) i i p sh (R i i).
    unfold joinLU, map_mx; rewrite !mxE; replace (ssrnat.leq _ _) with true by lia; auto.
    simpl.
   forward_for_simple_bound (Z.of_nat i)
     (EX k':Z, EX k:'I_n,
      PROP(k' = Z.of_nat k)
      LOCAL(temp _s (val_of_float (subtract_loop_jik (A i i) R i i k) );
            temp _j (Vint (Int.repr i)); 
            temp _n (Vint (Int.repr n));   lvar _scratch tint v_scratch; temp _A p;
            temp _err (Vfloat (cholesky_return' (lshift1 i) R)))
      SEP(data_at_ Tsh tint v_scratch; densematn sh (joinLU M (map_mx Some R)) p)).
  * Exists zero. entailer!!. unfold subtract_loop_jik. simpl. rewrite seq.take0.
    f_equal. destruct (H4 i i) as [_ [_ [? ?]]]. symmetry; apply H6; lia.
  * Intros. subst i0.
    forward_densematn_get  (joinLU M (map_mx Some R)) k i p sh (R k i).
    unfold joinLU, map_mx; rewrite !mxE; replace (ssrnat.leq _ _) with true by lia; auto.
    forward.
    assert (Datatypes.is_true (ssrnat.leq (S (S k)) n)) by lia.
    Exists (Ordinal H6).
    change Vfloat with (@val_of_float the_type).
    change Float.sub with (@BMINUS _ the_type).
    change Float.mul with (@BMULT _ the_type).    
    entailer!!.  split. simpl; lia. f_equal.
    apply @subtract_another; auto; lia.
  * Intros k. assert (k=i) by (apply ord_inj; lia). subst k.
    forward_call.
    replace (Binary.Bsqrt _ _ _ _ _ _) with (@BSQRT _ the_type).
2:{ (* Simplify this proof when https://github.com/VeriNum/vcfloat/issues/32
   is resolved. *)
 unfold BSQRT, UNOP. f_equal. extensionality x. simpl. f_equal. apply proof_irr.
   }
    set (s := BSQRT _).
    forward_call (s, v_scratch, Tsh).
    forward.
    forward_densematn_set  (joinLU M (map_mx Some R)) i i p sh (BSQRT (subtract_loop_jik (A i i) R i i i)).
    assert (Datatypes.is_true (ssrnat.leq (S (S i)) (S n))) by (lia).
    Exists (@Ordinal (S n) (S i) H6).
    Exists (update_mx R i i (BSQRT (subtract_loop_jik (A i i) R i i i))).
    entailer!!. split3. simpl. lia.
    apply cholesky_jik_upto_newrow; auto.
    f_equal. unfold cholesky_return'.  simpl.
    rewrite (take_snoc i) by (rewrite size_ord_enum; simpl; lia).
   rewrite seq.map_cat. rewrite seq.foldl_cat. simpl.
   change BMULT with Float.mul. f_equal. f_equal.
   change @seq.map with @map.
   apply map_ext_in. intros. unfold update_mx.
   rewrite mxE.
   assert (nat_of_ord a < nat_of_ord i). {
     clear - H7. apply (In_nth _ _ i) in H7. destruct H7 as [k [? ?]].
     rewrite <-mv_mathcomp.nth_List_nth in H0.
     change @length with @seq.size in H. rewrite seq.size_take, size_ord_enum in H.
     assert (k < nat_of_ord i) by (destruct (ssrnat.leq (S (nat_of_ord i)) n) eqn:?H; lia).
     rewrite seq.nth_take in H0 by lia. subst a.
     pose proof (ltn_ord i).
     mv_mathcomp.ordify n k.
     rewrite nth_ord_enum'; auto. 
   }
   repeat destruct (Nat.eq_dec _ _); try lia. simpl. auto.
   unfold update_mx; rewrite mxE.
    rewrite nth_ord_enum'. destruct (Nat.eq_dec _ _); try lia. auto.
    apply derives_refl'. f_equal.
    set (a := BSQRT _). clearbody a.
    clear.
    apply matrixP; simpl; intros i' j'.
    unfold update_mx, joinLU, map_mx; rewrite !mxE.
    repeat destruct (Nat.eq_dec _ _); simpl in *; auto.
    replace (ssrnat.leq _ _) with true by lia; auto.
 - Intros n' R.
   assert (cholesky_jik_spec A R). {
      intros i j; destruct (H3 i j) as [H4 _]; apply H4; pose proof (ltn_ord j); lia.
  }
  rewrite cholesky_return'_e by lia.
  forward_if; [ | forward_if]; forward; Exists R; fold A; entailer!!.
  + f_equal. f_equal. destruct (cholesky_return R); try destruct s; try discriminate; auto.
  + f_equal. f_equal. destruct (cholesky_return R); try destruct s; try discriminate; auto.
  + f_equal. f_equal. destruct (cholesky_return R); try destruct s; try discriminate; auto.
Qed.

Lemma body_densemat_cfactor: semax_body Vprog Gprog f_densemat_cfactor densemat_cfactor_spec.
Proof.
start_function.
rename X into M.
unfold densemat in POSTCONDITION|-*.
Intros.
forward.
forward.
forward_if True; [ | contradiction | ].
forward.
entailer!!.
forward.
pose (X := existT _ n M  :  {n & 'M[option (ftype the_type)]_n}).
forward_call (sh,X,offset_val densemat_data_offset p); clear X.
Intros R.
forward.
Exists R.
entailer!!.
Qed.

(** * [densemat_csolve] verification: Cholesky solve by forward substitution and back substitution *)

Lemma body_densematn_csolve: semax_body Vprog Gprog f_densematn_csolve densematn_csolve_spec.
Proof.
start_function. 
assert_PROP (0 <= n <= Int.max_signed /\ n*n <= Int.max_signed) by entailer!.
assert (LEN := Zlength_ord_enum n). 
pose (L := trmx (map_mx optfloat_to_float M)).

assert (HML: forall i j: 'I_n, (j <= i) -> M j i = Some (L i j)). {
 clear - H.
  intros i j ?.
  unfold L. rewrite map_trmx. unfold map_mx, trmx; rewrite !mxE.
  specialize (H j i). unfold mirror_UT, joinLU, trmx in H. rewrite !mxE in H.
  destruct (@ssrnat.leP j i).
  destruct (M j i); try contradiction; auto.
  assert (i=j) by (apply ord_inj; lia). subst j.
   destruct (M i i); try contradiction; auto.
}

pose (fstep i := seq.foldl (forward_subst_step L) x (sublist 0 i (ord_enum n))).
forward_for_simple_bound (Z.of_nat n) (EX i:Z,
   PROP ( )
   LOCAL (temp _R p; temp _x xp; temp _n (Vint (Int.repr n)))
   SEP (densematn rsh M p; 
            densematn sh (map_mx Some (fstep i)) xp))%assert.
- unfold fstep, seq.foldl; rewrite sublist_nil; entailer!!.
- mv_mathcomp.ordify n i.
  assert (IHn : Inhabitant 'I_n) by exact i. 
  forward_densematn_get (map_mx Some (fstep i)) i (@ord0 O) xp sh (fstep i i ord0).
  apply mxE.
  forward_for_simple_bound (Z.of_nat i) (EX j:Z,
   PROP ( )
   LOCAL (temp _bi (val_of_float (seq.foldl BMINUS (fstep i i ord0)
                     (map (fun j => BMULT (L i j) (fstep i j ord0)) (sublist 0 j (ord_enum n))))); 
          temp _i (Vint (Int.repr i)); temp _R p; 
   temp _x xp; temp _n (Vint (Int.repr n)))
   SEP (densematn rsh M p;
             densematn sh (map_mx Some (fstep i)) xp))%assert.
 + entailer!!.
 + rename i0 into j. mv_mathcomp.ordify n j.
    destruct H1 as [_ H1]. destruct H2 as [_ H2].
    forward_densematn_get M j i p rsh (L i j).
   apply HML; lia.
   forward_densematn_get (map_mx Some (fstep i)) j (@ord0 O) xp sh (fstep i j ord0).
   apply mxE.
   forward.
   entailer!!.
  change (@val_of_float _) with Vfloat. 
  change (@BMINUS _ _) with Float.sub.
  change (@BMULT _ _) with Float.mul.
  pose proof (Zlength_ord_enum n). 
   f_equal.
   rewrite (sublist_split 0 j (Z.of_nat j + 1)) by lia. 
   rewrite map_app, seq.foldl_cat.   
   rewrite (sublist_one j (j+1)) by lia.
   simpl.
  rewrite Znth_ord_enum.
  auto.
 +    
   forward_densematn_get M i i p rsh (L i i).
   apply HML; lia.
  set (bi := seq.foldl _ _ _ ).
  forward_densematn_set (map_mx Some (fstep i)) i (@ord0 O) xp sh (BDIV bi (L i i)).
  entailer!!.
  apply derives_refl'. f_equal.
   unfold fstep.
   rewrite (sublist_split 0 i (i+1)) by lia.
   rewrite seq.foldl_cat.
   rewrite (sublist_one i) by lia. simpl.
  rewrite Znth_ord_enum.
  set (al := seq.foldl _ _ _).
  subst bi. change (fstep i)  with al.
  unfold forward_subst_step.
  change ssralg.GRing.zero with (@ord0 O).
  change @seq.map with @map.
  rewrite take_sublist.
  set (uu := BDIV _ _).
  unfold update_mx.
  apply matrixP; intros i' j'.
  unfold map_mx; rewrite !mxE.
  ord1_eliminate j'.
  simpl.
  subst uu. unfold subtract_loop.
  destruct (Nat.eq_dec _ _); auto.
 simpl. f_equal. f_equal. f_equal.
 rewrite map_map.
  apply seq.eq_in_map. intros ? ?. reflexivity.
- 
 deadvars!.
 pose (R := map_mx optfloat_to_float M).
assert (HMR: forall i j: 'I_n, (j >= i) -> M i j = Some (R i j)). {
 clear - H.
 intros i j ?.
 unfold R.  unfold map_mx, trmx; rewrite !mxE.
 unfold mirror_UT, joinLU, trmx in H.
 specialize (H i j); rewrite mxE in H. 
 destruct (@ssrnat.leP i j); [ | lia]. 
 destruct (M i j); try contradiction; auto.
}

pose (bstep i := seq.foldl (backward_subst_step R) (fstep n) (rev (sublist i  n (ord_enum n)))).

forward_loop (EX i:Z,
   PROP (0 <= i <= n)
   LOCAL (temp _i__1 (Vint (Int.repr i));
          temp _R p; temp _x xp; temp _n (Vint (Int.repr n)))
   SEP (densematn rsh M p; 
            densematn sh (map_mx Some (bstep i)) xp))%assert.
 + forward.
  Exists (Z.of_nat n). entailer!!.
  unfold bstep. autorewrite with sublist. simpl. auto. 
 + Intros i.
  forward_if.
  * 
    rewrite <- (Z.sub_add 1 i) in *.
   set (i1 := i-1) in *.
   mv_mathcomp.ordify n i1. rewrite Hi0 in *. clear i Hi0. clear H2. 
  assert (IHn : Inhabitant 'I_n) by exact i1. 
   pose (i := i1+1).
   forward_densematn_get (map_mx Some (bstep i)) i1 (@ord0 O) xp sh (bstep i i1  ord0).
   entailer!!;  simpl; repeat f_equal; lia.
   subst i; cancel.
   apply mxE.
  forward_for_simple_bound (Z.of_nat n) (EX j:Z,
   PROP (i1 < j)
   LOCAL (temp _yi (val_of_float 
            (seq.foldl BMINUS (bstep i i1 ord0)
              (map (fun j => BMULT (R i1 j) (bstep i j ord0)) (sublist i j (ord_enum n)))));
          temp _i__1 (Vint (Int.repr i)); temp _R p; 
          temp _x xp; temp _n (Vint (Int.repr n)))
   SEP (densematn rsh M p;
             densematn sh (map_mx Some (bstep i)) xp))%assert.
  -- forward. Exists i; entailer!!. autorewrite with sublist. reflexivity. 
  -- rename i0 into j. Intros.
   mv_mathcomp.ordify n j.
   forward_densematn_get M i1 j p rsh (R i1 j).
   entailer!!. 
     simpl; repeat f_equal; lia.
     apply HMR; lia.
   forward_densematn_get (map_mx Some (bstep i)) j (@ord0 O) xp sh (bstep i j ord0).
   apply mxE.
   forward.
   entailer!!.
   rewrite (sublist_split i j) by lia.
   rewrite (sublist_one j) by lia.
   rewrite map_app, seq.foldl_cat.
   simpl.
   rewrite Znth_ord_enum.
   reflexivity.
 --
   forward_densematn_get M i1 i1 p rsh (R i1 i1).
   entailer!!. simpl. repeat f_equal; lia.
   apply HMR; lia.
    Intros vret. subst vret.
   set (bi := seq.foldl _ _ _).
   forward_densematn_set (map_mx Some (bstep i)) i1 (@ord0 O) xp sh (BDIV bi (R i1 i1)).
   entailer!!. simpl; repeat f_equal; lia.
   forward.
   Exists (Z.of_nat i1).
   entailer!!. f_equal; f_equal; lia.
   apply derives_refl'; f_equal.
   subst i.
   unfold bstep at 2.
   rewrite (sublist_split i1 (i1+1)) by lia.
   rewrite (sublist_one i1) by lia.
   simpl rev.
   rewrite seq.foldl_cat.
   simpl.
   rewrite Znth_ord_enum.
   unfold backward_subst_step at 1.
   unfold subtract_loop.
   apply matrixP; intros i' j'.
   unfold update_mx, map_mx; rewrite !mxE.
   ord1_eliminate j'.
   destruct (Nat.eq_dec i' i1); simpl; auto.
   rewrite drop_sublist.
   f_equal. f_equal. subst bi. f_equal.
   change @seq.map with @map.
   rewrite map_map.
   f_equal. f_equal; lia.
  *
   forward.
   entailer!!.
   assert (i=0) by lia. subst i.
   apply derives_refl'.
   f_equal. f_equal.
   unfold bstep, backward_subst, fstep, forward_subst.
   rewrite sublist_same by lia.
   subst R L.
   rewrite seq_rev_rev; reflexivity.
Qed.


Lemma body_densemat_csolve: semax_body Vprog Gprog f_densemat_csolve densemat_csolve_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*.
Intros. 
forward.
pose (X := existT _ n (M,x) : {n & 'M[option (ftype the_type)]_n * 'cV[ (ftype the_type)]_n}%type).
forward_call (rsh,sh,X, offset_val densemat_data_offset p, xp); clear X.
entailer!!.
Qed.

Lemma body_densematn_cfactor_and_solve: semax_body Vprog Gprog 
        f_densematn_cfactor_and_solve densematn_cfactor_and_solve_spec.
Proof.
start_function.
pose (X := existT _ n A  :  {n & 'M[option (ftype the_type)]_n}).
forward_call (shA,X,p); clear X.
Intros R.
forward_if (Zcholesky_return(cholesky_return R)=1%Z).
- forward_call. contradiction.
- forward. entailer!!. 
  destruct (cholesky_return R); try discriminate.
  destruct s,m; try discriminate; reflexivity.
- (* After the if statement *)
pose (X := existT _ n ((joinLU A (map_mx Some R)),x)  :  {n & 'M[option (ftype the_type)]_n * 'cV[ftype the_type]_n}%type).
forward_call (shA,sh,X,p,xp); clear X.
+ clear - H. intros. specialize (H i j). unfold mirror_UT, joinLU, map_mx, trmx in *. rewrite !mxE.  rewrite !mxE in H.
  destruct (ssrnat.leq (nat_of_ord i) (nat_of_ord j)) eqn:?H. hnf; auto.
  destruct (ssrnat.leq (nat_of_ord j) (nat_of_ord i)) eqn:?H; hnf; auto.
+ Exists R. entailer!!.
   eapply cholesky_return_success; auto.
   rewrite (backward_subst_UT _ R); [ rewrite (forward_subst_LT _ (R^T)); [ auto | ] | ].
  * intros. unfold map_mx, joinLU, trmx. rewrite !mxE. rewrite H2. auto.
  * intros. unfold map_mx, joinLU, trmx. rewrite !mxE. rewrite H2. auto.
Qed.

