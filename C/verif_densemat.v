(**  * LAProof.C.verif_densemat: VST proofs of functions on dense matrices. *)
(** ** Corresponds to C program [densemat.c] *)

(** * Prologue. 

 For explanation see the prologue of [LAProof.C.spec_densemat] *)
From VST.floyd Require Import proofauto VSU.
From LAProof.C Require Import densemat spec_alloc spec_densemat floatlib matrix_model.
From vcfloat Require Import FPStdCompCert FPStdLib.
Require Import VSTlib.spec_math VSTlib.spec_malloc.
Require Import Coq.Classes.RelationClasses.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
Import fintype matrix.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

(** * VSU definitions *)
(** VSU, "Verified Software Units" is VST's system for modular proofs about modular programs. 
 Here, we want to import a subset of the malloc/free interface ([MallocASI]),
 a subset of our own custom wrapper for malloc ([AllocASI]),
 and a subset of VSTlib's math library describing functions from C's standard [math.h] ([MathASI]).
 Finally, we construct [Gprog] which lists all the funspecs of the functions that might be called
 from a function in the [densemat] module.
*)
Definition densemat_E : funspecs := [].
Definition densemat_imported_specs : funspecs := 
   [free_spec'] (* subset of MallocASI *)
  ++ [surely_malloc_spec'; double_clear_spec] (* subset of allocASI *)
  ++ [fma_spec; sqrt_spec]. (* subset of MathASI *)
Definition densemat_internal_specs : funspecs := densematASI.
Definition Gprog :=  densemat_imported_specs ++ densemat_internal_specs.

(**  These [change_composite_env] definitions are a kind of standard boilerplate;
    this mechanism ought to be documented in the VST reference manual, but it isn't. *)
Instance change_composite_env_alloc :
  change_composite_env spec_alloc.CompSpecs CompSpecs.
Proof.
   make_cs_preserve spec_alloc.CompSpecs CompSpecs.
Qed.
 
Instance change_composite_env_alloc' :
  change_composite_env CompSpecs spec_alloc.CompSpecs.
Proof.
   make_cs_preserve CompSpecs spec_alloc.CompSpecs.
Qed.

(** * Many useful supporting lemmas about [column_major], [ordinal], [ord_enum], etc. *)

(** [column_major : forall {T : Type} [rows cols : nat], 'M_(rows, cols) -> list T]
    is a function from a matrix to the list of all its elements in column-major order.
 *)

Lemma map_const_ord_enum: forall {T} n (x: T), map (fun _ => x) (ord_enum n) = repeat x n.
Proof.
 intros.
 pose proof @val_ord_enum n.
 set (F := eqtype.isSub.val_subdef _ ) in H.
 transitivity (map (fun _: nat => x) (map F (ord_enum n))).
rewrite map_map. f_equal.
change @seq.map with @map in H.
rewrite H.
clear.
forget O as k.
revert k.
induction n; simpl; intros; f_equal; auto.
Qed.

Lemma column_major_const:
 forall {t: type} m n (x: option (ftype t)), 
  map val_of_optfloat (@column_major _ m n (const_mx x)) =
  Zrepeat (val_of_optfloat x) (Z.of_nat m * Z.of_nat n).
Proof.
intros.
unfold column_major, Zrepeat.
rewrite Z2Nat.inj_mul by lia.
rewrite !Nat2Z.id.
rewrite <- map_repeat.
f_equal.
symmetry.
transitivity (concat (repeat (repeat x m) n)).
-
 rewrite Nat.mul_comm. induction n; simpl; auto.
 rewrite repeat_app. f_equal; auto.
- f_equal.
 replace (fun j : 'I_n => map (fun i : 'I_m => fun_of_matrix (const_mx x) i j) (ord_enum m))
  with (fun _: 'I_n => repeat x m).
 rewrite map_const_ord_enum; auto.
 extensionality j.
 replace (fun i : 'I_m => fun_of_matrix (const_mx x) i j) with (fun _: 'I_m => x).
 rewrite map_const_ord_enum; auto.
 extensionality i.
 unfold const_mx; rewrite mxE; auto.
Qed.

Lemma densemat_field_compat0: 
 forall m n p, 
  0 <= m -> 0 <= n -> m*n <= Int.max_unsigned ->
  malloc_compatible
    (densemat_data_offset + sizeof (tarray tdouble (m * n))) p ->
  field_compatible0 (tarray tdouble (m*n)) (SUB (n * m)) 
        (offset_val densemat_data_offset p).
Proof.
intros.
destruct p; try contradiction.
destruct H2.
split3; [ | | split3]; auto.
- simpl; auto.
- simpl. rewrite Z.max_r by rep_lia.
unfold densemat_data_offset in *.
rewrite <- (Ptrofs.repr_unsigned i).
rewrite ptrofs_add_repr.
simpl in H3. rewrite Z.max_r in H3 by rep_lia.
rewrite Ptrofs.unsigned_repr by rep_lia.
lia.
- red. unfold offset_val, densemat_data_offset in *.
  apply align_compatible_rec_Tarray. 
  intros.
  eapply align_compatible_rec_by_value; try reflexivity.
  simpl in *.
  rewrite <- (Ptrofs.repr_unsigned i).
  rewrite ptrofs_add_repr.
  rewrite Ptrofs.unsigned_repr by rep_lia.
  unfold natural_alignment in H2.
  repeat apply Z.divide_add_r.
  destruct H2 as [x ?]. rewrite H2. 
  exists (2*x)%Z. lia.
  exists 2; lia.
  apply Z.divide_mul_l. exists 2; lia.
- split; simpl; auto. lia.
Qed.


Lemma Zlength_ord_enum: forall n, Zlength (ord_enum n) = Z.of_nat n.
Proof.
intros.
rewrite Zlength_correct, length_ord_enum; auto.
Qed.

Lemma nth_seq_nth: forall T al (d: T) i,  nth i al d = seq.nth d al i.
Proof.
induction al; destruct i; simpl; intros; auto.
Qed.

Lemma Znth_ord_enum: forall n `{IHn: Inhabitant 'I_n} (i: 'I_n), 
  Znth i (ord_enum n) = i.
Proof.
  intros.
  pose proof (ltn_ord i).
  pose proof Zlength_ord_enum n.
  rewrite <- nth_Znth by lia.
   rewrite Nat2Z.id.
   rewrite nth_seq_nth; 
  apply nth_ord_enum'.
Qed.

Lemma Znth_column_major:
  forall {T} {INH: Inhabitant T} m n i j (M: 'M[T]_(m,n)), 
  Znth (Z.of_nat (nat_of_ord i+nat_of_ord j * m))%nat (column_major M) = M i j.
Proof.
intros.
unfold column_major.
assert (Zlength (ord_enum n) = Z.of_nat n). rewrite Zlength_correct, length_ord_enum; auto.
pose proof (ltn_ord i). pose proof (ltn_ord j).
assert (Zlength (ord_enum m) = Z.of_nat m). rewrite Zlength_correct, length_ord_enum; auto.
assert (Zlength (ord_enum n) = Z.of_nat n). rewrite Zlength_correct, length_ord_enum; auto.
replace (ord_enum n) with 
 (sublist 0 (Z.of_nat j) (ord_enum n) ++ 
  sublist (Z.of_nat j) (Z.of_nat j+1) (ord_enum n) ++ 
  sublist (Z.of_nat j+1) (Z.of_nat n) (ord_enum n))
 by (rewrite !sublist_rejoin; try lia; apply sublist_same; lia).
rewrite !map_app.
rewrite !concat_app.
rewrite Znth_app2.
2:{
rewrite (Zlength_concat' (Z.of_nat j) (Z.of_nat m)). lia.
rewrite Zlength_map. rewrite Zlength_sublist; try lia.
apply Forall_map.
apply Forall_sublist.
apply Forall_forall.
intros.
simpl.
list_solve.
}
rewrite (Zlength_concat' (Z.of_nat j) (Z.of_nat m)).
2: list_solve.
2:{ 
apply Forall_map.
apply Forall_sublist.
apply Forall_forall.
intros.
simpl.
list_solve.
}
replace (_ - _) with (Z.of_nat i) by lia.
rewrite Znth_app1.
2:{
rewrite (@sublist_one _ j); try lia.
simpl.
list_solve.
}
rewrite (@sublist_one _ j); try lia.
simpl.
rewrite app_nil_r.
rewrite (@Znth_map _ i); try lia.
rewrite !Znth_ord_enum.
auto.
Qed.

Lemma Zlength_column_major: forall {T} m n (M: 'M[T]_(m,n)),
  Zlength (column_major M) = (Z.of_nat m*Z.of_nat n)%Z.
Proof.
intros.
unfold column_major.
rewrite (@Zlength_concat' _ (Z.of_nat n) (Z.of_nat m)).
lia.
rewrite Zlength_map, Zlength_correct, length_ord_enum; auto.
apply Forall_map.
apply Forall_forall; intros.
simpl.
rewrite Zlength_map, Zlength_correct, length_ord_enum; auto.
Qed.


Lemma firstn_seq: forall k i m, (i<=m)%nat -> firstn i (seq k m) = seq k i.
intros.
revert k i H; induction m; simpl; intros.
destruct i; try lia. auto.
destruct i; simpl; auto.
f_equal.
apply IHm.
lia.
Qed.

Lemma in_sublist_ord_enum: forall n (a: 'I_n) (lo hi: Z),
  0 <= lo <= hi -> hi <= Z.of_nat n ->
  In a (sublist lo hi (ord_enum n)) -> (lo <= Z.of_nat a < hi)%Z.
Proof.
intros.
pose proof (val_ord_enum n). simpl in H2.
assert (In (nat_of_ord a) (sublist lo hi (map (nat_of_ord(n:=n)) (ord_enum n)))).
rewrite sublist_map. apply in_map. auto.
change @seq.map with @map in H2.
rewrite H2 in H3.
change seq.iota with seq in H3.
forget (nat_of_ord a) as i.
apply In_Znth in H3.
destruct H3 as [j [? ?]].
assert (Zlength (seq 0 n) = Z.of_nat n).
rewrite Zlength_correct, length_seq; auto.
rewrite Zlength_sublist in H3; try lia.
rewrite Znth_sublist in H4 by list_solve.
subst.
rewrite <- nth_Znth by lia.
rewrite seq_nth by lia.
lia.
Qed.

Lemma upd_Znth_column_major: forall {T} [m n] (M:'M[T]_(m,n)) (i: 'I_m) (j: 'I_n) (x:T),
   upd_Znth (Z.of_nat (i + j * m)) (column_major M) x = column_major (update_mx M i j x).
Proof.
intros.
unfold column_major.
assert (Zlength (ord_enum n) = Z.of_nat n). rewrite Zlength_correct, length_ord_enum; auto.
pose proof (ltn_ord i). pose proof (ltn_ord j).
assert (Hm: Inhabitant 'I_m). apply i.
assert (Hn: Inhabitant 'I_n). apply j.
assert (Zlength (ord_enum m) = Z.of_nat m). rewrite Zlength_correct, length_ord_enum; auto.
assert (Zlength (ord_enum n) = Z.of_nat n). rewrite Zlength_correct, length_ord_enum; auto.
replace (ord_enum n) with 
 (sublist 0 (Z.of_nat j) (ord_enum n) ++ 
  sublist (Z.of_nat j) (Z.of_nat j+1) (ord_enum n) ++ 
  sublist (Z.of_nat j+1) (Z.of_nat n) (ord_enum n))
 by (rewrite !sublist_rejoin; try lia; apply sublist_same; lia).
rewrite !map_app.
rewrite !concat_app.
rewrite upd_Znth_app2.
2:{
rewrite (Zlength_concat' (Z.of_nat j) (Z.of_nat m)); try list_solve.
rewrite sublist_one; simpl concat; list_solve.
}
f_equal.
f_equal.
apply map_ext_in.
intros.
assert (nat_of_ord a < nat_of_ord j)%nat
 by (apply in_sublist_ord_enum in H4; lia).
f_equal.
extensionality i'.
unfold update_mx.
rewrite mxE.
destruct (Nat.eq_dec (nat_of_ord a) _); try lia. simpl.
rewrite andb_false_r. auto.
rewrite (Zlength_concat' (Z.of_nat j) (Z.of_nat m)); try list_solve.
rewrite sublist_one by list_solve.
simpl concat. rewrite !app_nil_r.
rewrite upd_Znth_app1 by list_solve.
f_equal.
2:{
f_equal.
apply map_ext_in.
intros.
assert (nat_of_ord j < nat_of_ord a)%nat
 by (apply in_sublist_ord_enum in H4; lia).
f_equal.
extensionality i'.
unfold update_mx.
rewrite mxE.
destruct (Nat.eq_dec (nat_of_ord a) _); try lia. simpl.
rewrite andb_false_r. auto.
}
replace (_ - _) with (Z.of_nat i) by nia.
replace (ord_enum m) with 
 (sublist 0 (Z.of_nat i) (ord_enum m) ++ 
  sublist (Z.of_nat i) (Z.of_nat i+1) (ord_enum m) ++ 
  sublist (Z.of_nat i+1) (Z.of_nat m) (ord_enum m))
 by (rewrite !sublist_rejoin; try lia; apply sublist_same; lia).
rewrite !map_app.
rewrite upd_Znth_app2 by list_solve.
autorewrite with sublist.
rewrite (sublist_one _ (Z.of_nat i + 1)); try lia.
simpl map.
unfold upd_Znth. simpl.
rewrite !Znth_ord_enum.
unfold update_mx at 2.
rewrite mxE.
repeat (destruct (Nat.eq_dec _ _); [ | lia]).
simpl.
f_equal; [ | f_equal].
apply map_ext_in.
intros.
assert (nat_of_ord a < nat_of_ord i)%nat
 by (apply in_sublist_ord_enum in H4; lia).
unfold update_mx; rewrite mxE.
destruct (Nat.eq_dec _ _); [lia | ]. auto.
apply map_ext_in.
intros.
assert (nat_of_ord i < nat_of_ord a)%nat
 by (apply in_sublist_ord_enum in H4; lia).
unfold update_mx; rewrite mxE.
destruct (Nat.eq_dec _ _); [lia | ]. auto.
Qed.

Lemma val_of_optfloat_column_major:
  forall t m n (M: 'M[ftype t]_(m,n)),
  map val_of_optfloat (column_major (map_mx Some M))
  = map val_of_float (column_major M).
Proof.
intros.
unfold column_major.
rewrite !concat_map.
f_equal.
rewrite !map_map.
f_equal. extensionality j. rewrite !map_map. f_equal.
extensionality i.
unfold map_mx.
rewrite mxE. reflexivity.
Qed.


Lemma fold_left_preserves: forall [A C: Type] (g: A -> C) [B: Type] (f: A -> B -> A) (bl: list B),
  (forall x y, g (f x y) = g x) -> 
  (forall x, g (fold_left f bl x) = g x).
Proof.
intros.
revert x; induction bl; simpl; intros; auto.
rewrite IHbl; auto.
Qed.

Lemma take_sublist: forall {T} (al: list T) i,
  seq.take i al = sublist 0 (Z.of_nat i) al.
Proof.
 intros. unfold sublist. simpl. rewrite  Nat2Z.id.
 revert i; induction al; simpl; intros. rewrite firstn_nil; auto.
 destruct i; simpl; auto. f_equal; auto.
Qed.

Lemma drop_sublist: forall {T} (al: list T) i,
   seq.drop i al = sublist (Z.of_nat i) (Zlength al) al.
Proof.
 intros. unfold sublist. simpl. rewrite  Nat2Z.id.
 revert al; induction i; simpl; intros.
 rewrite seq.drop0. rewrite Zlength_correct. rewrite Nat2Z.id.
 rewrite firstn_same by lia. auto.
 destruct al; simpl; auto.
 rewrite IHi.
 rewrite !Zlength_correct. simpl length.
  rewrite !Nat2Z.id. simpl. auto.
Qed.

Lemma seq_rev_rev: @seq.rev = @rev.
Proof.
extensionality T al.
symmetry.
apply rev_alt.
Qed.

(** * Tactics for ordinals *)
(** Given a variable [i] of type [Z], replace it everywhere with a variable [i] of type ['I_n],
    appropriately coerced. *)
Ltac ordify n i :=
  let Hi := fresh "H" i in
  let Hj := fresh "H" i in 
  let j := fresh "i" in 
  assert (Hi: Datatypes.is_true (ssrnat.leq (S (Z.to_nat i)) n)) by lia;
  set (j := @Ordinal n (Z.to_nat i) Hi);
  assert (Hj : i = Z.of_nat (nat_of_ord j)) by (simpl; lia);
  clearbody j; clear Hi;
  subst i;
  rename j into i.

(** Given a variable (j: 'I_1), substitute ord0  everywhere *)
Ltac ord1_eliminate j :=
  let H := fresh in assert (H:= ord1 j); simpl in H; subst j.

(** * [densemat_malloc] verification *)
Lemma body_densemat_malloc: semax_body Vprog Gprog f_densemat_malloc densemat_malloc_spec.
Proof.
start_function.
forward_call (densemat_data_offset+Z.of_nat m*Z.of_nat n*sizeof(tdouble), gv);
unfold densemat_data_offset.
simpl; rep_lia.
Intros p.
assert_PROP (isptr p /\ malloc_compatible (8 + Z.of_nat m * Z.of_nat n * sizeof tdouble) p) by entailer!.
destruct H2.
destruct p; try contradiction. clear H2.
destruct H3.
rewrite <- (Ptrofs.repr_unsigned i).
rewrite memory_block_split by (simpl in *; rep_lia).
rewrite !Ptrofs.repr_unsigned.
change (memory_block Ews 8) 
  with (memory_block Ews (sizeof (Tstruct _densemat_t noattr))).
rewrite memory_block_data_at_.
2:{
split3; auto. simpl; auto.
split3. simpl. simpl in H3. rep_lia.
red.
eapply align_compatible_rec_Tstruct.
reflexivity. simpl. auto.
simpl co_members.
intros.
unfold Ctypes.field_type in H4.
if_tac in H4. simpl in H6. inv H4. inv H5.
eapply align_compatible_rec_by_value. reflexivity.
unfold natural_alignment in H2. simpl.
destruct H2. exists (2*x)%Z. lia.
clear H6. 
if_tac in H4. simpl in H6. inv H4. inv H5.
eapply align_compatible_rec_by_value. reflexivity.
unfold natural_alignment in H2. simpl.
destruct H2. exists (2*x+1)%Z. lia.
clear H6.
if_tac in H4. simpl in H6. inv H4. inv H5.
eapply align_compatible_rec_Tarray.
intros.
eapply align_compatible_rec_by_value. reflexivity.
simpl.
destruct H2. exists (2*x+2)%Z. lia.
inv H4.
compute; auto.
}
Intros.
forward.
forward.
forward.
Exists (Vptr b i).
unfold densemat, densematn.
simpl sizeof.
unfold densemat_data_offset.
rewrite Z.max_r by lia.
rewrite (Z.mul_comm (Z.of_nat m * Z.of_nat n)).
entailer!.
unfold_data_at (data_at _ _ _ _).
cancel.
rewrite field_at_data_at.
simpl.
sep_apply data_at_zero_array_inv.
rewrite emp_sepcon.
unfold Ptrofs.add.
rewrite Ptrofs.unsigned_repr by rep_lia.
replace (8 * (Z.of_nat m*Z.of_nat n))%Z with (sizeof (tarray tdouble (Z.of_nat m*Z.of_nat n)))%Z
 by (simpl; lia).
sep_apply memory_block_data_at_.
-
clear - H H0 H1 H5 H8 H9.
destruct H5 as [_ [_ [? [? _]]]].
split3; auto.
simpl. auto.
split3; [ | | hnf; auto].
red in H2,H9|-*.
simpl. rewrite Z.max_r by rep_lia.
rep_lia.
red.
red in H3.
destruct H8.
apply align_compatible_rec_Tarray.
intros.
eapply align_compatible_rec_by_value.
reflexivity.
simpl.
simpl in H9.
rewrite Ptrofs.unsigned_repr in H9|-* by rep_lia.
unfold natural_alignment in H4.
destruct H4.
rewrite H4.
repeat apply Z.divide_add_r.
apply Z.divide_mul_r.
exists 2; auto.
exists 2; auto.
apply Z.divide_mul_l.
exists 2; auto.
-
sep_apply data_at__data_at.
apply derives_refl'.
f_equal.
clear - H H0.
unfold default_val.
simpl.
symmetry.
change Vundef with (@val_of_optfloat Tdouble None).
apply (@column_major_const Tdouble); lia.
Qed.

(** * [densemat_free] verification *)
Lemma body_densemat_free: semax_body Vprog Gprog f_densemat_free densemat_free_spec.
Proof.
start_function.
unfold densemat, densematn.
destruct X as [[m n] M].
simpl in M|-*.
Intros.
assert_PROP (isptr p
      /\ malloc_compatible (densemat_data_offset +
      sizeof (tarray tdouble (Z.of_nat m * Z.of_nat n))) p) by entailer!.
destruct H2 as [H2 COMPAT].
simpl in COMPAT. rewrite Z.max_r in COMPAT by lia.
red in COMPAT.
forward_call (densemat_data_offset+Z.of_nat m*Z.of_nat n*sizeof(tdouble), p, gv).
-
revert Frame.
instantiate (1:=nil). intro.
subst Frame.
rewrite if_false by (intro; subst; contradiction).
simpl.
rewrite Z.max_r by lia.
rewrite (Z.mul_comm (Z.of_nat m*Z.of_nat n)).
cancel.
destruct p; try contradiction; clear H2.
rewrite <- (Ptrofs.repr_unsigned i).
unfold densemat_data_offset in *.
saturate_local.
rewrite memory_block_split; try (simpl; rep_lia).
apply sepcon_derives.
change 8 with (4+4).
rewrite memory_block_split; try (simpl; rep_lia).
apply sepcon_derives;
rewrite field_at_data_at; simpl;
unfold field_address;
rewrite if_true by auto with field_compatible; simpl.
rewrite ptrofs_add_repr, Z.add_0_r.
apply data_at_memory_block.
rewrite ptrofs_add_repr.
apply data_at_memory_block.
simpl.
rewrite ptrofs_add_repr.
pose (x:= sizeof (tarray tdouble (Z.of_nat m*Z.of_nat n))).
simpl in x.
replace (8 * (Z.of_nat m*Z.of_nat n))%Z with (8 * (Z.max 0 (Z.of_nat m*Z.of_nat n)))%Z by rep_lia.
apply data_at_memory_block.
-
entailer!.
Qed.

(** * Unpacking dependently typed WITH components *)

(** When a funspec has a dependently typed package such as 
   [WITH X: {mn & 'M[option (ftype the_type)]_(fst mn, snd mn)}], 
  the funspec may destruct it by a let-definition immediately after PRE or POST,
  such as [let '(existT _ (m,n) M) := X in].  Standard VST 2.15's [start_function] tactic
  cannot process such funspects.  Here we add a new feature to [start_function].
  See also: https://github.com/PrincetonUniversity/VST/issues/839
 *)


(*  The following destructs any let-definitions immediately after PRE or POST *)
Ltac destruct_it B :=
 match B with 
 | ?C _ => destruct_it C
 | let '(x,y) := ?A in _ => destruct A as [x y]
 | match ?A with _ => _ end =>
     match type of A with
     | @sigT _ (fun x => _) => destruct A as [x A] 
     end
 end.

Ltac destruct_PRE_POST_lets :=
repeat lazymatch goal with 
| |- semax _ (sepcon (close_precondition _ ?B) _) _ _ => destruct_it B
| |- semax _ _ _ (frame_ret_assert (function_body_ret_assert _ ?B) _) => destruct_it B
end;
repeat change (fst (?A,?B)) with A in *;
repeat change (snd (?A,?B)) with B in *.

Ltac start_function ::= start_function1; destruct_PRE_POST_lets; start_function2; start_function3.


(** * [densemat_clear] verification *)

Lemma body_densematn_clear: semax_body Vprog Gprog f_densematn_clear densematn_clear_spec.
Proof.
start_function.
rename X into M.
unfold densematn.
Intros.
forward_call (p,Z.of_nat m* Z.of_nat n,sh)%Z.
unfold densematn.
entailer!.
change_compspecs CompSpecs.
apply derives_refl'.
f_equal.
symmetry.
apply (@column_major_const Tdouble); lia.
Qed.

(** This proof demonstrates a good way to prove a function call to a function whose
  funspec contains a dependently typed package.  Before doing the [forward_call],
  build the package using [existT].  There will be no use for [X] after the [forward_call],
  so it can be cleared immediately. *)

Lemma body_densemat_clear: semax_body Vprog Gprog f_densemat_clear densemat_clear_spec.
(* begin details *)
Proof.
start_function.
rename X into M.
unfold densemat in POSTCONDITION|-*.
Intros.
forward.
forward.
pose (X := existT _ (m,n) M : {mn & 'M[option (ftype the_type)]_(fst mn, snd mn)}).
forward_call (X, offset_val densemat_data_offset p, sh); clear X.
entailer!.
Qed.
(* end details *)

(** * [densemat_get] verification *)

Lemma body_densematn_get: semax_body Vprog Gprog f_densematn_get densematn_get_spec.
Proof.
start_function.
unfold densematn in POSTCONDITION|-*.
Intros.
pose proof (Zlength_column_major _ _ M).
assert (Hi := ltn_ord i).
assert (Hj := ltn_ord j).
assert (0 <= Z.of_nat (i + j * m) < Zlength (column_major M)) by nia.
forward;
replace (Z.of_nat (nat_of_ord i) + Z.of_nat (nat_of_ord j) * Z.of_nat m)
  with (Z.of_nat (i+j * m)) by lia.
entailer!.
change (reptype_ftype _ ?A) with A.
rewrite Znth_map by lia.
rewrite Znth_column_major by lia.
rewrite H; simpl; auto.
change (reptype_ftype _ ?A) with A.
rewrite Znth_map by lia.
rewrite Znth_column_major by lia.
forward.
simpl.
entailer!!.
rewrite H; simpl; auto.
Qed.

Lemma body_densemat_get: semax_body Vprog Gprog f_densemat_get densemat_get_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*; Intros.
forward.
set (X := existT _ (m,n) (M,(i,j)) : 
      {mn : nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)) }%type).
forward_call (X, offset_val densemat_data_offset p, sh, x).
forward.
entailer!!.
Qed.

(** * [densemat_set] verification *)

Lemma body_densematn_set: semax_body Vprog Gprog f_densematn_set densematn_set_spec.
Proof.
start_function.
unfold densematn in POSTCONDITION|-*.
Intros.
assert (Hi := ltn_ord i).
assert (Hj := ltn_ord j).
assert (0 <= Z.of_nat i + Z.of_nat j * Z.of_nat m < Z.of_nat m * Z.of_nat n) by nia.
change (reptype_ftype _ ?A) with A.
forward; simpl fst; simpl snd.
entailer!.
apply derives_refl'.
f_equal.
change (Vfloat x) with (@val_of_optfloat the_type (Some x)).
change (reptype_ftype _ ?A) with A.
rewrite upd_Znth_map.
f_equal.
replace (_ + _) with (Z.of_nat (i + j * m)) by lia.
apply upd_Znth_column_major.
Qed.


Lemma body_densemat_set: semax_body Vprog Gprog f_densemat_set densemat_set_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*.
Intros.
forward.
set (X := existT _ (m,n) (M,(i,j)) : 
      {mn : nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)) }%type).
forward_call (X, offset_val densemat_data_offset p, sh, x).
entailer!!.
Qed.

(** * [densemat_addto] verification *)

Lemma body_densematn_addto: semax_body Vprog Gprog f_densematn_addto densematn_addto_spec.
Proof.
start_function.
unfold densematn in POSTCONDITION|-*.
Intros.
assert (Hi := ltn_ord i).
assert (Hj := ltn_ord j).
pose proof (Zlength_column_major _ _ M).
assert (0 <= Z.of_nat i + Z.of_nat j * Z.of_nat m < Zlength (column_major M)) by nia.
change (reptype_ftype _ ?A) with A.
forward.
entailer!.
rewrite Znth_map by auto.
replace (_ + _) with (Z.of_nat (i + j * m)) by lia.
rewrite Znth_column_major by lia.
rewrite H. simpl; auto.
forward.
entailer!!; simpl.
apply derives_refl'; f_equal.
change (Vfloat x) with (@val_of_optfloat Tdouble (Some x)).
change (reptype_ftype _ ?A) with A.
replace (_ + _) with (Z.of_nat (i + j * m)) by lia.
rewrite Znth_map, Znth_column_major, H by (auto; lia).
simpl.
change (Vfloat ?A) with (@val_of_optfloat Tdouble (Some A)).
rewrite upd_Znth_map.
rewrite upd_Znth_column_major by lia.
auto.
Qed.


Lemma body_densemat_addto: semax_body Vprog Gprog f_densemat_addto densemat_addto_spec.
Proof.
start_function.
unfold densemat in POSTCONDITION|-*.
Intros.
forward.
set (X := existT _ (m,n) (M,(i,j)) : 
      {mn : nat*nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn)) }%type).
forward_call (X, offset_val densemat_data_offset p, sh, y, x).
entailer!!.
Qed.

(** * Tactics for calling matrix subscripting functions *)

(** When doing [forward_call] to the function [densematn_get] and [densematn_set], one
 must first build a dependently typed package as illustrated above in [body_densemat_clear].
 The tactics in this section help automate that, so one can do 
 - [forward_densematn_get] instead of [forward_call] when calling [densemat_get]
 - [forward_densematn_set] instead of [forward_call] when calling [densemat_set]
*)

(* begin hide *)
Ltac typecheck ctx x t :=
  lazymatch type of x with ?t2 =>
    tryif unify t t2 then idtac else fail 3 "In" ctx ", type of" x "should be" t "but is" t
  end.

Ltac typecheck_forward_densemat ctx M i j p sh x :=
  lazymatch type of M with
  |  (@matrix _ ?m ?n) => 
       typecheck ctx M  (@matrix (option (ftype the_type)) m n);
       typecheck ctx i (ordinal m);
       typecheck ctx j (ordinal n)
  | ?T => fail "type of" M "should be (matrix (ftype the_type) _ _) but is" T
  end;
  typecheck ctx p Values.val;
  typecheck ctx sh share;
  typecheck ctx x (ftype the_type).
(* end hide *)

 (** Parameters:  
   - [M: 'M[option (ftype the_type)]_(m,n)], the matrix value to be subscripted
   - [i: 'I_m] [j: 'I_n],  the indices at which to subscript
   - [p: val],  the address in memory where the matrix is represented column-major
   - [sh: share], the permission-share of the representation in memory
   - [x:  ftype the_type], the expected result of subscripting the matrix, or the value to store into the matrix
 *)

Ltac forward_densematn_get M i j p sh x:=
   typecheck_forward_densemat forward_densematn_get M i j p sh x;
   let X := fresh "X" in 
   pose (X := existT _ (_,_) (M,(i, j)) 
          : {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type);
    forward_call (X, p, sh, x); clear X.

Ltac forward_densematn_set M i j p sh x:=
   typecheck_forward_densemat forward_densematn_set M i j p sh x;
   let X := fresh "X" in 
   pose (X := existT _ (_,_) (M,(i, j)) 
          : {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type);
    forward_call (X, p, sh, x); clear X.

(** * [data_norm] and [densemat_norm] verification *)

Lemma body_data_norm2: semax_body Vprog Gprog f_data_norm2 data_norm2_spec.
Proof.
start_function.
forward.
forward_for_simple_bound (Zlength v) (EX j:Z,
      PROP ()
      LOCAL (temp _result (val_of_float (norm2 (sublist 0 j v)));
             temp _data p; temp _n (Vint (Int.repr (Zlength v))))
      SEP(data_at sh (tarray the_ctype (Zlength v)) (map val_of_float v) p))%assert.
- entailer!!.
- forward.
  forward_call.
  forward.
  entailer!!.
  (* Simplify this proof when https://github.com/VeriNum/vcfloat/issues/32
   is resolved. *)
  set (e := Binary.Bfma _ _ _ _ _ _ _ _ _).
  replace e with (FPStdLib.BFMA (Znth i v) (Znth i v) (norm2 (sublist 0 i v)))
    by (unfold e,BFMA,FPCore.fma_nan; simpl; f_equal; f_equal; apply proof_irr).
  rewrite <- norm2_snoc.
  rewrite (sublist_split 0 i (i+1)) by rep_lia.
  rewrite (sublist_one i) by rep_lia. reflexivity.
- forward.
  entailer!!.
  simpl. rewrite sublist_same by rep_lia. reflexivity.
Qed.

Lemma body_data_norm: semax_body Vprog Gprog f_data_norm data_norm_spec.
Proof.
start_function.
forward_call.
forward_call.
forward.
entailer!!.
(* Simplify this proof when https://github.com/VeriNum/vcfloat/issues/32
   is resolved. *)
f_equal.
unfold BSQRT, UNOP.
simpl.
f_equal.
extensionality z.
f_equal.
apply proof_irr.
Qed.

Lemma body_densemat_norm2: semax_body Vprog Gprog f_densemat_norm2 densemat_norm2_spec.
Proof.
start_function.
rename X into M.
unfold densemat, densematn in POSTCONDITION|-*.
Intros.
forward.
forward.
forward_call (sh, column_major M, offset_val densemat_data_offset p);
rewrite Zlength_column_major by lia.
- entailer!!.
- simpl. change (ctype_of_type the_type) with the_ctype.
   change (reptype_ftype _ ?A) with A.
   rewrite val_of_optfloat_column_major.
   cancel.
- lia.
- 
  rewrite Z.max_r by lia.
  forward; simpl.
  change (ctype_of_type the_type) with the_ctype.
  rewrite val_of_optfloat_column_major.
  change (reptype_ftype _ ?A) with A.
  entailer!!.
Qed.

Lemma body_densemat_norm: semax_body Vprog Gprog f_densemat_norm densemat_norm_spec.
Proof.
start_function.
rename X into M.
unfold densemat, densematn in POSTCONDITION|-*.
Intros.
forward.
forward.
forward_call (sh, column_major M, offset_val densemat_data_offset p);
rewrite Zlength_column_major by lia.
- entailer!!.
- simpl. change (ctype_of_type the_type) with the_ctype.
   change (reptype_ftype _ ?A) with A.
   rewrite val_of_optfloat_column_major.
   cancel.
- lia.
-
  rewrite Z.max_r by lia.
  forward; simpl.
  change (ctype_of_type the_type) with the_ctype.
  change (reptype_ftype _ ?A) with A.
  rewrite val_of_optfloat_column_major.
  entailer!!.
Qed.

(** * [densemat_cfactor] verification: Cholesky factorization *)

Lemma body_densematn_cfactor: semax_body Vprog Gprog f_densematn_cfactor densematn_cfactor_spec.
Proof.
start_function.
rename X into M.
assert_PROP (0< n <= Int.max_signed) by entailer!.
pose (A := map_mx optfloat_to_float (mirror_UT M)).
assert (Datatypes.is_true (ssrnat.leq 1 n)) by lia.
pose (zero := @Ordinal n 0 H1).
forward_for_simple_bound (Z.of_nat n) 
  (EX j':Z, EX j: 'I_(S n), EX R: 'M[ftype the_type]_n,
      PROP(j'=j; cholesky_jik_upto zero j A R)
      LOCAL(temp _n (Vint (Int.repr n)); temp _A p)
      SEP(densematn sh (joinLU M (map_mx Some R)) p))%assert.
- Exists (lshift1 zero) A.
  entailer!!.
  apply cholesky_jik_upto_zero; auto.
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
      LOCAL(temp _j (Vint (Int.repr j)); temp _n (Vint (Int.repr n)); temp _A p)
      SEP(densematn sh (joinLU M (map_mx Some R)) p))%assert.
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
      LOCAL(temp _s (val_of_float (subtract_loop A R i j k) );
            temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)); 
            temp _n (Vint (Int.repr n)); temp _A p)
      SEP(densematn sh (joinLU M (map_mx Some R)) p))%assert.
    pose proof (ltn_ord i); lia.
  * Exists zero. entailer!!. f_equal. unfold subtract_loop. simpl. rewrite seq.take0.
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
            (Float.sub (subtract_loop A R i j k)
               (Float.mul (R k i) (R k j))))
    with (val_of_float (BMINUS (subtract_loop A R i j k) (BMULT (R k i) (R k j)))).
    entailer!!. split. simpl; lia.
     f_equal.
     unfold subtract_loop.
     simpl nat_of_ord. rewrite (take_snoc k) by (rewrite size_ord_enum; lia). 
     rewrite !map_app, fold_left_app.
     simpl. rewrite !nth_ord_enum'.  f_equal.
    *
    Intros k'.
    assert (i=k')%nat by (apply ord_inj; lia). subst k'.
    forward_densematn_get  (joinLU M (map_mx Some R)) i i p sh (R i i).
    unfold joinLU, map_mx. rewrite !mxE. simpl. replace (ssrnat.leq _ _) with true by lia. auto.
    pose (X := existT _ (n,n) (joinLU M (map_mx Some R),(i,j)) 
          : {mn : nat * nat & 'M[option (ftype the_type)]_(fst mn, snd mn) * ('I_(fst mn) * 'I_(snd mn))}%type).
    forward_call (X,p,sh, BDIV (subtract_loop A R i j i) (R i i)); clear X.
    set (rij := BDIV _ _).
    assert (Datatypes.is_true (ssrnat.leq (S (S i)) n)) by (pose proof ltn_ord j; lia).
    pose (i1 := @Ordinal n _ H7).
    Exists i1 (update_mx R i j rij).
    entailer!!. split. subst i1. simpl.  lia.
    apply update_i_lt_j; auto. lia.
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
      LOCAL(temp _s (val_of_float (subtract_loop A R i i k) );
            temp _j (Vint (Int.repr i)); 
            temp _n (Vint (Int.repr n)); temp _A p)
      SEP(densematn sh (joinLU M (map_mx Some R)) p)).
  * Exists zero. entailer!!. unfold subtract_loop. simpl. rewrite seq.take0.
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
    forward_densematn_set  (joinLU M (map_mx Some R)) i i p sh (BSQRT (subtract_loop A R i i i)).
    assert (Datatypes.is_true (ssrnat.leq (S (S i)) (S n))) by (lia).
    Exists (@Ordinal (S n) (S i) H6).
    Exists (update_mx R i i (BSQRT (subtract_loop A R i i i))).
    entailer!!. split. simpl. lia.
    apply cholesky_jik_upto_newrow; auto.   
    apply derives_refl'. f_equal.
    set (a := BSQRT _). clearbody a.
    clear.
    apply matrixP; simpl; intros i' j'.
    unfold update_mx, joinLU, map_mx; rewrite !mxE.
    repeat destruct (Nat.eq_dec _ _); simpl in *; auto.
    replace (ssrnat.leq _ _) with true by lia; auto.
 - Intros n' R. Exists R.
   entailer!!. fold A.
   intros i j.
   destruct (H3 i j) as [H4 _ _ _].
   apply H4.
   pose proof (ltn_ord j).  lia.
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
Intros R. Exists R.
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

pose (fstep i := fold_left (forward_subst_step L) (sublist 0 i (ord_enum n)) x).
forward_for_simple_bound (Z.of_nat n) (EX i:Z,
   PROP ( )
   LOCAL (temp _R p; temp _x xp; temp _n (Vint (Int.repr n)))
   SEP (densematn rsh M p; 
            densematn sh (map_mx Some (fstep i)) xp))%assert.
- unfold fstep, fold_left; rewrite sublist_nil; entailer!!.
- ordify n i.
  assert (IHn : Inhabitant 'I_n) by exact i. 
  forward_densematn_get (map_mx Some (fstep i)) i (@ord0 O) xp sh (fstep i i ord0).
  apply mxE.
  forward_for_simple_bound (Z.of_nat i) (EX j:Z,
   PROP ( )
   LOCAL (temp _bi (val_of_float (fold_left BMINUS 
                     (map (fun j => BMULT (L i j) (fstep i j ord0)) (sublist 0 j (ord_enum n)))
                      (fstep i i ord0))); 
          temp _i (Vint (Int.repr i)); temp _R p; 
   temp _x xp; temp _n (Vint (Int.repr n)))
   SEP (densematn rsh M p;
             densematn sh (map_mx Some (fstep i)) xp))%assert.
 + entailer!!.
 + rename i0 into j. ordify n j.
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
   rewrite map_app, fold_left_app.   
   rewrite (sublist_one j (j+1)) by lia.
   simpl.
  rewrite Znth_ord_enum.
  auto.
 +    
   forward_densematn_get M i i p rsh (L i i).
   apply HML; lia.
  set (bi := fold_left _ _ _ ).
  forward_densematn_set (map_mx Some (fstep i)) i (@ord0 O) xp sh (BDIV bi (L i i)).
  entailer!!.
  apply derives_refl'. f_equal.
   unfold fstep.
   rewrite (sublist_split 0 i (i+1)) by lia.
   rewrite fold_left_app.
   rewrite (sublist_one i) by lia. simpl.
  rewrite Znth_ord_enum.
  set (al := fold_left _ _ _).
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
  destruct (Nat.eq_dec _ _); auto.

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

pose (bstep i := fold_left (backward_subst_step R) (rev (sublist i  n (ord_enum n))) (fstep n)).

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
   ordify n i1. rewrite Hi0 in *. clear i Hi0. clear H2. 
  assert (IHn : Inhabitant 'I_n) by exact i1. 
   pose (i := i1+1).
   forward_densematn_get (map_mx Some (bstep i)) i1 (@ord0 O) xp sh (bstep i i1  ord0).
   entailer!!;  simpl; repeat f_equal; lia.
   subst i; cancel.
   apply mxE.
  forward_for_simple_bound (Z.of_nat n) (EX j:Z,
   PROP (i1 < j)
   LOCAL (temp _yi (val_of_float 
            (fold_left BMINUS 
              (map (fun j => BMULT (R i1 j) (bstep i j ord0)) (sublist i j (ord_enum n)))
                      (bstep i i1 ord0)));
          temp _i__1 (Vint (Int.repr i)); temp _R p; 
          temp _x xp; temp _n (Vint (Int.repr n)))
   SEP (densematn rsh M p;
             densematn sh (map_mx Some (bstep i)) xp))%assert.
  -- forward. Exists i; entailer!!. autorewrite with sublist. reflexivity. 
  -- rename i0 into j. Intros.
   ordify n j.
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
   rewrite map_app, fold_left_app.
   simpl.
   rewrite Znth_ord_enum.
   reflexivity.
 --
   forward_densematn_get M i1 i1 p rsh (R i1 i1).
   entailer!!. simpl. repeat f_equal; lia.
   apply HMR; lia.
    Intros vret. subst vret.
   set (bi := fold_left _ _ _).
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
   rewrite fold_left_app.
   simpl.
   rewrite Znth_ord_enum.
   unfold backward_subst_step at 1.
   apply matrixP; intros i' j'.
   unfold update_mx, map_mx; rewrite !mxE.
   ord1_eliminate j'.
   destruct (Nat.eq_dec i' i1); simpl; auto.
   rewrite drop_sublist.
   f_equal. f_equal. subst bi. f_equal.
   change @seq.map with @map.
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

(** * Packaging the [densematVSU], the Verified Software Unit *)

(* BEGIN workaround for VST issue #814, until we can install VST 2.16 which fixes it. *)
Ltac new_simpl_fst_snd :=
  match goal with |- context[@fst ident funspec ?A] =>
     let j := eval hnf in A in 
     match j with (?x,?y) => 
      try change (fst A) with x;
      try change (snd A) with y
     end
    end.

Ltac SF_vacuous ::=
 try new_simpl_fst_snd;
 match goal with |- SF _ _ _ (vacuous_funspec _) => idtac end;
 match goal with H: @eq compspecs _ _ |- _ => rewrite <- H end;
red; red; repeat simple apply conj;
[ reflexivity (* id_in_list ... *)
| repeat apply Forall_cons; (* Forall complete_type fn_vars *)
  try apply Forall_nil; reflexivity
| repeat constructor; simpl; rep_lia (* var_sizes_ok *)
| reflexivity (* fn_callconv ... *)
| split3; [reflexivity | reflexivity | intros; apply semax_vacuous] (* semax_body *)
| eexists; split; compute; reflexivity (* genv_find_func *)
].
(* END workaround for VST issue #814 *)

Definition densematVSU: @VSU NullExtension.Espec
         densemat_E densemat_imported_specs 
         ltac:(QPprog prog) densematASI (fun _ => TT).
  Proof.
    mkVSU prog densemat_internal_specs.
    - solve_SF_internal body_densemat_malloc.
    - solve_SF_internal body_densemat_free.
    - solve_SF_internal body_densematn_clear.
    - solve_SF_internal body_densemat_clear.
    - solve_SF_internal body_densemat_get.
    - solve_SF_internal body_densematn_get.
    - solve_SF_internal body_densemat_set.
    - solve_SF_internal body_densematn_set.
    - solve_SF_internal body_densemat_addto.
    - solve_SF_internal body_densematn_addto.
    - solve_SF_internal body_data_norm.
    - solve_SF_internal body_data_norm2.
    - solve_SF_internal body_densemat_norm.
    - solve_SF_internal body_densemat_norm2.
    - solve_SF_internal body_densemat_csolve.
    - solve_SF_internal body_densematn_csolve.
    - solve_SF_internal body_densemat_cfactor.
    - solve_SF_internal body_densematn_cfactor.
  Qed.

