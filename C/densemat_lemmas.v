(**  * LAProof.C.densemat_lemmas: Supporting lemmas for VST proofs of functions on dense matrices. *)

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

(** Given a variable (j: 'I_1), substitute ord0  everywhere *)
Ltac ord1_eliminate j :=
  let H := fresh in assert (H:= ord1 j); simpl in H; subst j.


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
    tryif unify t t2 then idtac else fail 3 "In" ctx ", type of" x "should be" t "but is" t2
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


