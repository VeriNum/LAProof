(**  * LAProof.C.verif_densemat: VST proofs of functions on dense matrices. *)
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
