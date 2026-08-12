(**  * LAProof.C.spec_bandmat: VST specifications of functions on banded matrices. *)
(** ** Corresponds to C program [bandmat.h] and [bandmat.c] *)
Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From VSTlib Require Import spec_math spec_malloc.
From LAProof.accuracy_proofs Require Import solve_model.
From LAProof.C Require Import bandmat spec_alloc spec_bandmat floatlib matrix_model.
Require Import Coq.Classes.RelationClasses.

(** We [Require] the [mathcomp] files, but without [Import] because we don't want
   to use [ssreflect] tactics in VST proofs, and we don't want the namespace polluted with
   all that mathcomp stuff.
*) 
From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
(** Among all the mathcomp stuff, these are the files that we *do* want to Import: *)
Import fintype matrix.

Require Import LAProof.C.bandmat_lemmas.

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

(** * [bandmat_malloc] verification *)
Lemma body_bandmat_malloc: semax_body Vprog Gprog f_bandmat_malloc bandmat_malloc_spec.
Proof.
start_function.
forward_call (bandmat_data_offset + Z.of_nat m * Z.of_nat (S b) * sizeof(tdouble), gv).
- (* goal 1: witness value matches the C-evaluated call argument *)
  entailer!. simpl. f_equal. unfold bandmat_data_offset; simpl.
  repeat f_equal. lia.
- (* goal 2: witness stays within Ptrofs.max_unsigned *)
  unfold bandmat_data_offset; simpl; rep_lia.
- (* goal 3: continuation *)
  Intros p.
  assert_PROP (isptr p /\ malloc_compatible (8 + Z.of_nat m * Z.of_nat (S b) * sizeof tdouble) p)
    as Hp by entailer!.
  destruct Hp as [Hptr Hmalloc].
  destruct p; try contradiction. clear Hptr.
  destruct Hmalloc as [Halign Hbound].
  rewrite <- (Ptrofs.repr_unsigned i).
  rewrite memory_block_split.
  + rewrite !Ptrofs.repr_unsigned.
    unfold bandmat_data_offset. simpl.
    change (memory_block Ews 8) with (memory_block Ews (sizeof (Tstruct _bandmat_t noattr))).
    rewrite memory_block_data_at_.
    2:{ (* alignment proof for struct fields *)
      split3; auto. simpl; auto.
      split3. simpl. simpl in Hbound. rep_lia.
      red. eapply align_compatible_rec_Tstruct. reflexivity. simpl. auto.
      simpl co_members. intros ? ? ? Hft Hoff.
      unfold Ctypes.field_type in Hft.
      if_tac in Hft. simpl in Hoff. inv Hft. inv Hoff.
      eapply align_compatible_rec_by_value. reflexivity.
      unfold natural_alignment in Halign. simpl. destruct Halign as [x Hx]. exists (2*x)%Z. lia.
      if_tac in Hft. simpl in Hoff. inv Hft. inv Hoff.
      eapply align_compatible_rec_by_value. reflexivity.
      unfold natural_alignment in Halign. simpl. destruct Halign as [x Hx]. exists (2*x+1)%Z. lia.
      if_tac in Hft. simpl in Hoff. inv Hft. inv Hoff.
      eapply align_compatible_rec_Tarray. intros.
      eapply align_compatible_rec_by_value. reflexivity.
      simpl. destruct Halign as [x Hx]. exists (2*x+2)%Z. lia.
      inv Hft. compute; auto.
    }
    Intros.
    forward. (* vm->m = n *)
    forward. (* vm->b = b *)
    forward. (* return vm *)
    Exists (Vptr b0 i).
    unfold bandmat, bandmatn.
    simpl sizeof. unfold bandmat_data_offset.
    rewrite Z.max_r by lia.
    rewrite (Z.mul_comm (Z.of_nat m * Z.of_nat (S b))).
    entailer!.
    2:{ unfold_data_at (data_at _ _ _ _).
      cancel.
      rewrite field_at_data_at. simpl.
      sep_apply data_at_zero_array_inv.
      rewrite emp_sepcon.
      unfold Ptrofs.add.
      rewrite Ptrofs.unsigned_repr by rep_lia.
      replace (8 * (m * Z.pos (PosDef.Pos.of_succ_nat b)))%Z
        with (sizeof (tarray tdouble (m * Z.pos (PosDef.Pos.of_succ_nat b))))%Z by (simpl; lia).
      sep_apply memory_block_data_at_.
      * unfold field_compatible.
        repeat split.
        - (* size_compatible *)
          hnf. simpl.
          simpl sizeof in Hbound.
          assert (Hi8 : 0 <= Ptrofs.unsigned i + 8 <= Ptrofs.max_unsigned).
          { pose proof (Ptrofs.unsigned_range i). unfold Ptrofs.max_unsigned. nia. }
          rewrite (Ptrofs.unsigned_repr _ Hi8).
          rewrite Z.max_r by nia.
          rewrite Zpos_P_of_succ_nat.
          rewrite <- Nat2Z.inj_succ.
          apply Z.compare_lt_iff.
          nia.
        - (* align_compatible *)
          hnf.
          eapply align_compatible_rec_Tarray; intros i0 Hi0.
          eapply align_compatible_rec_by_value. reflexivity.
          simpl.
          simpl sizeof in Hbound.
          assert (Hi8 : 0 <= Ptrofs.unsigned i + 8 <= Ptrofs.max_unsigned).
          { pose proof (Ptrofs.unsigned_range i). unfold Ptrofs.max_unsigned. nia. }
          rewrite (Ptrofs.unsigned_repr _ Hi8).
          destruct Halign as [x Hx].
          unfold natural_alignment in Hx.
          exists (2*x + 2 + 2*i0)%Z. lia.
      * sep_apply data_at__data_at.
        apply derives_refl'. f_equal.
        symmetry.
        change (ctype_of_type the_type) with tdouble.
        change (reptype_ftype _ ?A) with A.
        f_equal.
        unfold default_val. simpl.
        rewrite Zpos_P_of_succ_nat.
        rewrite <- Nat2Z.inj_succ.
        apply banded_repr_init_undef; lia.
    }
    split.
    * apply matrixP; intros x y.
      unfold bandmat_init, trmx.
      rewrite !mxE.
      destruct (andb (x - b <=? y) (y <=? x + b)) eqn:Hxy;
      destruct (andb (y - b <=? x) (x <=? y + b)) eqn:Hyx;
      try reflexivity;
      exfalso;
      repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H as [? ?]
      | H : (_ && _)%bool = false |- _ => apply andb_false_iff in H as [?|?]
      end;
      lia.
    * intros i0 j Hj.
      unfold bandmat_init.
      rewrite mxE.
      destruct (andb (i0 - b <=? j) (j <=? i0 + b)) eqn:Hcond; [exfalso | reflexivity].
      apply andb_true_iff in Hcond as [_ Hle]; lia.
  + unfold bandmat_data_offset; simpl. lia.
  + unfold bandmat_data_offset; simpl; rep_lia.
  + unfold bandmat_data_offset; simpl. simpl sizeof in Hbound.
    rewrite Zpos_P_of_succ_nat.
    rewrite <- Nat2Z.inj_succ.
    pose proof (Ptrofs.unsigned_range i).
    lia. 
Qed.

(** * [bandmat_free] verification *)
Lemma body_bandmat_free: semax_body Vprog Gprog f_bandmat_free bandmat_free_spec.
Proof. Admitted.

(** * [bandmatn_clear] verification *)
Lemma body_bandmatn_clear: semax_body Vprog Gprog f_bandmatn_clear bandmatn_clear_spec.
Proof. Admitted.

(** * [bandmat_clear] verification *)
Lemma body_bandmat_clear: semax_body Vprog Gprog f_bandmat_clear bandmat_clear_spec.
Proof. Admitted.

(** * [bandmatn_get] verification *)
Lemma body_bandmatn_get: semax_body Vprog Gprog f_bandmatn_get bandmatn_get_spec.
Proof. Admitted.

(** * [bandmat_get] verification *)
Lemma body_bandmat_get: semax_body Vprog Gprog f_bandmat_get bandmat_get_spec.
Proof. Admitted.

(** * [bandmatn_set] verification *)
Lemma body_bandmatn_set: semax_body Vprog Gprog f_bandmatn_set bandmatn_set_spec.
Proof. Admitted.

(** * [bandmat_set] verification *)
Lemma body_bandmat_set: semax_body Vprog Gprog f_bandmat_set bandmat_set_spec.
Proof. Admitted.

(** * [bandmatn_addto] verification *)
Lemma body_bandmatn_addto: semax_body Vprog Gprog f_bandmatn_addto bandmatn_addto_spec.
Proof. Admitted.

(** * [bandmat_addto] verification *)
Lemma body_bandmat_addto: semax_body Vprog Gprog f_bandmat_addto bandmat_addto_spec.
Proof. Admitted.

(** * [bandmat_norm2] verification *)
Lemma body_bandmat_norm2: semax_body Vprog Gprog f_bandmat_norm2 bandmat_norm2_spec.
Proof. Admitted.

(** * [bandmat_norm] verification *)
Lemma body_bandmat_norm: semax_body Vprog Gprog f_bandmat_norm bandmat_norm_spec.
Proof. Admitted.

(** * [bandmat_print] verification *)
Lemma body_bandmat_print: semax_body Vprog Gprog f_bandmat_print bandmat_print_spec.
Proof. Admitted.

(** * [dense_to_band] verification *)
Lemma body_dense_to_band: semax_body Vprog Gprog f_dense_to_band dense_to_band_spec.
Proof. Admitted.

(** * [bandmat_factor] verification *)
Lemma body_bandmat_factor: semax_body Vprog Gprog f_bandmat_factor bandmat_factor_spec.
Proof. Admitted.

(** * [bandmat_solve] verification *)
Lemma body_bandmat_solve: semax_body Vprog Gprog f_bandmat_solve bandmat_solve_spec.
Proof. Admitted.
