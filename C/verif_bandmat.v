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
(* [densemat_lemmas] is loaded transitively through [bandmat_lemmas], but
   [Require Import] is not transitive for NAMES, so its lemmas are reachable
   here only qualified -- hence [densemat_lemmas.Zlength_ord_enum] and
   [densemat_lemmas.Znth_ord_enum] below.  Deliberately not [Import]ed: that
   would also pull in densemat's own [Gprog], shadowing bandmat's. *)

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
Proof.
start_function.
unfold bandmat, bandmatn.
destruct X as [m M].
simpl in M|-*.
Intros.
assert_PROP (isptr p
      /\ malloc_compatible (bandmat_data_offset +
      sizeof (tarray tdouble (Z.of_nat m * Z.of_nat (S b)))) p) by entailer!.
destruct H3 as [H3 COMPAT].
simpl in COMPAT. rewrite Z.max_r in COMPAT by lia.
red in COMPAT.
forward_call (bandmat_data_offset + Z.of_nat m * Z.of_nat (S b) * sizeof(tdouble), p, gv).
-
revert Frame.
instantiate (1:=nil). intro.
subst Frame.
rewrite if_false by (intro; subst; contradiction).
simpl.
rewrite Z.max_r by lia.
rewrite (Z.mul_comm (Z.of_nat m * Z.of_nat (S b))).
cancel.
destruct p; try contradiction; clear H3.
rewrite <- (Ptrofs.repr_unsigned i).
unfold bandmat_data_offset in *.
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
replace (8 * (m * Z.pos (PosDef.Pos.of_succ_nat b)))%Z
  with (8 * (Z.max 0 (m * Z.pos (PosDef.Pos.of_succ_nat b))))%Z by rep_lia.
apply data_at_memory_block.
-
entailer!.
Qed.

(** * [bandmatn_get] verification *)
Lemma body_bandmatn_get: semax_body Vprog Gprog f_bandmatn_get bandmatn_get_spec.
Proof.
start_function.
unfold bandmatn.
Intros.
assert_PROP (0 <= Z.of_nat j + (Z.of_nat j - Z.of_nat i) * Z.of_nat m
             < Z.of_nat m * Z.of_nat (S b)).
{ entailer!. pose proof (ltn_ord j). nia. }
forward.
-
entailer!.
bandmat_read_tac m b M i j H.
reflexivity.
-
bandmat_index_range_tac m b i j.
-
bandmat_read_tac m b M i j H.
forward.
unfold bandmatn.
bandmat_strip_reptype m b M.
entailer!.
Qed.

(** * [bandmat_get] verification *)
Lemma body_bandmat_get: semax_body Vprog Gprog f_bandmat_get bandmat_get_spec.
Proof.
start_function.
unfold bandmat.
Intros.
forward.
forward_call (existT (fun m => ('M[option (ftype the_type)]_(m,m) * ('I_(m) * 'I_(m)))%type) 
  m (M,(i,j)), b, offset_val bandmat_data_offset p, sh, x).
forward.
unfold bandmat.
entailer!.
Qed.

(** * [bandmatn_set] verification *)
Lemma body_bandmatn_set: semax_body Vprog Gprog f_bandmatn_set bandmatn_set_spec.
Proof.
start_function.
unfold bandmatn.
Intros.
assert_PROP (0 <= Z.of_nat j + (Z.of_nat j - Z.of_nat i) * Z.of_nat m
             < Z.of_nat m * Z.of_nat (S b)).
{ entailer!. pose proof (ltn_ord j). nia. }
forward.
-
bandmat_index_range_tac m b i j.
-
bandmat_strip_reptype m b M.
assert (Hveq: Vfloat x = val_of_optfloat (Some x)) by reflexivity.
rewrite Hveq.
bandmat_write_tac m b M i j (Some x) H2 H3 H.
Qed.

(** * [bandmat_set] verification *)
Lemma body_bandmat_set: semax_body Vprog Gprog f_bandmat_set bandmat_set_spec.
Proof.
start_function.
unfold bandmat.
Intros.
forward.
forward_call (existT (fun m => ('M[option (ftype the_type)]_(m,m) * ('I_(m) * 'I_(m)))%type) 
  m (M,(i,j)), b, offset_val bandmat_data_offset p, sh, x).
unfold bandmat.
entailer!.
Qed.

(** * [bandmatn_addto] verification *)
Lemma body_bandmatn_addto: semax_body Vprog Gprog f_bandmatn_addto bandmatn_addto_spec.
Proof.
start_function.
unfold bandmatn.
Intros.
assert_PROP (0 <= Z.of_nat j + (Z.of_nat j - Z.of_nat i) * Z.of_nat m
             < Z.of_nat m * Z.of_nat (S b)).
{ entailer!. pose proof (ltn_ord j). nia. }
forward.
-
entailer!.
bandmat_read_tac m b M i j H.
simpl. auto.
-
bandmat_index_range_tac m b i j.
-
bandmat_read_tac m b M i j H.
forward.
+
bandmat_index_range_tac m b i j.
+
change (Vfloat (Float.add y x)) with (val_of_optfloat (Some (BPLUS y x))).
bandmat_write_tac m b M i j (Some (BPLUS y x)) H3 H4 H0.
Qed.

(** * [bandmat_addto] verification *)
Lemma body_bandmat_addto: semax_body Vprog Gprog f_bandmat_addto bandmat_addto_spec.
Proof.
start_function.
unfold bandmat.
Intros.
forward.
forward_call (existT (fun m => ('M[option (ftype the_type)]_(m,m) * ('I_(m) * 'I_(m)))%type) 
  m (M,(i,j)), b, offset_val bandmat_data_offset p, sh, y, x).
unfold bandmat.
entailer!.
Qed.

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
(** STATUS: blocked, not a proof gap in our reasoning but a VST/Coq performance
    wall. [dense_to_band] reads [A->n] directly off a [densemat_t*] argument,
    which requires bridging [spec_densemat.CompSpecs] (from densemat.c's own
    compilation unit) into bandmat's own [CompSpecs]. The scalar-value parts of
    this bridge (data_at's own compspecs tag, nested_field_offset, size_compatible)
    all convert cleanly via [change_compspecs]/[field_at_data_at] plus plain
    [simpl]/[unfold]. The remaining piece, [align_compatible_rec], is only
    bridgeable via the official VST lemma [align_compatible_rec_change_composite],
    whose side condition [cs_preserve_type cs_from cs_to (coeq cs_from cs_to) t
    = true] requires forcing [coeq]'s full composite-environment table -- and
    doing that (tried both [vm_compute] and [native_compute]) crashed the IDE
    both times. This looks like a genuine cost/possible bug in how this
    project's two [change_composite_env] directions interact with [coeq]'s
    construction, not something fixable with a different tactic choice.
    Likely real fixes: VSU-based linking between densemat.c and bandmat.c
    (per VST's own error hint), or restructuring so [dense_to_band] calls a
    verified accessor instead of reading the struct field directly.

    The double-loop mathematics itself (the interesting part of this proof) is
    fully worked out and reusable: see [dtb_inv]/[dtb_inv_base]/[dtb_inv_step_j]/
    [dtb_inv_step_d]/[dtb_inv_final] and [bandmat_ext]/[banded_repr_ext] in
    bandmat_lemmas.v. Once [A->n]'s value is available as [temp _n (Vint
    (Int.repr m))], the rest of the proof (outer [forward_loop] over the band
    index with invariant [dtb_inv bw d d M P0 P], inner [forward_loop] over the
    column with invariant [dtb_inv bw d j M P0 P'], stepping via
    [dtb_inv_step_j]/[dtb_inv_step_d], closing via [bandmat_ext]) was drafted
    and worked mechanically -- only this one field read is the blocker. *)

(**
  AFOREMENTIONED FAILED ATTEMPT BELOW

  (** * [dense_to_band] verification - FAULTY FIRST TRY VERSION *)
Lemma body_dense_to_band: semax_body Vprog Gprog f_dense_to_band dense_to_band_spec.
Proof.
start_function.
rename X into M.
rename H into Hbound; rename H0 into Hbwm; rename H1 into Htrmx;
rename H2 into Hoffband; rename H3 into HisSome.
unfold spec_densemat.densemat.
Intros.
replace_SEP 1 (field_at sh (Tstruct _densemat_t noattr) (DOT _n) (Vint (Int.repr m)) p).
- entailer!.
  apply change_compspecs_field_at_cancel.
  + reflexivity.
  + vm_compute. reflexivity.
  + reflexivity.
- forward. (* _n := A->n *)
fold spec_densemat.densemat.
forward_call (m, bw, gv).
Intros q.
forward. (* _P := t'1 *)
forward. (* _d := 0 *)
set (P0 := bandmat_init bw m).
forward_loop (EX Zd: Z, EX P: 'M[option (ftype the_type)]_(m,m),
   PROP (0 <= Zd <= Z.of_nat bw + 1;
         dtb_inv bw (Z.to_nat Zd) (Z.to_nat Zd) M P0 P)
   LOCAL (temp _d (Vint (Int.repr Zd)); temp _n (Vint (Int.repr (Z.of_nat m)));
          temp _bw (Vint (Int.repr (Z.of_nat bw))); temp _A p; temp _P q; gvars gv)
   SEP (densemat sh M p; bandmat Ews bw P q; mem_mgr gv))%assert.
- (* initial entry into outer loop *)
  Exists 0 P0.
  entailer!.
  split; [lia | apply dtb_inv_base].
- (* outer loop body *)
  Intros Zd P.
  Intros HZdRange Hdtb.
  forward_if.
  + (* Zd <= bw : do band d = Zd *)
    forward. (* _j := d *)
    forward_loop (EX Zj: Z, EX P': 'M[option (ftype the_type)]_(m,m),
       PROP (Zd <= Zj <= Z.of_nat m;
             dtb_inv bw (Z.to_nat Zd) (Z.to_nat Zj) M P0 P')
       LOCAL (temp _j (Vint (Int.repr Zj)); temp _d (Vint (Int.repr Zd));
              temp _n (Vint (Int.repr (Z.of_nat m))); temp _bw (Vint (Int.repr (Z.of_nat bw)));
              temp _A p; temp _P q; gvars gv)
       SEP (densemat sh M p; bandmat Ews bw P' q; mem_mgr gv))%assert.
    * Exists Zd P. entailer!.
    * Intros Zj P'.
      Intros HZjRange Hdtb'.
      forward_if.
      -- (* Zj < n : process (i,j) *)
         forward. (* _i := j - d *)
         assert (Hjm: (Z.to_nat Zj < m)%nat) by lia.
         assert (Him: (Z.to_nat Zj - Z.to_nat Zd < m)%nat) by lia.
         pose (j_ord := @Ordinal m (Z.to_nat Zj) Hjm).
         pose (i_ord := @Ordinal m (Z.to_nat Zj - Z.to_nat Zd) Him).
         assert (Hij: (Z.of_nat j_ord - Z.of_nat i_ord = Zd)%Z) by (simpl; lia).
         specialize (HisSome i_ord j_ord).
         destruct (M i_ord j_ord) as [x|] eqn:HMx; [ | simpl in HisSome; contradiction].
         forward_call (existT (fun mn : nat * nat =>
             ('M[option (ftype the_type)]_(fst mn, snd mn) *
              ('I_(fst mn) * 'I_(snd mn)))%type) (m,m) (M,(i_ord,j_ord)), p, sh, x).
         forward_call (existT (fun m0 : nat =>
             ('M[option (ftype the_type)]_(m0,m0) * ('I_(m0) * 'I_(m0)))%type) m
             (P',(i_ord,j_ord)), bw, q, Ews, x).
         { entailer!. rewrite Hij. lia. }
         forward.
         Exists (Zj + 1) (update_mx (update_mx P' i_ord j_ord (Some x)) j_ord i_ord (Some x)).
         entailer!.
         split; [lia | ].
         replace (Z.to_nat (Zj + 1)) with (S (Z.to_nat Zj)) by lia.
         apply (dtb_inv_step_j bw (Z.to_nat Zd) (Z.to_nat Zj) M P0 P' i_ord j_ord x); auto.
         ++ simpl. lia.
         ++ simpl. reflexivity.
         ++ lia.
         ++ lia.
      -- (* Zj >= n : band d done, advance to d+1 *)
         forward.
         Exists (Zd + 1) P'.
         entailer!.
         split; [lia | ].
         replace (Z.to_nat Zj) with m in Hdtb' by lia.
         replace (Z.to_nat (Zd + 1)) with (S (Z.to_nat Zd)) by lia.
         apply dtb_inv_step_d; auto.
  + (* Zd > bw : outer loop done, return *)
    forward.
    Exists q.
    entailer!.
    apply bandmat_ext; auto.
    apply banded_repr_ext.
    intros i j Hrange.
    replace (Z.to_nat Zd) with (S bw) in Hdtb by lia.
    destruct Hdtb as [Hdone _].
    apply Hdone; auto.
    left. lia.
Qed.
*)
Lemma body_dense_to_band: semax_body Vprog Gprog f_dense_to_band dense_to_band_spec.
Proof. Admitted.

(** * [bandmat_factor] verification *)
Lemma body_bandmat_factor: semax_body Vprog Gprog f_bandmat_factor bandmat_factor_spec.
Proof. Admitted.

(** * [bandmat_solve] verification *)
(** THE FOLLOWING IS AN INCOMPLETE FIRST DRAFT OF BODY_BANDMAT_SOLVE

(** Forward and backward substitution using a band Cholesky factor.  The
    skeleton is [body_densematn_csolve] from [verif_densemat_cholesky.v]; the
    differences are all consequences of the banded data structure:

    - [PR->m] and [PR->b] are read off bandmat's OWN struct, so unlike
      [dense_to_band]'s read of a [densemat_t] field there is no cross-compspecs
      problem here: just [bandmat_unfold], two [forward]s, and fold back up so
      the [bandmat_get] calls still see the [bandmat] predicate their funspec
      wants.

    - Matrix entries arrive through [forward_call] to the (already verified)
      [bandmat_get].  Both inner loops are band-limited and hence have compound
      guards ([dj <= bw && dj <= i], [j <= i+bw && j < n]), which clightgen
      compiles to a short-circuit [_t'1]/[_t'4] plus [Sbreak].  So they are
      [forward_loop ... break:] with an explicit [forward_if] on the flag
      temp (the idiom in [body_csr_matrix_vector_multiply] and
      [verif_build_csr.v]), not [forward_for_simple_bound].

    - [x] is a bare [double*] subscripted directly by the C code, and
      [densematn_get_spec] is not in bandmat's [Gprog], so
      [forward_densematn_get]/[forward_densematn_set] are unavailable.
      [densematn_colvec] converts the column vector into a flat [data_at] once,
      up front, after which every [x[i]] is an ordinary VST array access.

    The postcondition is stated with [forward_subst_band]/[backward_subst_band]
    rather than the dense [forward_subst]/[backward_subst]; see the comment on
    those definitions in [spec_bandmat.v] for why the dense models are not what
    this C code computes. *)
Lemma body_bandmat_solve: semax_body Vprog Gprog f_bandmat_solve bandmat_solve_spec.
Proof.
start_function.
assert (HMirror: forall i j: 'I_m, isSome (mirror_UT M i j)) by auto.
assert (RSH: readable_share rsh) by auto.
assert (WSH: writable_share sh) by auto.

(** Sizes.  [bandmatn]'s own invariant carries both [b < m] and the product
    bound, from which everything else follows by [nia]. *)
assert_PROP ((b < m)%nat) as Hbm.
{ unfold bandmat, bandmatn. Intros. entailer!. }
assert_PROP (0 < Z.of_nat m * Z.of_nat (S b) <= Int.max_signed) as Hmb.
{ unfold bandmat, bandmatn. Intros. entailer!. }
(* Spell out [Z.of_nat (S b)] rather than leaving it an opaque atom, so that
   the nonlinear step below is within reach of [nia]. *)
assert (HSb: Z.of_nat (S b) = Z.of_nat b + 1) by (rewrite Nat2Z.inj_succ; lia).
assert (Hmpos: 0 < Z.of_nat m) by nia.
assert (Hm: 0 < Z.of_nat m <= Int.max_signed) by nia.
assert (Hbz: 0 <= Z.of_nat b < Z.of_nat m) by lia.
assert (LEN := densemat_lemmas.Zlength_ord_enum m).

(** [n = PR->m; bw = PR->b] *)
rewrite bandmat_unfold.
Intros.   (* flatten the [*] into separate SEP entries, or [forward] refuses *)
forward.
forward.
sep_apply (bandmat_fold rsh b M p).

(** Present [x] as a flat array of doubles for the rest of the proof. *)
rewrite (densematn_colvec sh x xp Hm).

pose (L := trmx (map_mx optfloat_to_float M)).
pose (R := map_mx optfloat_to_float M).

assert (HML: forall i j: 'I_m, (j <= i)%N -> M j i = Some (L i j)). {
 clear - HMirror.
  intros i j ?.
  unfold L. rewrite map_trmx. unfold map_mx, trmx; rewrite !mxE.
  specialize (HMirror j i). unfold mirror_UT, joinLU, trmx in HMirror.
  rewrite !mxE in HMirror.
  destruct (@ssrnat.leP j i).
  destruct (M j i); try contradiction; auto.
  assert (i=j) by (apply ord_inj; lia). subst j.
  destruct (M i i); try contradiction; auto.
}

assert (HMR: forall i j: 'I_m, (i <= j)%N -> M i j = Some (R i j)). {
 clear - HMirror.
 intros i j ?.
 unfold R. unfold map_mx, trmx; rewrite !mxE.
 unfold mirror_UT, joinLU, trmx in HMirror.
 specialize (HMirror i j); rewrite mxE in HMirror.
 destruct (@ssrnat.leP i j); [ | lia].
 destruct (M i j); try contradiction; auto.
}

assert (HLR: forall k: 'I_m, L k k = R k k). {
 intro k. unfold L, R. rewrite map_trmx. unfold map_mx, trmx.
 rewrite !mxE. reflexivity.
}

(** ** Forward substitution *)

pose (fstep (i:Z) := seq.foldl (forward_subst_band_step b L) x (sublist 0 i (ord_enum m))).

forward_for_simple_bound (Z.of_nat m) (EX i:Z,
   PROP ( )
   LOCAL (temp _PR p; temp _x xp;
          temp _n (Vint (Int.repr (Z.of_nat m)));
          temp _bw (Vint (Int.repr (Z.of_nat b))))
   SEP (bandmat rsh b M p;
        data_at sh (tarray the_ctype (Z.of_nat m))
                (map val_of_float (colvec_list (fstep i))) xp))%assert.
- (* the invariant holds on entry *)
  unfold fstep. autorewrite with sublist. entailer!!.
- (* body of the outer forward loop, row i *)
  mv_mathcomp.ordify m i.
  assert (IHm : Inhabitant 'I_m) by exact i.
  assert (Hi := ltn_ord i).

  (* bi = x[i] *)
  forward.
  rewrite Znth_colvec_list_val.

  (* the running accumulator, as a function of how many band terms are done *)
  pose (BI (k:Z) := val_of_float
          (seq.foldl BMINUS (fstep (Z.of_nat i) i ord0)
             (map (fun j => BMULT (L i j) (fstep (Z.of_nat i) j ord0))
                  (rev (sublist (Z.of_nat i - k) (Z.of_nat i) (ord_enum m)))))).

  (* for (dj = 1; dj <= bw && dj <= i; ++dj) *)
  forward_loop (EX dj:Z,
     PROP (1 <= dj <= Z.min (Z.of_nat b) (Z.of_nat i) + 1)
     LOCAL (temp _bi (BI (dj-1)); temp _dj (Vint (Int.repr dj));
            temp _i (Vint (Int.repr (Z.of_nat i))); temp _PR p; temp _x xp;
            temp _n (Vint (Int.repr (Z.of_nat m)));
            temp _bw (Vint (Int.repr (Z.of_nat b))))
     SEP (bandmat rsh b M p;
          data_at sh (tarray the_ctype (Z.of_nat m))
                  (map val_of_float (colvec_list (fstep (Z.of_nat i)))) xp))%assert
   break:
     (PROP ( )
      LOCAL (temp _bi (BI (Z.min (Z.of_nat b) (Z.of_nat i)));
             temp _i (Vint (Int.repr (Z.of_nat i))); temp _PR p; temp _x xp;
             temp _n (Vint (Int.repr (Z.of_nat m)));
             temp _bw (Vint (Int.repr (Z.of_nat b))))
      SEP (bandmat rsh b M p;
           data_at sh (tarray the_ctype (Z.of_nat m))
                   (map val_of_float (colvec_list (fstep (Z.of_nat i)))) xp))%assert.
  + (* dj = 1 establishes the inner invariant: no band terms consumed yet *)
    forward.
    Exists 1.
    unfold BI.
    replace (Z.of_nat i - (1-1)) with (Z.of_nat i) by lia.
    autorewrite with sublist.
    entailer!!.
  + (* inner loop body *)
    Intros dj.
    (* short-circuit [dj <= bw && dj <= i]; given the invariant this is
       exactly [dj <= min bw i] *)
    forward_if (PROP ( )
      LOCAL (temp _t'1 (Vint (Int.repr (Z.b2z (Z.leb dj (Z.min (Z.of_nat b) (Z.of_nat i))))));
             temp _bi (BI (dj-1)); temp _dj (Vint (Int.repr dj));
             temp _i (Vint (Int.repr (Z.of_nat i))); temp _PR p; temp _x xp;
             temp _n (Vint (Int.repr (Z.of_nat m)));
             temp _bw (Vint (Int.repr (Z.of_nat b))))
      SEP (bandmat rsh b M p;
           data_at sh (tarray the_ctype (Z.of_nat m))
                   (map val_of_float (colvec_list (fstep (Z.of_nat i)))) xp)).
    * forward. entailer!!.
      f_equal. f_equal.
      destruct (Z.leb_spec dj (Z.of_nat i));
      destruct (Z.leb_spec dj (Z.min (Z.of_nat b) (Z.of_nat i))); lia.
    * forward. entailer!!.
      f_equal. f_equal.
      destruct (Z.leb_spec dj (Z.min (Z.of_nat b) (Z.of_nat i))); lia.
    * (* now branch on the flag *)
      forward_if.
      -- (* one more band term: j = i - dj *)
         assert (Hdj: 1 <= dj <= Z.min (Z.of_nat b) (Z.of_nat i)).
         { destruct (Z.leb_spec dj (Z.min (Z.of_nat b) (Z.of_nat i))); simpl in *; try lia.
           contradiction. }
         assert (Hjlt: Datatypes.is_true (ssrnat.leq (S (Z.to_nat (Z.of_nat i - dj))) m)) by lia.
         pose (jo := @Ordinal m (Z.to_nat (Z.of_nat i - dj)) Hjlt).
         assert (Hjo: Z.of_nat (nat_of_ord jo) = Z.of_nat i - dj) by (simpl; lia).

         (* t'2 = bandmat_get(PR, i, dj) = M[i-dj][i] = L[i][i-dj] *)
         forward_call (existT (fun m => ('M[option (ftype the_type)]_(m,m) * ('I_(m) * 'I_(m)))%type)
                         m (M,(jo,i)), b, p, rsh, R jo i);
           try solve [ apply HMR; lia ];
           try solve [ simpl; split; lia ];
           try solve [ entailer!!; simpl; repeat f_equal; lia ].

         (* t'8 = x[i-dj] *)
         forward.
         rewrite <- Hjo.
         rewrite Znth_colvec_list_val.

         (* bi -= t'2 * t'8 *)
         forward.
         Exists (dj+1).
         replace (dj+1-1) with dj by lia.
         unfold BI.
         change (@val_of_float the_type) with Vfloat.
         change (@BMINUS _ the_type) with Float.sub.
         change (@BMULT _ the_type) with Float.mul.
         entailer!!.
         f_equal.
         rewrite (band_lower_step m (Z.of_nat i)
                    (Z.of_nat i - dj) (Z.of_nat i - (dj-1))) by lia.
         rewrite map_app, seq.foldl_cat.
         simpl.
         replace (Z.of_nat i - dj) with (Z.of_nat (nat_of_ord jo)) by lia.
         rewrite densemat_lemmas.Znth_ord_enum.
         (* the entry read by bandmat_get is [R jo i], which is [L i jo] *)
         replace (R jo i) with (L i jo).
         2:{ unfold L, R. rewrite map_trmx. unfold map_mx, trmx.
             rewrite !mxE. reflexivity. }
         reflexivity.
      -- (* dj > min bw i: leave the loop *)
         forward.
         entailer!!.
         unfold BI.
         f_equal. f_equal. f_equal. f_equal.
         lia.
  + (* after the inner loop: x[i] = bi / PR[i][i] *)
    forward_call (existT (fun m => ('M[option (ftype the_type)]_(m,m) * ('I_(m) * 'I_(m)))%type)
                    m (M,(i,i)), b, p, rsh, R i i);
      try solve [ apply HMR; lia ];
      try solve [ simpl; split; lia ];
      try solve [ entailer!!; simpl; repeat f_equal; lia ].
    forward.
    change (Vfloat (Float.div ?a ?c)) with (val_of_float (BDIV a c)).
    rewrite upd_Znth_colvec_list_val.
    entailer!!.
    apply derives_refl'.
    repeat f_equal.
    (* [update_mx (fstep i) i ord0 (BDIV bi (R i i))] is [fstep (i+1)] *)
    unfold fstep at 2.
    rewrite (fstep_step b L x i).
    unfold forward_subst_band_step, BI, band_lower_seq.
    rewrite subtract_loop_map.
    repeat f_equal; try lia; try (symmetry; apply HLR).
- (** ** Backward substitution *)
  deadvars!.
  pose (bstep (i:Z) := seq.foldl (backward_subst_band_step b R) (fstep (Z.of_nat m))
                         (rev (sublist i (Z.of_nat m) (ord_enum m)))).

  (* for (i__1 = n-1; i__1 >= 0; --i__1); the invariant variable is i__1 + 1,
     so it stays in [0, m] and the loop test is [i >= 1]. *)
  forward_loop (EX i:Z,
     PROP (0 <= i <= Z.of_nat m)
     LOCAL (temp _i__1 (Vint (Int.repr (i-1))); temp _PR p; temp _x xp;
            temp _n (Vint (Int.repr (Z.of_nat m)));
            temp _bw (Vint (Int.repr (Z.of_nat b))))
     SEP (bandmat rsh b M p;
          data_at sh (tarray the_ctype (Z.of_nat m))
                  (map val_of_float (colvec_list (bstep i))) xp))%assert.
  + forward.
    Exists (Z.of_nat m).
    unfold bstep.
    autorewrite with sublist.
    entailer!!.
  + Intros i.
    assert (IHm : Inhabitant 'I_m).
    { assert (H0m: Datatypes.is_true (ssrnat.leq 1 m)) by lia.
      exact (@Ordinal m 0 H0m). }
    forward_if.
    * (* i__1 = i-1 >= 0 *)
      assert (Hi1: Datatypes.is_true (ssrnat.leq (S (Z.to_nat (i-1))) m)) by lia.
      pose (io := @Ordinal m (Z.to_nat (i-1)) Hi1).
      assert (Hio: Z.of_nat (nat_of_ord io) = i - 1) by (simpl; lia).

      (* yi = x[i__1] *)
      forward.
      rewrite <- Hio.
      rewrite Znth_colvec_list_val.

      pose (YI (k:Z) := val_of_float
              (seq.foldl BMINUS (bstep i io ord0)
                 (map (fun j => BMULT (R io j) (bstep i j ord0))
                      (sublist i k (ord_enum m))))).

      (* for (j = i__1+1; j <= i__1+bw && j < n; ++j) *)
      forward_loop (EX j:Z,
         PROP (i <= j <= Z.min (i + Z.of_nat b) (Z.of_nat m))
         LOCAL (temp _yi (YI j); temp _j (Vint (Int.repr j));
                temp _i__1 (Vint (Int.repr (i-1))); temp _PR p; temp _x xp;
                temp _n (Vint (Int.repr (Z.of_nat m)));
                temp _bw (Vint (Int.repr (Z.of_nat b))))
         SEP (bandmat rsh b M p;
              data_at sh (tarray the_ctype (Z.of_nat m))
                      (map val_of_float (colvec_list (bstep i))) xp))%assert
       break:
         (PROP ( )
          LOCAL (temp _yi (YI (Z.min (i + Z.of_nat b) (Z.of_nat m)));
                 temp _i__1 (Vint (Int.repr (i-1))); temp _PR p; temp _x xp;
                 temp _n (Vint (Int.repr (Z.of_nat m)));
                 temp _bw (Vint (Int.repr (Z.of_nat b))))
          SEP (bandmat rsh b M p;
               data_at sh (tarray the_ctype (Z.of_nat m))
                       (map val_of_float (colvec_list (bstep i))) xp))%assert.
      -- forward.
         Exists i.
         unfold YI.
         autorewrite with sublist.
         entailer!!.
      -- Intros j.
         forward_if (PROP ( )
           LOCAL (temp _t'4 (Vint (Int.repr (Z.b2z (Z.ltb j (Z.min (i + Z.of_nat b) (Z.of_nat m))))));
                  temp _yi (YI j); temp _j (Vint (Int.repr j));
                  temp _i__1 (Vint (Int.repr (i-1))); temp _PR p; temp _x xp;
                  temp _n (Vint (Int.repr (Z.of_nat m)));
                  temp _bw (Vint (Int.repr (Z.of_nat b))))
           SEP (bandmat rsh b M p;
                data_at sh (tarray the_ctype (Z.of_nat m))
                        (map val_of_float (colvec_list (bstep i))) xp)).
         ++ forward. entailer!!.
            f_equal. f_equal.
            destruct (Z.ltb_spec j (Z.of_nat m));
            destruct (Z.ltb_spec j (Z.min (i + Z.of_nat b) (Z.of_nat m))); lia.
         ++ forward. entailer!!.
            f_equal. f_equal.
            destruct (Z.ltb_spec j (Z.min (i + Z.of_nat b) (Z.of_nat m))); lia.
         ++ forward_if.
            ** assert (Hj: i <= j < Z.min (i + Z.of_nat b) (Z.of_nat m)).
               { destruct (Z.ltb_spec j (Z.min (i + Z.of_nat b) (Z.of_nat m)));
                 simpl in *; try lia. contradiction. }
               assert (Hjlt: Datatypes.is_true (ssrnat.leq (S (Z.to_nat j)) m)) by lia.
               pose (jo := @Ordinal m (Z.to_nat j) Hjlt).
               assert (Hjo: Z.of_nat (nat_of_ord jo) = j) by (simpl; lia).

               (* t'5 = bandmat_get(PR, j, j - i__1) = M[i-1][j] = R[i-1][j] *)
               forward_call (existT (fun m => ('M[option (ftype the_type)]_(m,m) * ('I_(m) * 'I_(m)))%type)
                               m (M,(io,jo)), b, p, rsh, R io jo);
                 try solve [ apply HMR; lia ];
                 try solve [ simpl; split; lia ];
                 try solve [ entailer!!; simpl; repeat f_equal; lia ].

               (* t'7 = x[j] *)
               forward.
               rewrite <- Hjo.
               rewrite Znth_colvec_list_val.

               (* yi -= t'5 * t'7 *)
               forward.
               Exists (j+1).
               unfold YI.
               change (@val_of_float the_type) with Vfloat.
               change (@BMINUS _ the_type) with Float.sub.
               change (@BMULT _ the_type) with Float.mul.
               entailer!!.
               f_equal.
               rewrite (sublist_split i j (j+1)) by lia.
               rewrite (sublist_one j) by lia.
               rewrite map_app, seq.foldl_cat.
               simpl.
               rewrite <- Hjo, densemat_lemmas.Znth_ord_enum.
               reflexivity.
            ** forward.
               entailer!!.
               unfold YI.
               f_equal. f_equal. f_equal.
               lia.
      -- (* after the inner loop: x[i__1] = yi / PR[i__1][i__1] *)
         forward_call (existT (fun m => ('M[option (ftype the_type)]_(m,m) * ('I_(m) * 'I_(m)))%type)
                         m (M,(io,io)), b, p, rsh, R io io);
           try solve [ apply HMR; lia ];
           try solve [ simpl; split; lia ];
           try solve [ entailer!!; simpl; repeat f_equal; lia ].
         forward.
         rewrite <- Hio.
         change (Vfloat (Float.div ?a ?c)) with (val_of_float (BDIV a c)).
         rewrite upd_Znth_colvec_list_val.
         forward.
         Exists (i-1).
         entailer!!.
         { f_equal. f_equal. lia. }
         apply derives_refl'.
         repeat f_equal.
         unfold bstep at 2.
         replace (i-1) with (Z.of_nat (nat_of_ord io)) by lia.
         rewrite (bstep_step b R (fstep (Z.of_nat m)) io).
         replace (Z.of_nat (nat_of_ord io) + 1) with i by lia.
         unfold backward_subst_band_step, YI, band_upper_seq.
         rewrite subtract_loop_map.
         repeat f_equal; try lia.
    * (* i__1 < 0: done *)
      forward.
      assert (Hi0: i = 0) by lia.
      subst i.
      rewrite (densematn_colvec sh
                 (backward_subst_band b (map_mx optfloat_to_float M)
                    (forward_subst_band b (trmx (map_mx optfloat_to_float M)) x)) xp Hm).
      entailer!!.
      apply derives_refl'.
      repeat f_equal.
      unfold bstep, fstep, backward_subst_band, forward_subst_band.
      rewrite !sublist_same by lia.
      reflexivity.
Qed.
*)

Lemma body_bandmat_solve: semax_body Vprog Gprog f_bandmat_solve bandmat_solve_spec.
Proof. Admitted.