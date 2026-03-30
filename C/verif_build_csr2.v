Require Import VST.floyd.proofauto.
From LAProof.C Require Import floatlib build_csr2 sparse_model spec_sparse spec_build_csr2 distinct partial_csrg.
Require Import VSTlib.spec_math.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog: funspecs := Build_CSR2_ASI ++ SparseASI ++ MathASI.

Lemma body_swap_rc : semax_body Vprog Gprog f_swap_rc swap_rc_spec.
Proof.
  start_function.
  forward.
  { entailer!!. rewrite Znth_map by list_solve.
    destruct (Znth a coog). reflexivity. }
  forward.
  { entailer!!. rewrite Znth_map by list_solve.
    destruct (Znth a coog). reflexivity. }
  forward.
  { entailer!!. rewrite Znth_map by list_solve.
    destruct (Znth b coog). reflexivity. }
  forward. forward.
  { entailer!!. rewrite !Znth_map by list_solve.
    destruct (Z.eqb_spec a b).
    + subst b. rewrite upd_Znth_same by list_solve.
      destruct (Znth a coog). simpl. auto.
    + destruct (Znth a coog) as [a1 a2] eqn:Ea.
      destruct (Znth b coog) as [b1 b2] eqn:Eb.
      simpl. rewrite upd_Znth_diff by list_solve. 
      rewrite Znth_map by list_solve.
      rewrite Eb. simpl. auto. }
  forward. forward. forward. 
  destruct (Z.eqb_spec a b).
  + subst b. rewrite !upd_Znth_same, !Znth_map by list_solve.
    destruct (Znth a coog) as [a1 a2] eqn:Ea. simpl fst; simpl snd.
    rewrite !upd_Znth_twice by list_solve. entailer!!. simpl.
    apply derives_refl'. f_equal. list_solve.
  + rewrite !upd_Znth_diff, !Znth_map by list_solve.
    destruct (Znth a coog) as [a1 a2] eqn:Ea.
    destruct (Znth b coog) as [b1 b2] eqn:Eb.
    simpl fst; simpl snd.
    rewrite !upd_Znth_twice by list_solve.
    entailer!!. apply derives_refl'; f_equal. list_solve.
Qed.



Lemma body_coog_count : semax_body Vprog Gprog f_coog_count coog_count_spec.
Proof.
  start_function. forward. forward. forward.
  forward_for_simple_bound (Zlength coog)
  (EX i : Z, EX r : Z, EX c : Z,
    PROP (0 <= i <= Zlength coog;
      i = 0 -> (r, c) = (-1, 0);
      i <> 0 -> (r, c) = Znth (i-1) coog)
    LOCAL (temp _c (Vint (Int.repr c));
      temp _r (Vint (Int.repr r));
      temp _count (Vint (Int.repr (count_distinct (sublist 0 i coog))));
      temp _n (Vint (Int.repr (Zlength coog)));
      temp _p p)
    SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog) noattr)
          (map Zpair_to_valpair coog) p))%assert.
  { (* entering the loop *)
    Exists (-1). Exists 0. entailer!!. }
  { (* loop body *)
    forward.
    { entailer!!. rewrite Znth_map by list_solve. 
      destruct (Znth i coog). simpl. auto. } 
    forward.
    { entailer!!. rewrite Znth_map by list_solve. 
      destruct (Znth i coog). simpl. auto. } 
    rewrite !Znth_map by list_solve.
    destruct (Znth i coog) as [ri ci] eqn:Ei; simpl.
    assert (Hrrange: i <> 0 -> 0 <= r <= Int.max_unsigned).
    { intros. specialize (H5 H6).
      rewrite Forall_Znth in H0.
      specialize (H0 (i-1)). spec H0. list_solve.
      unfold rowcol_range in H0. 
      rewrite <- H5 in H0. lia. }
    assert (Hcrange: 0 <= c <= Int.max_unsigned).
    { destruct (Z.eqb_spec i 0).
      + specialize (H4 e). inversion H4. lia.
      + specialize (H5 n).
        rewrite Forall_Znth in H0.
        specialize (H0 (i-1)). spec H0. list_solve.
        unfold rowcol_range in H0.
        rewrite <- H5 in H0. lia. } 
    assert (Hrirange: 0 <= ri < Int.max_unsigned).
    { rewrite Forall_Znth in H0. 
      specialize (H0 i). spec H0. list_solve.
      unfold rowcol_range in H0. rewrite Ei in H0. lia. }
    assert (Hcirange: 0 <= ci < Int.max_unsigned).
    { rewrite Forall_Znth in H0. 
      specialize (H0 i). spec H0. list_solve.
      unfold rowcol_range in H0. rewrite Ei in H0. lia. }
    forward_if (
      PROP ( )
      LOCAL (temp _ci (Vint (Int.repr ci)); temp _ri (Vint (Int.repr ri));
        temp _i (Vint (Int.repr i)); temp _c (Vint (Int.repr c));
        temp _r (Vint (Int.repr r));
        temp _count (Vint (Int.repr (count_distinct (sublist 0 i coog))));
        temp _n (Vint (Int.repr (Zlength coog))); temp _p p;
        temp _t'1 (Vint (Int.repr (Z.b2z (negb (Z.eqb ri r) || negb (Z.eqb ci c))))))
      SEP (data_at sh (Tarray (Tstruct _rowcol noattr) (Zlength coog) noattr)
          (map Zpair_to_valpair coog) p)).
    { (* if true *)
      forward. entailer!.
      destruct (Z.eqb_spec ri r).
      + rewrite e in H6. exfalso. apply H6. reflexivity.
      + simpl. reflexivity. }
    { (* if false *)
      forward. entailer!. destruct (Z.eqb_spec ri r).
      + subst ri. simpl. destruct (Z.eqb_spec ci c).
        - subst ci. simpl. unfold zeq. destruct (Z.eq_dec c c); simpl.
          * unfold bool2val. reflexivity.
          * contradiction.
        - simpl. unfold zeq. destruct (Z.eq_dec ci c); simpl.
          * subst ci. contradiction.
          * unfold bool2val. reflexivity. 
      + destruct (Z.eqb_spec i 0).
        - specialize (H4 e). inversion H4. subst r c i. simpl.
          rewrite (modulo_samerepr (-1) Int.max_unsigned) in H6 by auto.
          apply repr_inj_unsigned in H6; rep_lia.
        - specialize (H5 n0). 
          apply repr_inj_unsigned in H6; rep_lia. }
    (* after if *)
    forward_if.
    + (* if true, count is incremented *)
      forward. forward. forward. 
      Exists (fst (Znth i coog)). Exists (snd (Znth i coog)).
      rewrite Ei. entailer!!. split. 
      - intros. replace (i + 1 - 1) with i by lia. auto.
      - f_equal. f_equal. 
        destruct (Z.eqb_spec i 0).
        { subst i. rewrite sublist_nil. 
          rewrite sublist_one by list_solve.
          simpl. reflexivity. }
        pose proof (count_distinct_incr coog i).
        assert (ri <> r \/ ci <> c) by lia.
        spec H7.
        { unfold BPO.lt. unfold coord2_le. 
          rewrite Ei, <-(H5 n). simpl. 
          pose proof (sorted_e _ H1 (i-1) i).
          spec H9. list_solve. spec H9. list_solve.
          unfold coord2_le in H9.
          rewrite Ei, <-(H5 n) in H9. simpl in H9.
          lia. }
        spec H7. list_solve. rewrite H7. reflexivity.
    + (* if false, count is not incremented *)
      forward. 
      assert (ri = r /\ ci = c) by lia.
      destruct (Z.eqb_spec i 0).
      { subst i. specialize (H4 eq_refl).
        inversion H4; subst. destruct H7; subst ri ci. lia. }
      Exists r. Exists c. clear H6. destruct H7; subst ri ci.
      entailer!!. split.
      - intros. replace (i + 1 - 1) with i by lia.
        rewrite Ei. reflexivity.
      - f_equal. f_equal.
        pose proof (count_distinct_noincr coog i).
        spec H6. list_solve.
        spec H6.
        { unfold BPO.lt. unfold coord2_le. 
          rewrite <-(H5 n), Ei. simpl. lia. }
        rewrite H6. reflexivity. }
  (* after the loop *)
  Intros r c. forward. entailer!!.
  f_equal. f_equal. f_equal. list_solve.
Qed.


Lemma body_start_coog : semax_body Vprog Gprog f_start_coog start_coog_spec.
Proof.
  start_function. 
  forward_call (Tarray (Tstruct _rowcol noattr) n noattr, gv).
  { entailer!!. simpl. f_equal. f_equal. f_equal. lia. }
  { simpl. rep_lia. }
  Intros ret. forward. Exists ret. entailer!!.
Qed.


Lemma body_add_to_coog : semax_body Vprog Gprog f_add_to_coog add_to_coog_spec.
Proof.
  start_function.
  forward. forward. entailer!!.
  rewrite !upd_Znth_twice by list_solve.
  rewrite !upd_Znth_same by list_solve.
  simpl fst. rewrite upd_Znth_app2 by list_solve.
  rewrite Zlength_map by list_solve.
  assert (map Zpair_to_valpair coog ++
   upd_Znth (Zlength coog - Zlength coog)
     (Zrepeat (Vundef, Vundef) (maxn - Zlength coog))
     (Vint (Int.repr r), Vint (Int.repr c)) = 
    (map Zpair_to_valpair coog ++
       (Vint (Int.repr r), Vint (Int.repr c))
       :: Zrepeat (Vundef, Vundef) (maxn - Zlength coog - 1))).
  { list_solve. }
  rewrite H2. entailer!.
Qed.

Lemma body_coog_quicksort : semax_body Vprog Gprog f_coog_quicksort coog_quicksort_spec.
Proof.
Admitted.
  
Lemma body_coog_to_csrg_aux : semax_body Vprog Gprog f_coog_to_csrg_aux coog_to_csrg_aux_spec.
Proof.
  start_function.
  forward. forward. forward. (* three initializations *)
  set (k := count_distinct (coog_entries coog)).
  set (n := Zlength (coog_entries coog)).
  Intros.
  forward_for_simple_bound n (* for (i = 0; i < n; i++) *)
  ( EX i : Z, EX l : Z, EX r : Z, EX c : Z,
    EX ROWPTR : list val, EX COLIND : list val, 
    PROP (0 <= l <= k; l <= i <= n; -1 <= r < coog_rows coog; 0 <= c <= coog_cols coog;
      partial_CSRG i r coog ROWPTR COLIND;
      l = count_distinct (sublist 0 i (coog_entries coog));
      (l = 0 -> r = -1);
      (i <> 0 -> r = (fst (Znth (i-1) (coog_entries coog)))%Z /\ c = snd (Znth (i-1) (coog_entries coog))))
    LOCAL (temp _l (Vint (Int.repr l));
      temp _r (Vint (Int.repr r));
      temp _c (Vint (Int.repr c));
      temp _row_ptr pr;
      temp _col_ind pc;
      temp _rc p;
      temp _n (Vint (Int.repr (Zlength (coog_entries coog))));
      temp _rows (Vint (Int.repr (coog_rows coog))))
    SEP (data_at sh2 (Tarray (Tstruct _rowcol noattr) (n) noattr)
      (map Zpair_to_valpair (coog_entries coog)) p;
      data_at sh1 (tarray tuint k) COLIND pc;
      data_at sh1 (tarray tuint (coog_rows coog + 1)) ROWPTR pr;
      spec_malloc.mem_mgr gv))%assert.
  { (* entering the loop *)
    Exists 0. Exists (-1). Exists 0. 
    Exists (Zrepeat Vundef (coog_rows coog + 1)).
    Exists (Zrepeat Vundef k).
    unfold coog_matrix_wellformed in H.
    entailer!!.
    split.
    { pose proof (count_distinct_bound (coog_entries coog)). lia. }
    pose proof (count_distinct_bound (coog_entries coog)).
    apply partial_CSRG_0; auto.
    transitivity (Zlength (coog_entries coog)); lia. }
  { (* loop body *)
    Intros.
    destruct (Znth i (coog_entries coog)) as [ri ci] eqn:Ei.
    assert (Hri : 0 <= ri < Int.max_unsigned).
    { unfold coog_matrix_wellformed in H. destruct H.
      rewrite Forall_Znth in H13.
      specialize (H13 i). spec H13. list_solve.
      rewrite Ei in H13. simpl in H13. lia. }
    assert (Hci : 0 <= ci < Int.max_unsigned).
    { unfold coog_matrix_wellformed in H. destruct H.
      rewrite Forall_Znth in H13.
      specialize (H13 i). spec H13. list_solve.
      rewrite Ei in H13. simpl in H13. lia. }
    forward. (* ri = rc[i].row *)
    { entailer!!. rewrite Znth_map, Ei by list_solve. reflexivity. } 
    forward. (* ci = rc[i].row *)
    { entailer!!. rewrite Znth_map, Ei by list_solve. reflexivity. }
    rewrite !Znth_map by list_solve. rewrite Ei. simpl.
    forward_if (* if (ri==r) *) ; [forward_if (* if (ci==c) *)| ].
    + (* ri = r; ci = c *)
      forward. 
      assert (0 <> l).
      { intro. rewrite <-H15 in *. spec H11. lia. subst. 
        inversion H13. 
        rewrite Int.Z_mod_modulus_eq in H14.
        replace (4294967295) with (Int.max_unsigned) in H14 by rep_lia.
        replace (Int.modulus) with (Int.max_unsigned + 1) in H14 by rep_lia.
        clear -Hri H14.
        rewrite (Z.mod_small ri (Int.max_unsigned + 1) ltac:(lia)) in H14. lia. }
      assert (0 <> n) by lia.
      specialize (H12 ltac:(lia)).
      assert (ri = r).
      { apply repr_inj_unsigned; try lia; auto.
        inversion H. rewrite Forall_Znth in H18. specialize (H18 (i-1) ltac:(lia)). lia. }
      subst ri. subst ci.
      Exists l. Exists r. Exists c. 
      Exists ROWPTR. Exists COLIND. entailer!!. split.
      { apply partial_CSRG_duplicate; auto.
        + list_solve.
        + rewrite Ei.
          destruct (Znth (i-1) (coog_entries coog)) as [r0 c0] eqn:E0. simpl in H12. 
          destruct H12. rewrite H10, H12. auto.
        + lia. }
      split.
      { apply count_distinct_noincr.
        + list_solve.
        + replace (Znth (i-1) (coog_entries coog)) with ((r, c)).
          rewrite Ei. unfold BPO.lt. unfold coord2_le. lia.
          destruct H12. destruct (Znth (i-1) (coog_entries coog)). simpl in *. auto. }
      intros.
      replace (i+1-1) with i by lia. rewrite Ei. auto.
    + (* ri = r; ci <> c *)
      assert (0 <> l).
      { intro. rewrite <-H15 in *. spec H11. lia. subst. 
        inversion H13. 
        rewrite Int.Z_mod_modulus_eq in H15.
        replace (4294967295) with (Int.max_unsigned) in H15 by rep_lia.
        replace (Int.modulus) with (Int.max_unsigned + 1) in H15 by rep_lia.
        clear -Hri H15.
        rewrite (Z.mod_small ri (Int.max_unsigned + 1) ltac:(lia)) in H15. lia. }
      assert (0 <> n) by lia.
      assert (0 <> i) by lia.
      assert (ri = r).
      { apply repr_inj_unsigned; try lia; auto.
        inversion H. rewrite Forall_Znth in H19. specialize (H19 (i-1)). lia. } subst ri.
      assert (l < k).
      { assert (0 < i) by lia. clear H17.
        specialize (H12 ltac:(lia)). destruct H12.
        subst l k. apply count_distinct_incr'.
        + rewrite Ei. 
          pose proof (sorted_e _ H3 (i-1) i ltac:(lia) ltac:(list_solve)).
          unfold coord2_le in H10. rewrite Ei in H10. simpl in H10.
          destruct (Znth (i-1) (coog_entries coog)). simpl in H10, H12, H17. subst z z0.
          unfold BPO.lt. unfold coord2_le. simpl. lia.
        + list_solve. } 
      forward. forward. forward.
      Exists (l+1). Exists r. Exists ci.
      Exists ROWPTR. 
      Exists (upd_Znth (count_distinct (sublist 0 i (coog_entries coog))) COLIND (Vint (Int.repr ci))).
      entailer!!.
      split.
      { inversion H. rewrite Forall_Znth in H19.
        specialize (H19 i ltac:(lia)). rewrite Ei in H19. simpl in H19. lia. }
      split.
      { apply partial_CSRG_newcol; try lia; auto. }
      split.
      { apply count_distinct_incr; [|list_solve].
        pose proof (sorted_e _ H3 (i-1) i ltac:(lia) ltac:(list_solve)).
        unfold coord2_le in H10. rewrite Ei in H10.
        rewrite Ei. spec H12. lia. destruct H12.
        destruct (Znth (i-1) (coog_entries coog)). simpl in H10, H12, H19. subst z z0.
        unfold BPO.lt, coord2_le. simpl. lia. }
      intros. replace (i+1-1) with i by lia.
      rewrite Ei. simpl. lia.
    + (* r <> ri *)
      deadvars!.
      forward_while (EX r : Z, EX ROWPTR : list val,
        PROP (-1 <= r <= ri; partial_CSRG i r coog ROWPTR COLIND)
        LOCAL (temp _ci (Vint (Int.repr ci)); 
          temp _ri (Vint (Int.repr ri)); temp _i (Vint (Int.repr i));
          temp _l (Vint (Int.repr l)); temp _r (Vint (Int.repr r)); 
          temp _row_ptr pr; temp _col_ind pc; 
          temp _rc p; temp _n (Vint (Int.repr (Zlength (coog_entries coog)))); 
          temp _rows (Vint (Int.repr (coog_rows coog))))
        SEP (data_at sh2 (Tarray (Tstruct _rowcol noattr) n noattr) (map Zpair_to_valpair (coog_entries coog)) p;
          data_at sh1 (tarray tuint k) COLIND pc; data_at sh1 (tarray tuint (coog_rows coog + 1)) ROWPTR pr; 
          spec_malloc.mem_mgr gv))%assert.
      { (* entering while loop *)
        Exists r. Exists ROWPTR. entailer!!.
        split;[lia|]. destruct (zeq i 0).
        + subst i. spec H11.
          { autorewrite with sublist. simpl. lia. }
          subst r. lia.
        + specialize (H12 n0).
          pose proof (sorted_e _ H3 (i-1) i ltac:(lia) ltac:(lia)).
          rewrite Ei in H10. 
          destruct (Znth (i-1) (coog_entries coog)). simpl in H12. destruct H12. subst z z0. 
          unfold coord2_le in H10. simpl in H10. lia. }
      { (* loop guard *)
        entailer!!. }
      { (* loop body *)
        forward. forward. clear dependent ROWPTR. rename ROWPTR0 into ROWPTR.
        clear dependent r. rename r0 into r.
        forward. 
        { entailer!!. inversion H. 
          rewrite Forall_Znth in H9.
          specialize (H9 i ltac:(list_solve)).
          rewrite Ei in H9. simpl in H9. lia. }
        Exists (r+1, upd_Znth (r+1) ROWPTR (Vint (Int.repr l))).
        entailer!!. split; auto. lia.
        apply partial_CSRG_skiprow; try lia; auto.
        + rewrite Ei. simpl. lia.
        + replace (r+1-1) with r by lia. auto.
      }
      (* after the loop *)
      assert (l < k).
      { destruct (zeq i 0).
        + subst i. subst l k. autorewrite with sublist. simpl.
          apply count_distinct_bound'. lia.
        + subst l k. specialize (H12 ltac:(lia)).
          apply count_distinct_incr'; [| list_solve].
          unfold BPO.lt. pose proof (sorted_e _ H3 (i-1) i ltac:(lia) ltac:(lia)).
          rewrite Ei in *. destruct (Znth (i-1) (coog_entries coog)).
          simpl in H12. destruct H12. subst z z0. unfold coord2_le in *. simpl in *. 
          pose proof (repr_neq_e _ _ H13). lia. }
      forward. forward. forward.
      Exists (l+1). Exists r0. Exists ci. Exists ROWPTR0. 
      Exists (upd_Znth (count_distinct (sublist 0 i (coog_entries coog))) COLIND (Vint (Int.repr ci))).
      entailer!!.
      inversion H. rewrite Forall_Znth in H17.
      specialize (H17 i ltac:(list_solve)). rewrite Ei in H17. simpl in H17.
      split. lia. split. lia. split.
      { apply partial_CSRG_newrow; try lia; auto.
        + assert (r0 = ri) by lia. rewrite Ei. rewrite H18. auto.
        + intros. specialize (H12 H18). destruct (Znth (i-1) (coog_entries coog)).
          simpl in H12. destruct H12. subst z z0. simpl. 
          apply repr_neq_e. auto. assert (r0 = ri) by lia. rewrite H12. auto. }
      split.
      { destruct (zeq i 0).
        + subst i. autorewrite with sublist. 
          rewrite sublist_one by list_solve. simpl. lia.
        + apply count_distinct_incr;[| list_solve].
          pose proof (sorted_e _ H3 (i-1) i ltac:(lia) ltac:(lia)).
          rewrite Ei in *. destruct (Znth (i-1) (coog_entries coog)).
          specialize (H12 n0). simpl in H12. destruct H12. subst z z0.
          pose proof (repr_neq_e _ _ H13).
          unfold BPO.lt. unfold coord2_le in *. simpl in *. lia. }
      intros. replace (i+1-1) with i by lia.
      rewrite Ei. simpl. split; lia.
  }
  (* after the for loop *) 
  Intros l r c ROWPTR COLIND.
  forward_while (EX r : Z, EX ROWPTR : list val,
    PROP (k <= n; -1 <= r <= coog_rows coog;
      partial_CSRG n r coog ROWPTR COLIND)
    LOCAL (temp _i (Vint (Int.repr n)); temp _l (Vint (Int.repr l)); temp _r (Vint (Int.repr r));
      temp _c (Vint (Int.repr c)); temp _row_ptr pr; temp _col_ind pc; temp _rc p;
      temp _n (Vint (Int.repr (Zlength (coog_entries coog)))); temp _rows (Vint (Int.repr (coog_rows coog))))
    SEP (data_at sh2 (Tarray (Tstruct _rowcol noattr) n noattr) (map Zpair_to_valpair (coog_entries coog)) p;
      data_at sh1 (tarray tuint k) COLIND pc; data_at sh1 (tarray tuint (coog_rows coog + 1)) ROWPTR pr; 
      spec_malloc.mem_mgr gv))%assert.
  { (* entering the loop *)
    Exists r. Exists ROWPTR. entailer!!.
    subst k n.
    apply count_distinct_bound. }
  { (* loop guard *)
    entailer!!. }
  { (* loop body *)
    forward. forward. forward.
    Exists (r0+1, (upd_Znth (r0+1) ROWPTR0 (Vint (Int.repr k)))).
    entailer!!.
    2:{ subst n k. autorewrite with sublist. entailer!!. }
    split. lia.
    apply partial_CSRG_lastrows. lia.
    replace (r0 + 1 - 1) with r0 by lia. auto. }
  (* after the loop *)
  forward. Exists ROWPTR0. Exists COLIND. entailer!!.
  subst n.
  assert (r0 = coog_rows coog) by lia. rewrite <-H9. auto.
Qed.

Lemma body_coog_to_csrg : semax_body Vprog Gprog f_coog_to_csrg coog_to_csrg_spec.
Proof.
  start_function.
  set (n := Zlength coog).
  forward_call (sh, coog, p, 0, n).
  Intros coog'.
  assert (Zlength coog' = n).
  { subst n. apply Permutation_Zlength. apply Permutation_sym. exact H3. }
  forward_call (sh, coog', p).
  { subst n. entailer!!. simpl. rewrite H5. reflexivity. }
  { rewrite H5. entailer!!. }
  { subst n. split.
    + inversion H. simpl in H6, H7. 
      pose proof (@Permutation_Forall _ rowcol_range).
      unfold Morphisms.Proper, Morphisms.respectful in H8.
      specialize (H8 coog coog' H3). apply H8.
      unfold rowcol_range. rewrite Forall_forall. intros.
      rewrite Forall_forall in H7.
      destruct x as [r c].
      specialize (H7 (r, c) H9). simpl in *. rep_lia.
    + rewrite <-H5 in H4. 
      replace (0 + Zlength coog') with (Zlength coog') in H4 by lia.
      autorewrite with sublist in H4. exact H4. } 
  set (k := count_distinct coog').
  assert (0 <= k <= n).
  { subst k n. rewrite <-H5. pose proof (count_distinct_bound coog'). lia. }  
  forward_call (tarray tuint k, gv).
  { entailer!!. simpl. f_equal. f_equal. f_equal. rep_lia. }
  { simpl. rep_lia.  }
  Intros pcolind.
  forward_call (tarray tuint (rows+1), gv).
  { subst n. entailer!!. simpl. f_equal. f_equal. f_equal. 
    rewrite Z.mul_comm. f_equal. inversion H. simpl in H7. 
    replace (Z.max 0 (rows + 1)) with (rows + 1) by rep_lia.
    rewrite Int.unsigned_repr_eq.
    apply Z.mod_small. rep_lia. }
  { simpl. rep_lia. }
  Intros prowptr.
  set (coog'_matrix := Build_coog_matrix rows cols coog').
  forward_call (Ews, sh, coog'_matrix, p, pcolind, prowptr, gv).
  { simpl. entailer!!. }
  { split3. 
    + unfold coog'_matrix. unfold coog_matrix_wellformed in H.
      constructor. simpl in H|-*. rep_lia.
      simpl in H|-*. destruct H.
      pose proof (@Permutation_Forall _ (fun e : Z * Z => 0 <= fst e < rows /\ 0 <= snd e < cols)).
      unfold Morphisms.Proper in H8. unfold Morphisms.respectful in H8.
      apply (H8 coog coog' H3 H7).
    + unfold coog'_matrix. simpl in *. lia. 
    + replace (0 + n) with (Zlength coog') in H4 by list_solve. 
      unfold coog'_matrix; simpl.
      replace (sublist 0 (Zlength coog') coog') with coog' in H4 by list_solve. apply H4. } 
  Intros RC. destruct RC as (ROWPTR, COLIND). simpl in H7.
  forward_call (Tstruct _csr_matrix noattr, gv).
  Intros q.
  forward_call (tarray tdouble k, gv).
  { simpl. entailer!!. rewrite Z.mul_comm. reflexivity. }
  { simpl. rep_lia. }
  Intros csrval.
  forward. forward. forward. forward. forward. forward.  
  inversion H7. Exists coog' csr q. entailer!!.
  { unfold coog_upto in partial_CSRG_coog_csr. simpl in *.
    replace (sublist 0 (Zlength coog') coog') with coog' in partial_CSRG_coog_csr by list_solve.
    auto. }
  unfold csrg_token. Exists csrval pcolind prowptr. 
  unfold csrg_rep. Exists csrval pcolind prowptr.
  simpl. entailer!!.
  simpl in *.
  assert (Hvalsk: Zlength (csr_vals csr) = k).
  { subst k. inversion partial_CSRG_coog_csr. rewrite coog_csr_vals.
    simpl. replace (sublist 0 (Zlength coog') coog') with coog' by list_solve. reflexivity. }
  rewrite Hvalsk.
  assert (Hrows: csr_rows csr = rows).
  { inversion partial_CSRG_coog_csr. rewrite <- coog_csr_rows. unfold coog_upto. auto. }
  rewrite Hrows.
  assert (Hcolindk : Zlength (csr_col_ind csr) = k).
  { subst k.  inversion partial_CSRG_coog_csr. inversion partial_CSRG_wf.
    rewrite <- CSR_wf_vals. auto. }
  assert (Hcols: csr_cols csr = cols).
  { inversion partial_CSRG_coog_csr. rewrite <- coog_csr_cols. unfold coog_upto. auto. }
  assert (Hrplen : Zlength (csr_row_ptr csr) = rows + 1).
  { unfold csr_rows in Hrows. lia. } 
  assert (HCOLIND: COLIND = map Vint (map Int.repr (csr_col_ind csr))).
  { replace COLIND with (sublist 0 (Zlength (csr_col_ind csr)) COLIND) by list_solve. 
    rewrite partial_CSRG_colind. list_solve. }
  assert (HROWPTR: ROWPTR = map Vint (map Int.repr (csr_row_ptr csr))).
  { replace ROWPTR with (sublist 0 (rows + 1) ROWPTR) by list_solve. 
    rewrite partial_CSRG_rowptr. list_solve. }
  rewrite <-(wand_eq _ (csrg_rep' Ews csr csrval pcolind prowptr q)
    (spec_malloc.malloc_token Ews t_csr q *
     spec_malloc.malloc_token Ews (tarray tdouble (Zlength (csr_vals csr))) csrval *
     spec_malloc.malloc_token Ews (tarray tuint (Zlength (csr_vals csr))) pcolind *
     spec_malloc.malloc_token Ews (tarray tuint (csr_rows csr + 1)) prowptr)).
  2:{ rewrite Hvalsk. apply pred_ext.
    + unfold csrg_rep'. rewrite Hcolindk. rewrite Hcols. entailer!!.
    + unfold csrg_rep'. rewrite Hcolindk. rewrite Hcols. entailer!!. }
  entailer!!. unfold csrg_rep'. rewrite Hcolindk. entailer!!.
Qed.

