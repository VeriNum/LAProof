Require Import VST.floyd.proofauto.
From LAProof.C Require Import floatlib build_csr2 sparse_model spec_sparse spec_build_csr2 distinct partial_csrg.
Require Import VSTlib.spec_math.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog: funspecs := Build_CSR2_ASI ++ SparseASI ++ MathASI.

Lemma body_swap : semax_body Vprog Gprog f_swap swap_spec.
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
  { rewrite <- Hrows. inversion partial_CSRG_wf.

  assert (HCOLIND: COLIND = map Vint (map Int.repr (csr_col_ind csr))).
  { replace COLIND with (sublist 0 (Zlength (csr_col_ind csr)) COLIND) by list_solve. 
    rewrite partial_CSRG_colind. list_solve. }
  (* assert (HROWPTR: ROWPTR = map Vint (map Int.repr (csr_row_ptr csr))).
  { replace ROWPTR with (sublist 0 (rows + 1) ROWPTR) by list_solve. 
    rewrite partial_CSRG_rowptr. admit. } *)

  (* transform the same variables first*)
  (* getting rid of the P * (P -* Q) *)
  rewrite (wand_eq _ (csrg_rep' Ews csr csrval pcolind prowptr q)
    (spec_malloc.malloc_token Ews t_csr q *
     spec_malloc.malloc_token Ews (tarray tdouble (Zlength (csr_vals csr))) csrval *
     spec_malloc.malloc_token Ews (tarray tuint (Zlength (csr_vals csr))) pcolind *
     spec_malloc.malloc_token Ews (tarray tuint (csr_rows csr + 1)) prowptr)).
  2:{ rewrite Hvalsk. apply pred_ext.
  + unfold csrg_rep'. rewrite Hcolindk. rewrite Hcols. rewrite HCOLIND. entailer!!.




  unfold csrg_rep, csrg_rep'.
  Exists csrval pcolind prowptr. 
  
  
  assert (Hk1: Zlength (csr_col_ind csr) = k).
  { inversion partial_CSRG_coog_csr. subst k. inversion partial_CSRG_wf.
    rewrite <- CSR_wf_vals. rewrite coog_csr_vals.
    unfold coog_upto. simpl. autorewrite with sublist. auto. }
  assert (Hk2: count_distinct (coog_entries coog'_matrix) = k).
  { subst k. unfold coog'_matrix. simpl. auto. }
  
  
  
    
  data_at Ews (Tstruct _csr_matrix noattr) (csrval, (pcolind, (prowptr, (Vint (Int.repr rows), Vint (Int.repr cols))))) q 
  data_at Ews t_csr (v, (ci, (rp, (Vint (Int.repr (csr_rows csr)), Vint (Int.repr (csr_cols csr)))))) q

  unfold csrg_rep, csrg_rep'.  
  (* set (csr:= Build_csr_matrix Tdouble cols 
    (repeat (Zconst Tdouble 0) (length coog)) 
    (map force_signed_int COLIND) (map force_signed_int ROWPTR)). *)

  Locate build_csr_matrix_correct.
  Exists coog'. 


  

    Search (data_at) (writable_share). 
Admitted.




  start_function.
  set (n := Zlength coog).
  forward_call (sh, coog, p, 0, n).
  Intros coog'.
  assert (Zlength coog' = n).
  { subst n. apply Permutation_Zlength. apply Permutation_sym. auto. }
  forward_call (sh, coog', p).
  { subst n. entailer!!. simpl. rewrite H5. auto. }
  { rewrite H5. subst n. cancel. }
  { subst n. autorewrite with sublist in H4. split;[|auto].
    inversion H. unfold rowcol_range. simpl in *. 
    pose proof Permutation_Forall. compute in H8.
    apply (H8 _ _ coog coog'); auto.
    eapply Forall_impl. 2:{ apply H7. }
    intros. destruct a. simpl in *. rep_lia. }
  set (k := count_distinct coog').
  assert (0 <= k <= n).
  { subst k n. rewrite <-H5. pose proof (count_distinct_bound coog'). lia. }  
  assert (0 <= sizeof (tarray tdouble k) <= Ptrofs.max_unsigned).
  { simpl. rep_lia. } 
  forward_call (tarray tuint k, gv).
  { entailer!!. simpl. f_equal. f_equal. f_equal. rep_lia. } 




Lemma fold_coo_rep:
  forall sh (coo: coo_matrix Tdouble) p (maxn: Z) (rp cp vp : val), 
  !! (0 <= Zlength (coo_entries coo) <= maxn /\ maxn <= Int.max_signed 
     /\ 0 <= coo_rows coo < Int.max_signed 
     /\ 0 <= coo_cols coo < Int.max_signed /\ coo_matrix_wellformed coo) &&
  data_at sh t_coo (rp, (cp, (vp, (Vint (Int.repr (Zlength (coo_entries coo))), (Vint (Int.repr maxn), 
                     (Vint (Int.repr (coo_rows coo)), 
                     (Vint (Int.repr (coo_cols coo))))))))) p *
  data_at sh (tarray tuint maxn)
    (map (fun e => Vint (Int.repr (fst (fst e)))) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-(Zlength (coo_entries coo)))) rp *
  data_at sh (tarray tuint maxn)
    (map (fun e => Vint (Int.repr (snd (fst e)))) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-(Zlength (coo_entries coo)))) cp *
  data_at sh (tarray tdouble maxn)
    (map (fun e => Vfloat (snd e)) (coo_entries coo) 
     ++ Zrepeat Vundef (maxn-(Zlength (coo_entries coo)))) vp
 |-- coo_rep sh coo p.
Proof. intros. unfold coo_rep. Exists maxn rp cp vp. entailer!!. Qed.

Lemma fold_csr_rep': forall sh (csr: csr_matrix Tdouble) (v: val) (ci: val) (rp: val) (p: val),
  data_at sh t_csr (v,(ci,(rp,(Vint (Int.repr (csr_rows csr)), Vint (Int.repr (csr_cols csr)))))) p *
  data_at sh (tarray tdouble (Zlength (csr_col_ind csr))) (map Vfloat (csr_vals csr)) v * 
  data_at sh (tarray tuint (Zlength (csr_col_ind csr))) (map Vint (map Int.repr (csr_col_ind csr))) ci *
  data_at sh (tarray tuint (csr_rows csr + 1)) (map Vint (map Int.repr (csr_row_ptr csr))) rp
  |-- csr_rep' sh csr v ci rp p.
Proof. intros. unfold csr_rep'. cancel. Qed.

Lemma body_coo_to_csr_matrix: semax_body Vprog Gprog f_coo_to_csr_matrix coo_to_csr_matrix_spec.
Proof.
start_function.
unfold coo_rep.
Intros maxn rp cp vp.
assert_PROP (sizeof tdouble * Zlength(coo_entries coo) <= Ptrofs.max_unsigned) as Hbound. {
  entailer. apply prop_right. clear - H0 H12.
  autorewrite with sublist in H12.
  destruct H12 as [? [_ [? _]]]. destruct vp; try contradiction.
  simpl in H1|-*. rewrite Z.max_r in H1 by rep_lia. rep_lia.
}
forward.  (* n = p->n; *)
set (n := Zlength (coo_entries coo)).
forward_call (sh,coo,p,0,n).  (* coo_quicksort(p,0,n); *)
  unfold coo_rep; Exists maxn rp cp vp; entailer!!.
Intros coo'.
clear rp cp vp.
eapply coo_matrix_wellformed_equiv in H; try apply H4.
generalize H4; intros [? [? ?]].
apply Permutation_Zlength in H8.
subst n.
rewrite H8 in H0 |-*.
set (n := Zlength (coo_entries coo')).
autorewrite with sublist in H5.
rewrite H6 in H2. rewrite H7 in H3.
clear H6 H7 H8.
clear maxn H0 H1.
forward_call.  (* k = coo_count(p); *)
set (k := count_distinct _).
forward. (* rows = p->rows; *)
assert_PROP (n <= maxn <= Int.max_signed) as Hn by entailer!.
clear H1; rename Hn into H1.  
forward. (* prow_ind = p->row_ind; *)
forward. (* pcol_ind = p->col_ind; *)
forward. (* pval = p->val; *)
forward_call (Tstruct _csr_matrix noattr, gv).  (* q = surely_malloc(sizeof(struct csr_matrix)); *)
Intros q. 
assert (Hbound' := count_distinct_bound (coo_entries coo')).
fold k in Hbound'.
forward_call (tarray tdouble k, gv).  (* val = surely_malloc(k*sizeof(double)); *)
 entailer!!.
  simpl. do 3 f_equal. rep_lia.
  simpl. rep_lia.
Intros val_p.
forward_call (tarray tuint k, gv). (* col_ind = surely_malloc(k*sizeof(uint)); *)
  entailer!!.
  simpl. do 3 f_equal. rep_lia. simpl; rep_lia.
Intros colind_p.
forward_call (tarray tuint (coo_rows coo+1), gv). (* row_ptr = surely_malloc((rows+1)*sizeof(tuint)); *)
  entailer!!; simpl; rewrite (proj1 H4). do 3 f_equal. rep_lia.
  simpl. rewrite (proj1 H4). rep_lia. 
rewrite (proj1 H4).
Intros rowptr_p.
forward. (* r=-1; *)
forward. (* c=0; *)
forward. (* l=0; *)
freeze FR1 := (spec_malloc.mem_mgr _) 
  (spec_malloc.malloc_token _ _ rowptr_p)
  (spec_malloc.malloc_token _ _ colind_p)
  (spec_malloc.malloc_token _ _ val_p)
  (spec_malloc.malloc_token _ _ q). 
forward_for_simple_bound n (* for (i=0;i<n; i++) *)
 (EX i:Z, EX l:Z, EX r:Z, EX c:Z, 
  EX ROWPTR: list val, EX COLIND: list val, EX VAL: list val,
  PROP(0<=l<=k; l<=i<=n; -1 <= r < coo_rows coo'; 0 <= c <= coo_cols coo';
       partial_CSR i r coo' ROWPTR COLIND VAL;
       l = count_distinct (sublist 0 i (coo_entries coo'));
       l=0 -> r=-1;
       i<>0 -> r=(fst (fst (Znth (i-1) (coo_entries coo'))))%Z /\ c = snd (fst (Znth (i-1) (coo_entries coo')))) 
 LOCAL (temp _l (Vint (Int.repr l));
       temp _r (Vint (Int.repr r)); temp _c (Vint (Int.repr c));
       temp _row_ptr rowptr_p; temp _col_ind colind_p; temp _val val_p;
       temp _q q;
       temp _pval vp; temp _pcol_ind cp; temp _prow_ind rp;
       temp _rows (Vint (Int.repr (coo_rows coo')));
       temp _n (Vint (Int.repr n));
       temp _p p)
  SEP(FRZL FR1;
      data_at Ews (tarray tuint (coo_rows coo' + 1)) ROWPTR rowptr_p;
      data_at Ews (tarray tuint k) COLIND colind_p; 
      data_at Ews (tarray tdouble k) VAL val_p;
      data_at_ Ews (Tstruct _csr_matrix noattr) q;
      data_at sh t_coo
        (rp, (cp, (vp,
          (Vint (Int.repr (Zlength (coo_entries coo'))),
           (Vint (Int.repr maxn),
            (Vint (Int.repr (coo_rows coo')), Vint (Int.repr (coo_cols coo')))))))) p;
       data_at sh (tarray tuint maxn)
         (map (fun e : Z * Z * ftype Tdouble => Vint (Int.repr (fst (fst e))))
           (coo_entries coo') ++ Zrepeat Vundef (maxn - Zlength (coo_entries coo')))
         rp;
       data_at sh (tarray tuint maxn)
         (map (fun e : Z * Z * ftype Tdouble => Vint (Int.repr (snd (fst e))))
        (coo_entries coo') ++ Zrepeat Vundef (maxn - Zlength (coo_entries coo')))
         cp;
       data_at sh (tarray tdouble maxn)
         (map (fun e : Z * Z * float => Vfloat (snd e)) (coo_entries coo') ++
          Zrepeat Vundef (maxn - Zlength (coo_entries coo'))) vp))%assert.
-
 Exists 0 (-1) 0
     (Zrepeat Vundef (coo_rows coo' + 1)) (Zrepeat Vundef k) (Zrepeat Vundef k).
 entailer!!.  
  apply partial_CSR_0; auto.
  pose proof count_distinct_bound (coo_entries coo'). rep_lia.  
- forward. (* ri=prow_ind[i]; *)
   entailer!!. list_solve.
  rewrite Znth_app1 by Zlength_solve; rewrite Znth_map by rep_lia.
  forward. (* ci=pcol_ind[i]; *)
   entailer!!. list_solve.
  rewrite Znth_app1 by Zlength_solve; rewrite Znth_map by rep_lia.
  forward. (* x = pval[i]; *)
   entailer!!.
   list_simplify. rewrite Znth_map.
   2: change (Zlength _) with n; lia. hnf; auto.
  rewrite Znth_app1 by Zlength_solve.
  rewrite Znth_map by (change (Zlength _) with n; rep_lia).
  destruct (Znth i (coo_entries coo')) as [[ri ci] xi] eqn:Hi.
  simpl snd; simpl fst.
  assert (H99 := coo_entry_bounds H i ltac:(lia)).
  rewrite  Hi in H99; simpl in H99. destruct H99 as [Hri Hci].
  assert (Hk: 0 < k) by (apply count_distinct_bound'; lia).
  forward_if (* if (ri==r) *) ; [forward_if (* if (ci==c) *)| ].
  + (* ri = r, ci = c *)
    subst r ci.
    assert (is_float (Znth (l-1) VAL))
      by (eapply partial_CSR_VAL_defined; try eassumption; lia).
    assert (Hl: 0<>l) by (intro; subst; lia).   
    clear H13.   
    forward. (* t' = val[l-1]; *)
    forward. (* val[l-1] = t'+x; *)
    destruct (Znth (l-1) VAL) eqn:VALl; try contradiction. clear H15.
    pose (VAL' := upd_Znth (l-1) VAL (Vfloat (Float.add f (snd (Znth i (coo_entries coo')))))).
    Exists l ri c ROWPTR COLIND VAL'.
    entailer!!.
    assert (i<>0). { intro; subst. rewrite sublist_nil in *. compute in Hl. auto. }
    specialize (H14 H12). destruct H14.
    rewrite Z.add_simpl_r. rewrite Hi. simpl. split3; auto.    
    2:{ clear - H13 H14 Hi H12 H6. subst.
        forget (coo_entries coo') as al.
        assert (0<i<n) by lia. clear H6 H12.
        assert (fst (Znth (i-1) al) = fst (Znth i al))
            by (rewrite Hi, <- surjective_pairing; auto).
        clear Hi; rename H0 into Hi. 
       apply count_distinct_noincr; auto.
       rewrite <- BPO_eqv_iff in Hi. unfold BPO.lt, BPO.eqv in *. tauto.
        }
     eapply partial_CSR_duplicate; try eassumption; try lia.
     destruct (Znth (i-1) (coo_entries coo')) as [[??]?].
     rewrite Hi. simpl in *; subst. auto.
  + (* ri = r, ci <> c *)
    subst r.
    assert (Hl: 0<>l) by (intro; subst; lia).   
    assert (Hi': i<>0). { intro; subst. rewrite sublist_nil in *. compute in Hl. auto. }
    assert (Hl': l<k). {
      clear - H12 H6 Hi H14 H16 Hk H5.
      destruct (zlt 0 i).
      * clear Hk. 
        spec H14; [rep_lia |]. destruct H14 as [_ H14]; subst.
        forget (coo_entries coo') as bl. subst k.
        destruct (Znth (i-1) bl) as [[r' c'] x'] eqn:H'. simpl in *.
        assert (fst (Znth i bl) <> fst (Znth (i-1) bl)). rewrite Hi,H'. simpl. congruence.
        clear ci c' H16 H' Hi ri r' xi x'.
        subst n.
        assert (0 <= i-1 < Zlength bl-1) by lia. clear H6 l0.
        apply count_distinct_incr'; auto.
        pose proof (sorted_e _ H5 (i-1) i) ltac:(lia) ltac:(lia).
       rewrite <- BPO_eqv_iff in H. unfold BPO.lt, BPO.eqv in *. tauto.        
      * assert (i=0) by lia. subst. autorewrite with sublist.
        unfold count_distinct. simpl. auto.
    }
    forward. (* c=ci; *)
    forward. (* col_ind[l]=ci; *)
    forward. (* val[l]=x; *)
    forward. (* l++; *)
    Exists (l+1) ri ci ROWPTR
     (upd_Znth l COLIND (Vint (Int.repr ci))) 
     (upd_Znth l VAL (Vfloat (snd (Znth i (coo_entries coo'))))).
    entailer!!.
    specialize (H14 Hi'). destruct H14 as [H14a H14b].
    split3; [ | | split].
    * eapply partial_CSR_newcol; try eassumption; try lia. rewrite Hi. auto.
    * apply count_distinct_incr; try lia.
      pose proof (sorted_e _ H5 (i-1) i) ltac:(lia) ltac:(lia).
      assert (~BPO.eqv (Znth (i-1) (coo_entries coo')) (Znth i (coo_entries coo'))). {
        rewrite BPO_eqv_iff. rewrite Hi. simpl.
      intro; subst. apply H16. rewrite H14. auto.
      }
      clear - H12 H14. unfold BPO.lt, BPO.eqv in *; tauto.
    * rewrite Z.add_simpl_r, Hi; auto.
    * rewrite Z.add_simpl_r, Hi; auto. 
  + (* ri <> r *)
    deadvars!.
  (* while (r<=rows) *) 
  forward_while (EX r: Z, EX ROWPTR: list val,
   PROP ( -1 <= r <= ri; partial_CSR i r coo' ROWPTR COLIND VAL )
   LOCAL (temp _x (Vfloat (snd (Znth i (coo_entries coo'))));
   temp _ci (Vint (Int.repr ci)); temp _ri (Vint (Int.repr ri));
   temp _i (Vint (Int.repr i)); temp _l (Vint (Int.repr l));
   temp _r (Vint (Int.repr r));
   temp _row_ptr rowptr_p; temp _col_ind colind_p; 
   temp _val val_p; temp _q q; temp _pval vp; temp _pcol_ind cp;
   temp _prow_ind rp; temp _rows (Vint (Int.repr (coo_rows coo')));
   temp _n (Vint (Int.repr n)); temp _p p)
   SEP (FRZL FR1;
   data_at Ews (tarray tuint (coo_rows coo' + 1)) ROWPTR rowptr_p;
   data_at Ews (tarray tuint k) COLIND colind_p;
   data_at Ews (tarray tdouble k) VAL val_p;
   data_at_ Ews (Tstruct _csr_matrix noattr) q;
   data_at sh t_coo
     (rp,
      (cp,
       (vp,
        (Vint (Int.repr (Zlength (coo_entries coo'))),
         (Vint (Int.repr maxn),
          (Vint (Int.repr (coo_rows coo')),
           Vint (Int.repr (coo_cols coo')))))))) p;
   data_at sh (tarray tuint maxn)
     (map
        (fun e : Z * Z * ftype Tdouble => Vint (Int.repr (fst (fst e))))
        (coo_entries coo') ++
      Zrepeat Vundef (maxn - Zlength (coo_entries coo'))) rp;
   data_at sh (tarray tuint maxn)
     (map
        (fun e : Z * Z * ftype Tdouble => Vint (Int.repr (snd (fst e))))
        (coo_entries coo') ++
      Zrepeat Vundef (maxn - Zlength (coo_entries coo'))) cp;
   data_at sh (tarray tdouble maxn)
     (map (fun e : Z * Z * float => Vfloat (snd e)) (coo_entries coo') ++
      Zrepeat Vundef (maxn - Zlength (coo_entries coo'))) vp))%assert.
  * Exists r ROWPTR. entailer!!.
    destruct (zeq i 0).
    -- subst. rewrite sublist_nil in *. rewrite H13 by reflexivity. lia.
    -- destruct (H14 n0). rewrite H12.
       pose proof coo_entry_bounds H (i-1) ltac:(lia). 
       replace ri with (fst (fst (Znth i (coo_entries coo')))) by (rewrite Hi; auto).
       clear - n0 H6 H17 H5.
    split; try lia.
    pose proof sorted_e1 _ H5 (i-1) ltac:(lia).
    rewrite Z.sub_add in H.
    destruct H; lia. 
  * entailer!!.
  * clear ROWPTR H11. rename ROWPTR0 into ROWPTR.
    clear dependent r. rename r0 into r.
    forward. (* t' = r; *)
    forward. (* r = t'+1; *)
    forward. (* row_ptr[t']=l; *)
    Exists (r+1, upd_Znth (r+1) ROWPTR (Vint (Int.repr l))).
    entailer!!. split; auto. lia.
   apply partial_CSR_skiprow; auto. rewrite Hi; simpl; lia.
   rewrite Z.add_simpl_r; auto.

  *
   assert (r0 = ri) by lia. subst r0.
   clear HRE H16.
   forward. (* c=ci; *)
   assert (H87: 0 <= count_distinct (sublist 0 i (coo_entries coo')) < k). {
     subst k.
     split; try lia.
     destruct (zeq i 0). list_solve.
     destruct (H14 n0).
     apply count_distinct_incr'.
     pose proof (sorted_e _ H5 (i-1) i) ltac:(lia) ltac:(lia).
     assert (~BPO.eqv (Znth (i-1) (coo_entries coo')) (Znth i (coo_entries coo'))). {
        rewrite BPO_eqv_iff. rewrite Hi. simpl. intro. rewrite H20 in *. simpl in *. lia.
     } 
     clear - H19 H20. unfold BPO.lt, BPO.eqv in *. tauto.
     lia.
   }
   forward. (* col_ind[l]=ci; *)
   forward. (* val[l]=x; *)
   forward. (* l++; *)
   Exists (l+1) ri ci ROWPTR0 (upd_Znth l COLIND (Vint (Int.repr ci)))
          (upd_Znth l VAL (Vfloat (snd (Znth i (coo_entries coo'))))).
   entailer!!.
   rewrite Z.add_simpl_r, Hi. simpl.
   split3; [ | | split]; auto; try lia.
   assert (i<>0 -> fst (fst (Znth (i-1) (coo_entries coo'))) <> ri)
       by (clear - H14 H15; lia). 
   clear r H15 H14 H9 H11 H13.
   2:{ destruct (zeq i 0).
        - subst. autorewrite with sublist. rewrite sublist_one by lia. reflexivity. 
        - destruct (H14 n0). apply count_distinct_incr ; [ | lia].
          pose proof (sorted_e _ H5 (i-1) i) ltac:(lia) ltac:(lia).
          assert (~BPO.eqv (Znth (i - 1) (coo_entries coo'))
                        (Znth i (coo_entries coo'))). {
           rewrite Hi. rewrite BPO_eqv_iff. 
          destruct (Znth (i-1) (coo_entries coo')); subst. simpl.  intro; subst; simpl in *; lia. 
          }
          clear - H18 H19; unfold BPO.eqv, BPO.lt in *; tauto.
    }
   apply partial_CSR_newrow; auto.
 - Intros l r c ROWPTR0 COLIND VAL.
   deadvars!.
   autorewrite with sublist in H11.
   forward. (* cols = p->cols; *)
   rename r into r1.
   (* while (r<=rows) *)
forward_while
 (EX r:Z,
  EX ROWPTR: list val,
  PROP(k<=n; -1 <= r <= coo_rows coo';
       partial_CSR n r coo' ROWPTR COLIND VAL)
  LOCAL (temp _l (Vint (Int.repr k));
       temp _r (Vint (Int.repr r)); temp _cols (Vint (Int.repr (coo_cols coo')));
       temp _row_ptr rowptr_p; temp _col_ind colind_p; temp _val val_p;
       temp _q q;
       temp _rows (Vint (Int.repr (coo_rows coo'))))
  SEP(FRZL FR1;
      data_at Ews (tarray tuint (coo_rows coo' + 1)) ROWPTR rowptr_p;
      data_at Ews (tarray tuint k) COLIND colind_p; 
      data_at Ews (tarray tdouble k) VAL val_p;
      data_at_ Ews (Tstruct _csr_matrix noattr) q;
      data_at sh t_coo
        (rp, (cp, (vp,
          (Vint (Int.repr (Zlength (coo_entries coo'))),
           (Vint (Int.repr maxn),
            (Vint (Int.repr (coo_rows coo')), Vint (Int.repr (coo_cols coo')))))))) p;
       data_at sh (tarray tuint maxn)
         (map (fun e : Z * Z * ftype Tdouble => Vint (Int.repr (fst (fst e))))
           (coo_entries coo') ++ Zrepeat Vundef (maxn - Zlength (coo_entries coo')))
         rp;
       data_at sh (tarray tuint maxn)
         (map (fun e : Z * Z * ftype Tdouble => Vint (Int.repr (snd (fst e))))
        (coo_entries coo') ++ Zrepeat Vundef (maxn - Zlength (coo_entries coo')))
         cp;
       data_at sh (tarray tdouble maxn)
         (map (fun e : Z * Z * float => Vfloat (snd e)) (coo_entries coo') ++
          Zrepeat Vundef (maxn - Zlength (coo_entries coo'))) vp))%assert.
 + Exists r1 ROWPTR0. entailer!!.
 + entailer!!.
 + clear r1 c H13 H9 H8 H10 H12.
   forward. (* t'= r; *)
   forward. (* r = t'+1; *)
   forward. (* row_ptr[t']=l; *)
   Exists (r+1, (upd_Znth (r+1) ROWPTR (Vint (Int.repr k)))).
   entailer!!.
   split. lia.
   apply partial_CSR_lastrows; auto. lia.
   rewrite Z.add_simpl_r; auto.
 +
   clear r1 c H13 H8 H9 H10 H12.
   forward. (* q->val = val; *)
   forward. (* q->col_ind = col_ind; *)
   forward. (* q->row_ptr = row_ptr; *)
   forward. (* q->rows = rows; *)
   forward. (* c->cols = cols; *)
Ltac entailer_for_return ::= idtac.
   assert (l=k) by lia. subst l.
   clear H7 H6 H0 H14.
   fold n in Hbound'. 
   assert (r = coo_rows coo') by lia.
   subst r. clear HRE H15 ROWPTR0 H8.
   forward. (* return q; *)
   entailer!!.
   destruct (partial_CSR_properties _ _ _ _ H16)
    as [m [csr [H6a [H6b [H6c [H6d [H6e [H6f [H6g [H6h H6i]]]]]]]]]].
   fold k in H6f, H6i.
   Exists coo' csr m q.
   assert (Hcoo: coo_to_matrix coo m). {
     eapply coo_to_matrix_equiv; try eassumption.
     apply coo_matrix_equiv_symm; auto.
   }
   thaw FR1.
   entailer!!.
   sep_apply fold_coo_rep; auto.
   fold n. split3; try lia. split3; try lia; auto.
   rewrite H6c, H6d.
   assert_PROP (matrix_rows m = csr_rows csr) as Hrows'. {
    entailer. apply prop_right. destruct csr.
    unfold sparse_model.csr_rows, sparse_model.csr_row_ptr in *. simpl. list_solve.
   }
   rewrite Hrows'.
   fold t_csr.
   rewrite <- H6f.
   sep_apply fold_csr_rep'.
   unfold csr_token, csr_rep.
   Exists csr H6a.
   Exists val_p colind_p rowptr_p.
   unfold csr_token'.
   Exists val_p colind_p rowptr_p.
   cancel.
   apply -> wand_sepcon_adjoint.
   rewrite H6f, H6i. cancel.
Qed.