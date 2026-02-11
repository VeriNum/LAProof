Require Import VST.floyd.proofauto.
From LAProof.C Require Import floatlib sparse_model distinct partial_csr.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Lemma coog_entry_bounds [coog : coog_matrix] :
  coog_matrix_wellformed coog ->
  forall i, 
  0 <= i < Zlength (coog_entries coog) ->
  0 <= fst (Znth i (coog_entries coog)) < coog_rows coog /\
  0 <= snd (Znth i (coog_entries coog)) < coog_cols coog.
Proof.
  intros.
  unfold coog_matrix_wellformed in H.
  destruct H as [[? ?] ?].
  rewrite Forall_Znth in H2.
  apply H2. exact H0.
Qed.

Definition coog_upto (i : Z) (coog : coog_matrix) :=
  Build_coog_matrix (coog_rows coog) (coog_cols coog) (sublist 0 i (coog_entries coog)).

Definition cd_upto_coog (i : Z) (coog : coog_matrix) : Z :=
  count_distinct (sublist 0 i (coog_entries coog)).

Definition entries_correspond_coog {t} (coog : coog_matrix) (csr : csr_matrix t) :=
  forall h,
  0 <= h < Zlength (coog_entries coog) ->
  let '(r, c) := Znth h (coog_entries coog) in 
  let k := cd_upto_coog (h + 1) coog - 1 in 
    Znth r (csr_row_ptr csr) <= k < Znth (r + 1) (csr_row_ptr csr) /\
    Znth k (csr_col_ind csr) = c.

Definition no_extra_zeros_coog {t} (coog : coog_matrix) (csr : csr_matrix t) :=
  forall r k, 0 <= r < coog_rows coog ->
    Znth r (csr_row_ptr csr) <= k < Znth (r+1) (csr_row_ptr csr) ->
    let c := Znth k (csr_col_ind csr) in 
    In (r, c) (coog_entries coog).

Inductive coog_csr {t} (coog : coog_matrix) (csr : csr_matrix t) : Prop :=
  build_coog_csr : forall 
    (coog_csr_rows : coog_rows coog = csr_rows csr)
    (coog_csr_cols : coog_cols coog = csr_cols csr)
    (coog_csr_vals : Zlength (csr_vals csr) = count_distinct (coog_entries coog))
    (coog_csr_entries : entries_correspond_coog coog csr)
    (coog_csr_zeros : no_extra_zeros_coog coog csr),
    coog_csr coog csr.

Inductive partial_CSRG (h : Z) (r : Z) (coog : coog_matrix) 
  (rowptr : list val) (colind : list val) : Prop :=
  build_partial_CSRG : forall 
    (partial_CSRG_coog : coog_matrix_wellformed coog)
    (partial_CSRG_coog_sorted : sorted coord2_le (coog_entries coog))
    (partial_CSRG_i : 0 <= h <= Zlength (coog_entries coog))
    (partial_CSRG_r : -1 <= r <= coog_rows coog)
    (partial_CSRG_r' : Forall (fun e => fst e <= r) (coog_entries (coog_upto h coog)))
    (partial_CSRG_r'' : Forall (fun e => fst e >= r) (sublist h (Zlength (coog_entries coog)) (coog_entries coog)))
    (csr : csr_matrix Tdouble)
    (partial_CSRG_wf : csr_matrix_wellformed csr)
    (partial_CSRG_coog_csr : coog_csr (coog_upto h coog) csr)
    (partial_CSRG_colind : sublist 0 (Zlength (csr_col_ind csr)) colind = map (Vint oo Int.repr) (csr_col_ind csr))
    (partial_CSRG_rowptr : sublist 0 (r + 1) rowptr = map (Vint oo Int.repr) (sublist 0 (r + 1) (csr_row_ptr csr)))
    (partial_CSRG_colind' : Zlength colind = count_distinct (coog_entries coog))
    (partial_CSRG_rowptr' : Zlength rowptr = coog_rows coog + 1)
    (partial_CSRG_dbound : count_distinct (coog_entries coog) <= (Int.max_unsigned))
    , partial_CSRG h r coog rowptr colind.

Lemma cd_upto_coog_pos i coog :
  0 <= cd_upto_coog i coog.
Proof.
  unfold cd_upto_coog.
  pose proof (count_distinct_bound (sublist 0 i (coog_entries coog))). lia. 
Qed.

Lemma last_cons {A : Type} (x : A) l default :
  last (x :: l) default = x \/
  last (x :: l) default = last l default.
Proof.
  destruct l.
  + left. simpl. auto.
  + right. simpl. auto.
Qed.

Lemma last_repeat {A : Type} (a : A) (n : nat) default :
  (n > 0)%nat -> last (repeat a n) default = a.
Proof.
  induction n as [|n']; intros.
  + inversion H.
  + destruct n' as [|n''].
    - simpl. auto.
    - replace (repeat a (S (S n''))) with (a :: repeat a (S n'')) by list_solve.
    pose proof (last_cons a (repeat a (S n'')) default).
    destruct H0; auto.
    apply IHn'. lia.
Qed.
    
Lemma last_Zrepeat {A : Type} (a : A) n default :
  n > 0 ->
  last (Zrepeat a n) default = a.
Proof.
  intros.
  unfold Zrepeat. apply last_repeat. lia.
Qed.

Lemma repeat_not_nil {A : Type} (a : A) n :
  (n > 0)%nat ->
  repeat a n <> [].
Proof.
  destruct n as [|n']; intros.
  inversion H.
  simpl. intros contra. inversion contra.
Qed.

Lemma Zrepeat_not_nil {A : Type} (a : A) n :
  n > 0 ->
  Zrepeat a n <> [].
Proof.
  unfold Zrepeat. intros. apply repeat_not_nil. lia.
Qed.

Lemma sublist_longer {A : Type} lo hi (l : list A) :
  Zlength l <= hi ->
  sublist lo hi l = sublist lo (Zlength l) l.
Proof.
  intros. unfold sublist. simpl. f_equal.
  generalize dependent hi. induction l as [|x l']; intros.
  + rewrite !firstn_nil. auto.
  + destruct (hi >? 0) eqn:E.
    2:{ assert (hi <= 0) by lia.
      rewrite Zlength_cons in H.
      pose proof (Zlength_nonneg l'). lia. }
    assert (hi > 0) by lia.
    replace (Z.to_nat hi) with (S (Z.to_nat (hi - 1))) by lia.
    rewrite firstn_cons.
    rewrite Zlength_cons.
    rewrite Z2Nat.inj_succ by list_solve.
    rewrite firstn_cons. f_equal.
    destruct (hi - 1 >? 0) eqn:E1.
    - apply IHl'. list_solve.
    - assert (hi = 1) by lia. subst hi.
      replace (Z.to_nat (1 - 1)) with O by lia. rewrite firstn_O.
      rewrite Zlength_cons in H.
      assert (Zlength l' <= 0) by lia.
      pose proof (Zlength_nonneg l').
      replace (Zlength l') with 0 by lia.
      replace (Z.to_nat 0) with O by lia. 
      rewrite firstn_O. auto.
Qed.


Lemma partial_CSRG_rowptr' : forall {t} r (coog : coog_matrix) (csr : csr_matrix t),
  coog_matrix_wellformed coog ->
  csr_matrix_wellformed csr ->
  coog_csr coog csr ->
  -1 <= r <= coog_rows coog ->
  Forall (fun e => fst e <= r) (coog_entries coog) ->
  sublist (r + 1) (coog_rows coog + 1) (csr_row_ptr csr) = Zrepeat (Zlength (csr_vals csr)) (coog_rows coog - r).
  (* All remaining rows are empty *)
Proof.
  intros.
  inversion_clear H1.
  unfold csr_rows in *.
  apply Znth_eq_ext. list_solve.
  intros.
  rewrite Znth_sublist by list_solve.
  rewrite Znth_Zrepeat by list_solve.
  autorewrite with sublist in H1.
  inversion_clear H0.
  unfold csr_rows in *.
  pose proof rowptr_sorted_e _ CSR_wf_sorted (i+(r+1)) (Zlength (csr_row_ptr csr) - 1) ltac:(list_solve).
  destruct H0 as [[? ?] _].
  destruct (zlt (Znth (i+(r+1)) (csr_row_ptr csr)) (Zlength (csr_vals csr))); [ | lia].
  exfalso. clear H0.
  clear CSR_wf_rowsorted.
  assert (exists i', i + (r + 1) <= i' < coog_rows coog /\ Znth i' (csr_row_ptr csr) < Znth (i' + 1) (csr_row_ptr csr)).
  { rewrite CSR_wf_vals' in l.
    rewrite coog_csr_rows in H1|-*.
    clear -H1 CSR_wf_sorted l H2. destruct H2 as [H2 _].
    unfold csr_rows in *.
    forget (csr_row_ptr csr) as al.
    assert (0 <= i+(r+1) < Zlength al) by lia; clear H1 H2.
    forget (i+(r+1)) as r'. clear r i. rename r' into r.
    pose (bl := sublist r (Zlength al) al).
    assert (Znth 0 bl < Znth (Zlength bl - 1) bl) by (subst bl; list_solve).
    assert (exists i, 0 <= i < Zlength bl-1 /\ Znth i bl < Znth (i+1) bl). 
    2:{ destruct H1 as [i [? ?]]. exists (i+r); split. subst bl; list_solve. subst bl; list_solve. }
    assert (list_solver.sorted Z.le bl). {
    clear - CSR_wf_sorted H.
    intros x y [? ?].
    subst bl.
    rewrite !Znth_sublist by list_solve.
    apply (rowptr_sorted_e _ CSR_wf_sorted (x+r) (y+r) ltac:(list_solve)). }
      assert (0 < Zlength bl) by (subst bl; list_solve).
    clearbody bl. clear - H1 H0 H2.
    destruct bl; [list_solve|].
    autorewrite with sublist in *. clear H2.
    unfold Z.succ in H0. rewrite Z.add_simpl_r in H0.
    revert z H0 H1; induction bl; simpl; intros.
    list_solve.
    autorewrite with sublist in *.
    rewrite Znth_pos_cons in H0 by list_solve.
    unfold Z.succ in H0. rewrite Z.add_simpl_r in H0.
    destruct (zlt z a).
    exists 0; list_solve.
    assert (a=z). { specialize (H1 0 1). list_solve. }
    subst a.
    destruct (IHbl z) as [i [? ?]].
    list_solve. intros x y ?; specialize (H1 (x+1) (y+1)).
    destruct H.
    rewrite !(Znth_pos_cons (_ + 1)) in H1 by list_solve.
    rewrite !Z.add_simpl_r in H1.
    apply H1. list_solve.
    exists (i+1). list_solve. }
  destruct H0 as [i' [? ?]].
  unfold csr_rows in *.
  pose proof coog_csr_zeros i' (Znth i' (csr_row_ptr csr)) ltac:(lia).
  specialize (H6 ltac:(lia)).
  rewrite Forall_forall in H3.
  apply In_Znth in H6. destruct H6 as [b [??]].
  specialize (H3 (Znth b (coog_entries coog))).
  spec H3. apply Znth_In. list_solve.
  rewrite H7 in H3. simpl in H3. lia.
Qed.

Lemma coog_upto_wellformed i coog :
  0 <= i <= Zlength (coog_entries coog) ->
  coog_matrix_wellformed coog ->
  coog_matrix_wellformed (coog_upto i coog).
Proof.
  intros Hi Hwf. inversion_clear Hwf.
  constructor; [split|].
  + unfold coog_upto. simpl. lia.
  + unfold coog_upto. simpl. lia.
  + rewrite Forall_Znth. intros i0 Hi0. unfold coog_upto in Hi0. simpl in Hi0.
    rewrite Zlength_sublist in Hi0 by lia.
    unfold coog_upto; simpl. 
    rewrite Forall_Znth in H0. specialize (H0 i0).
    spec H0. lia. rewrite Znth_sublist by list_solve.
    replace (i0 + 0) with i0 by lia. auto.
Qed.


Lemma BPO2_eqv_iff: forall a b, @BPO.eqv _ _ Coord2BPO a b <-> a = b.
Proof.
  intros. destruct a as [a1 a2]. destruct b as [b1 b2].
  split; intros.
  + unfold BPO.eqv in H. unfold coord2_le in H. destruct H.
    simpl in *. destruct H, H0; try lia.
    assert (a2 = b2) by lia. destruct H. rewrite H, H1. auto.
  + unfold BPO.eqv. unfold coord2_le. rewrite H. lia. 
Qed.

Lemma coord2_sorted_e : forall (al : list (Z * Z)) (H : sorted coord2_le al)
  (i j : Z),
  0 <= i <= j /\ j < Zlength al -> coord2_le (Znth i al) (Znth j al).
Proof.
  intros. destruct (zeq i j).
  + subst i. unfold coord2_le. right. lia.
  + destruct H0. apply sorted_e; auto. lia.
Qed. 

Lemma partial_CSRG_duplicate:
    forall h r coog ROWPTR COLIND,
    0 < h < Zlength (coog_entries coog) ->
    (Znth (h-1) (coog_entries coog)) = (Znth h (coog_entries coog)) ->
    r = (fst (Znth (h-1) (coog_entries coog))) ->
    (* Znth (cd_upto_coog h coog - 1) VAL = Vfloat f -> *)
    partial_CSRG h r coog ROWPTR COLIND ->
    partial_CSRG (h+1) r coog ROWPTR COLIND .
Proof.
  intros. rename H0 into Hdup.
  inversion_clear H2. apply build_partial_CSRG with csr; auto.
  + (* partial_CSRG_i *)
    split; try lia.
  + (* partial_CSRG_r' *)
    unfold coog_upto in partial_CSRG_r'. simpl in partial_CSRG_r'.
    unfold coog_upto. simpl.
    rewrite sublist_last_1 by list_solve.
    rewrite Forall_app. split; auto.
    apply Forall_cons; [|apply Forall_nil].
    rewrite <-Hdup. rewrite H1. lia.
  + (* partial_CSRG_r''*)
    rewrite (sublist_split h (h + 1)) in partial_CSRG_r'' by list_solve.
    rewrite Forall_app in partial_CSRG_r''.
    destruct partial_CSRG_r''. auto.
  + (* partial_CSRG_coog_csr *)
    inversion_clear partial_CSRG_coog_csr.
    apply build_coog_csr; try auto.
    - (* coog_csr_vals *)
      rewrite coog_csr_vals.
      unfold coog_upto; simpl.
      apply count_distinct_noincr; try list_solve.
      rewrite Hdup.
      remember (Znth h (coog_entries coog)) as xy.
      destruct xy as [x y].
      unfold BPO.lt, coord2_le. lia.
    - (* coog_csr_entries *) 
      unfold entries_correspond_coog.
      intros. simpl.
      remember (Znth h0 (sublist 0 (h + 1) (coog_entries coog))) as r0c0. 
      destruct r0c0 as [r0 c0].
      unfold entries_correspond_coog in coog_csr_entries.
      unfold coog_upto in H0. simpl in H0.
      rewrite Zlength_sublist in H0 by list_solve. 
      destruct (h0 <? h) eqn:E.
      { rewrite Z.ltb_lt in E. 
        assert (0 <= h0 < Zlength (coog_entries (coog_upto h coog))).
        { unfold coog_upto. simpl. rewrite Zlength_sublist by list_solve. lia. } 
        specialize (coog_csr_entries h0 H2); clear H2.
        simpl in coog_csr_entries.
        assert (Znth h0 (sublist 0 h (coog_entries coog)) = Znth h0 (sublist 0 (h + 1) (coog_entries coog))).
        { rewrite Znth_sublist by list_solve.
          rewrite Znth_sublist by list_solve.
          auto. }
        rewrite H2 in coog_csr_entries. clear H2.
        rewrite <-Heqr0c0 in coog_csr_entries.
        (* destruct coog_csr_entries as [H101 H102]. *)
        assert (cd_upto_coog (h0 + 1) (coog_upto h coog) = cd_upto_coog (h0 + 1) (coog_upto (h + 1) coog)).
          { unfold coog_upto, cd_upto_coog. simpl.
            rewrite sublist_sublist00 by list_solve.
            rewrite sublist_sublist00 by list_solve. auto. } 
        rewrite H2 in coog_csr_entries. auto. } 
      rewrite Z.ltb_ge in E. assert (h = h0) by lia. subst h0.
      specialize (coog_csr_entries (h-1)).
      assert (0 <= h - 1 < Zlength (coog_entries (coog_upto h coog))).
      { split. lia. unfold coog_upto; simpl. list_solve. } 
      specialize (coog_csr_entries H2); clear H2.
      assert (Znth (h - 1) (coog_entries (coog_upto h coog)) = Znth (h - 1) (coog_entries coog)).
      { unfold coog_upto; simpl. list_solve. } 
      rewrite H2 in coog_csr_entries. rewrite Hdup in coog_csr_entries.
      assert (Znth h (coog_entries coog) = Znth h (sublist 0 (h + 1) (coog_entries coog))).
      { rewrite Znth_sublist by list_solve. list_solve. } 
      rewrite H3 in coog_csr_entries.
      rewrite <- Heqr0c0 in coog_csr_entries.
      assert (cd_upto_coog (h - 1 + 1) (coog_upto h coog) = cd_upto_coog (h + 1) (coog_upto (h + 1) coog)).
      { unfold coog_upto, cd_upto_coog; simpl. 
        rewrite sublist_sublist00 by list_solve.
        rewrite sublist_sublist00 by list_solve.
        replace (h - 1 + 1) with h by lia.
        apply count_distinct_noincr; try list_solve.
        rewrite Hdup. unfold BPO.lt. unfold coord2_le. lia. } 
      rewrite H4 in coog_csr_entries. auto. 
    - (* coog_csr_zeros *)
      unfold no_extra_zeros_coog in *.
      intros r0 k0 ? ?.
      assert (coog_rows (coog_upto (h + 1) coog) = coog_rows (coog_upto h coog)).
      { unfold coog_upto. simpl. auto. } 
      rewrite H3 in H0; clear H3.
      specialize (coog_csr_zeros r0 k0 H0 H2).
      unfold coog_upto; simpl.
      unfold coog_upto in coog_csr_zeros; simpl in coog_csr_zeros.
      rewrite (sublist_split _ h) by list_solve.
      apply in_or_app. left. auto.
Qed.

Lemma partial_CSRG_newcol:
   forall i r c coog ROWPTR COLIND,
   0 < i < Zlength (coog_entries coog) ->
   Znth i (coog_entries coog) = (r, c) ->
   r = fst (Znth (i-1) (coog_entries coog)) ->
   c <> snd (Znth (i-1) (coog_entries coog)) ->
   partial_CSRG i r coog ROWPTR COLIND  ->
   partial_CSRG (i + 1) r coog ROWPTR
  (upd_Znth (count_distinct (sublist 0 i (coog_entries coog))) COLIND (Vint (Int.repr c))).
Proof.
  intros *. pose proof I. intros ? Hrc ? ? ?.
  inversion_clear H3.
  pose proof (proj1 (coog_entry_bounds partial_CSRG_coog i ltac:(lia))).
  rewrite Hrc in H3; simpl in H3.
  
  assert (Hlastrows : sublist (r + 1) (coog_rows (coog_upto i coog) + 1) (csr_row_ptr csr) 
    = Zrepeat (Zlength (csr_vals csr)) (coog_rows (coog_upto i coog) - r)).
  { apply partial_CSRG_rowptr'; auto.
    apply coog_upto_wellformed. list_solve. auto. }
  change (coog_rows _) with (coog_rows coog) in Hlastrows.
  
  pose (new_row_ptr := sublist 0 (r+1) (csr_row_ptr csr) ++ 
    Zrepeat (cd_upto_coog (i+1) coog) (Zlength (csr_row_ptr csr) - (r+1))).
  pose (csr' := Build_csr_matrix Tdouble (csr_cols csr) 
       (Zrepeat (Zconst Tdouble 0) (cd_upto_coog i coog) ++ [Zconst Tdouble 0]) 
       (sublist 0 (cd_upto_coog i coog) (csr_col_ind csr) ++ [c])
       new_row_ptr).
  
  assert (H4 : count_distinct (sublist 0 i (coog_entries coog)) + 1 =
    count_distinct (sublist 0 (i + 1) (coog_entries coog))).
  { apply count_distinct_incr; [|lia].
    pose proof (sorted_e _ partial_CSRG_coog_sorted (i-1) i ltac:(lia) ltac:(lia)).
    unfold BPO.lt. unfold coord2_le in H4 |- *.
    rewrite Hrc in H4|-*. simpl in H4|-*. lia. }
        
  assert (Hrows: csr_rows csr = Zlength (csr_row_ptr csr) - 1) by reflexivity.
  assert (Hrows': csr_rows csr' = csr_rows csr).
  { inversion_clear partial_CSRG_coog_csr.
    unfold csr_rows; simpl. unfold new_row_ptr, cd_upto_coog.
    rewrite <- H4. simpl in coog_csr_rows.
    unfold csr_rows in coog_csr_rows; list_solve. }
    
  assert (Hcde: cd_upto_coog i coog = Zlength (csr_vals csr)).
  { inversion_clear partial_CSRG_coog_csr.
    rewrite coog_csr_vals. unfold cd_upto_coog, coog_upto. simpl.
    reflexivity. }
    
  assert (BUMP : 0 < count_distinct (sublist 0 i (coog_entries coog)) <
    count_distinct (sublist 0 (i+1) (coog_entries coog))).
  { pose proof (count_distinct_incr' (sublist 0 (i+1) (coog_entries coog)) i).
    spec H5.
    { autorewrite with sublist.
      pose proof (sorted_e _ partial_CSRG_coog_sorted (i-1) i ltac:(lia) ltac:(lia)).
      unfold BPO.lt. unfold coord2_le in H6|-*. rewrite Hrc in H6|-*. 
      destruct (Znth (i-1) (coog_entries coog)) as [r' c']. simpl in *. lia. }
    spec H5. list_solve.
    autorewrite with sublist in H5.
    pose proof (count_distinct_mono (sublist 0 i (coog_entries coog)) 1).
    autorewrite with sublist in H6. rewrite (sublist_one 0 1) in H6 by lia.
    simpl in H6. lia. }
  
  apply build_partial_CSRG with (csr:=csr'); auto; try lia.
  
  + (* partial_CSRG_r' *)
    unfold coog_upto in partial_CSRG_r'|-*. simpl in partial_CSRG_r'|-*.
    rewrite (sublist_split 0 i) by list_solve.
    rewrite Forall_app. split; [auto|].
    rewrite (sublist_one) by list_solve.
    apply Forall_cons; [|apply Forall_nil].
    rewrite Hrc. simpl. lia.
    
  + (* partial_CSRG_r'' *)
    rewrite (sublist_split i (i+1)) in partial_CSRG_r'' by list_solve.
    rewrite Forall_app in partial_CSRG_r''. 
    destruct partial_CSRG_r''. apply H6.
  
  + (* partial_CSRG_wf *)
    inversion_clear partial_CSRG_wf.
    inversion_clear partial_CSRG_coog_csr.
    simpl in coog_csr_rows, coog_csr_vals, coog_csr_cols.
    assert (Zlength new_row_ptr = Zlength (csr_row_ptr csr)).
    { unfold csr_rows in *; simpl in Hrows'; lia. }
    apply build_csr_matrix_wellformed; simpl; auto; try lia.
    - (* CSR_wf_vals *)
      autorewrite with sublist. f_equal.
      rewrite <-CSR_wf_vals, coog_csr_vals.
      unfold cd_upto_coog. reflexivity. 
    - (* CSR_wf_vals' *)
      autorewrite with sublist. 
      rewrite Hrows'. unfold new_row_ptr.
      unfold csr_rows. autorewrite with sublist. simpl. auto.
    - (* CSR_wf_sorted *)
      intros a b. intros.
      destruct H6.
      pose proof (CSR_wf_sorted a b ltac:(list_solve)).
      unfold new_row_ptr. rewrite app_ass.
      change (?A :: ?B ++ ?C) with ((A :: B) ++ C).
      destruct (zle a (r+1)), (zle b (r+1)).
      * (* a <= r+1, b <= r+1 *)
        destruct (zeq 0 a), (zeq 0 b); list_solve.
      * (* a <= r+1, b > r+1 *)
        destruct (zeq 0 a).
        { subst a. autorewrite with sublist.
          pose proof (count_distinct_bound (coog_entries (coog_upto (i+1) coog))).
          unfold cd_upto_coog, coog_upto, csr_rows in *. list_solve. }
        destruct (zlt b (Zlength (csr_row_ptr csr) + 1)); [|list_solve].
        autorewrite with sublist.
        pose proof (rowptr_sorted_e _ CSR_wf_sorted (a-1) (Zlength (csr_row_ptr csr)-1) ltac:(list_solve)).
        replace (Znth a (0 :: sublist 0 (r+1) (csr_row_ptr csr))) 
          with (Znth (a-1) (csr_row_ptr csr)) by list_solve.
        unfold cd_upto_coog, coog_upto, csr_rows in *. list_solve.
      * lia.
      * (* a > r+1, b> r+1 *)
        simpl.
        destruct (zlt a (Zlength (csr_row_ptr csr) + 1)), (zlt b (Zlength (csr_row_ptr csr) + 1));
          autorewrite with sublist.
        ++  rewrite !Znth_pos_cons in H8|-* by list_solve. list_solve.
        ++  unfold csr_rows, cd_upto_coog in *.
            pose proof count_distinct_mono (coog_entries coog) (i+1). list_solve.
        ++  lia.
        ++  list_solve.
    - (* CSR_wf_rowsorted *)
      intros r' Hr'; pose proof CSR_wf_rowsorted r' ltac:(list_solve).
      apply sorted_i; [hnf; lia | ]; intros a b Ha Hb.
      pose proof (sorted_e _ H6 a b Ha).
      subst new_row_ptr. rewrite Hrows' in Hr'.
      clear coog_csr_entries CSR_wf_rowsorted Hrows' partial_CSRG_rowptr.
      clear partial_CSRG_colind partial_CSRG_colind'.
      destruct (rowptr_sorted_e _ CSR_wf_sorted r' (r'+1) ltac:(lia)) as [? _].
      pose proof (rowptr_sorted_e _ CSR_wf_sorted (r'+1) (csr_rows csr) ltac:(lia)).
      pose proof I.
      destruct (zlt r' r); [|destruct (zeq r' r)].
      * (* r' < r *)
        unfold cd_upto_coog, csr_rows in *.
        rewrite !Znth_app1 by list_solve.
        rewrite !Znth_app1 in Hb by list_solve.
        autorewrite with sublist in H7, Hb|-*.
        apply H7. lia.
      * clear g. subst r'. 
        autorewrite with sublist in Hb, H7 |-*.
        fold (cd_upto_coog i coog) in *.
        fold (cd_upto_coog (i+1) coog) in *.
        rewrite <- H4 in *. clear H5.
        unfold csr_rows in *.
        rewrite sublist_app' by list_solve.
        rewrite !sublist_sublist by list_solve.
        rewrite Zlength_sublist by list_solve.
        rewrite (sublist_one 0), Znth_0_cons by list_solve.
        autorewrite with sublist.
        rewrite app_ass. simpl.
        change (?A :: ?B ++ ?C) with ((A::B) ++ C) in H7|-*.
        assert (Znth (r+1) (csr_row_ptr csr) = cd_upto_coog i coog).
        { transitivity (Znth 0 (sublist (r+1) (coog_rows coog + 1) (csr_row_ptr csr))).
          list_solve. rewrite Hlastrows. list_solve. }
        destruct (zlt b (cd_upto_coog i coog + 1 - Znth r (csr_row_ptr csr))).
        ++ rewrite !Znth_app1 in H7|-* by list_solve.
          autorewrite with sublist in H7.
          rewrite H5 in *. apply H7. lia.
        ++ rewrite (Znth_app2 _ _ _ _ b) by list_solve.
          autorewrite with sublist.
          destruct (zlt a (cd_upto_coog i coog + 1 - Znth r (csr_row_ptr csr))).
          -- rewrite Znth_app1 in H7|-* by list_solve.
            rewrite H5 in *. autorewrite with sublist in H7.
            autorewrite with sublist in Hb.
            set (hi := cd_upto_coog i coog) in *.
            set (lo := Znth r (csr_row_ptr csr)) in *.
            destruct (zeq b (Z.succ (hi - lo))).
            rewrite <- e, Z.sub_diag, Znth_0_cons.
            clear H7 H6. destruct (zeq a 0).
            ** subst; rewrite Znth_0_cons.
              pose proof (proj2 (coog_entry_bounds partial_CSRG_coog i ltac:(lia))).
              rewrite Hrc in H1; simpl in H1; clear -H1; lia. 
            ** rewrite Znth_pos_cons by lia.
              pose proof coog_csr_zeros r (lo+(a-1)) H3 ltac:(lia).
              simpl in H6. apply In_Znth in H6. destruct H6 as [k [? ?]].
              autorewrite with sublist in H6.
              autorewrite with sublist in H7.
              autorewrite with sublist.
              rewrite Z.add_comm.
              pose proof (sorted_e _ partial_CSRG_coog_sorted k i H6 ltac:(lia)).
              destruct (Znth k (coog_entries coog)) as [rk ck] eqn:Hk.
              simpl in H7. inversion H7; clear H7.
              red in H11. rewrite Hrc in H11. simpl in H11.
              destruct H11 as [H11 | H11]. lia. destruct H11 as [_ H11].
              rewrite <- H14. destruct (zeq k (i-1)).
              { subst k. destruct (Znth (i-1) (coog_entries coog)); simpl in *.
                inv Hk. lia. }
              pose proof (sorted_e _ partial_CSRG_coog_sorted k (i-1) ltac:(lia) ltac:(lia)).
              red in H7. rewrite Hk in H7.
              destruct (Znth (i-1) (coog_entries coog)) as [ri1 ci1] eqn:Hi1; simpl in *.
              destruct H7. lia. destruct H7; subst rk. subst ri1.
              pose proof (sorted_e _ partial_CSRG_coog_sorted (i-1) i ltac:(lia) ltac:(lia)).
              red in H1. rewrite Hrc, Hi1 in H1. simpl in H1. lia.
            ** rewrite (Znth_pos_cons (b - _)) by lia.
              replace (b - Z.succ (hi - lo) - 1) with 0 by lia.
              rewrite Znth_0_cons.
              pose proof (sorted_e _ H6 a (1 + (hi - lo)) ltac:(lia) ltac:(list_solve)).
              change (?A :: ?B ++ ?C) with ((A :: B) ++ C) in H11.
              rewrite Znth_app1 in H11 by list_solve.
              rewrite Znth_app2 in H11 by list_solve.
              autorewrite with sublist in H11.
              replace (1 + (hi - lo) - Z.succ (hi - lo)) with 0 in H11 by lia.
              rewrite Znth_0_cons in H11. auto.
         -- rewrite Znth_app2 by list_solve. autorewrite with sublist.
            set (u := Z.succ _). assert (a-u=0 /\ b-u=1) by list_solve.
            destruct H11. rewrite H11, H12.
            change (c < csr_cols csr).
            clear dependent a. clear dependent b.
            rewrite <- coog_csr_cols.
            clear - Hrc H0 partial_CSRG_coog.
            pose proof (proj2 (coog_entry_bounds partial_CSRG_coog i ltac:(lia))).
            rewrite Hrc in H; apply H.
        * (* r' > r *)
          rewrite Znth_app2 by list_solve.
          autorewrite with sublist in Hb |- *. list_solve.

  + (* partial_CSRG_coog_csr *)
    inversion_clear partial_CSRG_coog_csr.
    apply build_coog_csr; auto.
    - (* coog_csr_rows *)
      rewrite Hrows'. simpl in coog_csr_rows|-*. apply coog_csr_rows.
    - (* coog_csr_vals *)
      unfold coog_upto; simpl. rewrite <- H4.
      rewrite Zlength_app. 
      replace (Zlength [Zconst Tdouble 0]) with 1 by list_solve. f_equal.
      rewrite Zlength_Zrepeat by list_solve. 
      unfold cd_upto_coog. reflexivity.
    - (* coog_csr_entries *)
      intros h Hh. simpl in Hh. 
      rewrite Zlength_sublist in Hh by list_solve.
      replace (i + 1 - 0) with (i+1) in Hh by lia.
      destruct (zlt h i).
      * (* h < i *)
        pose proof coog_csr_entries h ltac:(simpl; list_solve). simpl in H5|-*.
        unfold cd_upto_coog, coog_upto in H5; simpl in H5.
        destruct (Znth h (sublist 0 i (coog_entries coog))) as [rh ch] eqn:Hrch.
        destruct H5.
        replace (Znth h (sublist 0 (i+1) (coog_entries coog))) with (rh, ch).
        2:{ rewrite <- Hrch. list_solve. }
        unfold new_row_ptr, cd_upto_coog, coog_upto; simpl.
        simpl in coog_csr_rows.
        assert (0 <= rh <= r).
        { split.
          + pose proof (coog_entry_bounds partial_CSRG_coog h ltac:(list_solve)).
            autorewrite with sublist in Hrch. rewrite Hrch in H7. simpl in H7. lia.
          + pose proof (sorted_e _ partial_CSRG_coog_sorted h i ltac:(list_solve) ltac:(list_solve)).
            unfold coord2_le in H7.
            autorewrite with sublist in Hrch. rewrite Hrch in H7. simpl in H7. 
            rewrite Hrc in H7. simpl in H7. lia. }
        pose proof (count_distinct_mono (sublist 0 i (coog_entries coog)) (h+1)).
        autorewrite with sublist in H8.
        assert (0 <= count_distinct (sublist 0 i (coog_entries coog)) <= Zlength (csr_col_ind csr)).
        { pose proof (count_distinct_bound (sublist 0 i (coog_entries coog))).
          inversion_clear partial_CSRG_wf.
          rewrite <- CSR_wf_vals. rewrite coog_csr_vals. simpl. lia. }
        assert (0 <= count_distinct (sublist 0 (h+1) (coog_entries coog)) - 1
          < count_distinct (sublist 0 i (coog_entries coog))).
        { split; [|lia].
          destruct (zeq h 0). subst h. rewrite sublist_one by lia. simpl. lia.
          pose proof (count_distinct_bound' (sublist 0 (h+1) (coog_entries coog))); list_solve. }
        split.
        { rewrite Znth_app1 by list_solve.
          rewrite Znth_sublist by list_solve. 
          replace (rh + 0) with rh by lia.
          autorewrite with sublist in H5|-*.
          destruct (zlt rh r).
          + rewrite Znth_app1 by list_solve. 
            rewrite Znth_sublist by list_solve. list_solve.
          + assert (rh = r) by lia. subst rh.
            rewrite Znth_app2 by list_solve.
            rewrite Znth_Zrepeat by list_solve.
            split; list_solve. }
        autorewrite with sublist in H6|-*. lia.
      * assert (h=i) by lia; subst h. clear g Hh.
        simpl. autorewrite with sublist. rewrite Hrc. simpl.
        unfold new_row_ptr, cd_upto_coog, coog_upto; simpl.
        assert (r+1 < Zlength (csr_row_ptr csr)).
        { inversion_clear partial_CSRG_wf. simpl in *. lia. }
        assert (0 <= count_distinct (sublist 0 i (coog_entries coog)) <= Zlength (csr_col_ind csr)).
        { pose proof (count_distinct_bound (sublist 0 i (coog_entries coog))).
          inversion_clear partial_CSRG_wf.
          rewrite <- CSR_wf_vals, coog_csr_vals. simpl. lia. }
        autorewrite with sublist.
        rewrite <- H4. replace (_ - _ - _) with 0 by lia. split;[|list_solve].
        split; [|lia].
        rewrite Z.add_simpl_r.
        unfold cd_upto_coog in Hcde. rewrite Hcde.
        simpl in coog_csr_rows.
        inversion_clear partial_CSRG_wf.
        pose proof (rowptr_sorted_e _ CSR_wf_sorted r (Zlength (csr_row_ptr csr) - 1)).
        spec H7. list_solve.
        unfold csr_rows in *. list_solve.
    - (* coog_csr_zeros *)
      intros r' k. simpl. intros.
      unfold new_row_ptr in H6.
      assert (r+1 < Zlength (csr_row_ptr csr)).
      { inversion_clear partial_CSRG_wf. simpl in *. lia. }
      simpl in coog_csr_rows.
      assert (Hr'r : r' <= r) by list_solve.
      destruct (zlt r' r); autorewrite with sublist in H6.
      * (* r' < r *)
        pose proof coog_csr_zeros r' k H5 H6.
        simpl in H8 |- *.
        apply In_Znth in H8. destruct H8 as [h [? ?]].
        autorewrite with sublist in H8.
        rewrite Znth_sublist in H9 by list_solve.
        replace (h+0) with h in H9 by lia.
        assert (0 <= Znth r' (csr_row_ptr csr) /\
          Znth (r'+1) (csr_row_ptr csr) <= Zlength (csr_col_ind csr)).
        { inversion_clear partial_CSRG_wf. split.
          eapply rowptr_sorted_e1; try eassumption; lia.
          rewrite <- CSR_wf_vals, CSR_wf_vals'.
          eapply rowptr_sorted_e; try eassumption; lia. }
        assert (k < cd_upto_coog i coog <= Zlength (csr_col_ind csr)).
        { inversion_clear partial_CSRG_wf.
          pose proof sorted_e _ (CSR_wf_rowsorted r' ltac:(lia)) 0 
            (k+1-Znth r' (csr_row_ptr csr)) ltac:(list_solve) ltac:(list_solve).
          list_solve. }
        autorewrite with sublist.
        rewrite <- H9.
        replace (Znth h (coog_entries coog)) with
          (Znth h (sublist 0 (i+1) (coog_entries coog))) by list_solve.
        apply Znth_In. list_solve.
      * (* r' = r *)
        simpl in coog_csr_rows.
        assert (r' = r) by list_solve. clear g Hr'r; subst r'.
        autorewrite with sublist in H6.
        unfold cd_upto_coog, coog_upto.
        assert (0 <= count_distinct (sublist 0 i (coog_entries coog)) <= Zlength (csr_col_ind csr)).
        { pose proof (count_distinct_bound (sublist 0 i (coog_entries coog))).
          inversion_clear partial_CSRG_wf.
          rewrite <- CSR_wf_vals, coog_csr_vals. simpl. lia. }
        destruct (zeq k (cd_upto_coog i coog)).
        { (* k = cd_upto_coog i coog *)
          subst k. unfold cd_upto_coog, coog_upto in *.
          rewrite Znth_app2 by list_solve.
          autorewrite with sublist.
          rewrite <-Hrc.
          replace (Znth i (coog_entries coog)) 
            with (Znth i (sublist 0 (i+1) (coog_entries coog))) by list_solve.
          apply Znth_In. list_solve. }
        (* k <> cd_upto_coog i coog *)
        unfold cd_upto_coog, coog_upto in *.
        assert (0 <= Znth r (csr_row_ptr csr) /\
          Znth (r + 1) (csr_row_ptr csr) <= Zlength (csr_col_ind csr)).
        { inversion_clear partial_CSRG_wf.
          rewrite <- CSR_wf_vals, CSR_wf_vals'.
          pose proof rowptr_sorted_e _ CSR_wf_sorted r (r+1) ltac:(lia).
          pose proof rowptr_sorted_e _ CSR_wf_sorted (r+1) (csr_rows csr) ltac:(lia).
          lia. }
        autorewrite with sublist.
        pose proof coog_csr_zeros r k H5 ltac:(list_solve).
        simpl in H10. apply In_Znth in H10. destruct H10 as [h [? ?]].
        autorewrite with sublist in H10, H11. rewrite <- H11.
        replace (Znth h (coog_entries coog)) with (Znth h (sublist 0 (i+1) (coog_entries coog))) by list_solve.
        apply Znth_In. list_solve.

  + (* partial_CSRG_colind *)
    simpl. inversion_clear partial_CSRG_coog_csr.
    autorewrite with sublist.
    fold (cd_upto_coog i coog) in *.
    set (d := cd_upto_coog i coog) in *.
    replace (Z.succ 0) with 1 by lia.
    assert (d = Zlength (csr_col_ind csr)).
    { rewrite Hcde. simpl in *.
      inversion_clear partial_CSRG_wf. lia. }
    assert (d+1 <= Zlength COLIND).
    { simpl in *.
      rewrite partial_CSRG_colind'. rewrite H4.
      apply count_distinct_mono. }
    rewrite Zlength_sublist by list_solve.
    replace (d - 0 + 1) with (d + 1) by list_solve.
    rewrite (sublist_split 0 d (d+1)) by list_solve.
    rewrite (sublist_one d) by list_solve.
    rewrite upd_Znth_same by list_solve.
    rewrite map_app. simpl. f_equal.
    replace (sublist 0 d (csr_col_ind csr)) with (csr_col_ind csr) by list_solve.
    rewrite <- partial_CSRG_colind. list_solve.

  + (* partial_CSRG_rowptr *)
    rewrite partial_CSRG_rowptr. 
    unfold csr', new_row_ptr. simpl.
    f_equal.
    inversion_clear partial_CSRG_coog_csr.
    simpl in coog_csr_rows. list_solve.
    
  + (* partial_CSRG_colind' *)
    list_solve.
Qed.



Lemma partial_CSRG_0 : forall (coog : coog_matrix), 
  coog_matrix_wellformed coog ->
  sorted coord2_le (coog_entries coog) ->
  let k := count_distinct (coog_entries coog) in
    k <= Int.max_unsigned ->
    partial_CSRG 0 (-1) coog (Zrepeat Vundef (coog_rows coog + 1))
    (Zrepeat Vundef k).
Proof.
  intros. rename H1 into Hk.
  pose proof (count_distinct_bound (coog_entries coog)).
  apply build_partial_CSRG with 
    (csr := {| csr_cols := coog_cols coog; csr_vals := nil; csr_col_ind :=  nil;
               csr_row_ptr := Zrepeat 0 (coog_rows coog + 1) |}); auto; try rep_lia.
  + (* partial_CSRG_r *)
    unfold coog_matrix_wellformed in H. lia.
  + (* partial_CSRG_r'' *)
    inversion_clear H. autorewrite with sublist.
    eapply Forall_impl; [| apply H3]. 
    intros. simpl in H. destruct H. lia.
  + (* partial_CSRG_wf *)
    inversion_clear H. destruct H2.
    constructor; unfold csr_rows; simpl; try list_solve.
    - (* CSR_wf_sorted *)
      intros i j. intros. list_solve.
    - (* CSR_wf_rowsorted *)
      intros. rewrite sublist_nil' by list_solve.
      autorewrite with sublist. constructor; [lia | constructor].
  + (* partial_CSRG_coog_csr *)
    inversion_clear H. destruct H2.
    constructor; unfold csr_rows; simpl; try list_solve.
    - (* coog_csr_entries *)
      intros h. intros. simpl in H4. list_solve.
    - (* coog_csr_zeros *)
      intros h. intros. simpl in *. list_solve.
  + (* partial_CSRG_colind' *)
    list_solve.
  + (* partial_CSRG_rowptr' *)
    rewrite Zlength_Zrepeat; auto.
    inversion_clear H. list_solve.
Qed.

Lemma partial_CSRG_skiprow:
  forall i r coog ROWPTR COLIND,
  0 <= i < Zlength (coog_entries coog) ->
  r <= fst (Znth i (coog_entries coog)) ->
  partial_CSRG i (r - 1) coog ROWPTR COLIND ->
  partial_CSRG i r coog
    (upd_Znth r ROWPTR (Vint (Int.repr (count_distinct (sublist 0 i (coog_entries coog))))))
    COLIND.
Proof.
  intros *. pose proof I. intros.
  inversion_clear H2.
  pose (d := count_distinct (sublist 0 i (coog_entries coog))).
  pose (new_row_ptr := sublist 0 r (csr_row_ptr csr) ++ Zrepeat d (Zlength (csr_row_ptr csr) - r)).
  pose (csr' := Build_csr_matrix _ (csr_cols csr) (csr_vals csr) (csr_col_ind csr) new_row_ptr).
  assert (Hrows : csr_rows csr = Zlength (csr_row_ptr csr) - 1) by reflexivity.
  assert (Hlastrows := partial_CSRG_rowptr' (r-1) (coog_upto i coog) csr
   (coog_upto_wellformed i coog ltac:(lia) partial_CSRG_coog)
      partial_CSRG_wf partial_CSRG_coog_csr
      ltac:(change (coog_rows _) with (coog_rows coog); lia)
      partial_CSRG_r'). rewrite Z.sub_simpl_r in Hlastrows. simpl in Hlastrows.
  apply build_partial_CSRG with csr'; auto.
  + (* partial_CSRG_r *)
    inversion_clear partial_CSRG_coog_csr. simpl in *.
    pose proof (coog_entry_bounds partial_CSRG_coog i ltac:(lia)). lia.
  + (* partial_CSRG_r' *)
    eapply Forall_impl; [|apply partial_CSRG_r'].
    simpl; lia.
  + (* partial_CSRG_r'' *)
    rewrite Forall_forall. intros e He. apply In_Znth in He.
    destruct He as [j [? ?]].
    autorewrite with sublist in H2, H3. subst e.
    pose proof (coord2_sorted_e _ partial_CSRG_coog_sorted i (j+i) ltac:(lia)).
    destruct (Znth i (coog_entries coog)) as [ri ci].
    destruct (Znth (j+i) (coog_entries coog)) as [rj cj].
    red in H3. simpl in *. lia.
  + (* partial_CSRG_wf *)
    inversion_clear partial_CSRG_coog_csr.
    inversion_clear partial_CSRG_wf.  
    subst csr'. subst new_row_ptr. constructor; simpl; 
    unfold csr_rows in *; clear Hrows; simpl in *; auto.
    - list_solve.
    - list_solve.
    - (* CSR_wf_sorted *)
      intros a b [Ha Hb].
      repeat change (?A :: ?B ++ ?C) with ((A::B) ++ C).
      pose proof (CSR_wf_sorted a b (ltac:(list_solve))).
      destruct (a <? r+1) eqn:Ear; destruct (b <? r+1) eqn:Ebr.
      * rewrite Znth_app1 by list_solve. 
        rewrite Znth_app1 by list_solve. 
        rewrite Znth_app1 by list_solve. 
        rewrite Znth_app1 by list_solve. list_solve.
      * rewrite Znth_app1 by list_solve.
        rewrite Znth_app1 by list_solve.
        rewrite app_ass.
        rewrite Znth_app2 by list_solve.
        destruct (zlt b (Zlength (csr_row_ptr csr) + 1)); [ | list_solve].
        rewrite Znth_app1 by list_solve.
        autorewrite with sublist.
        destruct (zeq a 0). list_solve.
        rewrite Znth_pos_cons by list_solve.
        rewrite Znth_sublist by list_solve.
        destruct Ha; clear dependent b.
        pose proof CSR_wf_sorted a (Zlength (csr_row_ptr csr)) ltac:(list_solve).
        list_solve.
      * lia.
      * rewrite app_ass.
        rewrite Znth_app2 by list_solve.
        rewrite (Znth_app2 _ _ _ _ b) by list_solve.
        autorewrite with sublist. list_solve.
    - (* CSR_wf_rowsorted *)
      intros r' Hr'.
      assert (Znth r' (csr_row_ptr csr) <= Znth (r'+1) (csr_row_ptr csr) <= d).
      { split.
        + apply (rowptr_sorted_e (csr_row_ptr csr) CSR_wf_sorted). list_solve.
        + unfold d. rewrite <- coog_csr_vals, CSR_wf_vals'.
          apply (rowptr_sorted_e (csr_row_ptr csr) CSR_wf_sorted). list_solve. }
      autorewrite with sublist in Hr'.
      replace (r + (Zlength (csr_row_ptr csr) - r) - 1 ) with (Zlength (csr_row_ptr csr) -1) in Hr' by lia.
      pose proof (CSR_wf_rowsorted r' ltac:(lia)).
      destruct (r' <? r) eqn:Er'r; [destruct ((r'+1) =? r) eqn:ESr'r | ].
      * replace r' with (r-1) in * by lia.
        rewrite Z.sub_simpl_r in *.
        autorewrite with sublist in H3 |-*.
        assert (Znth r (csr_row_ptr csr) = d).
        { unfold csr_rows in *.
          rewrite coog_csr_rows in Hlastrows.
          replace (Znth r (csr_row_ptr csr)) with (Znth 0 (sublist r (Zlength (csr_row_ptr csr)) (csr_row_ptr csr))) by list_solve. 
          replace (Zlength (csr_row_ptr csr) - 1 + 1) with (Zlength (csr_row_ptr csr)) in Hlastrows by lia.
          rewrite Hlastrows. list_solve. }
        fold d in coog_csr_vals. rewrite H4 in H3. auto.
      * autorewrite with sublist. auto.
      * autorewrite with sublist. constructor. lia. constructor.
  + (* partial_CSRG_coog_csr *)
    inversion_clear partial_CSRG_coog_csr;
    subst csr' new_row_ptr; constructor; simpl; auto.
    - (* coog_csr_rows *)
      unfold csr_rows in *. simpl in *. list_solve.
    - (* coog_csr_entries *)
      clear dependent COLIND. clear dependent ROWPTR.
      simpl in *. rewrite coog_csr_rows in partial_CSRG_r. 
      unfold entries_correspond_coog, csr_rows, cd_upto, coog_upto in *.
      intros h Hh.
      pose proof (coog_csr_entries h Hh).
      (* clear coo_csr_entries. *)
      simpl Znth in H2|-*. simpl in Hh.
      autorewrite with sublist in Hh.
      autorewrite with sublist in H2|-*.
      pose proof proj1 (coog_entry_bounds partial_CSRG_coog h ltac:(lia)).
      destruct (Znth h (coog_entries coog)) as [rh ch] eqn:?Hh'.
      simpl in H2,H3|-*.
      destruct H2. split; auto.
      autorewrite with sublist.
      destruct (zlt rh r); [ destruct (zeq rh (r-1)) | ].
      * autorewrite with sublist in H2|-*.
        split; try lia.
        subst d.
        pose proof count_distinct_mono (sublist 0 i (coog_entries coog)) (h+1).
        autorewrite with sublist in H5. list_solve. 
      * autorewrite with sublist in H2|-*. auto.
      * autorewrite with sublist in H2|-*.
        exfalso.
        rewrite Forall_forall in partial_CSRG_r'.
        specialize (partial_CSRG_r' (Znth h (coog_entries coog))).
        spec partial_CSRG_r'.
        replace (Znth h (coog_entries coog)) with 
          (Znth h (sublist 0 i (coog_entries coog))) by list_solve.
        apply Znth_In. list_solve.
        rewrite Hh' in partial_CSRG_r'. simpl in partial_CSRG_r'. lia.
    - (* coog_csr_zeros *)
      unfold no_extra_zeros_coog.
      intros r' k Hk Hk'. simpl in Hk' |- *.
      unfold no_extra_zeros_coog in coog_csr_zeros.
      specialize (coog_csr_zeros r' k Hk). simpl in *.
      destruct (r'+1 <? r) eqn:Er.
      * autorewrite with sublist in Hk'. apply (coog_csr_zeros Hk').
      * autorewrite with sublist in Hk'.
        assert (Hlastrows' : Znth (r'+1) (csr_row_ptr csr) = d).
        { rewrite coog_csr_rows in partial_CSRG_r.
          unfold csr_rows in *.
          rewrite coog_csr_rows, Z.sub_simpl_r in Hlastrows.
          list_solve. }
        apply coog_csr_zeros. list_solve.
  + (* partial_CSRG_rowptr *)
    inversion_clear partial_CSRG_coog_csr.
    inversion_clear partial_CSRG_wf.
    subst csr' new_row_ptr; simpl in *.
    pose proof (proj1 (coog_entry_bounds partial_CSRG_coog i H0)).
    rewrite !(sublist_split 0 r (r + 1)) by list_solve.
    rewrite map_app. f_equal.
    - autorewrite with sublist.
      rewrite sublist_upd_Znth_l by list_solve. list_solve.
    - rewrite (sublist_one r) by list_solve. 
      autorewrite with sublist.
      rewrite upd_Znth_same by list_solve.
      auto.
  + list_solve.
Qed.


Lemma partial_CSRG_newrow:
  forall i r c coog ROWPTR COLIND,
  0 <= i < Zlength (coog_entries coog) ->
  Znth i (coog_entries coog) = (r, c) ->
  (i <> 0  -> fst (Znth (i - 1) (coog_entries coog)) <> r) ->
  partial_CSRG i r coog ROWPTR COLIND ->
  partial_CSRG (i + 1) r coog ROWPTR 
    (upd_Znth (count_distinct (sublist 0 i (coog_entries coog))) COLIND (Vint (Int.repr c))).
Proof.
  intros * H Hrc Hnew H0. inversion_clear H0.
  assert (Hr := proj1 (coog_entry_bounds partial_CSRG_coog i ltac:(lia))).
  rewrite Hrc in Hr; simpl in Hr. clear partial_CSRG_r.
  assert (Hr1 : Znth (r+1) (csr_row_ptr csr) = Znth r (csr_row_ptr csr)).
  { inversion_clear partial_CSRG_wf.
    inversion_clear partial_CSRG_coog_csr.
    red in coog_csr_zeros.
    unfold csr_rows in *. simpl in *.
    pose proof (proj2 (proj1 (rowptr_sorted_e _ CSR_wf_sorted r (r+1) ltac:(lia)))).
    destruct (zlt (Znth r (csr_row_ptr csr)) (Znth (r+1) (csr_row_ptr csr))); [|lia].
    exfalso.
    specialize (coog_csr_zeros r (Znth r (csr_row_ptr csr)) ltac:(lia)).
    spec coog_csr_zeros. lia.
    apply In_Znth in coog_csr_zeros.
    destruct coog_csr_zeros as [k [? ?]].
    autorewrite with sublist in H1, H2.
    pose proof (coord2_sorted_e _ partial_CSRG_coog_sorted k (i-1) ltac:(lia)).
    pose proof (coord2_sorted_e _ partial_CSRG_coog_sorted (i-1) i ltac:(lia)).
    specialize (Hnew ltac:(lia)).
    rewrite Hrc in *.
    destruct (Znth k (coog_entries coog)) as [rk ck].
    destruct (Znth (i-1) (coog_entries coog)) as [r1 c1].
    inv H2. unfold coord2_le in *. simpl in *. lia. }
  set (d:= count_distinct (sublist 0 i (coog_entries coog))) in *.
  pose (new_row_ptr := sublist 0 (r+1) (csr_row_ptr csr) ++
    Zrepeat (d+1) (Zlength (csr_row_ptr csr) - (r+1))).
  pose (csr' := {| csr_cols := csr_cols csr;
    csr_vals := (Zrepeat (Zconst Tdouble 0) (d+1));
    csr_col_ind := csr_col_ind csr ++ [c];
    csr_row_ptr := new_row_ptr |}).
  assert (Hrows : csr_rows csr = Zlength (csr_row_ptr csr) - 1) by reflexivity.
  assert (Hlastrows' := partial_CSRG_rowptr' r (coog_upto i coog) csr
         (coog_upto_wellformed i coog ltac:(lia) partial_CSRG_coog)
       partial_CSRG_wf partial_CSRG_coog_csr
      ltac:(change (coog_rows _) with (coog_rows coog); lia)
      partial_CSRG_r'). simpl in Hlastrows'.
  assert (Hlastrows : sublist r (coog_rows coog + 1) (csr_row_ptr csr) =
    Zrepeat (Zlength (csr_vals csr)) (coog_rows coog + 1 - r)).
  { inversion_clear partial_CSRG_coog_csr. 
    unfold csr_rows in *; simpl in *.
    rewrite (sublist_split r (r+1)) by list_solve.
    replace (coog_rows coog + 1 - r) with (1 + (coog_rows coog - r)) by lia.
    rewrite <-Zrepeat_app by list_solve. f_equal.
    rewrite sublist_one by list_solve. rewrite <-Hr1.
    replace (Znth (r+1) (csr_row_ptr csr)) with 
      (Znth 0 (sublist (r+1) (coog_rows coog + 1) (csr_row_ptr csr))) by list_solve.
    rewrite Hlastrows'. list_solve. list_solve. }
  clear Hlastrows'.
  assert (Hincr : count_distinct (sublist 0 i (coog_entries coog)) + 1 =
    count_distinct (sublist 0 (i+1) (coog_entries coog))).
  { destruct (zeq i 0).
    + (* i = 0 *) 
      subst i. simpl. rewrite sublist_one by list_solve. reflexivity.
    + (* i <> 0 *)
      specialize (Hnew n).
      apply count_distinct_incr; try lia.
      pose proof (coord2_sorted_e _ partial_CSRG_coog_sorted (i-1) i ltac:(lia)).
      unfold BPO.lt. rewrite Hrc in H0|-*.
      destruct (Znth (i-1) (coog_entries coog)) as [r0 c0].
      unfold coord2_le in *. simpl in *. lia. }
  
  apply build_partial_CSRG with csr'; auto; try lia.
  + (* partial_CSRG_r' *)
    simpl. rewrite (sublist_split 0 i) by list_solve. 
    rewrite Forall_app. split;[auto|]. 
    rewrite (sublist_one) by list_solve.
    constructor; [|apply Forall_nil].
    rewrite Hrc. simpl. lia.
  
  + (* partial_CSRG_r'' *)
    rewrite (sublist_split i (i+1)) in partial_CSRG_r'' by list_solve.
    rewrite Forall_app in partial_CSRG_r'' by list_solve.
    destruct partial_CSRG_r''. apply H1.
  
  + (* partial_CSRG_wf *)
    inversion_clear partial_CSRG_wf. constructor; simpl; auto.
    - (* CSR_wf_rows *)
      inversion_clear partial_CSRG_coog_csr.
      unfold csr', new_row_ptr, csr_rows in *. simpl in *. list_solve.
    - (* CSR_wf_vals *)
      rewrite Zlength_app. rewrite <- CSR_wf_vals.
      inversion_clear partial_CSRG_coog_csr.
      unfold d in *.
      pose proof (count_distinct_bound (sublist 0 i (coog_entries coog))). 
      rewrite Zlength_Zrepeat by list_solve.
      replace (Zlength [c]) with 1 by list_solve.
      f_equal. list_solve.
    - (* CSR_wf_vals' *)
      unfold csr', new_row_ptr, csr_rows in *; simpl in *.
      inversion_clear partial_CSRG_coog_csr.
      simpl in *. fold d in coog_csr_vals. list_solve.
    - (* CSR_wf_sorted *)
      assert (Hd' : d + 1 <= Int.max_unsigned). 
      { destruct (zeq i 0).
        + subst i. simpl in d. subst d. rep_lia.
        + unfold d. rewrite Hincr.
          transitivity (count_distinct (coog_entries coog)); auto.
          apply count_distinct_mono. }
      subst new_row_ptr. inversion_clear partial_CSRG_coog_csr.
      intros a b [? ?]. unfold csr_rows in *; simpl in *.
      autorewrite with sublist in H1.
      assert (b <= Zlength (csr_row_ptr csr) + 1) by lia; clear H1.
      destruct (zlt a b).
      2:{ assert (a = b) by lia. subst b. lia. }
      destruct H0 as [H0 _].
      destruct (zlt 0 b); [| list_solve].
      destruct (zlt 0 a); [| list_solve]. clear H0 l0.
      destruct (zlt b (r+2)).
      { pose proof (CSR_wf_sorted a b).
        spec H0. list_solve. list_solve. }
      rewrite !Znth_pos_cons by lia.
      rewrite (Znth_app1 _ _ _ _ (a-1)) by list_solve.
      destruct (zlt a (r+2)); [|list_solve].
      rewrite Znth_app1 by list_solve.
      rewrite app_ass by list_solve.
      rewrite Znth_app2 by list_solve.
      autorewrite with sublist.
      destruct (zlt b (Zlength (csr_row_ptr csr) + 1)); [|list_solve].
      { replace (b - 1 - (r+1)) with (b - r - 2) by list_solve.
        rewrite Znth_app1 by list_solve.
        rewrite Znth_Zrepeat by list_solve.
        unfold no_extra_zeros_coog in coog_csr_zeros.
        transitivity (Znth (Zlength (csr_row_ptr csr) - 1) (csr_row_ptr csr)).
        { pose proof (CSR_wf_sorted (a) (Zlength (csr_row_ptr csr))).
          spec H0. list_solve. list_solve. } list_solve. }
      - (* CSR_wf_rowsorted *)
        inversion_clear partial_CSRG_coog_csr.
        unfold csr_rows, new_row_ptr in *; simpl in *.
        autorewrite with sublist.
        intros r' Hr'.
        assert (0 <= r' < Zlength (csr_row_ptr csr) - 1) by lia. clear Hr'.
        pose proof (CSR_wf_rowsorted _ H0).
        pose proof (proj1 (rowptr_sorted_e _ CSR_wf_sorted r' (r'+1) ltac:(list_solve))).
        pose proof (rowptr_sorted_e _ CSR_wf_sorted (r'+1) 
          (Zlength (csr_row_ptr csr) - 1) ltac:(list_solve)).
        destruct (zlt r' r); [|destruct (zeq r' r)].
        * (* r' < r *)
          autorewrite with sublist. list_solve.
        * (* r' = r *) 
          subst r'. autorewrite with sublist.
          assert (Znth (r+1) (csr_row_ptr csr) = d). 
          { replace (Znth (r+1) (csr_row_ptr csr)) with 
            (Znth 0 (sublist (r+1) (coog_rows coog + 1) (csr_row_ptr csr))) by list_solve.
            autorewrite with sublist. list_solve. }
          rewrite <- Hr1, H4. autorewrite with sublist. simpl.
          assert (Hc := proj2 (coog_entry_bounds partial_CSRG_coog i ltac:(lia))).
          rewrite Hrc in Hc. simpl in Hc.
          apply sorted_cons;[lia|]. apply sorted_cons;[lia|]. apply sorted_1.
        * autorewrite with sublist. apply sorted_cons; [lia|apply sorted_1].
  
  + (* partial_CSRG_coog_csr *)
    inversion_clear partial_CSRG_coog_csr.
    subst csr' new_row_ptr; constructor; unfold csr_rows in *; simpl in *; auto.
    - (* coog_csr_rows *) 
      list_solve.
    - (* coog_csr_cols *)
      rewrite Zlength_Zrepeat by list_solve.
      unfold d. rewrite Hincr. reflexivity.
    - (* coog_csr_entries *)
      intros h Hh. simpl. unfold coog_upto in Hh. simpl in Hh.
      rewrite Zlength_sublist in Hh by list_solve.
      replace (i+1-0) with (i+1) in Hh by lia.
      destruct (zlt h i).
      * (* h < i *)
        red in coog_csr_entries. 
        pose proof (coog_csr_entries h). spec H0.
        { unfold coog_upto. simpl. list_solve. }
        rewrite Znth_sublist by list_solve. replace (h+0) with h by lia.
        unfold coog_upto at 1 in H0; simpl in H0.
        rewrite Znth_sublist in H0 by list_solve.
        replace (h+0) with h in H0 by lia.
        destruct (Znth h (coog_entries coog)) as [rh ch] eqn:Eh.
        unfold coog_upto, cd_upto_coog in H0. simpl in H0.
        autorewrite with sublist in H0 |- *.
        assert (0 <= rh <= r).
        { pose proof (proj1 (coog_entry_bounds partial_CSRG_coog h ltac:(lia))).
          pose proof (coord2_sorted_e _ partial_CSRG_coog_sorted h i ltac:(lia)).
          rewrite Eh, Hrc in *.
          unfold coord2_le in H2. simpl in *. lia. }
        split;[split|].
        { rewrite Znth_app1 by list_solve.
          destruct H0. destruct H0.
          unfold coog_upto, cd_upto_coog. simpl.
          autorewrite with sublist. lia. }
        { unfold coog_upto, cd_upto_coog; simpl.
          destruct H0 as [[? ?] ?].
          rewrite sublist_sublist by list_solve.
          replace (0 + 0) with 0 by lia.
          replace (h+1+0) with (h+1) by lia.
          rewrite Znth_app1 by list_solve.
          rewrite Znth_sublist by list_solve.
          replace (rh+1+0) with (rh+1) by lia. lia. }
        spec Hnew. lia.
        destruct H0.
        pose proof (coord2_sorted_e _ partial_CSRG_coog_sorted h (i-1) ltac:(lia)).
        pose proof (coord2_sorted_e _ partial_CSRG_coog_sorted (i-1) i ltac:(lia)).
        unfold coord2_le in *. rewrite Hrc, Eh in *. simpl in *.
        destruct (Znth (i-1) (coog_entries coog)) as [ri ci] eqn:Ei.
        simpl in *. unfold coog_upto, cd_upto_coog. simpl.
        autorewrite with sublist. inv Eh.
        apply Znth_app1.
        inversion_clear partial_CSRG_wf. 
        rewrite <- CSR_wf_vals.
        rewrite coog_csr_vals.
        pose proof (count_distinct_mono (sublist 0 i (coog_entries coog)) (h+1)).
        replace (sublist 0 (h + 1) (coog_entries coog))
          with (sublist 0 (h + 1) (sublist 0 i (coog_entries coog))) by list_solve.
        assert (forall x y, x <= y -> x - 1 < y) by lia.
        apply H5. apply H2.
      * assert (h = i) by lia. subst h.
        autorewrite with sublist. rewrite Hrc.
        unfold cd_upto_coog, coog_upto. simpl. 
        autorewrite with sublist.
        rewrite coog_csr_rows, Z.sub_simpl_r in Hlastrows.
        replace (Znth r (csr_row_ptr csr)) 
          with (Znth 0 (sublist r (Zlength (csr_row_ptr csr)) (csr_row_ptr csr))) by list_solve.
        rewrite Hlastrows. autorewrite with sublist.
        rewrite coog_csr_vals. rewrite <- Hincr. split;[split|].
        { lia. }
        { fold d. lia. }
        rewrite Z.add_simpl_r.
        assert (count_distinct (sublist 0 i (coog_entries coog)) = Zlength (csr_col_ind csr)).
        { inversion_clear partial_CSRG_wf. lia. }
        rewrite Znth_app2 by list_solve. list_solve.
    - (* coog_csr_zeros *)
      intros r' k Hr'. simpl.
      specialize (coog_csr_zeros r' k Hr').
      unfold cd_upto_coog, coog_upto, csr_rows in *; simpl in *.
      assert (Znth (r'+1) (csr_row_ptr csr) <= Znth (Zlength (csr_row_ptr csr) - 1) (csr_row_ptr csr)).
      { inversion_clear partial_CSRG_wf. 
        pose proof (rowptr_sorted_e _ CSR_wf_sorted (r'+1) (Zlength (csr_row_ptr csr) - 1)).
        lia. }
      destruct (zlt r' r); [|destruct (zeq r' r)].
      * (* r' < r *)
        rewrite Znth_app1 by list_solve.
        rewrite Znth_app1 by list_solve.
        intros. autorewrite with sublist in H1.
        rewrite Znth_app1.
        2:{ inversion_clear partial_CSRG_wf. list_solve. }
        spec coog_csr_zeros. list_solve.
        apply In_Znth in coog_csr_zeros.
        destruct coog_csr_zeros as [j [? ?]].
        rewrite <- H3.
        rewrite Zlength_sublist in H2 by list_solve.
        rewrite Z.sub_0_r in H2.
        rewrite Znth_sublist, Z.add_0_r by list_solve.
        replace (Znth j (coog_entries coog)) with
          (Znth j (sublist 0 (i+1) (coog_entries coog))) by list_solve.
        apply Znth_In. list_solve.
      * (* r' = r *)
        subst r'. autorewrite with sublist.
        intros.
        assert (Znth 0 (sublist r (coog_rows coog + 1) (csr_row_ptr csr)) = d).
        { rewrite Hlastrows. autorewrite with sublist. lia. }
        assert (k = d) by list_solve. subst k. 
        autorewrite with sublist in H2.
        assert (d = Zlength (csr_col_ind csr)).
        { rewrite <- H2. inversion_clear partial_CSRG_wf.
          list_solve. }
        rewrite Znth_app2 by list_solve.
        replace (d - Zlength (csr_col_ind csr)) with 0 by lia. 
        replace (Znth 0 [c]) with c by list_solve.
        rewrite <- Hrc.
        replace (Znth i (coog_entries coog)) 
          with (Znth i (sublist 0 (i+1) (coog_entries coog))) by list_solve.
        apply Znth_In. list_solve.
      * (* r' > r *)
        autorewrite with sublist. intros. lia.
  
  + (* partial_CSRG_colind *)
    inversion_clear partial_CSRG_wf.
    inversion_clear partial_CSRG_coog_csr.
    unfold cd_upto_coog, coog_upto, csr_rows in *; simpl in *.
    subst csr' new_row_ptr; simpl in *.
    pose proof (count_distinct_bound (sublist 0 i (coog_entries coog))).
    pose proof (count_distinct_mono (coog_entries coog) (i+1)).
    rewrite (sublist_split 0 d) by list_solve.
    rewrite (sublist_upd_Znth_l) by list_solve.
    rewrite (sublist_one d) by list_solve.
    rewrite upd_Znth_same by list_solve.
    rewrite map_app by list_solve. simpl. f_equal. list_solve.
    
  + (* partial_CSRG_rowptr *)
    inversion_clear partial_CSRG_wf.
    inversion_clear partial_CSRG_coog_csr.
    unfold cd_upto_coog, coog_upto, csr_rows in *; simpl in *.
    subst csr' new_row_ptr; simpl in *.
    rewrite partial_CSRG_rowptr.
    f_equal. list_solve.

  + list_solve. 
Qed.

Lemma partial_CSRG_lastrows:
  forall r coog ROWPTR COLIND,
  r <= coog_rows coog ->
  partial_CSRG (Zlength (coog_entries coog)) (r-1) coog ROWPTR COLIND ->
  partial_CSRG (Zlength (coog_entries coog)) r coog 
    (upd_Znth r ROWPTR (Vint (Int.repr (count_distinct (coog_entries coog))))) COLIND.
Proof.
  intros.
  inversion_clear H0.
  apply build_partial_CSRG with csr; auto; try lia.
  + eapply Forall_impl; try eassumption. simpl; intros. lia.
  + autorewrite with sublist. constructor.
  + replace (coog_upto (Zlength (coog_entries coog)) coog) with coog in *
      by (unfold coog_upto;  destruct coog; simpl; f_equal; rewrite sublist_same; auto).
    pose proof partial_CSRG_rowptr' (r-1) _ _ partial_CSRG_coog partial_CSRG_wf partial_CSRG_coog_csr ltac:(lia) ltac:(assumption).
    inversion_clear partial_CSRG_coog_csr; unfold csr_rows in *; simpl in *.
    rewrite !(sublist_split 0 r (r+1)) by list_solve.
    rewrite sublist_upd_Znth_l by list_solve.
    rewrite map_app.
    rewrite Z.sub_simpl_r in *.
    f_equal; auto.
    rewrite !sublist_one by list_solve. rewrite upd_Znth_same by list_solve.
    simpl. f_equal; f_equal; f_equal. list_solve.
  + list_solve.
Qed.


