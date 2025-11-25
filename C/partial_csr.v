Require Import VST.floyd.proofauto.
From LAProof.C Require Import floatlib sparse_model distinct.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".


Lemma coo_entry_bounds {t} [coo: coo_matrix t]:
  coo_matrix_wellformed coo ->
  forall i, 
  0 <= i < Zlength (coo_entries coo) ->
  0 <= fst (fst (Znth i (coo_entries coo))) < coo_rows coo /\
  0 <= snd (fst (Znth i (coo_entries coo))) < coo_cols coo.
Proof.
intros.
destruct H as [_ H].
eapply Forall_forall in H.
apply H.
apply Znth_In; auto.
Qed.

Definition coo_upto (i: Z) {t} (coo: coo_matrix t) :=
  Build_coo_matrix _ (coo_rows coo) (coo_cols coo) (sublist 0 i (coo_entries coo)).

Definition cd_upto (i: Z) {t} (coo: coo_matrix t) : Z :=
   count_distinct (sublist 0 i (coo_entries coo)).

Lemma sorted_cons_e2: forall {A} (lt: relation A) a al, sorted lt (a::al) -> sorted lt al.
Proof. intros. destruct al; inv H; auto; constructor. Qed.

Definition entries_correspond {t} (coo: coo_matrix t) (csr: csr_matrix t) :=
forall h, 
0 <= h < Zlength (coo_entries coo) ->
let '(r,c) := fst (Znth h (coo_entries coo)) in
let k := cd_upto (h+1) coo - 1 in
  Znth r (csr_row_ptr csr) <= k < Znth (r+1) (csr_row_ptr csr) /\
  Znth k (csr_col_ind csr) = c /\
  sum_any (map snd (filter (coord_eqb (r,c) oo fst) (coo_entries coo))) (Znth k (csr_vals csr)).

Definition no_extra_zeros {t} (coo: coo_matrix t) (csr: csr_matrix t) := 
  forall r k, 0 <= r < coo_rows coo ->
     Znth r (csr_row_ptr csr) <= k < Znth (r+1) (csr_row_ptr csr) ->
     let c := Znth k (csr_col_ind csr) in
        In (r,c) (map fst (coo_entries coo)).

Inductive coo_csr {t} (coo: coo_matrix t) (csr: csr_matrix t) : Prop :=
 build_coo_csr:
 forall
    (coo_csr_rows: coo_rows coo = csr_rows csr)
    (coo_csr_cols: coo_cols coo = csr_cols csr)
    (coo_csr_vals: Zlength (csr_vals csr) = count_distinct (coo_entries coo))
    (coo_csr_entries: entries_correspond coo csr)
    (coo_csr_zeros: no_extra_zeros coo csr),
    coo_csr coo csr.

Inductive partial_CSR (h: Z) (r: Z) (coo: coo_matrix Tdouble)
      (rowptr: list val) (colind: list val) (val: list val) : Prop :=
build_partial_CSR:
   forall 
    (partial_CSR_coo: coo_matrix_wellformed coo)
    (partial_CSR_coo_sorted: sorted coord_le (coo_entries coo))
    (partial_CSR_i: 0 <= h <= Zlength (coo_entries coo))
    (partial_CSR_r: -1 <= r <= coo_rows coo)
    (partial_CSR_r': Forall (fun e => fst (fst e) <= r) (coo_entries (coo_upto h coo)))
    (partial_CSR_r'': Forall (fun e => fst (fst e) >= r) (sublist h (Zlength (coo_entries coo)) (coo_entries coo)))
    (csr: csr_matrix Tdouble)
    (partial_CSR_wf: csr_matrix_wellformed csr)
    (partial_CSR_coo_csr: coo_csr (coo_upto h coo) csr)
    (partial_CSR_val: sublist 0 (Zlength (csr_vals csr)) val = map Vfloat (csr_vals csr))
    (partial_CSR_colind: sublist 0 (Zlength (csr_col_ind csr)) colind = map (Vint oo Int.repr) (csr_col_ind csr))
    (partial_CSR_rowptr: sublist 0 (r+1) rowptr = map (Vint oo Int.repr) (sublist 0 (r+1) (csr_row_ptr csr)))
    (partial_CSR_val': Zlength val = count_distinct (coo_entries coo))
    (partial_CSR_colind': Zlength colind = count_distinct (coo_entries coo))
    (partial_CSR_rowptr': Zlength rowptr = coo_rows coo + 1)
    (partial_CSR_dbound: count_distinct (coo_entries coo) <= Int.max_unsigned),
    partial_CSR h r coo rowptr colind val.

Hint Unfold csr_rows : list_solve_unfold. (* unfolds below the line but unfortunately not above the line *)

Lemma partial_CSR_rowptr': forall {t} r (coo: coo_matrix t) (csr: csr_matrix t),
   coo_matrix_wellformed coo ->
   csr_matrix_wellformed csr ->
   coo_csr coo csr ->
   -1 <= r <= coo_rows coo ->
   Forall (fun e => fst (fst e) <= r) (coo_entries coo) ->
   sublist (r+1) (coo_rows coo + 1) (csr_row_ptr csr) = Zrepeat (Zlength (csr_vals csr)) (coo_rows coo - r).
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
 assert (exists i', i + (r+1) <= i' < coo_rows coo /\ Znth i' (csr_row_ptr csr) < Znth (i'+1) (csr_row_ptr csr)). {
  rewrite CSR_wf_vals' in l. rewrite coo_csr_rows in H1|-*.
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
    apply (rowptr_sorted_e _ CSR_wf_sorted (x+r) (y+r) ltac:(list_solve)).
  }
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
  exists (i+1). list_solve.
 }
  destruct H0 as [i' [? ?]].
  unfold csr_rows in *.
  pose proof coo_csr_zeros i' (Znth i' (csr_row_ptr csr)) ltac:(lia).
  specialize (H6 ltac:(lia)).
  rewrite Forall_forall in H3.
  apply In_Znth in H6. destruct H6 as [b [??]].
  specialize (H3 (Znth b (coo_entries coo))).
  rewrite Znth_map in H7 by list_solve.
  rewrite H7 in H3. simpl in H3.
  spec H3. apply Znth_In. list_solve. lia.
Qed.

Definition matrix_upd {t} (i j: Z) (m: matrix t) (x: ftype t) : matrix t :=
  upd_Znth i m (upd_Znth j (Znth i m) x).

Lemma BPO_eqv_iff: forall {t} a b, @BPO.eqv _ _ (@CoordBPO t) a b <-> fst a = fst b.
 intros ? [[??]?] [[??]?]. unfold BPO.eqv, coord_le; simpl; split; intro.
 f_equal; lia. inv H; lia.
Qed.

Lemma partial_CSR_duplicate:
    forall h r coo (f: ftype Tdouble) ROWPTR COLIND VAL,
    0 < h < Zlength (coo_entries coo) ->
    fst (Znth (h-1) (coo_entries coo)) = fst (Znth h (coo_entries coo)) ->
    r = fst (fst (Znth (h-1) (coo_entries coo))) ->
    Znth (cd_upto h coo - 1) VAL = Vfloat f ->
    partial_CSR h r coo ROWPTR COLIND VAL ->
    partial_CSR (h+1) r coo ROWPTR COLIND 
      (upd_Znth (cd_upto h coo - 1) VAL
         (Vfloat (Float.add f (snd (Znth h (coo_entries coo)))))).
Proof.
intros * H Hdup **. 
assert (Hcde: 0 < cd_upto h coo). {
  apply count_distinct_bound'. autorewrite with sublist; lia.
}
inversion H2; clear H2.
destruct (coo_entry_bounds partial_CSR_coo h) as [Hr Hc]; [ lia |].
destruct (Znth h (coo_entries coo)) as  [[r' c] x] eqn:Hentry.
assert (r'=r) by (rewrite Hdup in H0; simpl in H0; auto).
subst r'. simpl in Hdup, Hr, Hc. 
clear H0. simpl.
assert (coo_matrix_wellformed (coo_upto h coo)). {
  clear - partial_CSR_coo H.
  inversion_clear partial_CSR_coo; constructor; auto.
  unfold coo_upto; simpl.
  apply Forall_sublist; auto.
}
assert (HR := partial_CSR_rowptr' r (coo_upto h coo) csr H0 partial_CSR_wf partial_CSR_coo_csr ltac:(simpl; lia) ltac:(auto)).
clear H0.
inversion_clear partial_CSR_coo_csr.
simpl in coo_csr_rows, coo_csr_cols.
set (d := cd_upto h coo) in *.
change (count_distinct (coo_entries (coo_upto h coo))) with d in *.
set (x' := Float.add f x).
pose (val' := upd_Znth (d - 1) (csr_vals csr) x').
pose (csr' := Build_csr_matrix _ (csr_cols csr) val' 
                (csr_col_ind csr) (csr_row_ptr csr)).
clear partial_CSR_r.
inversion_clear partial_CSR_wf.
apply (build_partial_CSR (h+1) r coo _ _ _ ltac:(assumption) ltac:(assumption) ltac:(lia)) with 
      (csr:=csr'); auto; try lia.
- simpl.  rewrite (sublist_split 0 h) by rep_lia. apply Forall_app; split; auto.
  rewrite sublist_one by lia. constructor; auto. rewrite Hentry; simpl. lia.
- clear - H partial_CSR_r''. list_solve.
-
 constructor; auto; simpl; change (csr_rows csr') with (csr_rows csr); try lia.
 + simpl. unfold val'. list_solve.
 + unfold val'. list_solve.
- 
   assert (H3: cd_upto (h+1) (coo_upto (h+1) coo) = cd_upto h (coo_upto h coo)). {
     unfold cd_upto, coo_upto. simpl. autorewrite with sublist.
     symmetry; apply count_distinct_noincr. lia.
     unfold BPO.lt, coord_le. rewrite Hdup, Hentry. simpl. lia.
   }
  constructor; auto.
 + transitivity d; [ simpl; unfold val'; list_solve | ].
   apply count_distinct_noincr; auto.
   unfold BPO.lt, coord_le; rewrite Hentry, Hdup; simpl; lia.
 + change float with (ftype Tdouble) in *.
   assert (Hf: Znth (d-1) (csr_vals csr) = f). {
         assert (Hf': Znth (d-1) (sublist 0 (Zlength (csr_vals csr)) VAL) = Vfloat f) by list_solve.
         rewrite partial_CSR_val in Hf'. 
         rewrite Znth_map in Hf' by list_solve.
         inv Hf'; auto. 
       }
   subst val'.
   intros g ?. simpl in H0. autorewrite with sublist in H0.
   simpl. autorewrite with sublist.
   rewrite (sublist_split 0 h) by lia. rewrite (sublist_one h) by lia.
   rewrite Hentry.
   destruct (zeq g h).
  * subst g. autorewrite with sublist.
   pose proof (coo_csr_entries (h-1) ltac:(simpl; list_solve)). simpl in H2.
   autorewrite with sublist in H2.
   rewrite Hentry. rewrite Hdup in H2. simpl.
   rewrite H3; clear H3.
   rewrite (sublist_split 0 h) by list_solve. autorewrite with sublist.
   rewrite filter_app, map_app.
   destruct H2 as [? [??]]; split3; auto.
   simpl map.
   replace (coord_eqb (r,c) (r,c)) with true by (unfold coord_eqb; simpl; clear; lia).
   simpl map. subst x'.
   replace (cd_upto h (coo_upto h coo)) with d in H4|-*
     by (unfold d, cd_upto, coo_upto; simpl; autorewrite with sublist; auto). 
   rewrite upd_Znth_same by lia. rewrite Hf in H4. 
   change (Float.add f x) with (BPLUS f x).
   apply Sum_Any_split; auto. constructor.
  *
    pose proof (coo_csr_entries g).  simpl in H2.
    autorewrite with sublist in H2.
    unfold cd_upto, coo_upto in H2|-*. simpl in H2|-*.
    autorewrite with sublist in H2. autorewrite with sublist.
    destruct (fst (Znth g (coo_entries coo))) as [r' c'] eqn:Hg.
    spec H2. lia.
    destruct H2 as [? [??]]; split3; auto.
    clear H2 H4.
    assert (Hg': 0 <= g < h) by lia. clear H0 n.
    rewrite filter_app, map_app; simpl.
    destruct (coord_eqb (r',c') (r,c)) eqn:H4.
   --  assert (Hrc: r'=r /\ c'=c) by (unfold coord_eqb in H4; simpl in H4; lia).
       destruct Hrc; subst r' c'. clear H4. simpl map. subst x'.
       change (Float.add f x) with (BPLUS f x).
       replace (count_distinct (sublist 0 (g + 1) (coo_entries coo))) with d in H5|-*.
    2:{ subst d. unfold cd_upto. 
         destruct (zeq g (h-1)). subst g. f_equal; f_equal; lia.
         rewrite <- Hdup in Hg.
         clear - Hg Hg' n partial_CSR_coo_sorted H. destruct H as [_ H].
         forget (coo_entries coo) as al.
         rewrite <- BPO_eqv_iff in Hg.
         symmetry; apply count_distinct_range_same; auto; lia.
        }
       rewrite upd_Znth_same by lia.
       rewrite Hf in H5. 
       apply Sum_Any_split; auto. constructor.
   -- simpl map. rewrite app_nil_r.
      assert (g<>h). { intro; subst g. rewrite Hentry in Hg. simpl in Hg.
                     unfold coord_eqb in H4. simpl in H4. inv Hg; lia.
     }
     assert (cd_upto (g + 1) coo  <> d). {
        unfold d.
        assert (fst (Znth g (coo_entries coo)) <> fst (Znth (h-1) (coo_entries coo))).
          unfold coord_eqb in H4. simpl in H4. rewrite Hg, Hdup.  intro Hx; inv Hx; lia.
        unfold cd_upto.
        destruct (zeq g (h-1)); [contradict H2; subst; auto | ].
        assert (0<=g<h-1) by lia.
        contradict H2.
        rewrite <- BPO_eqv_iff.
        apply count_distinct_range_same in H2; auto. lia. 
      }
     fold (cd_upto (g+1) coo).
     rewrite upd_Znth_diff; try lia. auto.
     unfold cd_upto.
     pose proof (count_distinct_bound (sublist 0 (g + 1) (coo_entries coo))).
     autorewrite with sublist in H6.
     pose proof (count_distinct_bound' (sublist 0 (g + 1) (coo_entries coo)) ltac:(list_solve)).
     split; try lia.
     rewrite coo_csr_vals.
     unfold d, cd_upto.
     pose proof count_distinct_mono (sublist 0 h (coo_entries coo)) (g+1).
     autorewrite with sublist in H8. lia.
 + intros r' k ? ?.
   specialize (coo_csr_zeros r' k H0 H2).
   simpl in coo_csr_zeros|-*.
   rewrite (sublist_split 0 h) by list_solve.
   rewrite map_app, in_app. auto.
 -
  simpl. unfold val'. autorewrite with sublist.
  clear csr' coo_csr_entries. rewrite coo_csr_vals.
  rewrite coo_csr_vals in *.
  assert (d <= Zlength VAL). {
      rewrite partial_CSR_val'. unfold d, cd_upto; simpl.
      apply count_distinct_mono.
  }
  rewrite sublist_upd_Znth_lr by lia.
  rewrite partial_CSR_val.
  rewrite <-upd_Znth_map. f_equal. lia.
 -
  simpl. unfold val'.  list_solve.
Qed.

Lemma coo_upto_wellformed: forall {t} i (coo: coo_matrix t),
  0 <= i <= Zlength (coo_entries coo) ->
  coo_matrix_wellformed coo -> coo_matrix_wellformed (coo_upto i coo).
Proof.
intros.
inversion_clear H0; constructor; simpl; auto.
apply Forall_sublist; auto.
Qed.

Lemma coord_sorted_e: forall {t} (al: list (Z*Z*ftype t)) (H: sorted coord_le al)
   (i j: Z), 0 <= i <= j /\ j < Zlength al -> coord_le (Znth i al) (Znth j al).
Proof.
intros.
destruct (zeq i j).
subst.
clear; destruct (Znth j al) as [[??]?]; red; simpl; lia.
apply sorted_e; auto; lia.
Qed.

Lemma partial_CSR_newcol:
   forall i r c x coo ROWPTR COLIND VAL,
   0 < i < Zlength (coo_entries coo) ->
   Znth i (coo_entries coo) = (r, c, x) ->
   r = fst (fst (Znth (i-1) (coo_entries coo))) ->
   c <> snd (fst (Znth (i-1) (coo_entries coo))) ->
   partial_CSR i r coo ROWPTR COLIND VAL ->
   partial_CSR (i + 1) r coo ROWPTR
  (upd_Znth (count_distinct (sublist 0 i (coo_entries coo))) COLIND (Vint (Int.repr c)))
  (upd_Znth (count_distinct (sublist 0 i (coo_entries coo))) VAL (Vfloat x)).
Proof.
intros *. pose proof I. intros ? Hrcx ? ? ?.
inversion_clear H3.
pose proof (proj1 (coo_entry_bounds partial_CSR_coo i ltac:(lia))).
rewrite Hrcx in H3; simpl in H3.
clear partial_CSR_r.
assert (Hlastrows := partial_CSR_rowptr' r (coo_upto i coo) csr
   (coo_upto_wellformed i coo ltac:(lia) partial_CSR_coo)
       partial_CSR_wf partial_CSR_coo_csr
      ltac:(change (coo_rows _) with (coo_rows coo); lia)
      partial_CSR_r'). change (coo_rows _) with (coo_rows coo) in Hlastrows.
(*      replace (coo_rows coo + 1 - (r + 1)) with (coo_rows coo - r) in Hlastrows by lia.*)
pose (new_row_ptr := sublist 0 (r+1) (csr_row_ptr csr) ++ Zrepeat (cd_upto (i+1) coo) (Zlength (csr_row_ptr csr) - (r+1))).
pose (csr' := Build_csr_matrix _ (csr_cols csr) 
       (sublist 0 (cd_upto i coo) (csr_vals csr) ++ [snd (Znth i (coo_entries coo))])
       (sublist 0 (cd_upto i coo) (csr_col_ind csr) ++ [c])
       new_row_ptr).
assert (H4: count_distinct (sublist 0 i (coo_entries coo)) + 1 = 
        count_distinct (sublist 0 (i+1) (coo_entries coo))). {
    apply count_distinct_incr; [ | lia].
    pose proof (sorted_e _ partial_CSR_coo_sorted  (i-1) i) ltac:(lia) ltac:(lia).
      red. rewrite Hrcx in H4|-*. split; auto. intro.
      clear - H4 H5 H1 H2. destruct (Znth (i - 1) (coo_entries coo)) as [[??]?]. simpl in *; subst.
      red in H5, H4; simpl in *. lia.
     }
assert (Hrows: csr_rows csr = Zlength (csr_row_ptr csr) - 1) by reflexivity.
assert (Hrows': csr_rows csr' = csr_rows csr). {
    inversion_clear partial_CSR_coo_csr.
    unfold csr_rows; simpl. unfold new_row_ptr, cd_upto.
    rewrite <- H4.
    simpl in coo_csr_rows.
    unfold csr_rows in *. list_solve.
  }
assert (Hcde: cd_upto i coo = Zlength (csr_vals csr)). {
    unfold cd_upto.
    pose proof (count_distinct_mono (coo_entries coo) i).
    pose proof (count_distinct_bound (sublist 0 i (coo_entries coo))).
    autorewrite with sublist in H6.
    inversion_clear partial_CSR_wf.
    inversion_clear partial_CSR_coo_csr. rewrite coo_csr_vals.
    unfold coo_upto. simpl. lia.
}
assert (BUMP: 0 < count_distinct (sublist 0 i (coo_entries coo)) <
               count_distinct (sublist 0 (i + 1) (coo_entries coo))). {
 pose proof count_distinct_incr' (sublist 0 (i+1) (coo_entries coo)) i.
 spec H5.  {
        autorewrite with sublist.
        pose proof sorted_e _ partial_CSR_coo_sorted (i-1) i ltac:(lia) ltac:(lia).
        rewrite Hrcx in *. clear - H6 H1 H2. subst. destruct (Znth _ _) as [[??]?].
        red; unfold coord_le in *; simpl in *. lia.
     }
  spec H5. list_solve.
  pose proof count_distinct_mono (sublist 0 i (coo_entries coo)) 1.
  autorewrite with sublist in H6. rewrite (sublist_one 0 1) in H6 by lia.
  simpl in H6. lia.
}
apply build_partial_CSR with (csr:=csr'); auto; try lia.
- unfold coo_upto. simpl. rewrite (sublist_split 0 i) by lia. apply Forall_app; split; auto.
  rewrite sublist_one by lia. rewrite Hrcx. constructor; auto. simpl. lia.
- unfold coo_upto. simpl. rewrite (sublist_split i (i+1)) in partial_CSR_r'' by lia.
  apply Forall_app in partial_CSR_r''. apply partial_CSR_r''.
- inversion_clear partial_CSR_wf.
  inversion_clear partial_CSR_coo_csr.
  simpl in coo_csr_rows, coo_csr_vals, coo_csr_cols.
  assert (Zlength new_row_ptr = Zlength (csr_row_ptr csr))
       by (unfold csr_rows in *; simpl in Hrows'; lia).  
  constructor; simpl; auto; try lia.
  + unfold cd_upto. list_solve.
  +  unfold cd_upto, csr', new_row_ptr, csr_rows; simpl. 
     rewrite Zlength_app, Zlength_sublist by lia.
     rewrite <- coo_csr_vals, CSR_wf_vals', Hrows.  
     list_solve.
  + intros a b [??].
    pose proof CSR_wf_sorted a b ltac:(list_solve).
    unfold new_row_ptr.
    rewrite app_ass.
    change (?A :: ?B ++ ?C) with ((A::B)++C).
    destruct (zle a (r+1)), (zle b (r+1)).    
    -- destruct (zeq 0 a), (zeq 0 b); list_solve.
    -- destruct (zeq 0 a).
      ++ pose proof count_distinct_bound (coo_entries (coo_upto (i+1) coo)). 
         unfold cd_upto, coo_upto, csr_rows in *. list_solve.
      ++
         destruct (zlt b (Zlength (csr_row_ptr csr)+1)); [ | list_solve].
         pose proof rowptr_sorted_e _ CSR_wf_sorted (a-1) (Zlength (csr_row_ptr csr) - 1) ltac:(list_solve).
         unfold cd_upto, coo_upto, csr_rows in *.
         list_solve.
    -- lia.
    -- simpl.
       destruct (zlt a (Zlength (csr_row_ptr csr)+1)), (zlt b (Zlength (csr_row_ptr csr)+1));
       autorewrite with sublist.
      ++ rewrite !Znth_pos_cons in H8|-* by list_solve. list_solve.
      ++ unfold csr_rows, cd_upto in *.
         pose proof count_distinct_mono (coo_entries coo) (i+1).
         list_solve.
      ++ lia.
      ++ list_solve.
  + intros r' Hr'; pose proof CSR_wf_rowsorted r' ltac:(lia).
    apply sorted_i; [hnf; lia | ]; intros a b Ha Hb.
    pose proof (sorted_e _ H6 a b Ha).
    subst new_row_ptr.
    rewrite Hrows' in Hr'.
    clear coo_csr_entries CSR_wf_rowsorted
         csr' Hrows' partial_CSR_rowptr partial_CSR_colind partial_CSR_val
         partial_CSR_val' partial_CSR_colind' partial_CSR_rowptr'0.
     destruct (rowptr_sorted_e _ CSR_wf_sorted r' (r'+1) ltac:(lia)) as [? _].
     pose proof rowptr_sorted_e _ CSR_wf_sorted (r'+1) (csr_rows csr) ltac:(lia).
     pose proof I.
    destruct (zlt r' r); [ | destruct (zeq r' r)].
   * unfold cd_upto, csr_rows in *.
     rewrite !Znth_app1 by list_solve.
     rewrite !Znth_app1 in Hb by list_solve.
     autorewrite with sublist in H7,Hb|-*.
     apply H7. lia.
   * clear g. subst r'.
     autorewrite with sublist in Hb,H7|-*.
     fold (cd_upto i coo) in *. fold (cd_upto (i+1) coo) in *.
     rewrite <- H4 in *. clear H5.
     unfold csr_rows in *.
     rewrite sublist_app' by list_solve.
     rewrite !sublist_sublist by list_solve.
     rewrite Zlength_sublist by list_solve.
     rewrite (sublist_one 0), Znth_0_cons by list_solve.
     autorewrite with sublist.
     rewrite app_ass. simpl.
     change (?A :: ?B ++ ?C) with ((A::B)++C).
     change (?A :: ?B ++ ?C) with ((A::B)++C) in H7.  
     assert (Znth (r+1) (csr_row_ptr csr) = cd_upto i coo). {
         transitivity (Znth 0 (sublist (r+1) (coo_rows coo + 1) (csr_row_ptr csr))).
         list_solve. rewrite Hlastrows. list_solve.
       }   
     destruct (zlt b (cd_upto i coo +1 - Znth r (csr_row_ptr csr))).
    -- rewrite !Znth_app1 in H7 |-* by list_solve.
       autorewrite with sublist in H7.
       rewrite H5 in *. apply H7. lia.
    -- rewrite (Znth_app2 _ _ _ _ b) by list_solve. autorewrite with sublist.
       destruct (zlt a (cd_upto i coo +1 - Znth r (csr_row_ptr csr))).
       ++
        rewrite Znth_app1 in H7|-* by list_solve.
        rewrite H5 in *. autorewrite with sublist in H7.
        autorewrite with sublist in Hb.
        set (hi := cd_upto i coo) in *. set (lo := Znth r (csr_row_ptr csr)) in *.
        destruct (zeq b (Z.succ (hi-lo))).
        rewrite <- e, Z.sub_diag, Znth_0_cons.
        clear H7 H6.
        destruct (zeq a 0).
          ** subst; rewrite Znth_0_cons.
             pose proof (proj2 (coo_entry_bounds partial_CSR_coo i ltac:(lia))).
             rewrite Hrcx in H1; simpl in H1; clear - H1; lia.
          ** rewrite Znth_pos_cons by lia.
            pose proof coo_csr_zeros r (lo+(a-1)) H3 ltac:(lia).
            simpl in H6. apply In_Znth in H6. destruct H6 as [k [? ?]].
            autorewrite with sublist in H6.
            rewrite Znth_map in H7 by list_solve. autorewrite with sublist in H7.
            autorewrite with sublist. rewrite Z.add_comm.
            pose proof sorted_e _ partial_CSR_coo_sorted k i H6 ltac:(lia).
            destruct (Znth k (coo_entries coo)) as [[rk ck] xk] eqn:Hk.
            simpl in H7. inversion H7; clear H7.
            red in H11. rewrite Hrcx in H11. simpl in H11.
            destruct H11 as [H11|H11]. lia. destruct H11 as [_ H11].
            rewrite <- H14.
            destruct (zeq k (i-1)).
            --- subst k. destruct (Znth (i-1) (coo_entries coo)) as [[??]?]; simpl in *. inv Hk. lia.
            --- pose proof sorted_e _ partial_CSR_coo_sorted k (i-1) ltac:(lia) ltac:(lia).
                red in H7. rewrite Hk in H7. 
                destruct (Znth (i-1) (coo_entries coo)) as [[ri1 ci1] xi1] eqn:Hi1; simpl in *.
                destruct H7; try lia. destruct H7; subst rk. subst ri1.
                pose proof sorted_e _ partial_CSR_coo_sorted (i-1) i ltac:(lia) ltac:(lia).
                red in H1. rewrite Hrcx,Hi1 in H1. simpl in H1. lia.
       ** rewrite (Znth_pos_cons (b - _)) by lia.
          replace (b - Z.succ(hi-lo)-1) with 0 by lia. rewrite Znth_0_cons.
          pose proof (sorted_e _ H6 a (1+(hi-lo)) ltac:(lia) ltac:(list_solve)).
          change (?A :: ?B ++ ?C) with ((A::B)++C) in H11.
          rewrite Znth_app1 in H11 by list_solve.
           rewrite Znth_app2 in H11 by list_solve.
           autorewrite with sublist in H11.
           replace (1 + (hi-lo) - Z.succ(hi-lo)) with 0 in H11 by lia.
           rewrite Znth_0_cons in H11. auto.
      ++ rewrite Znth_app2 by list_solve. autorewrite with sublist.
         set (u := Z.succ _). assert (a-u=0 /\ b-u=1) by list_solve.
         destruct H11. rewrite H11, H12.
         change (c < csr_cols csr).
         clear dependent a. clear dependent b.
         rewrite <- coo_csr_cols.
         clear - Hrcx H0 partial_CSR_coo.
         pose proof (proj2 (coo_entry_bounds partial_CSR_coo i ltac:(lia))).
         rewrite Hrcx in H; apply H.
   * rewrite Znth_app2 by list_solve.
     autorewrite with sublist.
     autorewrite with sublist in Hb.
     list_solve.
- inversion_clear partial_CSR_coo_csr. 
  constructor; auto.
  + rewrite Hrows'. simpl. auto.
  + simpl. rewrite <- H4.
    rewrite Zlength_app. f_equal.
    unfold cd_upto in coo_csr_vals|-*. simpl in coo_csr_vals.
    pose proof (count_distinct_mono (coo_entries coo) i).
    pose proof (count_distinct_bound (sublist 0 i (coo_entries coo))).
    list_solve.
  + intros h Hh. simpl in Hh. autorewrite with sublist in Hh.
    destruct (zlt h i).
   *
    pose proof coo_csr_entries h ltac:(simpl; list_solve). simpl.
    unfold new_row_ptr, cd_upto, coo_upto in H5|-*. simpl in H5|-*.
    rewrite !sublist_sublist, !Znth_sublist, !Z.add_0_r in H5|-* by list_solve.
    destruct (Znth h (coo_entries coo)) as [[rh ch]xh] eqn:Hh'.
    simpl in H5|-*.
    simpl in coo_csr_rows.
    assert (0 <= rh <= r). {
       split.
       - clear - partial_CSR_coo Hh' Hh H0.
         pose proof (proj1 (coo_entry_bounds partial_CSR_coo h ltac:(lia))).
         rewrite Hh' in H; apply H. 
       - pose proof sorted_e _ partial_CSR_coo_sorted h i ltac:(lia) ltac:(lia).
         red in H6. rewrite Hrcx, Hh' in H6. simpl in H6. lia.
     }
     rewrite !(Znth_app1 _ _ _ _ rh), Znth_sublist, Z.add_0_r by list_solve.
     pose proof count_distinct_mono (sublist 0 i (coo_entries coo)) (h+1).
     autorewrite with sublist in H7.
    assert (0 <= count_distinct (sublist 0 i (coo_entries coo)) <= Zlength (csr_col_ind csr)). {
        pose proof (count_distinct_bound (sublist 0 i (coo_entries coo))).
         inversion_clear partial_CSR_wf. rewrite <- CSR_wf_vals. rewrite coo_csr_vals. simpl. lia.
       }
     rewrite (Znth_app1 _ _ _ [c]) by list_solve.
    assert (0 <= count_distinct (sublist 0 (h + 1) (coo_entries coo)) - 1 <
            count_distinct (sublist 0 i (coo_entries coo))). {
       split; [ | lia].
       destruct (zeq h 0). subst h. rewrite sublist_one by lia. simpl. lia.
       pose proof (count_distinct_bound' (sublist 0 (h+1) (coo_entries coo))); list_solve.
    }
    rewrite (Znth_sublist _ (count_distinct (sublist 0 (h + 1) (coo_entries coo)) - 1)) by lia.
    rewrite Z.add_0_r.
    rewrite (sublist_split 0 i (i+1)), (sublist_one i) by lia.
    rewrite (Znth_app1 _ _  _ _ (count_distinct (sublist 0 (h + 1) (coo_entries coo)) - 1)).
    2:{ rewrite Zlength_sublist; try lia. rewrite coo_csr_vals. reflexivity. }          
    rewrite filter_app, map_app; simpl map.
    replace (coord_eqb (rh, ch) (fst (Znth i (coo_entries coo)))) with false.
    2:{ destruct (zeq h (i-1)).
        - subst h. rewrite Hh' in H2. simpl in H2. rewrite Hrcx. clear - H2.
                  unfold coord_eqb. simpl. lia.
        - pose proof sorted_e _ partial_CSR_coo_sorted h (i-1) ltac:(lia) ltac:(lia).
          pose proof sorted_e _ partial_CSR_coo_sorted (i-1) i ltac:(lia) ltac:(lia).
          clear - H11 H10 H2 Hh' H1 Hrcx.
          unfold coord_eqb. simpl. rewrite Hh' in H10. unfold coord_le in *.
          simpl in *. rewrite Hrcx in *.
          destruct (Znth (i-1) (coo_entries coo)) as [[??]?]; simpl in *. lia.
      }
    simpl map; rewrite app_nil_r.
    rewrite Znth_sublist, Z.add_0_r by lia.
    destruct H5 as [?[??]]. split3; auto.
    destruct (zeq rh r). 2: list_solve.
    rewrite Znth_app2 by list_solve.
    rewrite Znth_Zrepeat by list_solve. split; try lia.
    pose proof count_distinct_mono 
         (sublist 0 i (coo_entries coo) ++ [Znth i (coo_entries coo)]) i.
    autorewrite with sublist in H12. lia.
  * assert (h=i) by lia. clear Hh g; subst h.
     simpl. autorewrite with sublist.  rewrite Hrcx. simpl.
     unfold new_row_ptr, cd_upto, coo_upto; simpl.
     assert (r+1 < Zlength (csr_row_ptr csr))
        by (inversion_clear partial_CSR_wf; simpl in *; lia). 
     assert (0 <= count_distinct (sublist 0 i (coo_entries coo)) <= Zlength (csr_col_ind csr)). {
        pose proof (count_distinct_bound (sublist 0 i (coo_entries coo))).
         inversion_clear partial_CSR_wf. rewrite <- CSR_wf_vals. rewrite coo_csr_vals. simpl. lia.
       }     
     autorewrite with sublist.
     rewrite <- H4. replace (_ - _ - _) with 0 by lia.
     split3; [ | list_solve|].
   -- split; [ | lia].
     rewrite Z.add_simpl_r.
     unfold cd_upto in Hcde; rewrite Hcde.
     simpl in coo_csr_rows.
     clear - coo_csr_rows H5 H3 partial_CSR_wf.
     inversion_clear partial_CSR_wf.
     pose proof rowptr_sorted_e _ CSR_wf_sorted r (Zlength (csr_row_ptr csr) -1) ltac:(list_solve).
     unfold csr_rows in *. list_solve.
  -- 
    rewrite (sublist_split 0 i (i+1)), (sublist_one i) by lia.
    rewrite Hrcx, Z.add_simpl_r.
    rewrite filter_app, map_app. simpl map.
    replace (coord_eqb (r,c) (r,c)) with true by (unfold coord_eqb; simpl; lia).
    simpl map.
    simpl in coo_csr_vals. autorewrite with sublist.
    rewrite invariants.filter_none. simpl. constructor.
    clear H6.
    intros. apply In_Znth in H6. destruct H6 as [h [??]]. 
      autorewrite with sublist in H6,H7.
      subst x0.
         pose proof coord_sorted_e _ partial_CSR_coo_sorted h (i-1) ltac:(lia).
         pose proof coord_sorted_e _ partial_CSR_coo_sorted (i-1) i ltac:(lia).
         rewrite Hrcx in H8.
         clear - H7 H8 H2 H1.
         destruct (Znth h (coo_entries coo)) as [[??]?];
         destruct (Znth (i-1) (coo_entries coo)) as [[??]?]; 
         unfold coord_eqb, coord_le in *; simpl in *. lia.
  + intros r' k; simpl; intros.
    unfold new_row_ptr in H6.
    assert (r+1 < Zlength (csr_row_ptr csr))
        by (inversion_clear partial_CSR_wf; simpl in *; lia).
    simpl in coo_csr_rows.
     assert (Hr'r: r' <= r) by list_solve.
    destruct (zlt r' r); autorewrite with sublist in H6.
    * 
     pose proof coo_csr_zeros r' k H5 H6. simpl in H8|-*.
     apply In_Znth in H8. destruct H8 as [h [? ?]].
     autorewrite with sublist in H8.
     rewrite Znth_map in H9 by list_solve. rewrite Znth_sublist in H9 by list_solve.
     rewrite Z.add_0_r in H9.
     assert (0 <= Znth r' (csr_row_ptr csr) /\
             Znth (r' + 1) (csr_row_ptr csr) <= Zlength (csr_col_ind csr)). {
         inversion_clear partial_CSR_wf.
         split.
         eapply rowptr_sorted_e1; try eassumption; lia.
         rewrite <- CSR_wf_vals, CSR_wf_vals'.
         eapply rowptr_sorted_e; try eassumption; lia.
      }
     assert (k < cd_upto i coo <= Zlength (csr_col_ind csr)). {
        inversion_clear partial_CSR_wf. 
        pose proof sorted_e _ (CSR_wf_rowsorted r' ltac:(lia)) 0 (k+1-Znth r' (csr_row_ptr csr)) ltac:(list_solve) ltac:(list_solve).
        list_solve.
     }
     autorewrite with sublist.
     rewrite <- H9. apply in_map.
     replace (Znth h (coo_entries coo)) with (Znth h (sublist 0 (i+1) (coo_entries coo))) by list_solve.
     apply Znth_In. list_solve.
    *  simpl in coo_csr_rows.
       assert (r'=r) by list_solve. clear g Hr'r; subst r'.
       autorewrite with sublist in H6.
       unfold cd_upto, coo_upto.
       assert (0 <= count_distinct (sublist 0 i (coo_entries coo)) <= Zlength (csr_col_ind csr)). {
        pose proof (count_distinct_bound (sublist 0 i (coo_entries coo))).
         inversion_clear partial_CSR_wf. rewrite <- CSR_wf_vals. rewrite coo_csr_vals. simpl. lia.
       }
       destruct (zeq k (cd_upto i coo)).
      -- subst k. unfold cd_upto, coo_upto in *.
         rewrite Znth_app2 by list_solve.
         autorewrite with sublist.
         replace (r,c) with (fst (Znth i (coo_entries coo))) by (rewrite Hrcx; auto).
         apply in_map. replace (Znth i (coo_entries coo)) with (Znth i (sublist 0 (i+1) (coo_entries coo))) by list_solve.
         apply Znth_In. list_solve.
      -- unfold cd_upto, coo_upto  in *. 
           assert (0 <= Znth r (csr_row_ptr csr) /\
               Znth (r + 1) (csr_row_ptr csr) <= Zlength (csr_col_ind csr)). {
         inversion_clear partial_CSR_wf.
         rewrite <- CSR_wf_vals, CSR_wf_vals'.
         pose proof rowptr_sorted_e _ CSR_wf_sorted r (r+1) ltac:(lia).
         pose proof rowptr_sorted_e _ CSR_wf_sorted (r+1) (csr_rows csr) ltac:(lia).
         lia.
      }
      autorewrite with sublist.
      pose proof coo_csr_zeros r k H5 ltac:(list_solve).
      simpl in H10. apply In_Znth in H10. destruct H10 as [h [? ?]]. 
      autorewrite with sublist in H10,H11. rewrite <- H11.
      rewrite Znth_map, Znth_sublist, Z.add_0_r by list_solve.
      replace (Znth h (coo_entries coo)) with (Znth h (sublist 0 (i+1) (coo_entries coo))) by list_solve.
      apply in_map.
      apply Znth_In. list_solve.
-  simpl.
   inversion_clear partial_CSR_coo_csr.
   autorewrite with sublist.
   rewrite coo_csr_vals in partial_CSR_val. simpl in partial_CSR_val.
   fold (cd_upto i coo) in *. set (d := cd_upto i coo) in *. 
   assert (d < Zlength VAL). {
     rewrite partial_CSR_val'.
     unfold d, cd_upto in *.
     pose proof count_distinct_mono (coo_entries coo) (i+1).
     lia.
   }
   rewrite Hrcx. simpl.
   rewrite (sublist_split 0 d) by list_solve.
   rewrite (sublist_one d) by list_solve.
   rewrite sublist_upd_Znth_l by list_solve.
   rewrite partial_CSR_val.
   rewrite map_app.
   rewrite sublist_same by list_solve. f_equal.
   rewrite upd_Znth_same by list_solve. auto.
- simpl. 
  inversion_clear partial_CSR_wf.
  unfold cd_upto, coo_upto in *; simpl in *.
   set (d := count_distinct (sublist 0 i _)) in *.
   rewrite Zlength_app.
   rewrite Zlength_sublist by lia.
   change (Zlength [_]) with 1. rewrite Z.sub_0_r.
   pose proof count_distinct_bound (coo_entries coo).
   pose proof count_distinct_mono (coo_entries coo) (i+1).
   rewrite (sublist_split 0 d (d+1)); [ | lia | ].
      2:  rewrite Zlength_upd_Znth, partial_CSR_colind'; lia.
   rewrite (sublist_one d) by list_solve.
   rewrite map_app. rewrite upd_Znth_same by lia.
   simpl. f_equal.
   rewrite map_sublist.
   rewrite sublist_upd_Znth_l by lia.
   rewrite <- partial_CSR_colind.
   list_solve.
- rewrite partial_CSR_rowptr. f_equal. simpl. unfold new_row_ptr.
  inversion_clear partial_CSR_coo_csr.
  simpl in coo_csr_rows. list_solve.
- list_solve.
- list_solve.
Qed.

Lemma partial_CSR_0: forall (coo: coo_matrix Tdouble),
  coo_matrix_wellformed coo ->
    sorted coord_le (coo_entries coo) ->
 let k := count_distinct (coo_entries coo)
 in k <= Int.max_unsigned ->
   partial_CSR 0 (-1) coo (Zrepeat Vundef (coo_rows coo + 1))
  (Zrepeat Vundef k) (Zrepeat Vundef k).
Proof.
intros. rename H1 into Hk.
pose proof count_distinct_bound (coo_entries coo).
apply build_partial_CSR with (csr := {| csr_cols := coo_cols coo; csr_vals := nil; csr_col_ind :=  nil;
               csr_row_ptr := Zrepeat 0 (coo_rows coo + 1) |}); auto; try rep_lia.
-
inversion_clear H; lia.
- inversion_clear H.
  autorewrite with sublist.
  eapply Forall_impl; try apply H3.
  intros. simpl in H. lia.
- inversion_clear H.
  destruct H2.
  constructor; unfold csr_rows; simpl; try list_solve.
  + intros i j [??]. list_solve.
  + intros. rewrite sublist_nil'. simpl. constructor; try lia. constructor. list_solve.
- constructor; simpl; try list_solve.
  + inversion_clear H. unfold csr_rows; simpl. list_solve.
  + intros  h ?. simpl in H2. list_solve.
  + intros  h ? ?; simpl in *. list_solve.
- list_solve.
- list_solve.
- inversion_clear H. list_solve.
Qed.

Lemma partial_CSR_skiprow:
    forall i r coo ROWPTR COLIND VAL,
    0 <= i < Zlength (coo_entries coo) ->
    r <= fst (fst (Znth i (coo_entries coo))) ->
    partial_CSR i (r-1) coo ROWPTR COLIND VAL ->
    partial_CSR i r coo 
  (upd_Znth r ROWPTR
     (Vint
        (Int.repr (count_distinct (sublist 0 i (coo_entries coo))))))
  COLIND VAL.
Proof.
intros *. pose proof I. intros.
inversion_clear H2.  
pose (d := count_distinct (sublist 0 i (coo_entries coo))).
pose (new_row_ptr := sublist 0 r (csr_row_ptr csr) 
              ++ Zrepeat d (Zlength (csr_row_ptr csr)-r)).
pose (csr' := Build_csr_matrix _ (csr_cols csr) (csr_vals csr) 
                (csr_col_ind csr) new_row_ptr).
assert (Hrows: csr_rows csr = Zlength (csr_row_ptr csr) - 1) by reflexivity.
assert (Hlastrows := partial_CSR_rowptr' (r-1) (coo_upto i coo) csr
   (coo_upto_wellformed i coo ltac:(lia) partial_CSR_coo)
      partial_CSR_wf partial_CSR_coo_csr
      ltac:(change (coo_rows _) with (coo_rows coo); lia)
      partial_CSR_r'). rewrite Z.sub_simpl_r in Hlastrows. simpl in Hlastrows.
apply build_partial_CSR with csr'; auto.
- inversion_clear partial_CSR_coo_csr.
  simpl in *.
  pose proof coo_entry_bounds partial_CSR_coo i ltac:(lia).
  lia.
- eapply Forall_impl; try eassumption. simpl; intros. lia.
- rewrite Forall_forall; intros e He. apply In_Znth in He.
  destruct He as [j [? ?]].
  autorewrite with sublist in H2,H3. subst e.
  pose proof coord_sorted_e _ partial_CSR_coo_sorted i (j+i) ltac:(lia).
  clear - H1 H3 H2 H0.
  destruct (Znth i (coo_entries coo)) as [[ri ci] xi];
  destruct (Znth (j+i) (coo_entries coo)) as [[rj cj] xj]; 
  red in H3; simpl in *. lia.
- inversion_clear partial_CSR_coo_csr.
   inversion_clear partial_CSR_wf.
    subst csr'; subst new_row_ptr; constructor; simpl;
   unfold csr_rows in *; clear Hrows; simpl in *; auto.
  + list_solve.
  + list_solve.
  + intros a b [Ha Hb].
    repeat change (?A :: ?B ++ ?C) with ((A::B)++C).
    pose proof (CSR_wf_sorted a b ltac:(list_solve)).
    destruct (zlt a (r+1)), (zlt b (r+1)).
   * list_solve.
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
     clear dependent VAL. clear dependent COLIND. clear dependent ROWPTR.
     clear CSR_wf_rowsorted.
     fold d in coo_csr_vals. 
     pose proof CSR_wf_sorted a (Zlength (csr_row_ptr csr)) ltac:(list_solve).
     list_solve.
   * lia.
   * rewrite app_ass.
     rewrite Znth_app2 by list_solve. rewrite (Znth_app2 _ _ _ _ b) by list_solve.
     autorewrite with sublist. list_solve.
  + intros r' Hr'.
    assert (Znth r' (csr_row_ptr csr) <= Znth (r'+1) (csr_row_ptr csr) <= d). {
      split. apply (rowptr_sorted_e _ CSR_wf_sorted); list_solve.
      unfold d. rewrite <- coo_csr_vals, CSR_wf_vals'.
      pose proof rowptr_sorted_e _ CSR_wf_sorted (r'+1) (Zlength (csr_row_ptr csr)-1) ltac:(list_solve).
      list_solve.
    } 
    autorewrite with sublist in Hr'.
    replace (r + (Zlength (csr_row_ptr csr) - r) - 1 ) with (Zlength (csr_row_ptr csr) -1) in Hr' by lia.
    pose proof CSR_wf_rowsorted r' ltac:(lia).
    destruct (zlt r' r); [ destruct (zeq (r'+1) r) | ].
   * replace r' with (r-1) in * by lia. clear e l r'. rewrite Z.sub_simpl_r in *.
     autorewrite with sublist in H3|-*.
     assert (Znth r (csr_row_ptr csr) = d). {
        unfold csr_rows in *.
        rewrite coo_csr_rows, Z.sub_simpl_r in Hlastrows.
        transitivity (Znth 0 (sublist r (Zlength (csr_row_ptr csr)) (csr_row_ptr csr))).
        list_solve.
        rewrite Hlastrows. list_solve.
     }
     fold d in coo_csr_vals. rewrite H4 in H3. auto.
   * autorewrite with sublist. auto.
   * autorewrite with sublist. constructor. lia. constructor.
- inversion_clear partial_CSR_coo_csr; subst csr' new_row_ptr; constructor; simpl; auto.
 +
  unfold csr_rows in *; simpl in *; list_solve.
 +
   clear dependent VAL. clear dependent COLIND. clear dependent ROWPTR.
   clear partial_CSR_dbound coo_csr_zeros.
   simpl in *. rewrite coo_csr_rows in partial_CSR_r.
   unfold entries_correspond, csr_rows, cd_upto, coo_upto in *.
   intros h Hh.
   pose proof coo_csr_entries h Hh.
   clear coo_csr_entries.
   simpl Znth in H2|-*. simpl in Hh.
   autorewrite with sublist in Hh.
   autorewrite with sublist in H2|-*.
   pose proof proj1 (coo_entry_bounds partial_CSR_coo h ltac:(lia)).
   destruct (Znth h (coo_entries coo)) as [[rh ch] xh] eqn:?Hh'.
   simpl in H2,H3|-*.
   destruct H2. split; auto.
   autorewrite with sublist.
   destruct (zlt rh r); [ destruct (zeq rh (r-1)) | ].
  * autorewrite with sublist in H2|-*.
    split; try lia.
    subst d.
    pose proof count_distinct_mono (sublist 0 i (coo_entries coo)) (h+1).
    autorewrite with sublist in H5. lia.
  * autorewrite with sublist in H2|-*. auto.
  * autorewrite with sublist in H2|-*.
    exfalso.
    rewrite Forall_forall in partial_CSR_r'.
    specialize (partial_CSR_r' (Znth h (coo_entries coo))).
    spec partial_CSR_r'.
    replace (Znth h (coo_entries coo)) with (Znth h (sublist 0 i (coo_entries coo))) by list_solve.
    apply Znth_In. list_solve.
    rewrite Hh' in partial_CSR_r'. simpl in partial_CSR_r'.
    lia.
 + clear coo_csr_entries.
   clear dependent VAL. clear dependent COLIND. clear dependent ROWPTR.
   intros r' k Hk Hk'.
   specialize (coo_csr_zeros r' k Hk).
   simpl in *.
   destruct (zlt (r'+1) r).
   * autorewrite with sublist in Hk'. auto.
   * autorewrite with sublist in Hk'.
     assert (Hlastrows' : Znth (r'+1) (csr_row_ptr csr) = d). {
        rewrite coo_csr_rows in partial_CSR_r.
        unfold csr_rows in *.
        rewrite coo_csr_rows, Z.sub_simpl_r in Hlastrows.
        list_solve.
     }
     apply coo_csr_zeros.
     list_solve.
- inversion_clear partial_CSR_coo_csr; 
  inversion_clear partial_CSR_wf;
  subst csr' new_row_ptr; simpl in *.
  pose proof proj1 (coo_entry_bounds partial_CSR_coo i H0).
  rewrite !(sublist_split 0 r (r+1)) by list_solve.
  rewrite map_app. f_equal.
  + autorewrite with sublist. 
    rewrite sublist_upd_Znth_l by list_solve. list_solve.
  + rewrite (sublist_one r) by list_solve. autorewrite with sublist.
    rewrite upd_Znth_same by list_solve.
    reflexivity.
- list_solve.
Qed.

Lemma partial_CSR_newrow: 
    forall i r c x coo ROWPTR COLIND VAL,
    0 <= i < Zlength (coo_entries coo) ->
    Znth i (coo_entries coo) = (r,c,x) ->
    (i <> 0 -> fst (fst (Znth (i - 1) (coo_entries coo))) <> r) ->
    partial_CSR i r coo ROWPTR COLIND VAL ->
    partial_CSR (i + 1) r coo ROWPTR
     (upd_Znth (count_distinct (sublist 0 i (coo_entries coo))) COLIND
        (Vint (Int.repr c)))
     (upd_Znth (count_distinct (sublist 0 i (coo_entries coo))) VAL
        (Vfloat x)).
Proof.
intros * H Hrcx Hnew H0.
inversion_clear H0.
assert (Hr := proj1( coo_entry_bounds partial_CSR_coo i ltac:(lia))).
  rewrite Hrcx in Hr; simpl in Hr; clear partial_CSR_r.
assert (Hr1: Znth (r+1) (csr_row_ptr csr) = Znth r (csr_row_ptr csr)). {
    inversion_clear partial_CSR_wf.
    inversion_clear partial_CSR_coo_csr.
    red in coo_csr_zeros.
    unfold csr_rows in *. simpl in *.
    pose proof proj2 (proj1 (rowptr_sorted_e _ CSR_wf_sorted r (r+1) ltac:(lia))).
    destruct (zlt (Znth r (csr_row_ptr csr)) (Znth (r+1) (csr_row_ptr csr))); [ | lia].
    exfalso.
    specialize (coo_csr_zeros r (Znth r (csr_row_ptr csr)) ltac:(lia)).
    spec coo_csr_zeros. lia.
     apply In_Znth in coo_csr_zeros.
     destruct coo_csr_zeros as [k [? ?]].
     autorewrite with sublist in H1,H2.
     pose proof coord_sorted_e _ partial_CSR_coo_sorted k (i-1) ltac:(lia).
     pose proof coord_sorted_e _ partial_CSR_coo_sorted (i-1) i ltac:(lia).
     rewrite Znth_map, Znth_sublist, Z.add_0_r in H2 by list_solve.
     specialize (Hnew ltac:(lia)). 
     clear - H2 H3 H4 Hnew Hrcx. rewrite Hrcx in *.
     destruct (Znth k (coo_entries coo)) as [[rk ck]xk], (Znth (i-1) (coo_entries coo)) as [[r1 c1]x1].
     inv H2. unfold coord_le in *. simpl in *. lia.
  }
set (d := count_distinct (sublist 0 i (coo_entries coo))) in *.
pose (new_row_ptr := sublist 0 (r+1) (csr_row_ptr csr) 
              ++ Zrepeat (d+1) (Zlength (csr_row_ptr csr)-(r+1))).
pose (csr' := {| csr_cols := csr_cols csr; 
                 csr_vals := csr_vals csr ++ [x];
                 csr_col_ind := csr_col_ind csr ++ [c];
                 csr_row_ptr := new_row_ptr |}).
assert (Hrows: csr_rows csr = Zlength (csr_row_ptr csr) - 1) by reflexivity.
assert (Hlastrows' := partial_CSR_rowptr' r (coo_upto i coo) csr
         (coo_upto_wellformed i coo ltac:(lia) partial_CSR_coo)
       partial_CSR_wf partial_CSR_coo_csr
      ltac:(change (coo_rows _) with (coo_rows coo); lia)
      partial_CSR_r'). simpl in Hlastrows'.
assert (Hlastrows: sublist r (coo_rows coo + 1) (csr_row_ptr csr) = Zrepeat (Zlength (csr_vals csr)) (coo_rows coo + 1 - r)). {
  inversion_clear partial_CSR_coo_csr. unfold csr_rows in *; simpl in *.
  rewrite (sublist_split r (r+1)) by list_solve.
  replace (coo_rows coo + 1 - r) with (1 + (coo_rows coo - r)) by lia.
  rewrite <- Zrepeat_app by lia.
  f_equal.
  rewrite sublist_one by lia. rewrite <- Hr1.
  replace (Znth (r+1) (csr_row_ptr csr)) with (Znth 0 (sublist (r+1) (coo_rows coo + 1) (csr_row_ptr csr))) by list_solve.
  rewrite Hlastrows'. list_solve.
  list_solve.
}
clear Hlastrows'.  
assert (Hincr: count_distinct (sublist 0 i (coo_entries coo)) + 1 =
               count_distinct (sublist 0 (i + 1) (coo_entries coo))). {
  destruct (zeq i 0). subst; simpl. destruct (coo_entries coo); simpl; list_solve.
  spec Hnew. lia.
  apply count_distinct_incr; try lia.
  red. 
  pose proof coord_sorted_e _ partial_CSR_coo_sorted (i-1) i ltac:(lia).
  clear - Hnew H0 Hrcx. rewrite Hrcx in *.
      destruct (Znth (i-1) (coo_entries coo)) as [[r1 c1] x1]; hnf; unfold coord_le in *; simpl in *; lia.
}
apply build_partial_CSR with csr'; auto; try lia.
- simpl. rewrite (sublist_split 0 i) by lia. apply Forall_app. split; auto.
  rewrite sublist_one by lia. repeat constructor. rewrite Hrcx. simpl; lia.
- rewrite (sublist_split i (i+1)) in partial_CSR_r''  by lia.
  rewrite Forall_app in partial_CSR_r''. apply partial_CSR_r''.
- subst csr'; inversion_clear partial_CSR_wf; constructor; simpl; auto.
 + inversion_clear partial_CSR_coo_csr.
   unfold new_row_ptr, csr_rows in *; simpl in *. list_solve.
 + list_solve.
 + unfold new_row_ptr, csr_rows in *; simpl in *.
   inversion_clear partial_CSR_coo_csr.
   simpl in *. fold d in coo_csr_vals.
   list_solve.
 + assert (Hd': d + 1 <= Int.max_unsigned). {
      destruct (zeq i 0).
     - subst i. subst d. autorewrite with sublist. rep_lia.
     - unfold d. rewrite Hincr. 
      transitivity (count_distinct (coo_entries coo)); auto.
      apply count_distinct_mono.
   }
   subst new_row_ptr.
   inversion_clear partial_CSR_coo_csr.
   intros a b [? ?].
   unfold csr_rows in *; simpl in *.
   autorewrite with sublist in H1.
   assert (b <= Zlength (csr_row_ptr csr) + 1) by lia. clear H1.
   destruct (zlt a b); [ | assert (a=b) by lia; subst; lia].
   destruct H0 as [H0 _].
   destruct (zlt 0 b); [ | list_solve].
   destruct (zlt 0 a); [ | list_solve]. clear H0 l0.
   destruct (zlt b (r+2)); [pose proof (CSR_wf_sorted a b ltac:(list_solve)); list_solve | ].
   rewrite !Znth_pos_cons by lia.
   rewrite (Znth_app1 _ _ _ _ (a-1)) by list_solve.
   destruct (zlt a (r+2)); [ | list_solve].
   rewrite Znth_app1 by list_solve.
   rewrite app_ass. rewrite Znth_app2 by list_solve.
   autorewrite with sublist.
   destruct (zlt b (Zlength (csr_row_ptr csr) + 1)). list_solve.
   list_solve.
 + inversion_clear partial_CSR_coo_csr.
   unfold csr_rows, new_row_ptr in *; simpl in *.
   autorewrite with sublist.
   intros r' Hr'. assert (0 <= r' < Zlength (csr_row_ptr csr) - 1) by lia. clear Hr'.
   pose proof (CSR_wf_rowsorted _ H0).
   pose proof proj1 (rowptr_sorted_e _ CSR_wf_sorted r' (r'+1) ltac:(list_solve)).
   pose proof rowptr_sorted_e _ CSR_wf_sorted (r'+1) (Zlength (csr_row_ptr csr)-1) ltac:(list_solve).
   destruct (zlt r' r); [ | destruct (zeq r' r)].
  * autorewrite with sublist. auto.
  * subst r'. autorewrite with sublist.
    clear g.
    assert (Znth (r+1) (csr_row_ptr csr) = d). {
     replace (Znth (r+1) (csr_row_ptr csr)) with (Znth 0 (sublist (r + 1) (coo_rows coo + 1) (csr_row_ptr csr) ))
      by list_solve. list_solve.
    }
    rewrite <- Hr1, H4. autorewrite with sublist. simpl.
    assert (Hc := proj2 (coo_entry_bounds partial_CSR_coo i ltac:(lia))). rewrite Hrcx in Hc; simpl in Hc.
    constructor; auto. lia. constructor; auto. lia. constructor.
  * autorewrite with sublist. constructor; auto. lia. constructor.
- inversion_clear partial_CSR_coo_csr.
  subst csr' new_row_ptr; constructor; unfold csr_rows in *; simpl in *; auto.
  + list_solve.
  + rewrite <- Hincr.
    rewrite Zlength_app. f_equal. lia.
  + intros h Hh.
    destruct (zlt h i).
   * red in coo_csr_entries. unfold cd_upto, coo_upto, csr_rows in *; simpl in *.
     pose proof (coo_csr_entries h ltac:(list_solve)).
     autorewrite with sublist in H0|-*.
     destruct (Znth h (coo_entries coo)) as [[rh ch] xh] eqn:Hh'.
     simpl in *.
     assert (0 <= rh <= r). { 
       pose proof proj1 (coo_entry_bounds partial_CSR_coo h ltac:(lia)).
       pose proof coord_sorted_e _ partial_CSR_coo_sorted h i ltac:(lia). 
       rewrite Hh', Hrcx in *.
       clear - H1 H2; red in H2; simpl in *; lia.
     }
     autorewrite with sublist.
     rewrite (Znth_app1 _ _ _ _ (rh+1)) by list_solve.
     rewrite Znth_sublist by list_solve.
     rewrite Z.add_0_r.
     pose proof count_distinct_mono (sublist 0 i (coo_entries coo)) (h+1).
     autorewrite with sublist in H2.
     rewrite Znth_app1 by (inversion_clear partial_CSR_wf; lia).
     rewrite (sublist_split 0 i (i+1)), (sublist_one i) by lia.
     rewrite filter_app, map_app. simpl map.
     replace (coord_eqb _ _) with false. rewrite app_nil_r.
     2: { clear - Hrcx Hnew Hh Hh' l partial_CSR_coo_sorted H. spec Hnew. lia.
       pose proof coord_sorted_e _ partial_CSR_coo_sorted h (i-1) ltac:(lia).
       pose proof coord_sorted_e _ partial_CSR_coo_sorted (i-1) i ltac:(lia).
       unfold coord_eqb, coord_le in *.
       rewrite Hrcx in *.
       destruct (Znth (i-1) (coo_entries coo)) as [[??]?];
       destruct (Znth h (coo_entries coo)) as [[??]?];
       simpl in *; try lia. inv Hh'; lia.      
     }
     rewrite Znth_app1 by list_solve.
     destruct H0 as [?[??]]; split3; auto.
   * simpl in Hh. assert (h=i) by list_solve. subst h. clear Hh g.
     unfold cd_upto, coo_upto; simpl; autorewrite with sublist.
     rewrite Hrcx. simpl. autorewrite with sublist.
     rewrite coo_csr_rows, Z.sub_simpl_r in Hlastrows.
     replace (Znth r (csr_row_ptr csr)) with (Znth 0 (sublist r (Zlength (csr_row_ptr csr)) (csr_row_ptr csr))) by list_solve.
     rewrite Hlastrows. autorewrite with sublist.
     rewrite coo_csr_vals.
     rewrite <- Hincr. split3.
    -- lia.
    -- fold d. rewrite Z.add_simpl_r.
       replace d with (Zlength (csr_col_ind csr))
         by (inversion_clear partial_CSR_wf; list_solve).
       list_solve.
    -- rewrite Z.add_simpl_r, Znth_app2 by lia.
       rewrite coo_csr_vals. autorewrite with sublist.
     rewrite (sublist_split 0 i), (sublist_one i) by list_solve.
     rewrite filter_app.
     rewrite invariants.filter_none. simpl.
     replace (coord_eqb _ _) with true.
     rewrite Hrcx.  constructor.
     rewrite Hrcx. unfold coord_eqb. clear; simpl; lia.
     intros. apply In_Znth in H0. destruct H0 as [k [? ?]].
     autorewrite with sublist in H0,H1. subst x0.
      {clear - Hrcx Hnew H0 partial_CSR_coo_sorted H. spec Hnew. lia.
       pose proof coord_sorted_e _ partial_CSR_coo_sorted k (i-1) ltac:(lia).
       pose proof coord_sorted_e _ partial_CSR_coo_sorted (i-1) i ltac:(lia).
       unfold coord_eqb, coord_le in *.
       rewrite Hrcx in *.
       destruct (Znth (i-1) (coo_entries coo)) as [[??]?];
       destruct (Znth k (coo_entries coo)) as [[??]?];
       simpl in *; lia.      
     }
 + 
   inversion_clear partial_CSR_wf.
   intros r' k Hr'. specialize (coo_csr_zeros r' k Hr'). 
   unfold cd_upto, coo_upto, csr_rows in *; simpl in *.
   clear coo_csr_entries.
   pose proof proj2 (proj1 (rowptr_sorted_e _ CSR_wf_sorted (r'+1) (Zlength (csr_row_ptr csr) -1) ltac:(lia))).
  
   destruct (zlt r' r); [ | destruct (zeq r' r)].
   *  autorewrite with sublist. intro. 
      rewrite Znth_app1 by list_solve.
      spec coo_csr_zeros. list_solve.
      apply In_Znth in coo_csr_zeros.
      destruct coo_csr_zeros as [j [? ?]].
      autorewrite with sublist in H2.
      rewrite Znth_map, Znth_sublist, Z.add_0_r in H3 by list_solve.
      rewrite <- H3. apply in_map.
      assert (In (Znth j (sublist 0 (i+1) (coo_entries coo))) (sublist 0 (i+1) (coo_entries coo))).
      apply Znth_In; list_solve. autorewrite with sublist in H4; auto.
   * subst r'. autorewrite with sublist.
     intro.
     assert (Znth 0 (sublist r (coo_rows coo + 1) (csr_row_ptr csr))  = d).
     rewrite Hlastrows. autorewrite with sublist. lia.
     autorewrite with sublist in H2. assert (k=d) by lia. subst k.
     autorewrite with sublist.
     replace (d - Zlength (csr_col_ind csr)) with 0 by list_solve. rewrite Znth_0_cons.
     replace (r,c) with (fst (Znth i (coo_entries coo))) by (rewrite Hrcx; auto).
     apply in_map.
     replace (Znth i (coo_entries coo)) with (Znth i (sublist 0 (i+1) (coo_entries coo))) by list_solve.
     apply Znth_In. list_solve.
   * autorewrite with sublist. intro. lia.
- inversion_clear partial_CSR_wf.
  inversion_clear partial_CSR_coo_csr.
  unfold cd_upto, coo_upto, csr_rows in *; simpl in *.
  subst csr' new_row_ptr; simpl in *.
  pose proof count_distinct_bound (sublist 0 i (coo_entries coo)).
     pose proof count_distinct_mono (coo_entries coo) (i+1).
    rewrite (sublist_split 0 d) by list_solve.
    rewrite sublist_upd_Znth_l by list_solve.
    rewrite (sublist_one d) by list_solve.
    rewrite upd_Znth_same by list_solve.
    rewrite map_app. f_equal. list_solve.
- inversion_clear partial_CSR_wf.
  inversion_clear partial_CSR_coo_csr.
  unfold cd_upto, coo_upto, csr_rows in *; simpl in *.
  subst csr' new_row_ptr; simpl in *.
  pose proof count_distinct_bound (sublist 0 i (coo_entries coo)).
     pose proof count_distinct_mono (coo_entries coo) (i+1).
    rewrite (sublist_split 0 d) by list_solve.
    rewrite sublist_upd_Znth_l by list_solve.
    rewrite (sublist_one d) by list_solve.
    rewrite upd_Znth_same by list_solve.
    rewrite map_app. f_equal. list_solve.
- inversion_clear partial_CSR_wf.
  inversion_clear partial_CSR_coo_csr.
  unfold cd_upto, coo_upto, csr_rows in *; simpl in *.
  unfold csr', new_row_ptr. simpl. rewrite partial_CSR_rowptr.
  f_equal. list_solve.
- list_solve.
- list_solve.
Qed.

Lemma partial_CSR_lastrows:
   forall r coo ROWPTR COLIND VAL,
    r <= coo_rows coo ->
   partial_CSR (Zlength (coo_entries coo)) (r-1) coo ROWPTR COLIND VAL ->
   partial_CSR (Zlength (coo_entries coo)) r coo 
     (upd_Znth r ROWPTR (Vint (Int.repr (count_distinct (coo_entries coo))))) COLIND VAL.
Proof.
intros.
inversion_clear H0.
apply build_partial_CSR with csr; auto; try lia.
- eapply Forall_impl; try eassumption. simpl; intros. lia.
- autorewrite with sublist. constructor.
- replace (coo_upto (Zlength (coo_entries coo)) coo) with coo in *
    by (unfold coo_upto;  destruct coo; simpl; f_equal; rewrite sublist_same; auto).
 pose proof partial_CSR_rowptr' (r-1) _ _ partial_CSR_coo partial_CSR_wf partial_CSR_coo_csr ltac:(lia) ltac:(assumption).
  inversion_clear partial_CSR_coo_csr; unfold csr_rows in *; simpl in *.
  rewrite !(sublist_split 0 r (r+1)) by list_solve.
  rewrite sublist_upd_Znth_l by list_solve.
  rewrite map_app.
  rewrite Z.sub_simpl_r in *.
  f_equal; auto.
  rewrite !sublist_one by list_solve. rewrite upd_Znth_same by list_solve.
  simpl. f_equal; f_equal; f_equal. list_solve.
- list_solve.
Qed.

Lemma csr_row_rep_colsnonneg: 
   forall {t} cols (vals: list (ftype t)) col_ind v, 
       csr_row_rep cols vals col_ind v ->
       Zlength vals = Zlength col_ind ->
       Forall (Z.le 0) (col_ind ++ [cols]).
Proof.
intros.
apply Forall_app; split.
-
induction H. constructor. spec IHcsr_row_rep. list_solve.
 clear - IHcsr_row_rep. induction col_ind. constructor.
  inv IHcsr_row_rep. constructor. lia. auto.
  constructor.  lia. spec IHcsr_row_rep. list_solve.
 clear - IHcsr_row_rep. induction col_ind. constructor.
  inv IHcsr_row_rep. constructor. lia. auto.
-
repeat constructor.
induction H; try lia.
spec IHcsr_row_rep. list_solve. lia.
spec IHcsr_row_rep. list_solve. lia.
Qed.


Lemma matrix_index_Z: forall {t} (m: matrix t) cols i j,
  matrix_cols m cols ->
  0 <= i < matrix_rows m ->
  0 <= j < cols ->
  matrix_index m (Z.to_nat i) (Z.to_nat j) = Znth j (Znth i m).
Proof.
  unfold matrix_index, matrix_rows. intros.
  rewrite (nth_Znth i) by list_solve.
  red in H; rewrite Forall_forall in H.
  rewrite nth_Znth by (rewrite H; auto; apply Znth_In; lia).
  auto.
Qed.

Lemma coo_to_matrix_build_csr_matrix: 
  forall {t} 
  (coo : coo_matrix t)
  (csr : csr_matrix t)
  (partial_CSR_coo : coo_matrix_wellformed coo)
  (partial_CSR_wf : csr_matrix_wellformed csr)
  (partial_CSR_coo_csr : coo_csr coo csr),
  csr_to_matrix csr (build_csr_matrix csr) ->
  coo_to_matrix coo (build_csr_matrix csr).
Proof.
intros.
inversion_clear partial_CSR_coo.
inversion_clear partial_CSR_wf.
inversion_clear partial_CSR_coo_csr.
red in H; decompose [and] H; clear H.
assert (Hcols: matrix_cols (build_csr_matrix csr) (coo_cols coo)). {
  red. unfold build_csr_matrix in *.
  rewrite coo_csr_cols.
  clear dependent coo.
  unfold csr_rows in *.
  destruct csr as [cols vals colind rowptr].
  simpl csr_vals in *. simpl csr_row_ptr in *. simpl csr_col_ind in *. simpl csr_cols in *.
  destruct rowptr as [ | k rowptr];  [ list_solve | ].
  subst csr_rows. clear H5.
  pose (u := k::rowptr). change (build_csr_rows
     {|
       csr_cols := cols;
       csr_vals := vals;
       csr_col_ind := colind;
       csr_row_ptr := k :: rowptr
     |}) with (build_csr_rows
     {|
       csr_cols := cols;
       csr_vals := vals;
       csr_col_ind := colind;
       csr_row_ptr := u
     |}) in *.
  clearbody u. 
  set (csr := {|
            csr_cols := cols;
            csr_vals := vals;
            csr_col_ind := colind;
            csr_row_ptr := u
          |}) in *.
  clear H3 H4.
  revert k CSR_wf_rows CSR_wf_vals' CSR_wf_sorted CSR_wf_rowsorted H2 H7.
  induction rowptr; intros; constructor.
 + specialize (H7 0 ltac:(list_solve)). autorewrite with sublist in H7.
   unfold build_csr_rows in H7; fold (@build_csr_rows t) in H7.
   rewrite !(Znth_pos_cons 1), !Z.sub_diag, !Znth_0_cons in H7 by lia.
   set (row := build_csr_row _ _ _) in H7|-*. clearbody row.
   assert (0 <= k <= a /\ a <= Zlength vals). {
     clear - CSR_wf_sorted CSR_wf_vals CSR_wf_vals'.
     rewrite CSR_wf_vals'.
     pose proof rowptr_sorted_e _ CSR_wf_sorted 0 1 ltac:(list_solve).
     pose proof rowptr_sorted_e _ CSR_wf_sorted 1 (Zlength (a::rowptr)) ltac:(list_solve).
     list_solve.
    }
    pose proof CSR_wf_rowsorted 0 ltac:(list_solve).
    autorewrite with sublist in H0.
    rewrite Znth_pos_cons, Z.sub_diag, Znth_0_cons in H0 by lia.
    assert (Zlength (sublist k a vals) = a-k) by list_solve.
    assert (Zlength (sublist k a colind) = a-k) by list_solve.
    rewrite <- H3 in H1.
    forget (sublist k a vals) as vals'.
    forget (sublist k a colind) as colind'.
    clear - H1 H0 H7.
    induction H7.
    * list_solve.
   * 
    pose proof csr_row_rep_colsnonneg _ _ _ _ H7 ltac:(list_solve).
    assert (Zlength v = cols - 1); [ | list_solve].
    apply IHcsr_row_rep.
    --
    clear - H H0.
    change [cols-1] with (map Z.pred [cols]) in *. rewrite <- map_app in *.  
    apply sorted_cons_e2 in H0.
    induction (col_ind++[cols]); simpl in *; constructor; try lia.
    inv H. lia. change (sorted Z.lt (map Z.pred (a::l))).
    clear - H0. induction H0; constructor; auto. lia.
    -- list_solve.
   * pose proof csr_row_rep_colsnonneg _ _ _ _ H7 ltac:(list_solve).
    assert (Zlength v = cols - 1); [ | list_solve].
    apply IHcsr_row_rep.
    --
    clear - H H0. simpl in H0.
    change [cols-1] with (map Z.pred [cols]) in *. rewrite <- map_app in *.  
    apply sorted_cons_e2 in H0.
    change (-1) with (Z.pred 0). 
    change (sorted Z.lt (map Z.pred (0::col_ind ++ [cols]))). clear H.
    induction H0; constructor; auto. lia.
    -- list_solve.
 + fold (@build_csr_rows t).
    apply IHrowptr; auto; try lia.
   * list_solve.
   * list_solve. 
   * clear - CSR_wf_sorted.
     intros i j [? ?].
     destruct (zeq i 0), (zeq j 0); subst; autorewrite with sublist; try lia.
     -- specialize (CSR_wf_sorted 0 (j+1) ltac:(list_solve)); list_solve.
     -- specialize (CSR_wf_sorted (i+1) (j+1) ltac:(list_solve)); list_solve.
   * intros. specialize (CSR_wf_rowsorted (r+1) ltac:(list_solve)).
     clear - CSR_wf_rowsorted H.
     rewrite !(Znth_pos_cons (_ + _)), !Z.add_simpl_r in CSR_wf_rowsorted by list_solve.     
     rewrite !(Znth_pos_cons (_ + _)), Z.add_simpl_r in CSR_wf_rowsorted by list_solve.
     rewrite !(Znth_pos_cons (_ + _)), Z.add_simpl_r  by list_solve.
     auto.
   * clear - H2. autorewrite with sublist in *.
     unfold build_csr_rows in H2; fold (@build_csr_rows t) in H2. list_solve.
   * intros. unfold build_csr_rows in H7; fold (@build_csr_rows t) in H7.
     specialize (H7 (j+1) ltac:(list_solve)).
     repeat rewrite !(Znth_pos_cons (_ + _)), !Z.add_simpl_r in H7 by list_solve.
     rewrite !(Znth_pos_cons (_ + _)), !Z.add_simpl_r by list_solve.
     auto.
}
split3; auto.
- unfold matrix_rows, csr_rows in *; lia.
- intros.
  assert (csr_rows csr = Zlength (csr_row_ptr csr) - 1) by reflexivity.
  specialize (H7 i ltac:(lia)).
  erewrite matrix_index_Z; try eassumption;
 [ | unfold matrix_rows; list_solve].
  red in coo_csr_zeros, coo_csr_entries.
  assert (Hi := CSR_wf_sorted 0 (i+1) ltac:(list_solve)).
    autorewrite with sublist in Hi.
    rewrite Znth_pos_cons, Z.add_simpl_r, Znth_app1 in Hi by list_solve.
  assert (Hi' := CSR_wf_sorted (i+1) (i+1+1) ltac:(list_solve)).
    autorewrite with sublist in Hi.
    rewrite !Znth_pos_cons, !Z.add_simpl_r in Hi' by list_solve.
    rewrite !Znth_app1 in Hi' by list_solve.
  assert (Hi1 := CSR_wf_sorted (i+1+1) (Zlength (csr_row_ptr csr)) ltac:(list_solve)).
    rewrite (Znth_pos_cons (i+1+1)), Z.add_simpl_r in Hi1 by list_solve.
    rewrite (Znth_pos_cons (Zlength (csr_row_ptr csr))) in Hi1 by list_solve.
    rewrite !Znth_app1 in Hi1 by list_solve.
    rewrite <- H8 in Hi1.
  destruct (filter _ _) eqn:Hfilter.
 +
  simpl.
  specialize (coo_csr_zeros i).
  assert (Znth j (Znth i (build_csr_matrix csr)) = Zconst t 0); [ |rewrite H9; constructor].
  assert (~In (i,j) (map fst (coo_entries coo))). {
    intro. apply list_in_map_inv in H9. destruct H9 as [x [? ?]].
    assert (In x (filter (coord_eqb (i, j) oo fst) (coo_entries coo))). {
      destruct x. simpl in H9; subst p. rewrite filter_In. split; auto. simpl.
      unfold coord_eqb; simpl; lia.
    }
  rewrite Hfilter in H11. apply H11.
  }
  clear Hfilter.
  assert (~In j (sublist (Znth i (csr_row_ptr csr))
                         (Znth (i + 1) (csr_row_ptr csr)) (csr_col_ind csr))). {
    contradict H9.  apply In_Znth in H9. destruct H9 as [k [? ?]].
    autorewrite with sublist in H9, H10.
    specialize (coo_csr_zeros (k + Znth i (csr_row_ptr csr)) ltac:(list_solve) ltac:(list_solve)).
    subst j. auto. 
  }
  clear H9.
  forget (Znth i (csr_row_ptr csr)) as lo.
  forget (Znth (i+1) (csr_row_ptr csr)) as hi.
  assert (Zlength (sublist lo hi (csr_vals csr)) = Zlength (sublist lo hi (csr_col_ind csr))) by list_solve.
  red in Hcols; rewrite Forall_forall in Hcols. specialize (Hcols (Znth i (build_csr_matrix csr))).
  rewrite <- Hcols in H6 by (apply Znth_In; lia).
  forget (Znth i (build_csr_matrix csr)) as rowvals.
  forget (sublist lo hi (csr_vals csr)) as vals.
  forget (sublist lo hi (csr_col_ind csr)) as colind.
  clear - H10 H9 H7 H6.
  revert j H6 H10; induction H7; intros.
  * list_solve.
  * destruct (zeq j 0). subst. reflexivity.
    rewrite Znth_pos_cons by lia.
    apply IHcsr_row_rep. list_solve. list_solve.
    contradict H10. apply list_in_map_inv in H10.
    destruct H10 as [x [? ?]]. assert (j=x) by lia. subst. auto.
  * assert (j<>0 /\ ~ In j col_ind). split; contradict H10; simpl; auto.
    destruct H.
    rewrite Znth_pos_cons by lia.
    apply IHcsr_row_rep. list_solve. list_solve.
    contradict H0.
   apply list_in_map_inv in H0.
    destruct H0 as [y [? ?]]. assert (j=y) by lia. subst. auto.
 + 
  assert (In p (coo_entries coo) /\ (coord_eqb (i,j) oo fst) p = true). {
    apply filter_In. rewrite Hfilter. left; auto.
  }
 rewrite <- Hfilter. clear l Hfilter.
 destruct H9.
 apply In_Znth in H9. destruct H9 as [h [? ?]].
 subst p.
 specialize (coo_csr_entries h H9).
 destruct (Znth h (coo_entries coo)) as [[i' j'] x] eqn:?Hh.
 unfold coord_eqb in H10. simpl in H10.
 assert (i'=i /\ j'=j) by lia. clear H10; destruct H11; subst i' j'.
 simpl in coo_csr_entries.
 destruct coo_csr_entries as [H10 [H11 coo_csr_values]].
 replace   (Znth j (Znth i (build_csr_matrix csr)))
   with (Znth (cd_upto (h + 1) coo - 1) (csr_vals csr)); auto.
 subst j.
 forget (cd_upto (h + 1) coo - 1) as k.
 rewrite coo_csr_rows in H.
 rewrite coo_csr_cols in H6, Hcols.
 clear h Hh H9 H5. clear dependent coo.
 forget (build_csr_matrix csr) as m.
 forget (Znth i (csr_row_ptr csr)) as lo.
 forget (Znth (i+1) (csr_row_ptr csr)) as hi.
 assert (Zlength (sublist lo hi (csr_vals csr)) = Zlength (sublist lo hi (csr_col_ind csr))) by list_solve.
 forget (Znth i m) as rowvals.
 assert (0 <= Znth (k-lo) (sublist lo hi (csr_col_ind csr)) < csr_cols csr)
   by (autorewrite with sublist; auto); clear H6.
 transitivity (Znth (k-lo) (sublist lo hi (csr_vals csr))); [
   | transitivity (Znth (Znth (k-lo) (sublist lo hi (csr_col_ind csr))) rowvals)];
   [ list_solve | | list_solve].
 assert (0 <= k-lo < Zlength (sublist lo hi (csr_vals csr))) by list_solve.
 forget (k-lo) as k'. clear dependent k.
 forget (sublist lo hi (csr_vals csr)) as vals.
 forget (sublist lo hi (csr_col_ind csr)) as colind.
 clear lo hi Hi Hi' Hi1. clear i H.
 clear m Hcols H2 H4 H3 H8.
(* ? *)
 clear - H7 H1 H5 H0.
 revert k' H1 H5; induction H7; intros.
  * list_solve.
  * pose proof csr_row_rep_colsnonneg _ _ _ _ H7 ltac:(list_solve).
    apply Forall_app in H. destruct H.
    rewrite Forall_forall in H. specialize (H (Z.pred (Znth k' col_ind))).
    spec H. apply in_map. apply Znth_In. lia.
    rewrite Znth_pos_cons by lia. rewrite IHcsr_row_rep by list_solve.
    f_equal. rewrite Znth_map by lia. lia.
  * destruct (zeq k' 0). subst. autorewrite with sublist. auto.
    rewrite !(Znth_pos_cons k') by lia.
    rewrite Znth_pos_cons in H1 by lia.
    assert (Znth (k'-1) col_ind > 0).
    pose proof csr_row_rep_colsnonneg _ _ _ _ H7 ltac:(list_solve).
    apply Forall_app in H. destruct H.
    rewrite Forall_forall in H. specialize (H (Z.pred (Znth (k'-1) col_ind))).
    spec H. apply in_map. apply Znth_In. list_solve. lia.
    rewrite Znth_pos_cons by lia. rewrite IHcsr_row_rep by list_solve.
    f_equal. list_solve.
Qed.

Lemma partial_CSR_properties:
  forall coo ROWPTR COLIND VAL,
    partial_CSR (Zlength (coo_entries coo)) (coo_rows coo) coo ROWPTR COLIND VAL ->
    exists (m: matrix Tdouble) (csr: csr_matrix Tdouble),
            csr_to_matrix csr m /\ coo_to_matrix coo m
            /\ coo_rows coo = matrix_rows m 
            /\ coo_cols coo = csr_cols csr 
            /\ map Vfloat (csr_vals csr) = VAL
            /\ Zlength (csr_col_ind csr) = count_distinct (coo_entries coo)
            /\ map Vint (map Int.repr (csr_col_ind csr)) = COLIND
            /\ map Vint (map Int.repr (csr_row_ptr csr)) = ROWPTR
            /\ Zlength (csr_vals csr) = count_distinct (coo_entries coo).
Proof.
intros.
inversion_clear H.
pose proof build_csr_matrix_correct csr partial_CSR_wf.
set (m := build_csr_matrix csr) in *.
exists m, csr.
replace (coo_upto (Zlength (coo_entries coo)) coo) with coo in *. 2:{
  unfold coo_upto. autorewrite with sublist. clear. destruct coo; auto.
}
repeat simple apply conj; auto.
- apply coo_to_matrix_build_csr_matrix; auto.
- red in H. decompose[and] H; clear H. unfold matrix_rows.
  inversion_clear partial_CSR_coo_csr. rewrite coo_csr_rows.
  unfold csr_rows; rewrite H0. lia.
-   inversion_clear partial_CSR_coo_csr; auto.
- rewrite <- partial_CSR_val.  
  inversion_clear partial_CSR_coo_csr. rewrite coo_csr_vals.
  rewrite sublist_same; auto.
- 
  inversion_clear partial_CSR_coo_csr. 
  inversion_clear partial_CSR_wf. 
  lia.
- rewrite list_map_compose. fold (Vint oo Int.repr). rewrite <- partial_CSR_colind.
  apply sublist_same; auto. rewrite partial_CSR_colind'. 
  inversion_clear partial_CSR_coo_csr. 
  inversion_clear partial_CSR_wf. lia.
- 
  inversion_clear partial_CSR_coo_csr. 
  inversion_clear partial_CSR_wf.
  unfold csr_rows in *.
  rewrite list_map_compose. fold (Vint oo Int.repr).
  autorewrite with sublist in partial_CSR_rowptr. list_solve.
- 
  inversion_clear partial_CSR_coo_csr. 
  inversion_clear partial_CSR_wf.
  unfold csr_rows in *.
  list_solve.
Qed.


Lemma partial_CSR_VAL_defined:
  forall i r coo ROWPTR COLIND VAL h,
    0 <= i < Zlength (coo_entries coo) ->
    0 < h <= count_distinct (sublist 0 i (coo_entries coo)) -> 
    partial_CSR i r coo ROWPTR COLIND VAL ->
    is_float (Znth (h-1) VAL).
Proof.
intros.
inversion_clear H1.
inversion_clear partial_CSR_wf.
inversion_clear partial_CSR_coo_csr.
unfold csr_rows in *.
assert (0 <= h - 1 < Zlength (csr_vals csr))
 by (rewrite coo_csr_vals; simpl coo_entries; lia).
replace (Znth (h-1) VAL)
  with (Znth (h-1) (sublist 0 (Zlength (csr_vals csr)) VAL)) by list_solve.
rewrite partial_CSR_val. rewrite Znth_map by auto.
red. auto.
Qed.
