Require Import VST.floyd.proofauto.
Require Import LAProof.C.floatlib.
From LAProof.C Require Import build_csr sparse_model spec_sparse distinct partial_csr.
Require Import VSTlib.spec_math.
Require Import vcfloat.FPStdCompCert.
Require Import vcfloat.FPStdLib.
Require Import Coq.Classes.RelationClasses.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Lemma body_coo_count: semax_body Vprog Gprog f_coo_count coo_count_spec.
Proof.
start_function.
forward.
forward.
forward.
forward.
forward.
forward.
assert (WF := H).
destruct H as [_ H]. rewrite Forall_Znth in H.
set (el := coo_entries coo) in *.
freeze FR1 := - (data_at _ _ _ rp) (data_at _ _ _ cp).
set (rest := Zrepeat _ _).
set (n := Zlength el) in *.
forward_for_simple_bound n (* for (i=0;i<n; i++) *)
 (EX i:Z, EX count:Z, EX r:Z, EX c:Z, 
  PROP(0 <= i <= n; 
       count = count_distinct (sublist 0 i el);
       i=0 -> (r,c)=(-1,0);
       i<>0 -> (r,c)= fst (Znth (i-1) el))
  LOCAL(temp _r (Vint (Int.repr r)); temp _c (Vint (Int.repr c)); 
        temp _count (Vint (Int.repr count));
        temp _n (Vint (Int.repr n)); 
        temp _row_ind rp; temp _col_ind cp)
  SEP(FRZL FR1;
   data_at sh (tarray tuint maxn)
     (map (fun e => Vint (Int.repr (fst (fst e)))) el ++ rest) rp;
   data_at sh (tarray tuint maxn)
     (map (fun e => Vint (Int.repr (snd (fst e)))) el ++ rest) cp))%assert.
- Exists 0 (-1) 0.
  entailer!!.
- forward. 
    { rewrite Znth_app1, Znth_map by list_solve. entailer!!. }
  rewrite Znth_app1, Znth_map by list_solve.
  set (ri := fst _).
  forward.
    { rewrite Znth_app1, Znth_map by list_solve. entailer!!. }
  rewrite Znth_app1, Znth_map by list_solve.
  set (ci := snd _). 
 assert (i<>0 -> 0 <= r <= Int.max_unsigned). {
      intro n0. destruct (H (i-1) ltac:(lia)).
      specialize (H9 n0). rewrite <- H9 in  H10. simpl in H10.
      rep_lia.
   }
 assert (0 <= c <= Int.max_unsigned). {
      destruct (zeq i 0). specialize (H8 e); inv H8; rep_lia.
      destruct (H (i-1) ltac:(lia)).
      specialize (H9 n0). rewrite <- H9 in  H12. simpl in H12.
      rep_lia.
   }
 assert (0 <= ri < Int.max_unsigned). {
     subst ri; destruct (H i ltac:(lia)). rep_lia.
   }
 assert (0 <= ci < Int.max_unsigned). {
     subst ci; destruct (H i ltac:(lia)). rep_lia.
   }
  forward_if 
  (PROP ( )
   LOCAL (temp _ci (Vint (Int.repr ci));
   temp _ri (Vint (Int.repr ri));
   temp _i (Vint (Int.repr i));
   temp _r (Vint (Int.repr r));
   temp _c (Vint (Int.repr c));
   temp _count (Vint (Int.repr count));
   temp _n (Vint (Int.repr n)); temp _row_ind rp;
   temp _col_ind cp;
   temp _t'1 (Vint (Int.repr (Z.b2z (negb (Z.eqb ri r) || negb (Z.eqb ci c))))))
   SEP (FRZL FR1;
   data_at sh (tarray tuint maxn)
     (map (fun e => Vint (Int.repr (fst (fst e)))) el ++ rest) rp;
   data_at sh (tarray tuint maxn)
     (map (fun e => Vint (Int.repr (snd (fst e)))) el ++ rest) cp)).
 + forward.
   entailer!!.
   destruct (Z.eqb_spec ri r). congruence. reflexivity.
 + forward.
   entailer!!.
   assert (ri=r). {
     destruct (zeq i 0).
     2: specialize (H10 n0); apply repr_inj_unsigned; try rep_lia; auto.
     specialize (H8 e). inv H8.
     exfalso. clearbody ri. clear - H14 H12.
     rewrite (modulo_samerepr (-1) Int.max_unsigned) in H14 by reflexivity.
     apply repr_inj_unsigned in H14; rep_lia.
   }
   subst r. rewrite Z.eqb_refl. simpl.
   destruct (zeq ci c). subst c. rewrite Z.eqb_refl. reflexivity.
   simpl.
   rewrite <- Z.eqb_neq in n0. rewrite n0; reflexivity.
 + forward_if.
  * forward.
    forward.
    forward.
    Exists (count+1) ri ci.
    entailer!!.
    split.
    -- destruct (zeq i 0). subst.
       rewrite (sublist_one 0 (0+1)) by lia. reflexivity.
       apply count_distinct_incr; try lia.
       red.
       assert (coord_le (Znth (i - 1) el) (Znth i el))
         by (apply coord_sorted_e; auto; lia).
       split; auto.
       assert (ri<>r \/ ci<>c) by (clear - H14; lia).
       intro.
       red in H7,H16.  fold ri in H7,H16.
       rewrite <- (H9 n0) in H7,H16. simpl in H7,H16.
       clear - H7 H15 H16. lia.
    -- intros. rewrite Z.add_simpl_r.
       unfold ri,ci. clear; destruct (Znth i el) as [[??]?]; auto.
  * assert (ri=r /\ ci=c) by (clear - H14; lia). clear H14.
    destruct H15; subst r c.
    forward.
    Exists count ri ci.
    entailer!!.
    split. 
    -- assert (i<>0)
        by (intro; subst i; specialize (H8 eq_refl); inv H8; lia).
       specialize (H10 H7).
       apply count_distinct_noincr. rep_lia.
       intro. destruct H14.
       specialize (H9 H7).
       unfold coord_le in H14,H15.
       rewrite <- H9 in H14,H15.
       unfold ri,ci in H14,H15. simpl in H14, H15.
       clear - H14 H15; lia.
    -- rewrite Z.add_simpl_r. intro.
       unfold ri,ci. destruct (Znth i el) as [[??]?]; simpl; auto.
-
 Intros count r c.
 thaw FR1.
 forward.
 unfold coo_rep.
 Exists maxn rp cp vp.
 entailer!!.
 autorewrite with sublist. auto.
Qed.

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
forward_call (spec_alloc.surely_malloc_spec_sub (Tstruct _csr_matrix noattr)) gv.  (* q = surely_malloc(sizeof(struct csr_matrix)); *)
Intros q. 
assert (Hbound' := count_distinct_bound (coo_entries coo')).
fold k in Hbound'.
forward_call (spec_alloc.surely_malloc_spec_sub (tarray tdouble k)) gv.  (* val = surely_malloc(k*sizeof(double)); *)
 entailer!!.
  simpl. do 3 f_equal. rep_lia.
  simpl. rep_lia.
Intros val_p.
forward_call (spec_alloc.surely_malloc_spec_sub (tarray tuint k)) gv. (* col_ind = surely_malloc(k*sizeof(uint)); *)
  entailer!!.
  simpl. do 3 f_equal. rep_lia. simpl; rep_lia.
Intros colind_p.
forward_call (spec_alloc.surely_malloc_spec_sub (tarray tuint (coo_rows coo+1))) gv. (* row_ptr = surely_malloc((rows+1)*sizeof(tuint)); *)
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