Require Import VST.floyd.proofauto.
Require Import Iterative.floatlib.
From Iterative.sparse Require Import sparse sparse_model spec_sparse.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Definition Gprog: funspecs := SparseASI ++ MathASI.

Lemma fold_crs_rep:
  forall sh  (p v ci rp: val) mval cols (vals: list (ftype Tdouble))  col_ind row_ptr,
     crs_rep_aux mval cols vals col_ind row_ptr ->
     data_at sh t_crs
          (v, (ci, (rp, (Vint (Int.repr (matrix_rows mval)),
                      Vint (Int.repr cols))))) p *
     data_at sh (tarray tdouble (Zlength col_ind)) (map Vfloat vals) v *
     data_at sh (tarray tuint (Zlength col_ind))
                     (map Vint (map Int.repr col_ind)) ci *
     data_at sh (tarray tuint (matrix_rows mval + 1))
            (map Vint (map Int.repr row_ptr)) rp
     |-- crs_rep sh mval p.
Proof.
intros.
unfold crs_rep.
Exists v ci rp cols vals col_ind row_ptr.
rewrite prop_true_andp by auto.
cancel.
Qed.

Lemma body_crs_matrix_rows: semax_body Vprog Gprog f_crs_matrix_rows crs_matrix_rows_spec.
Proof.
start_function.
forward.
sep_apply fold_crs_rep.
forward.
Qed.

Lemma body_crs_row_vector_multiply: semax_body Vprog Gprog f_crs_row_vector_multiply crs_row_vector_multiply_spec.
Proof.
start_function.
rename H3 into FINmval.
assert (0 <= matrix_rows mval) by (unfold matrix_rows; rep_lia).
forward.
forward.
forward.
freeze FR1 := (data_at sh1 _ _ _).
rename v0 into vp.
assert_PROP (0 <= i + 1 < Zlength row_ptr)
  by (entailer!; list_solve).
forward.
forward.
clear H6.
assert (CRS := H5).
assert (COLS: cols = Zlength vval). {
  pose proof (crs_rep_matrix_cols _ _ _ _ _ H5).
  rewrite <- (sublist.Forall_Znth _ _ _ H2 H).
  rewrite (sublist.Forall_Znth _ _ _ H2 H6); auto.
}
destruct H5 as [H2' [H7 [H8 [H9 H10]]]].
unfold matrix_rows in *.
assert (H9': 0 <= Znth i row_ptr <= Znth (i+1) row_ptr 
            /\ Znth (i+1) row_ptr <= Znth (Zlength mval) row_ptr <= Int.max_unsigned)
   by (clear - H9 H2' H2; list_solve).
clear H9. destruct H9' as [H9 H9'].
forward_for_simple_bound (Znth (i + 1) row_ptr)
  (EX h:Z, PROP(0 <= Znth i row_ptr <= h)
   LOCAL (
   temp _s (Vfloat (partial_row i h vals col_ind row_ptr vval));
   temp _i (Vint (Int.repr i));
   temp _hi (Vint (Int.repr (Znth (i+1) row_ptr))); 
   temp _row_ptr rp; temp _col_ind ci; temp _val vp;
   temp _m m; temp _v v)
   SEP (FRZL FR1;
   data_at sh1 (tarray tdouble (Zlength col_ind)) (map Vfloat vals) vp;
   data_at sh1 (tarray tuint (Zlength col_ind))
     (map Vint (map Int.repr col_ind)) ci;
   data_at sh1 (tarray tuint (matrix_rows mval + 1))
     (map Vint (map Int.repr row_ptr)) rp;
   data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v))%assert.
-
 forward.
 change float with (ftype Tdouble) in *. 
 EExists. entailer!.
 f_equal. erewrite partial_row_start. reflexivity. eassumption.
-
rename i0 into h.
forward.
change float with (ftype Tdouble) in *. 
forward.
assert (0 <= Znth h col_ind < Zlength vval). {
    specialize (H10 _ H2).
    assert (H11 := crs_row_rep_col_range _ _ _ _ H10 (h - Znth i row_ptr)).
    autorewrite with sublist in H11.
  subst cols.
  apply H11. rep_lia.
  }
forward.
rewrite (@Znth_map (ftype Tdouble) _ _ _ h Vfloat) by rep_lia.
rewrite (@Znth_map (ftype Tdouble) _ _ _ (Znth h col_ind)) by rep_lia.
forward_call (Znth h vals, Znth (Znth h col_ind) vval, partial_row i h vals col_ind row_ptr vval).
forward.
entailer!.
f_equal.
change (Binary.Bfma _ _ _ _ _ _ _ _ _) with 
   (@BFMA _ Tdouble (Znth h vals) (Znth (Znth h col_ind) vval)
     (partial_row i h vals col_ind row_ptr vval)
  ).
eapply partial_row_next; try eassumption; lia.
-
 forward.
 Exists  (partial_row i (Znth (i + 1) row_ptr) vals col_ind row_ptr vval).
 entailer!.
 erewrite partial_row_end; try eassumption; auto.
 unfold matrix_vector_mult.
 rewrite Znth_map by rep_lia. reflexivity.
 unfold crs_rep.
 thaw FR1.
 Exists vp ci rp (Zlength vval) vals col_ind row_ptr.
 entailer!.
Qed.

Lemma body_crs_matrix_vector_multiply_byrows: semax_body Vprog Gprog f_crs_matrix_vector_multiply_byrows crs_matrix_vector_multiply_byrows_spec.
Proof.
start_function.
forward_call.
forward_for_simple_bound (Zlength mval)
  (EX i:Z, EX result: list (ftype Tdouble),
   PROP(Forall2 feq result (sublist 0 i (matrix_vector_mult mval vval))) 
   LOCAL (temp _rows (Vint (Int.repr (matrix_rows mval))); 
   temp _m m; temp _v v; temp _p p)
   SEP (crs_rep sh1 mval m;
   data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v;
   data_at sh3 (tarray tdouble (matrix_rows mval)) 
      (map Vfloat result ++ Zrepeat Vundef (matrix_rows mval - i)) p))%assert.
- unfold matrix_rows in H0; lia.
- Exists (@nil (ftype Tdouble)). simpl app. entailer!.
     apply derives_refl.
- forward_call (sh1,sh2,sh3, m, mval, v, vval, i).
   Intros s.
   unfold matrix_rows in H0.
   forward.
   progress change float with (ftype Tdouble) in *. 
   Exists (result ++ [s]).
   entailer!. 
   clear H11 H12 H10 H9 H8 H7 PNp PNv PNm.
   assert (Zlength (matrix_vector_mult mval vval) = Zlength mval). 
      unfold matrix_vector_mult. list_solve.
   rewrite (sublist_split 0 i (i+1)) by list_solve.
   apply Forall2_app.
   auto.
   rewrite sublist_len_1 by rep_lia.
   constructor; [ | constructor].
   unfold matrix_vector_mult. rewrite Znth_map by rep_lia. auto.
   assert (Zlength result = i). {
     clear - H5 H4. unfold matrix_vector_mult in H5.
      apply Forall2_Zlength in H5. rewrite H5.
    list_solve.
   }
   apply derives_refl'; f_equal.
   unfold matrix_rows; subst i. clear H9 H11 H12 H10 H8 H7 PNp PNv PNm H5.
    list_solve.
-
 Intro result. Exists result.
 unfold matrix_rows in *. list_simplify.
 entailer!.
 unfold matrix_vector_mult in H8 |- *.
 rewrite sublist_same in H8 by list_solve. auto.
Qed.

