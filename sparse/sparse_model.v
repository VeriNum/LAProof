Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.
Require Import Iterative.floatlib.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Inductive crs_row_rep {t: type}: forall (cols: Z) (vals: list (ftype t)) (col_ind: list Z) (v: list  (ftype t)), Prop :=
 | crs_row_rep_nil: crs_row_rep 0%Z nil nil nil
 | crs_row_rep_zero: forall cols vals col_ind v,
          crs_row_rep (cols-1) vals (map Z.pred col_ind) v ->
          crs_row_rep cols vals col_ind (Zconst t 0 :: v)
 | crs_row_rep_val: forall cols x vals col_ind v,
          crs_row_rep (cols-1) vals (map Z.pred col_ind) v ->
          crs_row_rep cols (x::vals) (0::col_ind) (x::v).

Definition crs_rep_aux {t} (mval: matrix t) (cols: Z) (vals: list (ftype t)) (col_ind: list Z) (row_ptr: list Z) : Prop :=
  Zlength row_ptr = 1 + Zlength mval /\
  Zlength vals = Znth (Zlength mval) row_ptr /\
  Zlength col_ind = Znth (Zlength mval) row_ptr /\
  sorted Z.le (0::row_ptr ++ [Int.max_unsigned]) /\ 
  forall j, 0 <= j < Zlength mval ->
        crs_row_rep cols 
             (sublist (Znth j row_ptr) (Znth (j+1) row_ptr) vals)
             (sublist (Znth j row_ptr) (Znth (j+1) row_ptr) col_ind)
             (Znth j mval).

Lemma sorted_app_e1: 
 forall {A} {HA: Inhabitant A} (le: A -> A -> Prop) al bl,
  sorted le (al++bl) -> sorted le al.
Proof.
intros.
intros i j [??]. specialize (H i j).
rewrite !Znth_app1 in H by lia.
apply H; list_solve.
Qed.

Lemma crs_rep_matrix_cols {t: type}:
   forall (mval: matrix t) cols vals col_ind row_ptr,
   crs_rep_aux mval cols vals col_ind row_ptr -> matrix_cols mval cols.
Proof.
unfold crs_rep_aux.
intros mval cols.
induction mval; intros; [constructor | ].
destruct H as [L [L0 [L1 (*[COL*) [SORT ?]]]](*]*).
constructor.
-
specialize (H 0 ltac:(list_solve)).
clear - H.
rewrite Znth_0_cons in H.
simpl in H.
forget (Znth 0 row_ptr) as x.
forget (Znth 1 row_ptr) as x'.
forget (sublist x x' vals) as v.
forget (sublist x x' col_ind) as c.
clear - H.
induction H.
reflexivity.
list_solve.
list_solve.
-
destruct row_ptr as [| r row_ptr]. list_solve.
apply (IHmval (sublist r (Zlength vals) vals)
                 (sublist r (Zlength col_ind) col_ind)
                 (map (fun i => i-r) row_ptr)); clear IHmval.
rewrite !Zlength_cons in *.
unfold Z.succ in *.
rewrite Znth_pos_cons in * by list_solve.
rewrite Z.add_simpl_r in *.
rewrite !Zlength_map.
rewrite !Znth_map by list_solve.
pose proof (SORT 0 1 ltac:(list_solve)).
change (0 <= r) in H0.
split3; [ | | split3].
 + list_solve.
 + rewrite L0. clear - H0 L L0  SORT. abstract list_solve.
 + rewrite L1. clear - H0 L L1 SORT. abstract list_solve.
 + intros i j [? ?].
     autorewrite with sublist in H2.
     clear - H0 H1 H2 SORT. change (Z.succ 0) with 1 in H2.
     abstract (list_simplify;
     (* BUG! in list_solve / list_simplify: one of the tactics is leaving
         this trivial subgoal.  Please report. *) rep_lia).
  + intros.
      specialize (H (j+1) ltac:(lia)).
       rewrite !Znth_pos_cons in H by lia.
       rewrite !Z.add_simpl_r in H.
       rewrite !Znth_map by lia.
       assert (0 <= Znth j row_ptr - r <= Znth (j + 1) row_ptr - r) 
                    by (clear - H0 H1 SORT L; abstract list_solve).
       assert (Znth (j + 1) row_ptr - r <= Zlength col_ind - r)
                    by (clear - H0 H1 SORT L L1; abstract list_solve).
       rewrite !sublist_sublist by lia.
       rewrite !Z.sub_add. auto.
Qed.

Lemma crs_row_rep_cols_nonneg:
 forall {t} cols (vals: list (ftype t)) col_ind vval,
  crs_row_rep cols vals col_ind vval ->
  0 <= cols.
Proof.
induction 1; intros.
- list_solve.
- lia.
- lia.
Qed.

Lemma crs_row_rep_col_range:
 forall {t} cols (vals: list (ftype t)) col_ind vval,
  crs_row_rep cols vals col_ind vval ->
   forall j, 0 <= j < Zlength col_ind -> 0 <= Znth j col_ind < cols.
Proof.
induction 1; intros.
- list_solve.
- specialize (IHcrs_row_rep j ltac:(list_solve)). rewrite Znth_map in * by list_solve. lia.
- destruct (zeq j 0).
  + subst. rewrite Znth_0_cons. apply crs_row_rep_cols_nonneg in H. lia.
  + rewrite Znth_pos_cons by lia.
     specialize (IHcrs_row_rep (j-1) ltac:(list_solve)).
     rewrite Znth_map in IHcrs_row_rep by list_solve. 
     lia.
Qed.

Lemma crs_row_rep_property: 
 forall {t} (P: ftype t -> Prop) cols (vals: list (ftype t)) col_ind vval,
  crs_row_rep cols vals col_ind vval ->
  Forall P vval -> Forall P vals.
Proof.
intros.
induction H; auto.
inversion H0; auto.
inversion H0; constructor; auto.
Qed.

Fixpoint rowmult {t} (s: ftype t)
            (vals: list (ftype t)) (col_ind: list Z) (vval: list (ftype t)) :=
 match vals, col_ind with
  | v1::vals', c1::col_ind' => rowmult (BFMA v1 (Znth c1 vval) s) vals' col_ind' vval
  | _, _ => s
 end.

Add Parametric Morphism {t: type}  : rowmult
  with signature (@float_eqv t) ==> strict_floatlist_eqv ==> @eq (list Z) ==> strict_floatlist_eqv ==> float_eqv
  as rowmult_mor.
Proof.
intros s s' Hs vals vals' Hvals ci vval vval' Hvval.
red in Hvals, Hvval.
revert s s' Hs ci vval vval' Hvval.
induction Hvals; intros.
-
simpl. auto.
-
destruct ci; simpl.
auto.
apply IHHvals; auto.
apply BFMA_mor; auto.
pose proof (Forall2_Zlength Hvval).
destruct (zlt z 0).
rewrite !Znth_underflow by auto. apply I.
destruct (zle (Zlength vval) z).
rewrite !Znth_overflow by lia. apply I.
apply Forall2_Znth with (i:=z) in Hvval; auto.
lia.
Qed.

Definition partial_row {t} (i: Z) (h: Z) (vals: list (ftype t)) (col_ind: list Z) (row_ptr: list Z) 
                (vval: vector t) : ftype t :=
 let vals' := sublist (Znth i row_ptr) h vals in
 let col_ind' := sublist (Znth i row_ptr) h col_ind in
   rowmult (Zconst t 0) vals' col_ind' vval.

Lemma partial_row_start:
 forall {t} i (mval: matrix t) cols vals col_ind row_ptr vval,
  crs_rep_aux mval cols vals col_ind row_ptr ->
  partial_row i (Znth i row_ptr) vals col_ind row_ptr vval = Zconst t 0.
Proof.
intros.
unfold partial_row.
autorewrite with sublist.
reflexivity.
Qed.

Lemma strict_float_eqv_i:
 forall {t} (x: ftype t), finite x -> strict_float_eqv x x.
Proof. auto. Qed.

Lemma strict_floatlist_eqv_i:
  forall {t} (vec: list (ftype t)), Forall finite vec -> strict_floatlist_eqv vec vec.
Proof.
intros.
induction H; constructor; auto.
Qed.

#[export] Hint Resolve strict_float_eqv_i strict_floatlist_eqv_i : core.

Lemma partial_row_end:
 forall {t} i (mval: matrix t) cols vals col_ind row_ptr vval
  (FINvval: Forall finite vval)
  (FINmval: Forall (Forall finite) mval)
  (LEN: Zlength vval = cols),
  0 <= i < matrix_rows mval ->
  crs_rep_aux mval cols vals col_ind row_ptr ->
  float_eqv (partial_row i (Znth (i+1) row_ptr) vals col_ind row_ptr vval)
      (Znth i (matrix_vector_mult mval vval)).
Proof.
intros.
unfold partial_row.
unfold matrix_vector_mult.
assert (COL := crs_rep_matrix_cols _ _ _ _ _ H0).
red in COL.
destruct H0 as [? [? [? [? ?]]]].
specialize (H4 _ H).
set (vals' := sublist _ _ vals) in *. clearbody vals'. 
set (col_ind' := sublist _ _ col_ind)  in *. clearbody col_ind'.
unfold matrix_rows in *.
rewrite Znth_map by list_solve.
assert (FINrow := sublist.Forall_Znth _ _ _ H FINmval).
set (row := Znth i mval) in *. clearbody row.
assert (FINvals': Forall finite vals'). {
 clear - FINrow H4.
 eapply crs_row_rep_property; eauto.
}
clear - H4 FINvval FINvals' FINrow LEN.
unfold dotprod.
forget (Zconst t 0) as s.
revert s vval FINvval LEN; induction H4; intros.
-
reflexivity.
-
 inv FINrow. clear H1. rename H2 into FINrow.
destruct vval as [ | v0 vval'].
 +
  simpl.
  pose proof (float_eqv_refl s).
  clear - FINvals' FINvval FINrow H.
  revert s col_ind H; induction vals; intros; destruct col_ind; simpl; auto.
  rewrite Znth_nil. unfold default, zerof.
  inv FINvals'.
  specialize (IHvals H3 s col_ind H).
   etransitivity; [ | apply IHvals].
   apply rowmult_mor; auto.
   apply BFMA_zero2; auto.
 +
   simpl.
   transitivity  (fold_left
     (fun (s0 : ftype t) (x12 : ftype t * ftype t) =>
      BFMA (fst x12) (snd x12) s0) (combine v vval') s).
  *
   inv FINvval.
   rewrite <- IHcrs_row_rep; clear IHcrs_row_rep; auto.
   pose proof (crs_row_rep_col_range _ _ _ _ H4). clear H4.
   rewrite Zlength_map in H by list_solve.
   rewrite Zlength_cons in H.
   assert (Forall (fun j => 1 <= j <= (Zlength vval')) col_ind).
   apply Forall_Znth. intros.
   specialize (H _ H0).
   rewrite Znth_map in H by list_solve. lia. clear H.
   revert s col_ind H0; induction vals; destruct col_ind; simpl; intros; auto.
   inv FINvals'.
   rewrite IHvals; auto. f_equal. f_equal.
   inv H0.
   list_solve. 
   inv H0; auto. clear; list_solve.
 * clear - FINvval FINrow.
    inv FINvval.
    assert (float_eqv s (BFMA (Zconst t 0) v0 s)). symmetry; apply BFMA_zero1; auto.
    forget (BFMA (Zconst t 0) v0 s) as s'. clear v0 H1.
    revert s s' H vval' H2; induction v; simpl; intros; auto.
    destruct vval'; simpl; auto.
    inv H2. inv FINrow.
    apply IHv; auto.
    apply BFMA_mor; auto. 
-
  inv FINrow. rename H1 into FINx. rename H2 into FINrow.
  inv FINvals'. clear H1. rename H2 into FINvals.
  specialize (IHcrs_row_rep FINrow FINvals).
  destruct vval as [ | v0 vval'].
 + simpl. rewrite Znth_nil. unfold default, zerof.
   transitivity  (rowmult s vals col_ind []).
   apply rowmult_mor; auto. apply BFMA_zero2; auto.
   clear - FINvals. revert s col_ind; induction vals; destruct col_ind; simpl; auto.
   rewrite Znth_nil. unfold default, zerof. inv FINvals.
   rewrite IHvals; auto.
   rewrite BFMA_zero2; auto.
 +
   simpl. rewrite Znth_0_cons.
   forget (BFMA x v0 s) as s1. clear s x FINx.
   inv FINvval. rename H1 into FINv0. rename H2 into FINvval.
   rewrite <- IHcrs_row_rep; auto; clear IHcrs_row_rep.
   pose proof (crs_row_rep_col_range _ _ _ _ H4). clear H4.
   rewrite Zlength_map in H by list_solve.
   assert (Forall (fun j => 1 <= j <= Zlength vval') col_ind). {
     apply Forall_Znth. intros.
     specialize (H _ H0).
     rewrite Znth_map in H by list_solve. rewrite Zlength_cons in H; lia.
   } clear H.
   revert s1 col_ind H0; induction vals; destruct col_ind; simpl; intros; auto.
   inv FINvals.
   inv H0.
   rewrite IHvals; auto.
   apply rowmult_mor; auto. apply BFMA_mor; auto.
   rewrite Znth_pos_cons by list_solve.
   unfold Z.pred. apply strict_float_eqv_i.
   apply Forall_Znth; auto.
   lia. list_solve.
Qed.

Lemma rowmult_app:
 forall {t} (s: ftype t) vals1 col_ind1 vals2 col_ind2 vvals,
   Zlength vals1 = Zlength col_ind1 ->
   rowmult s (vals1++vals2) (col_ind1++col_ind2) vvals =
   rowmult (rowmult s vals1 col_ind1 vvals) vals2 col_ind2 vvals.
Proof.
intros.
rewrite !Zlength_correct in H. apply Nat2Z.inj in H.
revert s col_ind1 H.
induction vals1; destruct col_ind1; simpl; intros; inv H; auto.
Qed.

Lemma partial_row_next:
 forall {t} i h (mval: matrix t) cols vals col_ind row_ptr vval,
  0 <= Znth i row_ptr ->
  Znth i row_ptr <= h < Zlength vals ->
  Zlength vals = Zlength col_ind ->
  crs_rep_aux mval cols vals col_ind row_ptr ->
partial_row i (h + 1) vals col_ind row_ptr vval = 
BFMA (Znth h vals) (Znth (Znth h col_ind) vval)
  (partial_row i h vals col_ind row_ptr vval).
Proof.
intros.
unfold partial_row.
rewrite !(sublist_split (Znth i row_ptr) h (h+1)) by lia.
rewrite rowmult_app by list_solve.
set (s1 := rowmult (Zconst t 0) _ _ _). clearbody s1.
rewrite !sublist_len_1 by lia.
reflexivity.
Qed.

