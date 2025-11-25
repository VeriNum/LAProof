Require Import VST.floyd.proofauto.
Require Import vcfloat.VCFloat.
Require Import vcfloat.FPStdCompCert.
Require Import VSTlib.spec_math.
From LAProof.C Require Import floatlib distinct.

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Record csr_matrix {t: type} := {
  csr_cols: Z;
  csr_vals: list (ftype t);
  csr_col_ind: list Z;
  csr_row_ptr: list Z;
  csr_rows: Z := Zlength (csr_row_ptr) - 1
}.
Arguments csr_matrix t : clear implicits.

Inductive csr_row_rep {t: type} : 
  forall (cols: Z) (vals: list (ftype t)) (col_ind: list Z) 
  (v: list  (ftype t)), Prop :=
 | csr_row_rep_nil: csr_row_rep 0%Z nil nil nil
 | csr_row_rep_zero: forall cols vals col_ind v,
          csr_row_rep (cols-1) vals (map Z.pred col_ind) v ->
          csr_row_rep cols vals col_ind (Zconst t 0 :: v)
 | csr_row_rep_val: forall cols x vals col_ind v,
          csr_row_rep (cols-1) vals (map Z.pred col_ind) v ->
          csr_row_rep cols (x::vals) (0%Z::col_ind) (x::v).

Definition csr_to_matrix {t} (csr: csr_matrix t) (mval: matrix t) :=
  Zlength (csr_row_ptr csr) = 1 + Zlength mval /\
  Zlength (csr_vals csr) = Znth (Zlength mval) (csr_row_ptr csr) /\
  Zlength (csr_col_ind csr) = Znth (Zlength mval) (csr_row_ptr csr) /\
  list_solver.sorted Z.le (0 :: csr_row_ptr csr ++ [Int.max_unsigned]) /\ 
  forall j, 0 <= j < Zlength mval ->
        csr_row_rep (csr_cols csr) 
             (sublist (Znth j (csr_row_ptr csr)) (Znth (j+1) (csr_row_ptr csr)) (csr_vals csr))
             (sublist (Znth j (csr_row_ptr csr)) (Znth (j+1) (csr_row_ptr csr)) (csr_col_ind csr))
             (Znth j mval).

Lemma sorted_app_e1: 
 forall {A} {HA: Inhabitant A} (le: A -> A -> Prop) al bl,
  list_solver.sorted le (al++bl) -> list_solver.sorted le al.
Proof.
intros.
intros i j [??]. specialize (H i j).
rewrite !Znth_app1 in H by lia.
apply H; list_solve.
Qed.

Lemma csr_to_matrix_rows {t: type}:
   forall (mval: matrix t) (csr: csr_matrix t),
   csr_to_matrix csr mval -> 
  csr_rows csr = matrix_rows mval.
Proof.
intros.
destruct H.
unfold csr_rows, matrix_rows; lia.
Qed.

Lemma csr_to_matrix_cols {t: type}:
   forall (mval: matrix t) (csr: csr_matrix t),
   csr_to_matrix csr mval -> matrix_cols mval (csr_cols csr).
Proof.
unfold csr_to_matrix.
intros mval [cols vals col_ind row_ptr].
simpl in *.
clear csr_rows0.
revert vals col_ind row_ptr.
induction mval; intros; [constructor | ].
destruct H as [L [L0 [L1 [SORT ?]]]].
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

Lemma csr_row_rep_cols_nonneg:
 forall {t} cols (vals: list (ftype t)) col_ind vval,
  csr_row_rep cols vals col_ind vval ->
  0 <= cols.
Proof.
induction 1; intros.
- list_solve.
- lia.
- lia.
Qed.

Lemma csr_row_rep_col_range:
 forall {t} cols (vals: list (ftype t)) col_ind vval,
  csr_row_rep cols vals col_ind vval ->
   forall j, 0 <= j < Zlength col_ind -> 0 <= Znth j col_ind < cols.
Proof.
induction 1; intros.
- list_solve.
- specialize (IHcsr_row_rep j ltac:(list_solve)). rewrite Znth_map in * by list_solve. lia.
- destruct (zeq j 0).
  + subst. rewrite Znth_0_cons. apply csr_row_rep_cols_nonneg in H. lia.
  + rewrite Znth_pos_cons by lia.
     specialize (IHcsr_row_rep (j-1) ltac:(list_solve)).
     rewrite Znth_map in IHcsr_row_rep by list_solve. 
     lia.
Qed.

Lemma csr_row_rep_property: 
 forall {t} (P: ftype t -> Prop) cols (vals: list (ftype t)) col_ind vval,
  csr_row_rep cols vals col_ind vval ->
  Forall P vval -> Forall P vals.
Proof.
intros.
induction H; auto.
inversion H0; auto.
inversion H0; constructor; auto.
Qed.

Inductive csr_matrix_wellformed {t} (csr: csr_matrix t) : Prop :=
 build_csr_matrix_wellformed:
 forall (CSR_wf_rows: 0 <= csr_rows csr)
        (CSR_wf_cols: 0 <= csr_cols csr)
        (CSR_wf_vals: Zlength (csr_vals csr) = Zlength (csr_col_ind csr))
        (CSR_wf_vals': Zlength (csr_vals csr) = Znth (csr_rows csr) (csr_row_ptr csr))
        (CSR_wf_sorted: list_solver.sorted Z.le (0 :: csr_row_ptr csr ++ [Int.max_unsigned]))
        (CSR_wf_rowsorted: forall r, 0 <= r < csr_rows csr -> 
              sorted Z.lt 
                (-1 :: sublist (Znth r (csr_row_ptr csr)) (Znth (r+1) (csr_row_ptr csr)) (csr_col_ind csr) ++ [csr_cols csr])),
    csr_matrix_wellformed csr.


Lemma rowptr_sorted_e: 
 forall row_ptr (H: list_solver.sorted Z.le (0 :: row_ptr ++ [Int.max_unsigned]))
       (i j: Z),
   0 <= i <= j /\ j < Zlength row_ptr ->
   0 <= Znth i row_ptr <= Znth j row_ptr /\ Znth j row_ptr <= Int.max_unsigned.
Proof.
intros.
pose proof H 0 (i+1) ltac:(list_solve).
rewrite Znth_0_cons, Znth_pos_cons, Z.add_simpl_r in H1 by list_solve.
rewrite Znth_app1 in H1 by list_solve.
pose proof H (i+1) (j+1) ltac:(list_solve).
rewrite !(Znth_pos_cons (_+_)), !Z.add_simpl_r in H2 by list_solve.
rewrite !Znth_app1 in H2 by list_solve.
pose proof H (j+1) (Zlength row_ptr + 1) ltac:(list_solve).
rewrite !(Znth_pos_cons (_+_)), !Z.add_simpl_r in H3 by list_solve.
rewrite Znth_app1 in H3 by list_solve.
rewrite Znth_app2 in H3 by list_solve.
autorewrite with sublist in H3.
lia.
Qed.

Lemma rowptr_sorted_e1: 
  forall row_ptr (H: list_solver.sorted Z.le (0 :: row_ptr ++ [Int.max_unsigned]))
       (i: Z),
   0 <= i < Zlength row_ptr ->
   0 <= Znth i row_ptr <= Int.max_unsigned.
Proof.
intros.
pose proof rowptr_sorted_e _ H i i ltac:(lia); lia.
Qed.

Fixpoint build_csr_row {t} (cols: Z) (vals: list (ftype t)) (col_ind: list Z) : list (ftype t) :=
 match vals, col_ind  with
 | v::vals', c::col_ind' => Zrepeat (Zconst t 0) c ++ v :: 
                            build_csr_row (cols-c-1) vals' (map (fun j => j-c-1) col_ind')

 | _, _ => Zrepeat (Zconst t 0) cols
 end.

Fixpoint build_csr_rows {t} (csr: csr_matrix t) (k: Z) (row_ptr: list Z) : list (list (ftype t)) :=
 match row_ptr with
 | [] => nil
 | k'::row_ptr' => build_csr_row (csr_cols csr) (sublist k k' (csr_vals csr)) 
                  (sublist k k' (csr_col_ind csr)) ::
                  build_csr_rows csr k' row_ptr'
 end.

Definition build_csr_matrix {t} (csr: csr_matrix t) : matrix t :=
 match csr_row_ptr csr with
 | k::row_ptr' => build_csr_rows csr k row_ptr'
 | [] => []
 end.

Lemma build_csr_row_correct:
  forall {t} cols (vals: list (ftype t)) col_ind,
     0 <= cols ->
     Zlength vals = Zlength col_ind ->
     sorted Z.lt (-1 :: col_ind ++ [cols]) ->
    csr_row_rep cols vals col_ind (build_csr_row cols vals col_ind).
Proof.
intros.
pose proof I.
revert col_ind cols H H0 H1; induction vals; destruct col_ind; intros; try list_solve.
-
unfold build_csr_row.
rewrite <- (Z2Nat.id cols) by auto.
clear H H1 H2.
induction (Z.to_nat cols). constructor.
replace (Z.of_nat (S n)) with (1+Z.of_nat n) by lia.
rewrite <- Zrepeat_app by lia.
simpl.
constructor.
replace (1 + Z.of_nat n - 1) with (Z.of_nat n) by lia.
simpl. auto.
-
assert (0<=z) by (inversion H1; clear H1; subst; lia).
rewrite <- (Z2Nat.id z) in H0,H1|-* by lia.
forget (Z.to_nat z) as n.
clear z H3 H2.
autorewrite with sublist in H0.
simpl.
revert cols col_ind H0 H1 H; induction n; intros.
 + simpl Z.of_nat in *.
  rewrite !Z.sub_0_r.
  constructor.
  replace (map (fun j : Z => j - 0 - 1) col_ind) with (map Z.pred col_ind).
  2:{ clear. induction col_ind; auto. simpl. f_equal. lia. apply IHcol_ind; auto. }
  apply IHvals; auto; try list_solve.
  *pose proof sorted_e _ H1 1 (Zlength col_ind + 2) ltac:(list_solve) ltac:(list_solve). autorewrite with sublist in H2.
   rewrite (Znth_pos_cons 1), Z.sub_diag in H2 by lia. simpl in H2.  rewrite Znth_0_cons in H2.
   repeat change (?A :: ?B ++ ?C) with ((A::B)++C) in H2. rewrite Znth_app2 in H2 by list_solve.
   clear - H2. list_solve.
  * simpl in H1. inv H1. inv H6. list_solve.
    replace (map Z.pred col_ind ++ [cols-1]) with (map Z.pred (y::l))
      by (rewrite H2; apply map_app). clear - H3 H5. simpl. constructor. lia.
    clear H3. change (sorted Z.lt (map Z.pred (y::l))). forget (y::l) as al.
    induction H5; constructor; auto. lia.
 + rewrite inj_S.
   replace (Z.succ (Z.of_nat n)) with (1 + Z.of_nat n) by lia.
   rewrite <- Zrepeat_app by lia.
   change (Zrepeat (Zconst t 0) 1) with [Zconst t 0].
   simpl.
   apply csr_row_rep_zero.
   specialize (IHn (cols-1) (map Z.pred col_ind)).
   simpl map. replace (Z.pred (1+Z.of_nat n)) with (Z.of_nat n) by lia.
   replace (cols - (1+Z.of_nat n) -1 ) with (cols - 1 - Z.of_nat n - 1) by lia.
   replace (map (fun j : Z => j - (1 + Z.of_nat n) - 1) col_ind)
     with (map (fun j : Z => j - Z.of_nat n - 1) (map Z.pred col_ind)). 2: {
     clear. induction col_ind; simpl; auto. f_equal. lia. auto. 
   } 
   apply IHn; try list_solve.
   * clear - H1. rewrite inj_S in H1. simpl in *. inv H1. constructor. lia.
     replace (Z.of_nat n :: map Z.pred col_ind ++ [cols - 1])
          with (map Z.pred (Z.succ (Z.of_nat n) :: col_ind ++ [cols]))
       by (simpl; f_equal; [lia | apply map_app]).
     forget (Z.succ (Z.of_nat n) :: col_ind ++ [cols]) as al.
     induction H4; constructor; auto; lia.
   * clear - H1. rewrite inj_S in H1. inv H1.
     pose proof (sorted_e _ H4 0 (Zlength col_ind + 1) ltac:(list_solve) ltac:(list_solve)).
     rewrite Znth_0_cons in H. clear H4. list_solve.
Qed.

Lemma build_csr_matrix_correct:
  forall {t} (csr: csr_matrix t),
  csr_matrix_wellformed csr ->
  csr_to_matrix csr (build_csr_matrix csr).
Proof.
 intros.
 inversion_clear H.
 unfold build_csr_matrix.
 unfold csr_to_matrix.
 unfold csr_rows in *.
 destruct (csr_row_ptr csr) as [| k rowptr]. list_solve.
 assert (Zlength rowptr = Zlength (build_csr_rows csr k rowptr)). {
   clear.
   revert k; induction rowptr; simpl; intros. auto.
   autorewrite with sublist. f_equal. auto.
 }
 split3; [ | | split3].
 - list_solve.
 - rewrite <- H. rewrite CSR_wf_vals'. f_equal. list_solve.
 - rewrite <- H. list_solve.
 - auto.
 - rewrite <- H.
   intros r ?.
   rewrite !(Znth_pos_cons (r+1)), Z.add_simpl_r by lia.
   pose proof @build_csr_row_correct t (csr_cols csr)
    (sublist (Znth r (k :: rowptr)) (Znth r rowptr) (csr_vals csr))
    (sublist (Znth r (k :: rowptr)) (Znth r  rowptr) (csr_col_ind csr))
     ltac:(lia).
   autorewrite with sublist in CSR_wf_vals'. unfold Z.succ  in CSR_wf_vals'.
   assert (0 <= Znth r (k :: rowptr) <= Znth r rowptr /\
           Znth r rowptr <= Zlength (csr_col_ind csr)). {
    clear - CSR_wf_sorted H0 CSR_wf_vals CSR_wf_vals'.
    rewrite <- CSR_wf_vals, CSR_wf_vals', Z.add_simpl_r.
    pose proof rowptr_sorted_e _ CSR_wf_sorted r (r+1) ltac:(list_solve).
    pose proof rowptr_sorted_e _ CSR_wf_sorted (r+1) (Zlength rowptr) ltac:(list_solve).
    rewrite !(Znth_pos_cons (r+1)), !Z.add_simpl_r in * by lia. lia.
    }
   destruct H2.
   spec H1; [list_solve | ].
   spec H1. { clear H1. 
      assert (H1 := CSR_wf_rowsorted r ltac:(list_solve)); simpl in H1.
      rewrite !(Znth_pos_cons (r+1)), Z.add_simpl_r in H1 by lia. auto.
   }
   assert (Znth r (build_csr_rows csr k rowptr) =
       build_csr_row (csr_cols csr)
       (sublist (Znth r (k :: rowptr)) (Znth r rowptr) (csr_vals csr))
       (sublist (Znth r (k :: rowptr)) (Znth r rowptr) (csr_col_ind csr))); [clear H1 | rewrite H4; auto].
   clear - H0.
   revert k r H0; induction rowptr; simpl; intros; [list_solve | ].
   destruct (zeq r 0).
      + list_solve. 
      + rewrite !(Znth_pos_cons r) by lia.
        apply (IHrowptr a (r-1) ltac:(list_solve)).
Qed.


Fixpoint rowmult {t} (s: ftype t)
            (vals: list (ftype t)) (col_ind: list Z) (vval: list (ftype t)) :=
 match vals, col_ind with
  | v1::vals', c1::col_ind' => rowmult (BFMA v1 (Znth c1 vval) s) vals' col_ind' vval
  | _, _ => s
 end.

Add Parametric Morphism {t: type}  : rowmult
  with signature (@feq t) ==> Forall2 feq ==> @eq (list Z) ==> Forall2 feq ==> feq
  as rowmult_mor.
Proof.
intros s s' Hs vals vals' Hvals ci vval vval' Hvval.
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

Add Parametric Morphism {t: type}  : rowmult
  with signature (@feq t) ==> Forall2 strict_feq ==> @eq (list Z) ==> Forall2 strict_feq ==> feq
  as rowmult_stricter_mor.
Proof.
intros s s' Hs vals vals' Hvals ci vval vval' Hvval.
revert s s' Hs ci vval vval' Hvval.
induction Hvals; intros.
-
simpl. auto.
-
destruct ci; simpl.
auto.
apply IHHvals; auto.
apply BFMA_mor; auto; apply subrelation_strict_feq; auto.
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
 forall {t} i (mval: matrix t) csr (*cols vals col_ind row_ptr*) vval,
  csr_to_matrix csr mval ->
  partial_row i (Znth i (csr_row_ptr csr)) (csr_vals csr) (csr_col_ind csr) (csr_row_ptr csr) vval = Zconst t 0.
Proof.
intros.
unfold partial_row.
autorewrite with sublist.
reflexivity.
Qed.

Lemma strict_feq_i:
 forall {t} (x: ftype t), finite x -> strict_feq x x.
Proof. auto. Qed.

Lemma strict_floatlist_eqv_i:
  forall {t} (vec: list (ftype t)), Forall finite vec -> Forall2 strict_feq vec vec.
Proof.
intros.
induction H; constructor; auto.
Qed.
#[export] Hint Resolve strict_feq_i strict_floatlist_eqv_i : core.

Lemma partial_row_end:
 forall {t} i (mval: matrix t) csr (*cols vals col_ind row_ptr*)  vval
  (FINvval: Forall finite vval)
  (FINmval: Forall (Forall finite) mval)
  (LEN: Zlength vval = csr_cols csr),
  0 <= i < matrix_rows mval ->
  csr_to_matrix csr mval ->
  feq (partial_row i (Znth (i+1) (csr_row_ptr csr)) (csr_vals csr) (csr_col_ind csr) (csr_row_ptr csr) vval)
      (Znth i (matrix_vector_mult mval vval)).
Proof.
intros.
destruct csr as [cols vals col_ind row_ptr _].
simpl in *.
unfold partial_row.
unfold matrix_vector_mult.
assert (COL := csr_to_matrix_cols _ _ H0).
red in COL. simpl in COL.
destruct H0 as [? [? [? [? ?]]]].
simpl in *.
specialize (H4 _ H).
set (vals' := sublist _ _ vals) in *. clearbody vals'. 
set (col_ind' := sublist _ _ col_ind)  in *. clearbody col_ind'.
unfold matrix_rows in *.
rewrite Znth_map by list_solve.
assert (FINrow := sublist.Forall_Znth _ _ _ H FINmval).
set (row := Znth i mval) in *. clearbody row.
assert (FINvals': Forall finite vals'). {
 clear - FINrow H4.
 eapply csr_row_rep_property; eauto.
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
  pose proof (feq_refl s).
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
   rewrite <- IHcsr_row_rep; clear IHcsr_row_rep; auto.
   pose proof (csr_row_rep_col_range _ _ _ _ H4). clear H4.
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
    assert (feq s (BFMA (Zconst t 0) v0 s)). symmetry; apply BFMA_zero1; auto.
    forget (BFMA (Zconst t 0) v0 s) as s'. clear v0 H1.
    revert s s' H vval' H2; induction v; simpl; intros; auto.
    destruct vval'; simpl; auto.
    inv H2. inv FINrow.
    apply IHv; auto.
    apply BFMA_mor; auto. 
-
  inv FINrow. rename H1 into FINx. rename H2 into FINrow.
  inv FINvals'. clear H1. rename H2 into FINvals.
  specialize (IHcsr_row_rep FINrow FINvals).
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
   rewrite <- IHcsr_row_rep; auto; clear IHcsr_row_rep.
   pose proof (csr_row_rep_col_range _ _ _ _ H4). clear H4.
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
   replace (Z.pred z) with (z-1) by lia. reflexivity.
   list_solve.
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
 forall {t} i h (mval: matrix t) csr vval,
  0 <= Znth i (csr_row_ptr csr) ->
  Znth i (csr_row_ptr csr) <= h < Zlength (csr_vals csr) ->
  Zlength (csr_vals csr) = Zlength (csr_col_ind csr) ->
  csr_to_matrix csr mval ->
partial_row i (h + 1) (csr_vals csr) (csr_col_ind csr) (csr_row_ptr csr) vval = 
BFMA (Znth h (csr_vals csr)) (Znth (Znth h (csr_col_ind csr)) vval)
  (partial_row i h (csr_vals csr) (csr_col_ind csr)  (csr_row_ptr csr) vval).
Proof.
intros.
unfold partial_row.
rewrite !(sublist_split (Znth i (csr_row_ptr csr)) h (h+1)) by lia.
rewrite rowmult_app by list_solve.
set (s1 := rowmult (Zconst t 0) _ _ _). clearbody s1.
rewrite !sublist_len_1 by lia.
reflexivity.
Qed.

Inductive sum_any {t}: forall (v: vector t) (s: ftype t), Prop :=
| Sum_Any_0: sum_any nil (Zconst t 0)
| Sum_Any_1: forall x, sum_any [x] x
| Sum_Any_split: forall al bl a b, sum_any al a -> sum_any bl b -> sum_any (al++bl) (BPLUS a b)
| Sum_Any_perm: forall al bl s, Permutation al bl -> sum_any al s -> sum_any bl s.

Require LAProof.accuracy_proofs.common.

Lemma sum_any_accuracy{t}: forall (v: vector t) (s: ftype t), 
  let mag := fold_left Rmax (map FT2R v) R0 in
  sum_any v s ->
  (Rabs (fold_left Rplus (map FT2R v) R0 - FT2R s) <= @common.g t (length v) * (INR (length v) * mag))%R.
(* see Theorem fSUM in LAProof/accuracy_proofs/sum_acc.v *)
Admitted.

Record coo_matrix {t: type} := {
  coo_rows: Z;
  coo_cols: Z;
  coo_entries: list (Z * Z * ftype t)
}.
Arguments coo_matrix t : clear implicits.


Definition coo_matrix_wellformed {t} (coo: coo_matrix t) :=
 (0 <= coo_rows coo /\ 0 <= coo_cols coo) (* need this conjunct just in case entries=nil *)
  /\ Forall (fun e => 0 <= fst (fst e) < coo_rows coo /\ 0 <= snd (fst e) < coo_cols coo)
      (coo_entries coo).

Definition coo_matrix_equiv {t: type} (a b : coo_matrix t) :=
  coo_rows a = coo_rows b /\ coo_cols a = coo_cols b
  /\ Permutation (coo_entries a) (coo_entries b).

Lemma coo_matrix_wellformed_equiv {t: type} (a b: coo_matrix t):
   coo_matrix_equiv a b -> coo_matrix_wellformed a -> coo_matrix_wellformed b.
Proof.
intros.
destruct H as [? [? ?]].
destruct H0 as [[Hr Hc] H0].
split. split; lia.
eapply Permutation_Forall; try apply H0.
eassumption.
rewrite <- H, <- H1.
apply H0.
Qed.


Definition coord_eqb (a b: Z * Z) :=
       andb (Z.eqb (fst a) (fst b)) (Z.eqb (snd a) (snd b)).

Definition coo_to_matrix {t: type} (coo: coo_matrix t) (m: matrix t) : Prop :=
  coo_rows coo = matrix_rows m /\
  matrix_cols m (coo_cols coo) /\
   forall i, 0 <= i < coo_rows coo ->
    forall j, 0 <= j < coo_cols coo -> 
     sum_any (map snd (filter (coord_eqb (i,j) oo fst) (coo_entries coo)))
          (matrix_index m (Z.to_nat i) (Z.to_nat j)).

Lemma coo_to_matrix_equiv:
  forall {t} (m: matrix t) (coo coo': coo_matrix t),
    coo_matrix_equiv coo coo' -> coo_to_matrix coo m -> coo_to_matrix coo' m.
Proof.
intros.
destruct H0 as [? [? ?]].
destruct H as [? [? ?]].
split3; try congruence.
intros.
rewrite <- H in H5. rewrite <- H3 in H6.
specialize (H2 i H5 j H6).
econstructor 4; try apply H2.
apply Permutation_map.
apply Permutation_filter.
auto.
Qed.

Lemma coo_matrix_equiv_refl:
  forall {t} (a : coo_matrix t), coo_matrix_equiv a a.
Proof.
intros.
split3; auto.
Qed.

Lemma coo_matrix_equiv_symm:
  forall {t} (a b : coo_matrix t), coo_matrix_equiv a b -> coo_matrix_equiv b a.
Proof.
intros.
destruct H as [? [? ?]].
split3; auto.
apply Permutation_sym; auto.
Qed.

Lemma coo_matrix_equiv_trans:
  forall {t} (a b c : coo_matrix t), coo_matrix_equiv a b -> coo_matrix_equiv b c -> coo_matrix_equiv a c.
Proof.
intros.
destruct H as [? [? ?]], H0 as [? [? ?]].
split3; try congruence.
eapply Permutation_trans; eassumption.
Qed.

Definition coord_le {t} (a b : Z*Z*ftype t) : Prop :=
  fst (fst a) < fst (fst b) 
 \/ fst (fst a) = fst (fst b) /\ snd (fst a) <= snd (fst b).

Definition coord_leb {t} (a b : Z*Z*ftype t) : bool :=
  orb (fst (fst a) <? fst (fst b))
       (andb (fst (fst a) =? fst (fst b)) (snd (fst a) <=? snd (fst b))).

Lemma reflect_coord_le {t} a b : reflect (@coord_le t a b) (@coord_leb t a b).
Proof.
destruct (coord_leb a b) eqn:?H; [constructor 1 | constructor 2];
 unfold coord_le, coord_leb in *; lia.
Qed.

Instance CoordBO {t}: BoolOrder (@coord_le t) := 
  {| test := coord_leb; test_spec := reflect_coord_le |}.

Instance CoordPO {t: type}: PreOrder (@coord_le t).
Proof.
constructor.
- intro. unfold complement, coord_le; simpl. lia.
- intros ? ? ? *. unfold coord_le; simpl; lia.
Qed.

Instance CoordBPO {t: type}: BPO.BoolPreOrder (@coord_le t) :=
 {| BPO.BO := CoordBO; BPO.PO := CoordPO |}.


  

