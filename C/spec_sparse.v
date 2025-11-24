Require Import VST.floyd.proofauto.
From LAProof.C Require Import sparse sparse_model.
Require Import vcfloat.FPStdCompCert.
Require Import VSTlib.spec_math.
Require Import LAProof.C.floatlib.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

Definition t_csr := Tstruct _csr_matrix noattr.

Definition csr_rep (sh: share) (mval: matrix Tdouble) (p: val) : mpred :=
  EX v: val, EX ci: val, EX rp: val, 
  EX cols, EX vals: list (ftype Tdouble), EX col_ind: list Z, EX row_ptr: list Z,
  !! csr_rep_aux mval cols vals col_ind row_ptr &&
  data_at sh t_csr (v,(ci,(rp,(Vint (Int.repr (matrix_rows mval)), Vint (Int.repr cols))))) p *
  data_at sh (tarray tdouble (Zlength col_ind)) (map Vfloat vals) v * 
  data_at sh (tarray tuint (Zlength col_ind)) (map Vint (map Int.repr col_ind)) ci *
  data_at sh (tarray tuint (matrix_rows mval + 1)) (map Vint (map Int.repr row_ptr)) rp.

Definition csr_matrix_rows_spec :=
 DECLARE _csr_matrix_rows
 WITH sh: share, m: val, mval: matrix Tdouble
 PRE [ tptr t_csr ]
    PROP (readable_share sh; matrix_rows mval < Int.max_unsigned)
    PARAMS (m)
    SEP (csr_rep sh mval m)
 POST [ tuint ]
    PROP ()
    RETURN (Vint (Int.repr (matrix_rows mval)))
    SEP (csr_rep sh mval m).

Definition csr_row_vector_multiply_spec {NAN : FPCore.Nans} :=
 DECLARE _csr_row_vector_multiply
 WITH sh1: share, sh2: share, sh3: share,
      m: val, mval: matrix Tdouble, v: val, vval: vector Tdouble, i: Z
 PRE [ tptr t_csr, tptr tdouble, tuint ]
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             matrix_cols mval (Zlength vval);
             matrix_rows mval < Int.max_unsigned;
             Zlength vval < Int.max_unsigned;
             0 <= i < matrix_rows mval;
             Forall finite vval;
             Forall (Forall finite) mval)
    PARAMS(m; v; Vint (Int.repr i))
    SEP (csr_rep sh1 mval m;
         data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v)
 POST [ tdouble ]
   EX s: ftype Tdouble,
    PROP(feq s (dotprod (Znth i mval) vval)) 
    RETURN(Vfloat s)
    SEP (csr_rep sh1 mval m;
          data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v).

Definition csr_matrix_vector_multiply_byrows_spec {NAN : FPCore.Nans} :=
 DECLARE _csr_matrix_vector_multiply_byrows
 WITH sh1: share, sh2: share, sh3: share,
      m: val, mval: matrix Tdouble, v: val, vval: vector Tdouble, p: val
 PRE [ tptr t_csr, tptr tdouble, tptr tdouble ]
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             matrix_cols mval (Zlength vval);
             matrix_rows mval < Int.max_unsigned;
             Zlength vval < Int.max_unsigned;
             Forall finite vval;
             Forall (Forall finite) mval)
    PARAMS(m; v; p)
    SEP (csr_rep sh1 mval m;
         data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
         data_at_ sh3 (tarray tdouble (matrix_rows mval)) p)
 POST [ tvoid ]
   EX result: vector Tdouble,
    PROP(Forall2 feq result (matrix_vector_mult mval vval)) 
    RETURN()
    SEP (csr_rep sh1 mval m;
          data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
          data_at sh3 (tarray tdouble (matrix_rows mval)) 
             (map Vfloat result) p).

Definition csr_matrix_vector_multiply_spec {NAN : FPCore.Nans} :=
 DECLARE _csr_matrix_vector_multiply
 WITH sh1: share, sh2: share, sh3: share,
      m: val, mval: matrix Tdouble, v: val, vval: vector Tdouble, p: val
 PRE [ tptr t_csr, tptr tdouble, tptr tdouble ]
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             matrix_cols mval (Zlength vval);
             matrix_rows mval < Int.max_unsigned;
             Zlength vval < Int.max_unsigned;
             Forall finite vval;
             Forall (Forall finite) mval)
    PARAMS(m; v; p)
    SEP (csr_rep sh1 mval m;
         data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
         data_at_ sh3 (tarray tdouble (matrix_rows mval)) p)
 POST [ tvoid ]
   EX result: vector Tdouble,
    PROP(Forall2 feq result (matrix_vector_mult mval vval)) 
    RETURN()
    SEP (csr_rep sh1 mval m;
          data_at sh2 (tarray tdouble (Zlength vval)) (map Vfloat vval) v; 
          data_at sh3 (tarray tdouble (matrix_rows mval)) 
             (map Vfloat result) p).


Section MathComp.
(** Among all the mathcomp stuff, these are the files that we *do* want to Import: *)
Local Import fintype matrix mv_mathcomp.


Definition csr_matrix_vector_multiply_spec' {NAN : FPCore.Nans} :=
 DECLARE _csr_matrix_vector_multiply
 WITH sh1: share, sh2: share, sh3: share,
      mp: val, X: { mn & 'M[ftype Tdouble]_(fst mn, snd mn) * 'cV[ftype Tdouble]_(snd mn)}%type, v: val, p: val
 PRE [ tptr t_csr, tptr tdouble, tptr tdouble ] let '(existT _ (rows,cols) (A,x)) := X in
    PROP(readable_share sh1; readable_share sh2; writable_share sh3;
             Z.of_nat rows < Int.max_unsigned; Z.of_nat cols < Int.max_unsigned;
             (forall (i: 'I_cols), finite (x i ord0));
             (forall (i: 'I_rows) (j:'I_cols), finite (A i j)))
    PARAMS(mp; v; p)
    SEP (csr_rep sh1 (listlist_of_mx A) mp;
         data_at sh2 (tarray tdouble (Z.of_nat cols)) (map Vfloat (list_of_cV x)) v; 
         data_at_ sh3 (tarray tdouble (Z.of_nat rows)) p)
 POST [ tvoid ] let '(existT _ (rows,cols) (A,x)) := X in
   EX result: 'cV[ftype Tdouble]_rows,
    PROP(forall i, feq (result i ord0) (F.FMA_mulmx A x i ord0))
    RETURN()
    SEP (csr_rep sh1 (listlist_of_mx A) mp;
          data_at sh2 (tarray tdouble (Z.of_nat cols)) (map Vfloat (list_of_cV x)) v; 
          data_at sh3 (tarray tdouble (Z.of_nat rows)) 
             (map Vfloat (list_of_cV result)) p).

Lemma zip_combine: @seq.zip = @combine.
Proof.
extensionality A B.
extensionality l1 l2.
revert l2; induction l1; destruct l2; simpl; auto.
f_equal; auto.
Qed.

Lemma foldl_fold_left: forall A B (f: B -> A -> B) (b: B) (al: list A),
   seq.foldl f b al = fold_left f al b.
Proof.
intros.
revert b; induction al; simpl; intros; auto.
Qed.

Lemma mc_matrix_vector_mult: @floatlib.matrix_vector_mult = @matrix_vector_mult.
Proof.
extensionality NAN t m v.
unfold floatlib.matrix_vector_mult, matrix_vector_mult.
change @seq.map with @map.
f_equal.
extensionality row.
unfold dotprod, list_dotprod.
rewrite zip_combine.
symmetry.
apply foldl_fold_left.
Qed.

Lemma matrix_cols_nat':
    forall t (al: list (list (ftype t))) n, matrix_cols al (Z.of_nat n) <-> matrix_cols_nat al n.
Proof.
induction al; simpl; intros; split; intro H; inv H; constructor; auto.
rewrite Zlength_correct in H2. apply Nat2Z.inj in H2; auto.
apply IHal in H3. auto.
apply Zlength_correct.
apply IHal; auto.
Qed.

Lemma Forall2_nth: forall {A B} `{d1: Inhabitant A} `{d2: Inhabitant B} (P: A -> B -> Prop)
       (l1: list A) (l2: list B),
  Forall2 P l1 l2 -> forall i: nat, (i < length l1)%nat -> P (seq.nth d1 l1 i) (seq.nth d2 l2 i).
Proof.
induction 1; simpl; intros. lia.
destruct i; simpl; auto.
apply (IHForall2 i); lia.
Qed.


Lemma csr_matrix_vector_multiply_spec_sub:
   funspec_sub (snd csr_matrix_vector_multiply_spec) (snd (csr_matrix_vector_multiply_spec')).
Proof.
do_funspec_sub.
destruct w as [[[[[[sh1 sh2] sh3] m] X] v] p].
destruct X as [[rows cols] [mval vval]].
Exists (sh1,sh2,sh3, m, listlist_of_mx mval, v, list_of_cV vval, p).
Exists (emp: mpred).
assert (d: ftype Tdouble) by apply (Zconst _ 0).
entailer!!; [ split | ]; clear dependent args.
- intros. Intros x.
  Exists (@cV_of_list _ d rows x).
  entailer!!.
 + intros.
    rewrite mc_matrix_vector_mult in H7.
    rewrite (@Fmulmx_matrix_vector_mult _ Tdouble rows cols) in H7.
  * rewrite mx_of_listlist_of_mx, cV_of_list_of_cV in H7.

    pose proof (Forall2_length H7). rewrite size_list_of_cV in H8.
    assert (Hi := ltn_ord i).    
    pose proof (Forall2_nth _ _ _ H7 i ltac:(lia)).
    unfold Inhabitant in H9.   
    rewrite nth_list_of_cV in H9.
    rewrite <- H9. rewrite <- (@nth_list_of_cV (ftype Tdouble) zerof).
    rewrite list_of_cV_of_list. reflexivity.
    auto.
  * symmetry; apply matrix_rows_listlist_of_mx.
  * symmetry; apply size_list_of_cV.
  * apply matrix_cols_listlist_of_mx.
 + unfold matrix_rows. rewrite !Zlength_correct. change @Datatypes.length with @seq.size.
    rewrite size_list_of_cV,  matrix_rows_listlist_of_mx; simpl.
    rewrite list_of_cV_of_list.
    apply derives_refl.
    apply Forall2_length in H7.
    change @seq.size with @length; rewrite H7; clear H7.
    unfold floatlib.matrix_vector_mult. rewrite length_map.
    rewrite matrix_rows_listlist_of_mx; auto.
- repeat simple apply conj.
 + rewrite  Zlength_correct, size_list_of_cV.

   rewrite matrix_cols_nat'.
   apply  matrix_cols_listlist_of_mx.
 + unfold matrix_rows.  rewrite Zlength_correct. rewrite matrix_rows_listlist_of_mx; simpl; auto.
 + rewrite Zlength_correct, size_list_of_cV; auto.
 + apply Forall_nth; intros.
    rewrite size_list_of_cV in H. simpl in H.


    ordify cols i.
     rewrite <- nth_List_nth, nth_list_of_cV.
   apply H5.
 + apply Forall_nth; intros. 
    rewrite matrix_rows_listlist_of_mx in H. simpl in H.
    ordify rows i.
    assert (Inh_rows: Inhabitant 'I_rows) by  apply i.  
    apply Forall_nth; intros j d' Hj. 
    assert (i < length (ord_enum rows))%nat by (rewrite size_ord_enum; auto).
    assert (length (nth i (listlist_of_mx mval) d0) = cols). {
      unfold listlist_of_mx. simpl.  
     rewrite nth_map' with (d':=Inh_rows); auto.
     rewrite length_map, size_ord_enum; auto.
   }
   rewrite H8 in Hj.
   ordify cols j.
   unfold listlist_of_mx. simpl.
   rewrite nth_map' with (d' := i); auto. rewrite nth_map' with (d':=j).
   apply H6. rewrite size_ord_enum; auto.
- rewrite Zlength_correct, size_list_of_cV.
  unfold matrix_rows.  rewrite Zlength_correct.
   rewrite matrix_rows_listlist_of_mx. simpl. apply derives_refl.
Qed.
End MathComp.

Definition SparseASI : funspecs := [ 
   csr_matrix_rows_spec;
   csr_row_vector_multiply_spec;
   csr_matrix_vector_multiply_byrows_spec;
   csr_matrix_vector_multiply_spec ].

Definition SubsetMathASI := [fma_spec].
Definition Gprog : funspecs := SubsetMathASI ++ SparseASI.

Lemma BFMA_eq:
   forall H H' H0 (x y z : Binary.binary_float (fprec Tdouble) (femax Tdouble)),
  Binary.Bfma (fprec Tdouble) (femax Tdouble) H H0
    (FPCore.fma_nan (fprec Tdouble) (femax Tdouble) H') BinarySingleNaN.mode_NE x y z = 
  BFMA x y z.
Proof.
intros.
 unfold BFMA. simpl.
 repeat f_equal; apply proof_irr.
Qed.
