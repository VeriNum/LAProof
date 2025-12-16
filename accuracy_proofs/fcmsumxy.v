(** * Importing a proof from libValidSDP into LAProof *)

(** libValidSDP and LAProof each have proofs about the accuracy of linear-algebra operations in 
  floating-point, but they represent floating-point very differently.
 -  LAProof says that [ftype t] is an IEEE-754 floating-point number with a number of exponent bits
   and mantissa bits specified by [t], and with all the Infinity and NaN behaviors specified by IEEE-754.
 - libValidSDP says that a floating pointer number is a real number that satisfies the [format] predicate,
     where [format] is a predicate [R->bool].  The abstraction in libValidSDP makes some things easier
     to prove, perhaps; in any case, some very useful things are proved there.  But we might not want
     to use the [format] abstraction globally, because then we couldn't distinguish infinities from NaNs.
  Because it is proved (in module libvalidsdp.flocq_float) that the IEEE floats are an instance of
  a legal format, one can import theorems from libValidSDP into LAProof (though not vice versa).
  This module is a demonstration of how to do that.  The theorem in libValidSDP is 
     [cholesky.lemma_2_1], and it is imported here as [LVSDP_lemma_2_1].
 
*)


From LAProof.accuracy_proofs Require Import preamble common.
From libValidSDP Require cholesky flocq_float float_spec float_infnan_spec flocq_float binary_infnan.
From LAProof Require accuracy_proofs.mv_mathcomp.

Definition max_mantissa t : positive := Pos.pow 2 (fprecp t) - 1.

Lemma digits_max_mantissa t: Z.pos (SpecFloat.digits2_pos (max_mantissa t))  = fprec t.
Proof.
intros.
rewrite Digits.Zpos_digits2_pos.
unfold max_mantissa.
rewrite Pos2Z.inj_sub.
2: apply Pos.pow_gt_1; compute; auto.
rewrite Pos2Z.inj_pow.
pose proof Digits.Zdigits_correct Zaux.radix2 (2 ^ Z.pos (fprecp t) - 1).
simpl in H.
assert (0 < 2 ^ Z.pos (fprecp t) - 1)%Z. {
  assert (2 ^ 0 < 2 ^ Z.pos (fprecp t))%Z; [ | lia].
  apply Z.pow_lt_mono_r; auto; lia.
}
simpl; pose proof (Zaux.Zpower_pos_gt_0 2 (fprecp t) ltac:(lia)).
rewrite Z.pow_pos_fold in H.
rewrite Z.abs_eq in H; auto; try lia.
clear H1.
fold (fprec t) in H0,H|-*.
set d := Digits.Zdigits Zaux.radix2 (2 ^ fprec t - 1) in H|-*. 
assert (d>0)%Z. {
 pose proof (Digits.Zdigits_le Zaux.radix2 1%Z (2 ^ fprec t - 1) ltac:(lia) ltac:(lia)). fold d in H1. simpl in H1. lia.
}
set (e := fprec t) in H0,H|-*.
assert (d<e \/ d=e \/ d>e)%Z by lia.
destruct H2 as [?| [?| ?]]; auto.
assert (2 ^ d < 2^e)%Z. apply Z.pow_lt_mono_r; auto; try lia. lia.
assert (2 ^ (d-1) >= 2^ e)%Z. apply Z.le_ge. apply Z.pow_le_mono_r; lia.
lia.
Qed.

Lemma max_mantissa_bounded t: SpecFloat.bounded (fprec t) (femax t) (max_mantissa t) (femax t - fprec t).
hnf.
unfold SpecFloat.bounded.
unfold SpecFloat.canonical_mantissa.
unfold SpecFloat.fexp, SpecFloat.emin.
rewrite digits_max_mantissa.
rewrite Z.max_l; try lia.
pose proof fprec_lt_femax t.
pose proof fprec_gt_0 t.
red in H0.
lia.
Qed.

Definition Float_max t := Binary.B754_finite (fprec t) (femax t) false _ _ (max_mantissa_bounded t).

Section WithNaN.

Context {NAN: FPCore.Nans} {t : type}.

Definition default_rel : R :=
  / 2 * Raux.bpow Zaux.radix2 (- fprec t + 1).

Definition default_abs : R :=
  / 2 * Raux.bpow Zaux.radix2 (3 - femax t - fprec t).

Lemma prec_lt_emax: @flocq_float.prec (fprecp t) <? femax t.
Proof.
pose proof fprec_lt_femax t.
rewrite /flocq_float.prec.
rewrite /fprec in H.
apply Z.ltb_lt; auto.
Qed.

Notation F := (ftype t).
Notation eps := (default_rel).
Notation eta := (default_abs).

Lemma default_abs_nonzero:  default_abs <> 0.
rewrite /eta.
apply Rmult_integral_contrapositive.
split. lra.
rewrite bpow_powerRZ.
apply powerRZ_NOR.
simpl. lra.
Qed.

Definition fspec := @flocq_float.flocq_float (fprecp t) (femax t) (fprec_gt_one _) prec_lt_emax.

Lemma fspec_eta_nonzero: float_spec.eta fspec <> 0.
Proof.
simpl.
rewrite /flocq_float.eta.
rewrite bpow_powerRZ.
apply powerRZ_NOR.
simpl. lra.
Qed.

Definition iszero {t} (x: ftype t) : bool := 
  match x with Binary.B754_zero _ _ _ => true | _ => false end.

Fixpoint fsum_l2r_rec [n: nat] (c : F) : F^n -> F :=
  match n with
    | 0%N => fun _ => c
    | n'.+1 =>
      fun a => fsum_l2r_rec (BPLUS c (a ord0)) [ffun i => a (lift ord0 i)]
  end.


Definition fcmsum_l2r [n] (c : F) (x : F^n) : F :=
  fsum_l2r_rec c [ffun i => BOPP (x i)].

Definition stilde [k] (c : F) (a b : F^k) : F :=
  fcmsum_l2r c [ffun i => BMULT (a i) (b i) : F].    

Definition ytilded [k : nat] (c : F) (a b : F^k) (bk : F) :=
  BDIV (stilde c a b) bk.

Definition ytildes [k : nat] (c : F) (a : F^k):=
  BSQRT (stilde c a a).


Lemma BPLUS_B2R_zero (a : ftype t):
  Binary.is_finite a ->
  FT2R (BPLUS a (Zconst t 0)) = FT2R a.
Proof.
unfold BPLUS, BINOP, Zconst; intros;
destruct a; simpl; try discriminate; auto.
destruct s; simpl; auto.
Qed.

Lemma format_FT2R: forall (x: ftype t), is_true (@flocq_float.format (fprecp t) (femax t) (FT2R x)).
Proof.
move => x.
rewrite /flocq_float.format  /flocq_float.generic_format_pred /FT2R.
set fexp := (FLT.FLT_exp _ _).
change (Defs.F2R _) with (Generic_fmt.round Zaux.radix2  fexp Ztrunc (Binary.B2R _ _ x)).
apply /eqP.
symmetry.
destruct x eqn:Hx; try (apply Generic_fmt.round_0; constructor; intros; [ apply Ztrunc_le; auto | apply Ztrunc_IZR]).
symmetry.
apply Binary.generic_format_B2R; auto.
Qed.

Definition LVSDP_NAN : binary_infnan.Nans.
destruct NAN.
constructor.
apply conv_nan.
apply plus_nan.
apply mult_nan.
apply div_nan.
apply abs_nan.
apply opp_nan.
apply sqrt_nan.
apply fma_nan.
Defined.

Definition mkFS (x: F) : float_spec.FS fspec  := float_spec.Build_FS_of (format_FT2R x).

Section A.

Import float_infnan_spec.
Definition origFIS := 
  @binary_infnan.binary_infnan LVSDP_NAN (fprecp t) (femax t) 
       (fprec_gt_one t) prec_lt_emax.

(*Definition the_compare (x y: ftype t) :  *)

Definition the_FIS : float_infnan_spec.Float_infnan_spec :=
           {| FIS := origFIS.(FIS);
              FIS0 := origFIS.(FIS0);
              FIS1 := origFIS.(FIS1);
              finite0 := origFIS.(finite0);
              finite1 := origFIS.(finite1);
              fis := fspec;
              m := origFIS.(m);
              m_ge_2 := origFIS.(m_ge_2);
              FIS2FS := mkFS;
              FIS2FS_spec := origFIS.(FIS2FS_spec);
              FIS2FS0 := origFIS.(FIS2FS0);
              FIS2FS1 := origFIS.(FIS2FS1);
              firnd := origFIS.(firnd);
              firnd_spec := origFIS.(firnd_spec);
              firnd_spec_f := origFIS.(firnd_spec_f);
              fiopp := _;
              fiopp_spec := origFIS.(fiopp_spec);
              fiopp_spec_f1 := origFIS.(fiopp_spec_f1);
              fiopp_spec_f := origFIS.(fiopp_spec_f);
              fiplus := _;
              fiplus_spec := origFIS.(fiplus_spec);
              fiplus_spec_fl := origFIS.(fiplus_spec_fl);
              fiplus_spec_fr := origFIS.(fiplus_spec_fr);
              fiplus_spec_f := origFIS.(fiplus_spec_f);
              fiminus := _;
              fiminus_spec := origFIS.(fiminus_spec);
              fiminus_spec_fl := origFIS.(fiminus_spec_fl);
              fiminus_spec_fr := origFIS.(fiminus_spec_fr);
              fiminus_spec_f := origFIS.(fiminus_spec_f);
              fimult:= _;
              fimult_spec := origFIS.(fimult_spec);
              fimult_spec_fl := origFIS.(fimult_spec_fl);
              fimult_spec_fr := origFIS.(fimult_spec_fr);
              fimult_spec_f := origFIS.(fimult_spec_f);
              fidiv := _;
              fidiv_spec := origFIS.(fidiv_spec);
              fidiv_spec_fl := origFIS.(fidiv_spec_fl);
              fidiv_spec_f := origFIS.(fidiv_spec_f);
              fisqrt := _;
              fisqrt_spec := origFIS.(fisqrt_spec);
              fisqrt_spec_f1 := origFIS.(fisqrt_spec_f1);
              fisqrt_spec_f := origFIS.(fisqrt_spec_f);
              ficompare := origFIS.(ficompare);
              ficompare_spec := origFIS.(ficompare_spec);
              ficompare_spec_eq := origFIS.(ficompare_spec_eq);
              ficompare_spec_eq_f := origFIS.(ficompare_spec_eq_f);
          |}.

Definition F' := the_FIS.(FIS).


Lemma FS_val_mkFS: forall x: F', float_spec.FS_val (mkFS x) = (FT2R x).
Proof. reflexivity. Qed.


Lemma FS_val_fplus: forall x y: ftype t, 
  is_true (the_FIS.(finite) (the_FIS.(fiplus) x y)) -> 
  float_spec.FS_val (float_spec.fplus (mkFS x) (mkFS y)) = FT2R (BPLUS x y).
Proof.
intros * FIN.
rewrite <- the_FIS.(fiplus_spec); auto.
simpl.
f_equal. rewrite /BPLUS /BINOP /binary_infnan.fiplus.
f_equal.
apply ProofIrrelevance.proof_irrelevance.
rewrite /LVSDP_NAN /=.
destruct NAN; reflexivity.
Qed.


Lemma FS_val_fplus': forall x y: ftype t, 
  Binary.is_finite (BPLUS x y) -> 
  float_spec.FS_val (float_spec.fplus (mkFS x) (mkFS y)) = FT2R (BPLUS x y).
Proof.
intros * FIN.
apply FS_val_fplus.
simpl.
red in FIN|-*.
rewrite -FIN.
f_equal.
rewrite /binary_infnan.fiplus /BPLUS /BINOP; f_equal.
apply ProofIrrelevance.proof_irrelevance.
rewrite  /LVSDP_NAN /=.
destruct NAN; reflexivity.
Qed.


Lemma FS_val_fmult: forall x y: ftype t, 
  is_true (the_FIS.(finite) (the_FIS.(fimult) x y)) -> 
  float_spec.FS_val (float_spec.fmult (mkFS x) (mkFS y)) = FT2R (BMULT x y).
Proof.
intros * FIN.
rewrite <- the_FIS.(fimult_spec); auto.
simpl.
f_equal. rewrite /BMULT /BINOP /binary_infnan.fimult.
f_equal.
apply ProofIrrelevance.proof_irrelevance.
rewrite /LVSDP_NAN /=.
destruct NAN; reflexivity.
Qed.

Lemma FS_val_fmult': forall x y: ftype t, 
  Binary.is_finite (BMULT x y) -> 
  float_spec.FS_val (float_spec.fmult (mkFS x) (mkFS y)) = FT2R (BMULT x y).
Proof.
intros * FIN.
apply FS_val_fmult.
simpl.
red in FIN|-*.
rewrite -FIN.
f_equal.
rewrite /binary_infnan.fimult /BMULT /BINOP; f_equal.
apply ProofIrrelevance.proof_irrelevance.
rewrite  /LVSDP_NAN /=.
destruct NAN; reflexivity.
Qed.


Lemma FS_val_fopp: forall x: ftype t, 
  is_true (the_FIS.(finite) (the_FIS.(fiopp) x)) ->
  float_spec.FS_val (float_spec.fopp (mkFS x)) = FT2R (BOPP x).
Proof.
intros * FIN.
rewrite <- the_FIS.(fiopp_spec); auto.
simpl.
f_equal. rewrite /BOPP /UNOP /binary_infnan.fiopp.
f_equal.
rewrite /LVSDP_NAN /=.
destruct NAN; reflexivity.
Qed.

Lemma FS_val_fopp': forall x: ftype t, 
  Binary.is_finite (BOPP x) -> 
  float_spec.FS_val (float_spec.fopp (mkFS x)) = FT2R (BOPP x).
Proof.
intros * FIN.
apply FS_val_fopp.
red in FIN|-*. rewrite -{}FIN.
simpl.
f_equal.
rewrite /binary_infnan.fiopp /BOPP /UNOP; f_equal.
rewrite /LVSDP_NAN /=.
destruct NAN; reflexivity.
Qed.

Lemma FS_val_fdiv: forall x y: ftype t, 
  is_true (the_FIS.(finite) (the_FIS.(fidiv) x y)) -> 
  is_true (the_FIS.(finite) y) -> 
  float_spec.FS_val (float_spec.fdiv (mkFS x) (mkFS y)) = FT2R (BDIV x y).
Proof.
intros * FINxy FINy.
rewrite <- the_FIS.(fidiv_spec); auto.
simpl.
f_equal. rewrite /BDIV /BINOP /binary_infnan.fidiv.
f_equal.
apply ProofIrrelevance.proof_irrelevance.
rewrite /binary_infnan.div_nan /LVSDP_NAN /FPCore.div_nan /=.
destruct NAN; reflexivity.
Qed.

Lemma FS_val_fdiv': forall x y: ftype t, 
  Binary.is_finite (BDIV x y) -> 
  Binary.is_finite y -> 
  float_spec.FS_val (float_spec.fdiv (mkFS x) (mkFS y)) = FT2R (BDIV x y).
intros.
apply FS_val_fdiv; auto.
simpl.
red in H|-*.
rewrite -H.
f_equal.
rewrite /binary_infnan.fidiv /BDIV /BINOP; f_equal.
apply ProofIrrelevance.proof_irrelevance.
rewrite /binary_infnan.div_nan /LVSDP_NAN /FPCore.div_nan /=.
destruct NAN; reflexivity.
Qed.


Lemma FS_val_fsqrt': forall x: ftype t, 
  Binary.is_finite (BSQRT x) -> 
  float_spec.FS_val (float_spec.fsqrt (mkFS x)) = FT2R (BSQRT x).
intros.
rewrite <- the_FIS.(fisqrt_spec); auto.
simpl. f_equal. rewrite /BSQRT /UNOP /binary_infnan.fisqrt.
f_equal.
apply ProofIrrelevance.proof_irrelevance.
rewrite /binary_infnan.sqrt_nan /LVSDP_NAN /FPCore.sqrt_nan /=.
destruct NAN; reflexivity.
rewrite /is_true -{}H /finite /= /BSQRT /UNOP /fisqrt /finite /= /binary_infnan.fisqrt.
f_equal. f_equal.
apply ProofIrrelevance.proof_irrelevance.
rewrite /binary_infnan.div_nan /LVSDP_NAN /FPCore.div_nan /=.
destruct NAN; reflexivity.
Qed.

Lemma FT2R_congr: forall x y : ftype t, feq x y -> FT2R x = FT2R y.
Proof.
intros.
destruct x,y; try destruct s; try destruct s0; simpl in H; try contradiction; try reflexivity;
destruct H as [? [? ?]]; subst; auto; try discriminate.
Qed.

Lemma FT2R_feq: forall x y: ftype t, Binary.is_finite x -> Binary.is_finite y -> FT2R x = FT2R y -> feq x y.
Proof.
intros.
destruct x,y; try discriminate; repeat match goal with s: bool |- _ => destruct s; try discriminate end; try reflexivity;
repeat match goal with
     | H: FT2R (Binary.B754_zero _ _ _) = FT2R _ |- _ => symmetry in H; apply Float_prop.eq_0_F2R in H; discriminate H 
     | H: FT2R _ = FT2R (Binary.B754_zero _ _ _)  |- _ => apply Float_prop.eq_0_F2R in H; discriminate H 
     | H: FT2R _ = FT2R _ |- _ => unfold FT2R in H; apply Binary.B2R_inj in H; [inversion H; clear H; subst | reflexivity | reflexivity]
    end;
repeat proof_irr;
try reflexivity.
Qed.

Lemma FT2R_BDIV_congr: forall x x' y y': ftype t,
  Binary.is_finite x -> Binary.is_finite x' -> Binary.is_finite y -> Binary.is_finite y' ->
  FT2R x = FT2R x' ->
  FT2R y = FT2R y' ->
  FT2R (BDIV x y) = FT2R (BDIV x' y').
Proof.
intros.
apply FT2R_feq in H3; auto.
apply FT2R_feq in H4; auto.
apply FT2R_congr.
apply BDIV_mor; auto.
apply feq_strict_feq; auto.
destruct y,y'; try discriminate; try contradiction; auto.
red. red. auto.
Qed.

End A.


Lemma default_abs_eq: eta = float_spec.eta fspec.
Proof.
rewrite /eta /flocq_float.eta /fspec /flocq_float.flocq_float /float_spec.eta /flocq_float.eta bpow_minus1;
      simpl IZR; change (flocq_float.prec) with (fprec t); nra.
Qed.

Lemma default_rel_eq: eps = float_spec.eps fspec.
Proof.
rewrite /eps /flocq_float.eps /fspec /flocq_float.flocq_float /float_spec.eps /flocq_float.eps
           bpow_plus bpow_opp bpow_1.
rewrite Rmult_comm Rmult_assoc /= Rmult_inv_r; lra.
Qed.

Lemma FS_val_ext: forall {format} x y, 
  @float_spec.FS_val format x = float_spec.FS_val y -> x = y.
Proof.
intros.
destruct x,y; simpl in *.
subst FS_val0.
f_equal.
apply ProofIrrelevance.proof_irrelevance.
Qed.


Lemma BDIV_finite_e: forall (x y: ftype t) (H: Binary.is_finite (BDIV x y)), Binary.is_finite x.
Proof.
intros.
destruct x, y; try destruct s; try destruct s0; try discriminate; auto.
Qed.

Lemma BMULT_finite_e : (* copied from float_acc_lemmas, FIXME *)
 forall (a b : ftype t) (Hfin : Binary.is_finite (BMULT  a b)),
 Binary.is_finite a  /\ Binary.is_finite b.
Proof.
unfold BMULT, BINOP; intros.
destruct a,b; inversion Hfin; clear Hfin; subst; auto.
Qed.

Lemma BPLUS_finite_e : (* copied from float_acc_lemmas, FIXME *)
 forall (a b : ftype t) (Hfin : Binary.is_finite (BPLUS  a b)),
 Binary.is_finite a  /\  Binary.is_finite b.
Proof.
unfold BPLUS, BINOP; intros.
destruct a,b; inversion Hfin; clear Hfin; subst; simpl; auto.
destruct s,s0; discriminate; auto.
Qed.

Lemma BSQRT_finite_e: forall (x: ftype t) (H: Binary.is_finite (BSQRT x)), Binary.is_finite x.
Proof.
intros.
destruct x; try destruct s; try discriminate; auto.
Qed.

Ltac case_splitP j := (* copied from mv_mathcomp and improved; FIXME *)
  tryif clearbody j then fail "case_splitP requires a variable, but got  a local definition" j
  else tryif is_var j then idtac else fail "case_splitP requires a variable, but got" j;
 match type of j with 'I_(addn ?a ?b) =>
  let i := fresh "j" in let H := fresh in 
  destruct (splitP j) as [i H | i H];
 [replace j with (@lshift a b i); [ | apply ord_inj; simpl; lia]
 |replace j with (@rshift a b i); [ | apply ord_inj; simpl; lia]];
 clear j H; rename i into j
 end.

Lemma fsum_l2r_rec_finite_e: forall k (c: ftype t) (a: ftype t ^ k.+1),
  Binary.is_finite (fsum_l2r_rec c a) ->
  Binary.is_finite c 
  /\ (forall i, Binary.is_finite (a i))
  /\ Binary.is_finite (fsum_l2r_rec (BPLUS c (a ord0)) [ffun i => a (rshift 1 i)]).
Proof.
induction k; intros.
-
split; [ | split]; auto; apply BPLUS_finite_e in H; destruct H; auto.
intro. rewrite (_:(i=ord0)) //.
apply ord_inj.
destruct i. simpl. lia.
-
rewrite /fsum_l2r_rec -/fsum_l2r_rec in H.
set c1 := BPLUS c _ in H|-*.
destruct (IHk c1 [ffun i => a (rshift 1 i)]) as [? [? ?]]; clear IHk.
+
red. rewrite -H. f_equal. f_equal.
apply eq_dffun. move => i. rewrite rshift1 //.
+
apply BPLUS_finite_e in H0. destruct H0.
split; auto.
split.
*
simpl in H1|-*.
intro.
assert (k.+2 = 1+k.+1)%nat by lia.
pose i' := cast_ord H4 i.
rewrite -(cast_ordK H4 i) -/i'.
clearbody i'.
case_splitP i'.
replace (cast_ord (esym H4) (lshift k.+1 i')) with (@ord0 k.+1); auto.
apply ord_inj; simpl. destruct i'. simpl. lia.
specialize (H1 i').
red; rewrite -H1.
f_equal.
rewrite ffunE. f_equal.
apply ord_inj; auto.
*
red; rewrite -H.
f_equal.
f_equal.
apply eq_dffun => i. rewrite rshift1 //.
Qed.


Lemma fsum_l2r_rec_finite_e1: forall k (c: ftype t) (a: ftype t ^ k),
  Binary.is_finite (fsum_l2r_rec c a) ->
  Binary.is_finite c 
  /\ (forall i, Binary.is_finite (a i)).
Proof.
destruct k; intros.
-
simpl in *.
split; auto.
intros i. destruct i. lia.
-
apply fsum_l2r_rec_finite_e in H.
tauto.
Qed.

Lemma LVSDP_fcmsum_eq:
 forall [k] (c: F) (a: F^k) 
   (FIN: Binary.is_finite (fcmsum_l2r c a)),
   mkFS (fcmsum_l2r c a) = fcmsum.fcmsum_l2r (mkFS c) [ffun i => float_spec.FS_val (mkFS (a i))].
Proof.
rewrite /fcmsum_l2r /fcmsum.fcmsum_l2r.
induction k; intros; auto.
simpl.
set c1 := BPLUS c _.
specialize (IHk c1 [ffun i => a (rshift 1 i)]).
replace  [ffun i => fun_of_fin [ffun i0 => BOPP (fun_of_fin a i0)] (lift ord0 i)]
  with [ffun i => BOPP (fun_of_fin [ffun i0 => fun_of_fin a (rshift 1 i0)] i)].
2: apply eq_dffun; simpl; intro; rewrite ffunE rshift1 ffunE //.
rewrite {}IHk.
2:{
red. rewrite -FIN. f_equal.
simpl. f_equal.
apply eq_dffun => i. rewrite ffunE rshift1 ffunE //.
}
simpl.
f_equal.
-
subst c1.
apply FS_val_ext.
rewrite ffunE.
rewrite FS_val_mkFS -FS_val_fplus'.
2:{
apply fsum_l2r_rec_finite_e in FIN.
destruct FIN as [? [? ?]]. simpl in *.
rewrite ffunE in H1.
destruct (fsum_l2r_rec_finite_e1 _ _ _ H1); auto.
}
simpl float_spec.fplus.
f_equal. f_equal. f_equal.
rewrite !ffunE.
rewrite -FS_val_fopp'.
f_equal. f_equal.
apply FS_val_ext.
rewrite FS_val_mkFS.
etransitivity. symmetry. apply round_FT2R.
reflexivity.
apply fsum_l2r_rec_finite_e1 in FIN.
destruct FIN.
specialize (H0 ord0).
rewrite ffunE in H0. auto.
-
apply eq_dffun. simpl; intro i.
rewrite !ffunE.
rewrite rshift1; auto.
Qed.


Lemma LVSDP_stilde_eq: forall [k] (a b : F ^ k) (c: F),
    Binary.is_finite (stilde c a b) ->
    cholesky.stilde (mkFS c) [ffun i => mkFS (fun_of_fin a i)] [ffun i => mkFS (fun_of_fin b i)] = mkFS (stilde c a b).
Proof.
rewrite /stilde /cholesky.stilde => k a b c Hfin.
rewrite LVSDP_fcmsum_eq; auto.
f_equal. apply eq_dffun => i.
rewrite !ffunE.
rewrite FS_val_mkFS -FS_val_fmult' //.
destruct (fsum_l2r_rec_finite_e1 _ _ _ Hfin).
specialize (H0 i).
rewrite !ffunE in H0.
destruct (BMULT _ _); try discriminate; auto.
Qed.

Lemma LVSDP_ytilded_eq: forall [k] (a b : F ^ k) (c bk: F),
    Binary.is_finite bk ->
    Binary.is_finite (ytilded c a b bk) ->
  float_spec.FS_val (cholesky.ytilded (mkFS c) [ffun i => mkFS (fun_of_fin a i)]  [ffun i => mkFS (fun_of_fin b i)]  (mkFS bk)) =
  FT2R (ytilded c a b bk).
Proof.
intros * FINbk H. 
rewrite /cholesky.ytilded /ytilded in H|-*.
(* /cholesky.stilde /stilde.*)
rewrite -FS_val_fdiv'; auto.
f_equal. f_equal.
apply BDIV_finite_e in H; auto.
rewrite /ytilded in H.
apply LVSDP_stilde_eq; auto.
Qed.


Lemma LVSDP_ytildes_eq: forall [k] (a : F ^ k) (c: F),
    Binary.is_finite (ytildes c a) ->
  float_spec.FS_val (cholesky.ytildes (mkFS c) [ffun i => mkFS (fun_of_fin a i)]  ) =
  FT2R (ytildes c a).
Proof.
intros * H. 
rewrite /cholesky.ytildes /ytilded.
rewrite -FS_val_fsqrt'; auto.
f_equal. f_equal.
rewrite /ytildes in H.
apply BSQRT_finite_e in H; auto.
apply LVSDP_stilde_eq; auto.
Qed.

Lemma LVSDP_lemma_2_1 k (a b : F^k) (c bk : F) 
   (Hbk : ~iszero bk)
   (FINbk: Binary.is_finite bk)
   (FINyt: Binary.is_finite (ytilded c a b bk)):
  Rabs (FT2R bk * FT2R (ytilded c a b bk) - (FT2R c - \sum_i (FT2R (a i) * FT2R (b i))%Re))
  < INR k.+1 * eps * (Rabs (FT2R bk * FT2R (ytilded c a b bk)) + \sum_i Rabs (FT2R(a i) * FT2R(b i)))
    + (1 + INR k.+1 * eps) * (INR k.+1 + Rabs (FT2R bk)) * eta.
Proof.
pose a' := [ffun i => mkFS (a i)].
pose b' := [ffun i => mkFS (b i)].
have Hbk': float_spec.FS_val (mkFS bk) <> 0. {
  contradict Hbk.
  apply iszeroR_iszeroF; auto.
}
pose proof @cholesky.lemma_2_1 fspec fspec_eta_nonzero k a' b' (mkFS c) (mkFS bk) Hbk'.
repeat change (float_spec.FS_val (mkFS ?x)) with (FT2R x) in H|-*.
rewrite LVSDP_ytilded_eq in H; auto.
replace (\sum_i (float_spec.FS_val _ * _)) with (\sum_i (FT2R (fun_of_fin a i) * (FT2R (b i)))) in H.
2: apply eq_big; auto; [  move => x // | move => i _; rewrite /a' /b' !ffunE //].
replace (\sum_i Rabs (float_spec.FS_val _ * _)) with (\sum_i Rabs (FT2R (fun_of_fin a i) * (FT2R (b i)))) in H.
2: apply eq_big; auto; [ move => x // | move => i _; rewrite /a' /b' !ffunE //].
rewrite default_abs_eq default_rel_eq.
apply H.
Qed.

(*
Definition cholesky_spec : Prop :=
  (forall (j i : 'I_n.+1),
     (i < j)%N ->
     (Rt i j = ytilded (A i j)
                       [ffun k : 'I_i => Rt (inord k) i]
                       [ffun k : 'I_i => Rt (inord k) j]
                       (Rt i i) :> R))
  /\ (forall (j : 'I_n.+1),
        (Rt j j = ytildes (A j j) [ffun k : 'I_j => Rt (inord k) j] :> R)).

*)

(* Definitions copied from C/matrix_model.v *)

Definition subtract_loop {t} (c: ftype t) (l: seq (ftype t * ftype t)) :=
  foldl BMINUS c (map (uncurry BMULT) l).

Definition subtract_loop_jik {t}  [n] (c: ftype t) (R: 'M[ftype t]_n) (i j k: 'I_n) : ftype t :=
   subtract_loop c (map (fun k' => (R k' i, R k' j)) (take k (ord_enum n))).

Definition cholesky_jik_ij {t} [n: nat] (A R: 'M[ftype t]_n) (i j: 'I_n) : Prop :=
     (forall Hij: (i<j)%N,  R i j = BDIV (subtract_loop_jik (A i j) R i j i) (R i i))
   /\ (forall Hij: i=j, R i j = BSQRT (subtract_loop_jik (A i j) R i j i)).

Definition cholesky_jik_spec {t} [n: nat] (A R: 'M[ftype t]_n) : Prop :=
  forall i j, cholesky_jik_ij A R i j.

Definition cholesky_success {t} [n: nat] (A R: 'M[ftype t]_n) : Prop :=
   cholesky_jik_spec A R /\
   forall i, Binary.is_finite_strict _ _ (R i i).

Lemma subtract_loop_finite_e: forall (c: ftype t) (al: seq (ftype t * ftype t)), 
  Binary.is_finite (subtract_loop c al) ->
  Binary.is_finite c /\ forallb (fun p => Binary.is_finite (fst p) && Binary.is_finite (snd p)) al.
Proof.
 intros c al; revert c; induction al as [ | [x y] al] ; intros.
 - split; auto.
 - unfold subtract_loop in H.  simpl in H. 
  apply IHal in H.
  destruct H.
  apply float_acc_lems.BMINUS_finite_sub in H. destruct H; auto.
  split; auto.
  simpl. apply BMULT_finite_e in H1. destruct H1. rewrite H1 H2. apply H0.
Qed.

Import mv_mathcomp.

Lemma cholesky_success_R_finite:
 forall [n] (A R: 'M[ftype t]_n),
  A^T = A ->
  cholesky_success A R ->
  forall i j, (nat_of_ord i <= nat_of_ord j)%N -> Binary.is_finite (R i j).
Proof.
intros n A R H [H0 H1] i j H2.
red in H1.
assert (H1': forall i, Binary.is_finite (R i i)).
intro k; apply is_finite_strict_finite; apply H1.
assert ((i<j) \/ (nat_of_ord i == nat_of_ord j))%N by lia.
destruct H3.
2: assert (i=j) by (apply ord_inj; lia); subst j; apply (H1' i).
destruct (H0 i j) as [? _].
specialize (H4 H3).
pose proof (H1' j).
pose proof (H0 j j).
destruct H6 as [_ ?].
rewrite H6 in H5; auto.
apply BSQRT_finite_e in H5.
unfold subtract_loop_jik in H5.
apply subtract_loop_finite_e in H5.
destruct H5 as [_ H5].
red in H5. rewrite -> forallb_forall in H5.
specialize (H5 (R i j, R i j)).
simpl in H5.
assert (Binary.is_finite (fun_of_matrix R i j) && Binary.is_finite (fun_of_matrix R i j) = true).
2: rewrite Bool.andb_true_iff in H7; destruct H7; auto.
apply H5.
clear - H3.
rewrite map_take.
set f := (fun k' : ordinal n => pair (fun_of_matrix R k' j) (fun_of_matrix R k' j)).
change (pair _ _) with (f i).
clearbody f.
pose proof (ltn_ord j).
replace (f i) with  (ListDef.nth (nat_of_ord i) (take (nat_of_ord j) (map f (ord_enum n))) (Zconst t 0, Zconst t 0)).
apply nth_In.
change @length with @size.
rewrite size_take.
rewrite size_map.
rewrite size_ord_enum.
rewrite H.
lia.
rewrite -nth_List_nth.
rewrite nth_take; auto.
rewrite (nth_map i).
rewrite nth_ord_enum' //.
rewrite size_ord_enum.
lia.
Qed.

Definition cholesky_bound (n: nat) := FT2R (Float_max t) - (eps * INR(2*(n-1)) + INR(n+1)*FT2R(Float_max t)).

Lemma cholesky_jik_spec_backwards_finite:
  forall n (A R: 'M[F]_n),
  A^T = A ->
  cholesky_jik_spec A R ->
  (forall i j: 'I_n, i <= j -> Binary.is_finite (R i j)) ->
  (forall i j, Binary.is_finite (A i j)).
Proof.
  move => n A R Hsym H FINR i j.
  assert (Hsub: forall (x: F) al, Binary.is_finite (subtract_loop x al) -> Binary.is_finite x). {
   intros. apply subtract_loop_finite_e in H0. apply H0.
 }
  assert (H2: ((i<j) \/ (nat_of_ord i== nat_of_ord j) \/ (j<i))%N) by lia.
  destruct H2 as [H2 | [H2 | H2]].
-
  destruct (H i j) as [H0 _].
  specialize (H0 H2). 
  specialize (FINR i j). rewrite H0 in FINR. apply BDIV_finite_e in FINR; [ | rewrite leEord; lia]. 
  apply Hsub in FINR. auto.
- destruct (H i j) as [_ H0].
  assert (H1: i=j) by (apply ord_inj; lia). apply H0 in H1.
  specialize (FINR i j). rewrite H1 in FINR. apply BSQRT_finite_e in FINR; [ | rewrite leEord; lia]. 
  apply Hsub in FINR. auto.
- rewrite -Hsym. rewrite mxE.
  destruct (H j i) as [H0 _].
  specialize (H0 H2). 
  specialize (FINR j i). rewrite H0 in FINR. apply BDIV_finite_e in FINR; [ | rewrite leEord; lia].  
  apply Hsub in FINR. auto.
Qed.

Lemma ord_enum_S: forall n, ord_enum (S n) = (@inord n 0) :: (map (@inord n \o S \o (@nat_of_ord n)) (ord_enum n)).
Proof.
intros.
apply (@eq_from_nth _ ord0).
simpl.
rewrite size_map !size_ord_enum //.
rewrite size_ord_enum.
intros.
destruct i; simpl.
change O with (nat_of_ord (@ord0 n)).
rewrite nth_ord_enum'.
apply ord_inj; simpl.
rewrite inordK; auto.
change (S i) with (nat_of_ord (Ordinal H)).
rewrite nth_ord_enum'.
apply ord_inj.
simpl.
destruct n; simpl. lia.
rewrite (nth_map (@ord0 n)).
2: rewrite size_ord_enum //.
simpl.
assert (i<n.+1)%N by lia.
change i with (nat_of_ord (Ordinal H0)).
rewrite nth_ord_enum' //.
simpl.
rewrite inordK; lia.
Qed.

Lemma Forall_take_ord_enum: forall [n] (u: 'I_n), Forall (fun x: 'I_n => is_true (x< u)) (take u (ord_enum n)).
Proof.
intros.
replace (fun x : ordinal n => is_true (@Order.lt Order.OrdinalOrder.ord_display (Order.OrdinalOrder.fintype_ordinal__canonical__Order_POrder n) x u))
  with (fun x: ordinal n => is_true (nat_of_ord x < nat_of_ord u)).
2:{ apply FunctionalExtensionality.functional_extensionality; intro j.
destruct j as [j Hj]; destruct u as [u Hu]; simpl in *. reflexivity.
}
rewrite Forall_nth; intros.
rewrite -nth_List_nth.
change @length with @size in H.
rewrite size_take size_ord_enum in H.
assert (i < n /\ i<u)%N.
  destruct (u<n)%N eqn:?H; lia.
clear H. destruct H0.
change i with (nat_of_ord (Ordinal H)).
rewrite nth_take.
rewrite nth_ord_enum'.
simpl. lia.
simpl; lia.
Qed. 

Lemma stilde_subtract_loop: forall [n] (c: F) (R: 'M_n.+1) (i j: 'I_n.+1) (Hij: (i<=j)%N),
  feq (stilde c [ffun k : 'I_i => R (inord (nat_of_ord k)) i] [ffun k => R (inord (nat_of_ord k)) j])
  (subtract_loop_jik c R i j i).
Proof.
rewrite /stilde /fcmsum_l2r /subtract_loop_jik /subtract_loop.
induction n; move => c R i j Hij /=.
-
rewrite !ord1 /=. rewrite take0 //.
-
destruct (nat_of_ord i) as [ | u] eqn:?H. rewrite take0 //.
destruct (nat_of_ord j) as [ | v] eqn:?H; [ lia |].
simpl.
rewrite !ffunE.
have H3 :((n.+2=addn 1 n.+1)*(n.+2= addn 1 n.+1))%type by (split; lia).
set c1 := BPLUS _ _.
assert (Hu: u < n.+1). pose proof (ltn_ord j); lia.
assert (Hv: v < n.+1). pose proof (ltn_ord j); lia.
ordify n.+1 u.
ordify n.+1 v.
specialize (IHn c1 (drsubmx (castmx H3 R)) u v).
etransitivity; [ | etransitivity; [ apply IHn; lia | ]]; clear IHn.
+
simpl.
match goal with |- feq ?A ?B => replace B with A; try reflexivity end.
f_equal.
apply eq_dffun => k.
have Hk := ltn_ord k.
rewrite !ffunE !lift0.
f_equal.
f_equal.
rewrite drsubmxEsub !mxE castmxE /=.
f_equal; apply ord_inj; simpl; rewrite ?inordK; try (simpl; lia).
rewrite drsubmxEsub !mxE castmxE /=.
f_equal; apply ord_inj; simpl; rewrite ?inordK; try (simpl; lia).
+
rewrite (ord_enum_S n.+1).
simpl.
match goal with |- feq (foldl _ _ ?A) (foldl _ _ ?B) => replace B with A; [ set al := A | ] end.
*
clearbody al.
set d1 := BMINUS c _.
assert (feq c1 d1).
symmetry; apply MINUS_PLUS_BOPP.
clear - H1.
clearbody c1. clearbody d1. clear - H1.
revert c1 d1 H1; induction al; simpl; intros; auto.
apply IHal. rewrite H1; auto.
*
f_equal.
clear c1.
rewrite  -map_take.
rewrite -map_comp.
assert (Forall (fun x => x < u) (take (nat_of_ord u) (ord_enum n.+1))).
 apply Forall_take_ord_enum.
set (al := take _ _) in H1|-*.
clearbody al.
induction H1; simpl; auto.
f_equal; auto.
rewrite !drsubmxEsub.
rewrite castmxEsub.
rewrite -mxsub_comp.
rewrite /mxsub.
rewrite  !mxE.
f_equal; f_equal; apply ord_inj; simpl; try lia; rewrite inordK; auto;
clear - H1 Hu; destruct x,u; simpl in *; lia.
Qed.

Lemma ytilded_subtract_loop: forall n (A R: 'M[F]_n.+1) (i j: 'I_n.+1), 
 (forall i j: 'I_n.+1, (i<=j)%N -> Binary.is_finite (R i j)) ->
   (i<j)%N ->
  feq (ytilded (A i j) [ffun k: 'I_i => R (inord (nat_of_ord k)) i] [ffun k => R (inord (nat_of_ord k)) j] (R i i))  (BDIV (subtract_loop_jik (A i j) R i j i) (R i i)).
Proof.
intros.
rewrite /ytilded.
apply BDIV_mor.
apply stilde_subtract_loop; lia.
apply strict_feq_refl.
apply H; auto.
Qed.

Add Parametric Morphism: BSQRT  (* move this to vcfloat.FPStdLib and vcfloat.StdLib *)
 with signature @feq t ==> @feq t
 as BSQRT_mor.
Proof.
intros.
destruct x; try destruct s; try discriminate; destruct y ; try destruct s; try contradiction; try reflexivity.
destruct H; discriminate.
destruct H; discriminate.
destruct H as [? [? ?]].
subst.
proof_irr.
reflexivity.
Qed.

Lemma ytildes_subtract_loop: forall n (A R: 'M[F]_n.+1) (i: 'I_n.+1), 
  feq (ytildes (A i i) [ffun k: 'I_i => R (inord (nat_of_ord k)) i]) (BSQRT (subtract_loop_jik (A i i) R i i i)).
Proof.
intros.
rewrite /ytildes.
rewrite stilde_subtract_loop; auto.
Qed.

Lemma LVSDP_cholesky_spec: forall n (A R: 'M[F]_n.+1),
  A^T = A ->
  (forall i j: 'I_n.+1, (i <= j)%N -> Binary.is_finite (R i j)) ->
  cholesky_jik_spec A R ->
  libValidSDP.cholesky.cholesky_spec (map_mx mkFS A) (map_mx mkFS R).
Proof.
move => n A R HA HR H.
move :(cholesky_jik_spec_backwards_finite _ _ _ HA H HR). clear HA. move => HA.
split.
-
move => j i Hij; specialize (H i j). destruct H as [H _]. specialize (H Hij).
rewrite !mxE !FS_val_mkFS.
match goal  with |- _ = _ (_ ?X ?Y _) => set Rki := X; set Rkj := Y end.
simpl in Rki, Rkj.
replace Rki with   [ffun i0 => mkFS ([ffun k: 'I_i => R (inord k) i] i0)].
2: apply eq_dffun => k; rewrite /map_mx !mxE ffunE //.
replace Rkj with  [ffun i0 => mkFS ([ffun k: 'I_i => R (inord k) j] i0)].
2: apply eq_dffun => k; rewrite /map_mx !mxE ffunE //.
rewrite LVSDP_ytilded_eq; auto.
2: rewrite ytilded_subtract_loop // -H //.
apply FT2R_congr.
rewrite H.
rewrite ytilded_subtract_loop; auto.
apply HR. lia.
-
move => i.
rewrite !mxE !FS_val_mkFS.
specialize (H i i). destruct H as [_ H]. specialize (H Logic.eq_refl).
match goal  with |- _ = _ (_ ?X) => set Rki := X end.
simpl in Rki.
replace Rki with   [ffun i0 => mkFS ([ffun k: 'I_i => R (inord k) i] i0)].
2: apply eq_dffun => k; rewrite /map_mx !mxE ffunE //.
rewrite LVSDP_ytildes_eq; auto.
2: rewrite ytildes_subtract_loop // -H //.
rewrite H.
apply FT2R_congr.
rewrite ytildes_subtract_loop; auto.
apply HR; lia.
Qed.

Lemma BSQRT_nonneg: forall x:F,  
   match BSQRT x with Binary.B754_finite _ _ false _ _ _ => true
                      | Binary.B754_zero _ _ _ => true
                      | Binary.B754_infinity _ _ false => true
                      | Binary.B754_nan _ _ _ _ _ => true
                      | _ => false 
   end = true.
Proof.
intros.
unfold BSQRT, UNOP, Binary.Bsqrt, Binary.BSN2B.
destruct (BinarySingleNaN.Bsqrt_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t) BinarySingleNaN.mode_NE
  (Binary.B2BSN _ _ x)) 
  as [? [? ?]].
set x' := BinarySingleNaN.Bsqrt BinarySingleNaN.mode_NE (Binary.B2BSN (fprec t) (femax t) x) in H,H0,H1|-*.
destruct x eqn:Hx; try destruct s; simpl in *; try discriminate; auto.
destruct x'; simpl in *; try discriminate; auto.
rewrite H1; auto.
Qed.

Lemma LVDSP_cholesky_success: forall [n] (A R: 'M[F]_n.+1),
  A^T = A ->
  cholesky_success A R ->
  libValidSDP.cholesky.cholesky_success (map_mx mkFS A) (map_mx mkFS R).
Proof.
intros n A R HA H.
pose proof cholesky_success_R_finite A R HA H.
destruct H; split.
apply LVSDP_cholesky_spec; auto.
intro i.
rewrite mxE. specialize (H1 i).
destruct (H i i) as [_ ?]. specialize (H2 (Logic.eq_refl _)).
 destruct (R i i); try discriminate H1. simpl.
pose proof (BSQRT_nonneg (subtract_loop_jik (fun_of_matrix A i i) R i i i)).
rewrite - H2 in H3.
destruct s; try discriminate.
simpl.
apply Float_prop.F2R_gt_0; simpl. lia.
Qed.

End WithNaN.


