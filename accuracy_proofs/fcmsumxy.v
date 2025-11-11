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
Search (1 < fprec _)%Z.
Search (fprec _ <? femax _)%Z.
Search (_ < _ -> (_ <? _)=true)%Z.


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

End A.

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
(*
Lemma fsum_l2r_rec_finite_e: forall k (c: ftype t) (a: ftype t ^ k),
  Binary.is_finite (fsum_l2r_rec c [ffun i : 'I_k => a (rshift1 i)]) ->
  Binary.is_finite c /\ 
  Binary.is_finite (a ord0) /\ 
  Binary.is_finite (fsum_l2r_rec (BPLUS c (a ord0)) a).

  Binary
a' :=
  [ffun i => fun_of_fin
               [ffun i0 => BOPP (fun_of_fin [ffun i1 => BMULT (fun_of_fin a i1) (fun_of_fin b i1)] i0)]
               (lift ord0 i)] : {ffun 'I_k -> F}
FINyt : is_true (Binary.is_finite (fsum_l2r_rec c1 a'))
______________________________________(1/1)

*)

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

Lemma LVSDP_ytilded_eq: forall [k] (a b : F ^ k) (c bk: F),
    Binary.is_finite bk ->
    Binary.is_finite (ytilded c a b bk) ->
  float_spec.FS_val (cholesky.ytilded (mkFS c) [ffun i => mkFS (fun_of_fin a i)]  [ffun i => mkFS (fun_of_fin b i)]  (mkFS bk)) =
  FT2R (ytilded c a b bk).
Proof.
intros * FINbk H. 
rewrite /cholesky.ytilded /ytilded /cholesky.stilde /stilde.
rewrite -FS_val_fdiv'; auto.
f_equal. f_equal.
rewrite /ytilded /stilde in H.
apply BDIV_finite_e in H; auto.
rewrite LVSDP_fcmsum_eq; auto.
f_equal. apply eq_dffun => i.
rewrite !ffunE.
rewrite FS_val_mkFS -FS_val_fmult' //.
destruct (fsum_l2r_rec_finite_e1 _ _ _ H).
specialize (H1 i).
rewrite !ffunE in H1.
destruct (BMULT _ _); try discriminate; auto.
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
  change (FT2R bk <> 0). contradict Hbk. destruct bk; auto; try discriminate.
  apply iszeroR_iszeroF; auto.
}
pose proof @cholesky.lemma_2_1 fspec fspec_eta_nonzero k a' b' (mkFS c) (mkFS bk) Hbk'.
repeat change (float_spec.FS_val (mkFS ?x)) with (FT2R x) in H|-*.
rewrite LVSDP_ytilded_eq in H; auto.
replace (\sum_i (float_spec.FS_val _ * _)) with (\sum_i (FT2R (fun_of_fin a i) * (FT2R (b i)))) in H.
2: apply eq_big; auto; move => i _; rewrite /a' /b' !ffunE //.
replace (\sum_i Rabs (float_spec.FS_val _ * _)) with (\sum_i Rabs (FT2R (fun_of_fin a i) * (FT2R (b i)))) in H.
2: apply eq_big; auto; move => i _; rewrite /a' /b' !ffunE //.
replace (float_spec.eta fspec) with eta in H.
2: rewrite /eta /flocq_float.eta /fspec /flocq_float.flocq_float /float_spec.eta /flocq_float.eta bpow_minus1;
      simpl IZR; change (flocq_float.prec) with (fprec t); nra.
replace (float_spec.eps fspec) with eps in H.
apply H.
simpl.
rewrite /eps /flocq_float.eps /flocq_float.prec.
rewrite bpow_plus_1.
fold (fprec t).
simpl. nra.
Qed.

End WithNaN.
