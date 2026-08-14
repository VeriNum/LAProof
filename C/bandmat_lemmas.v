(**  * LAProof.C.bandmat_lemmas: Supporting lemmas for VST proofs of functions on band matrices. *)

From VST.floyd Require Import proofauto VSU.
From LAProof.C Require Import bandmat spec_alloc spec_densemat spec_bandmat.
From LAProof.C Require Import densemat_lemmas.
From VSTlib Require Import spec_math spec_malloc.
From Stdlib Require Import Classes.RelationClasses.
From vcfloat Require Import FPStdLib.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
Import fintype matrix.

Set Bullet Behavior "Strict Subproofs".
Open Scope logic.

Definition memset_spec :=
  DECLARE _memset
  WITH p: val, n: Z, sh: share
  PRE [ tptr tvoid, tint, tulong ]
    PROP (writable_share sh; 0 <= n <= Ptrofs.max_unsigned)
    PARAMS (p; Vint Int.zero; Vptrofs (Ptrofs.repr n))
    SEP (memory_block sh n p)
  POST [ tptr tvoid ]
    PROP ()
    RETURN (p)
    SEP (mapsto_zeros n sh p).

Definition bandmat_E : funspecs := [].
Definition bandmat_imported_specs : funspecs :=
   [free_spec'] (* subset of MallocASI *)
  ++ [exit_spec; surely_malloc_spec'] (* subset of allocASI *)
  ++ [sqrt_spec] (* subset of MathASI *)
  ++ [memset_spec] (* axiomatized libc memset, not part of any ASI *)
  ++ [data_norm2_spec; data_norm_spec; densemat_get_spec] (* subset of densematASI *).
Definition bandmat_internal_specs : funspecs := bandmatASI.
Definition Gprog := bandmat_imported_specs ++ bandmat_internal_specs.

(* compspecs bridging boilerplate, same pattern as densemat_lemmas.v *)
Instance change_composite_env_alloc :
  change_composite_env spec_alloc.CompSpecs CompSpecs.
Proof. make_cs_preserve spec_alloc.CompSpecs CompSpecs. Qed.

Instance change_composite_env_alloc' :
  change_composite_env CompSpecs spec_alloc.CompSpecs.
Proof. make_cs_preserve CompSpecs spec_alloc.CompSpecs. Qed.

Instance change_composite_env_densemat :
  change_composite_env spec_densemat.CompSpecs CompSpecs.
Proof. make_cs_preserve spec_densemat.CompSpecs CompSpecs. Qed.

Instance change_composite_env_densemat' :
  change_composite_env CompSpecs spec_densemat.CompSpecs.
Proof. make_cs_preserve CompSpecs spec_densemat.CompSpecs. Qed.

Lemma map_concat_comm {A B} (f: A -> B) (l: list (list A)):
  map f (concat l) = concat (map (map f) l).
Proof.
induction l as [|x l IH]; simpl; auto.
rewrite map_app, IH; reflexivity.
Qed.

Lemma concat_repeat_repeat {A} (x: A) (n m: nat):
  concat (List.repeat (List.repeat x m) n) = List.repeat x (n * m).
Proof.
induction n as [|n IH]; simpl; auto.
rewrite IH, <- repeat_app.
f_equal.
Qed.

Lemma banded_repr_init_undef:
  forall m b : nat, (b < m)%nat ->
  map val_of_optfloat (banded_repr b (bandmat_init b m))
  = Zrepeat Vundef (Z.of_nat m * Z.of_nat (S b)).
Proof.
intros m b Hb.
unfold Zrepeat.
replace (Z.to_nat (Z.of_nat m * Z.of_nat (S b))) with (m * S b)%nat
  by (rewrite <- Nat2Z.inj_mul, Nat2Z.id; reflexivity).
unfold banded_repr.
rewrite map_concat_comm, map_map.
replace (m * S b)%nat with (S b * m)%nat by lia.
rewrite <- (concat_repeat_repeat Vundef (S b) m).
rewrite <- (map_const_ord_enum (S b) (List.repeat Vundef m)).
f_equal.
apply map_ext_in; intros j _.
assert (Hj: (nat_of_ord j <= b)%nat) by (pose proof (ltn_ord j); lia).
rewrite map_app, map_map.
replace (List.repeat Vundef m) with (List.repeat Vundef (nat_of_ord j) ++ List.repeat Vundef (m - nat_of_ord j))
  by (rewrite <- repeat_app; f_equal; lia).
f_equal.
- induction (nat_of_ord j) as [|k IH]; simpl; auto.
  f_equal; apply IH; lia.
- rewrite (map_ext _ (fun _ => Vundef)).
  + apply map_const_ord_enum.
  + intros i.
    assert (Hentry: bandmat_init b m (inord_inj i) (inord_add j i) = None).
    { unfold bandmat_init.
      rewrite mxE.
      unfold inord_inj, inord_add; simpl.
      assert (Hi := ltn_ord i).
      match goal with
      | |- (if ?c then _ else _) = _ =>
          destruct c eqn:Hcond; [reflexivity | exfalso]
      end.
      exfalso. apply andb_false_iff in Hcond as [H1|H1]; lia.
    }
    rewrite Hentry; reflexivity.
Qed.

Lemma data_at_tarray_zero_weaken:
  forall sh (L: list val) p,
  Forall (fun v => v = Vfloat Float.zero \/ v = Vundef) L ->
  data_at sh (tarray tdouble (Zlength L)) (Zrepeat (Vfloat Float.zero) (Zlength L)) p
  |-- data_at sh (tarray tdouble (Zlength L)) L p.
Proof.
intros sh L.
induction L as [|x L' IH]; intros p HL.
- rewrite Zlength_nil. apply derives_refl.
- rewrite Zlength_cons.
  assert (Hz1: Z.succ (Zlength L') = 1 + Zlength L') by lia.
  rewrite Hz1.
  assert (HzrepeatEq: Zrepeat (Vfloat Float.zero) (1 + Zlength L')
                     = [Vfloat Float.zero] ++ Zrepeat (Vfloat Float.zero) (Zlength L')).
  { unfold Zrepeat.
  pose proof (Zlength_nonneg L').
  rewrite Z2Nat.inj_add by lia.
  reflexivity. }
  rewrite HzrepeatEq.
  change (x :: L') with ([x] ++ L').
  rewrite (split2_data_at_Tarray_app 1 (1 + Zlength L') sh tdouble
             [Vfloat Float.zero] (Zrepeat (Vfloat Float.zero) (Zlength L')) p)
    by (try list_solve; lia).
  rewrite (split2_data_at_Tarray_app 1 (1 + Zlength L') sh tdouble
             [x] L' p)
    by (try list_solve; lia).
  replace (1 + Zlength L' - 1) with (Zlength L') by lia.
  apply sepcon_derives.
  + rewrite (data_at_singleton_array_eq sh tdouble (Vfloat Float.zero) [Vfloat Float.zero] p eq_refl).
    rewrite (data_at_singleton_array_eq sh tdouble x [x] p eq_refl).
    apply Forall_inv in HL as [Heq | Heq]; rewrite Heq.
    * apply derives_refl.
    * change Vundef with (default_val tdouble).
      apply data_at_data_at_.
  + apply IH.
    eapply Forall_inv_tail; eauto.
Qed.

Lemma banded_repr_const_zero_or_undef:
  forall m b : nat, (b < m)%nat ->
  Forall (fun v => v = Vfloat Float.zero \/ v = Vundef)
    (map val_of_optfloat (banded_repr b (@const_mx _ m m (Some (Zconst the_type 0))))).
Proof.
intros m b Hb.
unfold banded_repr.
rewrite map_concat_comm, map_map.
apply Forall_concat.
apply Forall_map.
apply Forall_forall; intros j _.
simpl.
rewrite map_app, map_map.
apply Forall_app; split.
- apply Forall_forall; intros x Hx.
  apply in_map_iff in Hx as [x0 [<- Hx0]].
  apply repeat_spec in Hx0.
  subst x0.
  right; reflexivity.
- rewrite (map_ext _ (fun _ => Vfloat Float.zero)).
  + apply Forall_forall; intros x Hx.
    apply in_map_iff in Hx as [i0 [<- _]]. left. reflexivity.
  + intros i0. unfold const_mx. rewrite mxE. reflexivity.
Qed.

Lemma Zlength_banded_repr {T} {InhT: Inhabitant T} :
  forall (m b: nat) (M: 'M[T]_(m,m)),
  (b < m)%nat ->
  Zlength (banded_repr b M) = (Z.of_nat m * Z.of_nat (S b))%Z.
Proof.
intros m b M Hb.
unfold banded_repr.
rewrite (Zlength_concat' (Z.of_nat (S b)) (Z.of_nat m)).
- lia.
- rewrite Zlength_map. apply Zlength_ord_enum.
- apply Forall_map.
  apply Forall_forall.
  intros j _.
  simpl.
  rewrite Zlength_app, Zlength_map.
  rewrite Zlength_correct, repeat_length.
  rewrite Zlength_ord_enum.
  assert (Hjm: (nat_of_ord j <= m)%nat) by (pose proof (ltn_ord j); lia).
  lia.
Qed.