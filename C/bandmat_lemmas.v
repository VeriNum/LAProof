(**  * LAProof.C.bandmat_lemmas: Supporting lemmas for VST proofs of functions on band matrices. *)

From VST.floyd Require Import proofauto VSU.
From LAProof.C Require Import bandmat spec_alloc spec_densemat spec_bandmat.
From LAProof.C Require Import densemat_lemmas.
From LAProof.accuracy_proofs Require Import solve_model.
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

Lemma Znth_concat_at {A: Type} {Inh: Inhabitant A}:
  forall (m : Z) (l: list (list A)) (outer local: Z),
  Forall (fun x => Zlength x = m) l ->
  0 <= outer < Zlength l ->
  0 <= local < m ->
  Znth (outer * m + local) (concat l) = Znth local (Znth outer l).
Proof.
  intros m l. induction l as [|a l' IHl]; intros outer local Hall Houter Hlocal.
  - exfalso. rewrite Zlength_nil in Houter. lia.
  - simpl concat.
    assert (Ha: Zlength a = m) by (inversion Hall; auto).
    assert (Hall': Forall (fun x => Zlength x = m) l') by (inversion Hall; auto).
    destruct (Z.eq_dec outer 0) as [Ho|Ho].
    + subst outer.
      rewrite Z.mul_0_l, Z.add_0_l.
      rewrite app_Znth1 by lia.
      rewrite Znth_0_cons.
      reflexivity.
    + assert (Houter1: 1 <= outer) by lia.
      rewrite app_Znth2 by nia.
      replace (outer * m + local - Zlength a) with ((outer - 1) * m + local) by (rewrite Ha; ring).
      assert (Hbound: 0 <= outer - 1 < Zlength l') by (rewrite Zlength_cons in Houter; lia).
      rewrite (IHl (outer - 1) local Hall' Hbound Hlocal).
      rewrite Znth_pos_cons by lia.
      reflexivity.
Qed.

Lemma banded_repr_Znth {T} {InhT: Inhabitant T} (m b: nat) (M: 'M[T]_(m,m)) (i j: 'I_m):
  0 <= (Z.of_nat j - Z.of_nat i) <= Z.of_nat b ->
  (b < m)%nat ->
  @Znth T InhT (Z.of_nat j + (Z.of_nat j - Z.of_nat i) * Z.of_nat m) (@banded_repr T InhT m b M) = M i j. 
Proof.
  intros Hd Hb.
  set (d := (j - i)%nat).
  assert (Hd_eq: Z.of_nat j - Z.of_nat i = Z.of_nat d) by (unfold d; lia).
  assert (Hd_le: (d <= b)%nat) by (unfold d; lia).
  rewrite Hd_eq.
  unfold banded_repr.
  assert (Hunif: Forall (fun x => Zlength x = Z.of_nat m)
                  (map (fun j0: 'I_(S b) =>
                     ListDef.repeat InhT (nat_of_ord j0) ++
                     map (fun i0: 'I_(m - j0) => M (inord_inj i0) (inord_add j0 i0)) (ord_enum (m - j0)))
                   (ord_enum (S b)))).
  { apply Forall_map. apply Forall_forall. intros j0 _. simpl.
    rewrite Zlength_app, Zlength_map.
    rewrite Zlength_correct, repeat_length.
    rewrite Zlength_ord_enum.
    assert (Hjm: (nat_of_ord j0 <= m)%nat) by (pose proof (ltn_ord j0); lia).
    lia. }
  assert (Hd_ge: 0 <= Z.of_nat d) by lia.
  assert (Hd_lt: Z.of_nat d < Zlength (map (fun j0: 'I_(S b) =>
                 ListDef.repeat InhT (nat_of_ord j0) ++
                 map (fun i0: 'I_(m - j0) => M (inord_inj i0) (inord_add j0 i0)) (ord_enum (m - j0)))
               (ord_enum (S b)))).
  { rewrite Zlength_map, Zlength_ord_enum. lia. }
  assert (Hj_bound: 0 <= Z.of_nat j < Z.of_nat m) by (pose proof (ltn_ord j); lia).
  replace (j + d * m) with (d * m + j) by lia.
  rewrite (Znth_concat_at (Z.of_nat m) _ (Z.of_nat d) (Z.of_nat j) Hunif (conj Hd_ge Hd_lt) Hj_bound).
  assert (Hd_ord: (d < S b)%nat) by lia.
  pose (d_ord := @Ordinal (S b) d ltac:(lia)).
  rewrite (@Znth_map 'I_(S b) d_ord (list T) _ (Z.of_nat d) _ (ord_enum (S b)) ltac:(rewrite Zlength_ord_enum; lia)).
  assert (Hznth_d: Znth (Z.of_nat d) (ord_enum (S b)) = d_ord) by exact (@Znth_ord_enum (S b) d_ord d_ord).
  rewrite Hznth_d.
  simpl nat_of_ord.
  rewrite app_Znth2 by (rewrite Zlength_correct, repeat_length; lia).
  rewrite Zlength_correct, repeat_length.
  replace (Z.of_nat j - Z.of_nat d) with (Z.of_nat i) by (unfold d; lia).
  pose (i_ord := @Ordinal (m - d) i ltac:(unfold d; lia)).
  rewrite (@Znth_map 'I_(m - d) i_ord T InhT (Z.of_nat i) _ (ord_enum (m - d)) ltac:(rewrite Zlength_ord_enum; lia)).
  assert (Hznth_i: Znth (Z.of_nat i) (ord_enum (m - d)) = i_ord) by exact (@Znth_ord_enum (m - d) i_ord i_ord).
  rewrite Hznth_i.
  assert (E1: inord_inj i_ord = i) by (apply ord_inj; reflexivity).
  assert (E2: inord_add d_ord i_ord = j) by (apply ord_inj; simpl; unfold d; lia).
  rewrite E1, E2. reflexivity.
Qed.

Lemma upd_Znth_concat_at {A: Type} {Inh: Inhabitant A}:
  forall (chunklen : Z) (l: list (list A)) (outer local: Z) (v: A),
  Forall (fun x => Zlength x = chunklen) l ->
  0 <= outer < Zlength l ->
  0 <= local < chunklen ->
  upd_Znth (outer * chunklen + local) (concat l) v
  = concat (upd_Znth outer l (upd_Znth local (Znth outer l) v)).
Proof.
  intros chunklen l. induction l as [|a l' IHl]; intros outer local v Hall Houter Hlocal.
  - exfalso. rewrite Zlength_nil in Houter. lia.
  - simpl concat.
    assert (Ha: Zlength a = chunklen) by (inversion Hall; auto).
    assert (Hall': Forall (fun x => Zlength x = chunklen) l') by (inversion Hall; auto).
    destruct (Z.eq_dec outer 0) as [Ho|Ho].
    + subst outer.
      rewrite Z.mul_0_l, Z.add_0_l.
      rewrite upd_Znth_app1 by lia.
      rewrite Znth_0_cons, upd_Znth0.
      reflexivity.
    + assert (Houter1: 1 <= outer) by lia.
      assert (Houter': outer <= Zlength l') by (rewrite Zlength_cons in Houter; lia).
      assert (Hlen': Zlength (concat l') = (Zlength l' * chunklen)%Z)
        by (apply (Zlength_concat' (Zlength l') chunklen l'); [reflexivity | exact Hall']).
      rewrite upd_Znth_app2 by (rewrite Ha; nia).
      replace (outer * chunklen + local - Zlength a) with ((outer - 1) * chunklen + local) by (rewrite Ha; ring).
      assert (Hbound: 0 <= outer - 1 < Zlength l') by (rewrite Zlength_cons in Houter; lia).
      rewrite (IHl (outer - 1) local v Hall' Hbound Hlocal).
      rewrite Znth_pos_cons by lia.
      rewrite upd_Znth_cons by lia.
      reflexivity.
Qed.

Lemma Znth_list_eq {A: Type} {Inh: Inhabitant A}:
  forall (l1 l2: list A),
  Zlength l1 = Zlength l2 ->
  (forall i, 0 <= i < Zlength l1 -> Znth i l1 = Znth i l2) ->
  l1 = l2.
Proof.
  induction l1 as [|a1 l1' IH]; intros l2 Hlen Hpt.
  - destruct l2 as [|a2 l2'].
    + reflexivity.
    + rewrite Zlength_nil, Zlength_cons in Hlen. exfalso. pose proof (Zlength_nonneg l2'). lia.
  - destruct l2 as [|a2 l2'].
    + rewrite Zlength_cons, Zlength_nil in Hlen. exfalso.
      pose proof (Zlength_nonneg l1'). lia.
    + assert (Ha: a1 = a2).
      { specialize (Hpt 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg l1'); lia)).
        rewrite !Znth_0_cons in Hpt. exact Hpt. }
      subst a2. f_equal.
      apply IH.
      * rewrite !Zlength_cons in Hlen. lia.
      * intros i Hi.
        specialize (Hpt (i+1) ltac:(rewrite Zlength_cons; lia)).
        rewrite !Znth_pos_cons in Hpt by lia.
        replace (i+1-1) with i in Hpt by lia.
        exact Hpt.
Qed.

Lemma upd_Znth_map_ord_eq {T: Type} {InhT: Inhabitant T} (n: nat) (f g: 'I_n -> T) (a0: 'I_n) (v: T):
  (forall k: 'I_n, k <> a0 -> f k = g k) ->
  g a0 = v ->
  upd_Znth (Z.of_nat a0) (map f (ord_enum n)) v = map g (ord_enum n).
Proof.
  intros Hoff Hv.
  assert (Hb0: 0 <= Z.of_nat a0 < Zlength (map f (ord_enum n)))
    by (rewrite Zlength_map, Zlength_ord_enum; pose proof (ltn_ord a0); lia).
  apply Znth_list_eq.
  - rewrite upd_Znth_Zlength by exact Hb0.
    rewrite !Zlength_map, !Zlength_ord_enum. reflexivity.
  - intros i Hi.
    rewrite upd_Znth_Zlength in Hi by exact Hb0.
    destruct (Z.eq_dec i (Z.of_nat a0)) as [Heq|Hneq].
    + subst i.
      rewrite upd_Znth_same by exact Hb0.
      rewrite (@Znth_map 'I_n a0 T InhT (Z.of_nat a0) g (ord_enum n) 
        ltac:(rewrite Zlength_ord_enum; pose proof (ltn_ord a0); lia)).
      assert (Hza0: Znth (Z.of_nat a0) (ord_enum n) = a0) by exact (@Znth_ord_enum n a0 a0).
      rewrite Hza0. symmetry. exact Hv.
    + rewrite upd_Znth_diff by lia.
      assert (Hin: i < Z.of_nat n) by (rewrite Zlength_map, Zlength_ord_enum in Hi; lia).
      pose (i_ord := @Ordinal n (Z.to_nat i) ltac:(lia)).
      rewrite (@Znth_map 'I_n i_ord T InhT i f (ord_enum n) ltac:(rewrite Zlength_ord_enum; lia)).
      rewrite (@Znth_map 'I_n i_ord T InhT i g (ord_enum n) ltac:(rewrite Zlength_ord_enum; lia)).
      assert (Hi_eq: Z.of_nat i_ord = i) by (unfold i_ord; simpl; lia).
      pose proof (@Znth_ord_enum n i_ord i_ord) as Hzi0.
      rewrite Hi_eq in Hzi0.
      rewrite Hzi0.
      apply Hoff.
      intro Hcontra. apply Hneq. rewrite <- Hi_eq, Hcontra. reflexivity.
Qed.

Lemma update_mx_same {T} [m n] (M: 'M[T]_(m,n)) (i: 'I_m) (j: 'I_n) (x: T):
  update_mx M i j x i j = x.
Proof.
  unfold update_mx. rewrite mxE. repeat destruct (Nat.eq_dec _ _); auto; lia.
Qed.

Lemma update_mx_diff {T} [m n] (M: 'M[T]_(m,n)) (i: 'I_m) (j: 'I_n) (x: T) (i' : 'I_m) (j': 'I_n):
  i' <> i \/ j' <> j ->
  update_mx M i j x i' j' = M i' j'.
Proof.
  intros Hneq.
  unfold update_mx. rewrite mxE.
  repeat destruct (Nat.eq_dec _ _); auto.
  exfalso. destruct Hneq as [Hneq|Hneq]; apply Hneq; apply ord_inj; auto.
Qed.

Lemma banded_repr_lower_update {T} {InhT: Inhabitant T} (m b: nat) (M: 'M[T]_(m,m)) (x y: 'I_m) (v: T):
  (nat_of_ord y < nat_of_ord x)%nat ->
  @banded_repr T InhT m b (update_mx M x y v) = @banded_repr T InhT m b M.
Proof.
  intros Hxy.
  unfold banded_repr.
  f_equal.
  apply map_ext_in.
  intros j0 _.
  f_equal.
  apply map_ext_in.
  intros i0 _.
  apply update_mx_diff.
  destruct (Nat.eq_dec (inord_inj i0) x) as [Heq|Hneq].
  - right. intro Hc.
    assert (Hc': nat_of_ord (inord_add j0 i0) = nat_of_ord y) by (rewrite Hc; reflexivity).
    simpl in Hc', Heq.
    lia.
  - left. intro Hc. apply Hneq. rewrite Hc. reflexivity.
Qed.

Lemma banded_repr_upd_Znth {T} {InhT: Inhabitant T} (m b: nat) (M: 'M[T]_(m,m)) (i j: 'I_m) (v: T):
  0 <= (Z.of_nat j - Z.of_nat i) <= Z.of_nat b ->
  (b < m)%nat ->
  upd_Znth (Z.of_nat j + (Z.of_nat j - Z.of_nat i) * Z.of_nat m) (@banded_repr T InhT m b M) v
  = @banded_repr T InhT m b (update_mx M i j v).
Proof.
  intros Hd Hb.
  set (d := (j - i)%nat).
  assert (Hd_eq: Z.of_nat j - Z.of_nat i = Z.of_nat d) by (unfold d; lia).
  assert (Hd_le: (d <= b)%nat) by (unfold d; lia).
  rewrite Hd_eq.
  unfold banded_repr.
  assert (Hunif: Forall (fun x => Zlength x = Z.of_nat m)
                  (map (fun j0: 'I_(S b) =>
                     @ListDef.repeat T InhT (nat_of_ord j0) ++
                     map (fun i0: 'I_(m - j0) => M (inord_inj i0) (inord_add j0 i0)) (ord_enum (m - j0)))
                   (ord_enum (S b)))).
  { apply Forall_map. apply Forall_forall. intros j0 _. simpl.
    rewrite Zlength_app, Zlength_map.
    rewrite Zlength_correct, repeat_length.
    rewrite Zlength_ord_enum.
    assert (Hjm: (nat_of_ord j0 <= m)%nat) by (pose proof (ltn_ord j0); lia).
    lia. }
  assert (Hd_ge: 0 <= Z.of_nat d) by lia.
  assert (Hd_lt: Z.of_nat d < Zlength (map (fun j0: 'I_(S b) =>
             @ListDef.repeat T InhT (nat_of_ord j0) ++
             map (fun i0: 'I_(m - j0) => M (inord_inj i0) (inord_add j0 i0)) (ord_enum (m - j0)))
           (ord_enum (S b)))).
  { rewrite Zlength_map, Zlength_ord_enum. lia. }
  assert (Hj_bound: 0 <= Z.of_nat j < Z.of_nat m) by (pose proof (ltn_ord j); lia).
  replace (j + d * m) with (d * m + j) by lia.
  pose proof (upd_Znth_concat_at (Z.of_nat m) _ (Z.of_nat d) (Z.of_nat j) v Hunif (conj Hd_ge Hd_lt) Hj_bound) as Hstep1.
  etransitivity; [exact Hstep1 | ].
  pose (d_ord := @Ordinal (S b) d ltac:(lia)).
  rewrite (@Znth_map 'I_(S b) d_ord (list T) _ (Z.of_nat d) _ (ord_enum (S b)) ltac:(rewrite Zlength_ord_enum; lia)).
  assert (Hznth_d: Znth (Z.of_nat d) (ord_enum (S b)) = d_ord) by exact (@Znth_ord_enum (S b) d_ord d_ord).
  rewrite Hznth_d.
  simpl nat_of_ord.
  assert (Hrep_len: Zlength (@ListDef.repeat T InhT d) = Z.of_nat d)
    by (rewrite Zlength_correct, repeat_length; reflexivity).
  rewrite upd_Znth_app2 by (rewrite Hrep_len, Zlength_map, Zlength_ord_enum; pose proof (ltn_ord i); unfold d; lia).
  rewrite Hrep_len.
  replace (j - d) with (Z.of_nat i) by (unfold d; lia).
  pose (i_ord := @Ordinal (m - d) i ltac:(unfold d; lia)).
  assert (E1: inord_inj i_ord = i) by (apply ord_inj; reflexivity).
  assert (E2: inord_add d_ord i_ord = j) by (apply ord_inj; simpl; unfold d; lia).
  assert (Hi_iord: Z.of_nat i = Z.of_nat i_ord) by reflexivity.
  rewrite Hi_iord.
  assert (Hval_local: update_mx M i j v (inord_inj i_ord) (inord_add d_ord i_ord) = v).
  { rewrite E1, E2. apply update_mx_same. }
  assert (Hoff_local: forall k: 'I_(m - d), k <> i_ord ->
            M (inord_inj k) (inord_add d_ord k) =
            update_mx M i j v (inord_inj k) (inord_add d_ord k)).
  { intros k Hk.
    rewrite update_mx_diff; [reflexivity | ].
    destruct (Nat.eq_dec (inord_inj k) i) as [Heq|Hneq].
    - right.
      intro Hc.
      apply Hk. apply ord_inj.
      assert (H1: nat_of_ord (inord_inj k) = nat_of_ord k) by reflexivity.
      assert (H2: nat_of_ord i_ord = nat_of_ord i) by reflexivity.
      rewrite H2, <- H1. exact Heq.
    - left. intro Hc. apply Hneq. rewrite Hc. reflexivity. }
  rewrite (upd_Znth_map_ord_eq (m - d)
             (fun i0 : 'I_(m - d) => M (inord_inj i0) (inord_add d_ord i0))
             (fun i0 : 'I_(m - d) => update_mx M i j v (inord_inj i0) (inord_add d_ord i0))
             i_ord v Hoff_local Hval_local).
  assert (Houter_off: forall k: 'I_(S b), k <> d_ord ->
    (@ListDef.repeat T InhT (nat_of_ord k) ++
     map (fun i0: 'I_(m - k) => M (inord_inj i0) (inord_add k i0)) (ord_enum (m - k)))
    =
    (@ListDef.repeat T InhT (nat_of_ord k) ++
     map (fun i0: 'I_(m - k) => update_mx M i j v (inord_inj i0) (inord_add k i0)) (ord_enum (m - k)))).
  { intros k Hk.
    f_equal.
    apply map_ext_in.
    intros i0 _.
    rewrite update_mx_diff; [reflexivity | ].
    destruct (Nat.eq_dec (inord_inj i0) i) as [Heq|Hneq].
    - right.
      intro Hc.
      apply Hk. apply ord_inj.
      assert (Hc': nat_of_ord (inord_add k i0) = nat_of_ord j) by (rewrite Hc; reflexivity).
      simpl in Hc', Heq.
      simpl.
      unfold d in *.
      lia.
    - left. intro Hc. apply Hneq. rewrite Hc. reflexivity. }
  assert (Hd_iord: Z.of_nat d = Z.of_nat d_ord) by reflexivity.
  rewrite Hd_iord.
  assert (Houter_val:
    (@ListDef.repeat T InhT (nat_of_ord d_ord) ++
     map (fun i0: 'I_(m - d_ord) => update_mx M i j v (inord_inj i0) (inord_add d_ord i0)) (ord_enum (m - d_ord)))
    = (@ListDef.repeat T InhT d ++
     map (fun i0: 'I_(m - d) => update_mx M i j v (inord_inj i0) (inord_add d_ord i0)) (ord_enum (m - d)))).
  { simpl nat_of_ord. reflexivity. }
  rewrite (upd_Znth_map_ord_eq (S b)
             (fun j0: 'I_(S b) => @ListDef.repeat T InhT (nat_of_ord j0) ++
                map (fun i0: 'I_(m - j0) => M (inord_inj i0) (inord_add j0 i0)) (ord_enum (m - j0)))
             (fun j0: 'I_(S b) => @ListDef.repeat T InhT (nat_of_ord j0) ++
                map (fun i0: 'I_(m - j0) => update_mx M i j v (inord_inj i0) (inord_add j0 i0)) (ord_enum (m - j0)))
             d_ord
             (@ListDef.repeat T InhT d ++
              map (fun i0: 'I_(m - d) => update_mx M i j v (inord_inj i0) (inord_add d_ord i0)) (ord_enum (m - d)))
             Houter_off Houter_val).
  reflexivity.
Qed.

Lemma Hsym_of_trmx {T} [m] (M: 'M[T]_(m,m)):
  trmx M = M -> forall a c: 'I_m, M a c = M c a.
Proof.
  intros H2 a c.
  assert (Htmp: trmx M a c = M a c) by (rewrite H2; reflexivity).
  unfold trmx in Htmp. rewrite mxE in Htmp.
  symmetry. exact Htmp.
Qed.

Lemma update_mx_idem {T} [m n] (M: 'M[T]_(m,n)) (i: 'I_m) (j: 'I_n) (v: T):
  update_mx (update_mx M i j v) i j v = update_mx M i j v.
Proof.
  apply matrixP. intros k l.
  unfold update_mx. rewrite !mxE.
  repeat destruct (Nat.eq_dec _ _); auto.
Qed.

Lemma bandmatn_invariant_update {t: type} (m b: nat) (M: 'M[option (ftype t)]_(m,m)) (i j: 'I_m) (v: option (ftype t)):
  trmx M = M ->
  (forall a c: 'I_m, c > a + b -> M a c = Some (Zconst t 0)) ->
  0 <= (Z.of_nat j - Z.of_nat i) <= Z.of_nat b ->
  trmx (update_mx (update_mx M i j v) j i v) = update_mx (update_mx M i j v) j i v /\
  (forall a c: 'I_m, c > a + b -> update_mx (update_mx M i j v) j i v a c = Some (Zconst t 0)).
Proof.
  intros Htrmx Hoffband Hd.
  pose proof (Hsym_of_trmx M Htrmx) as Hsym.
  split.
  - apply matrixP. intros a c.
    unfold trmx, update_mx. rewrite !mxE.
    destruct (Nat.eq_dec a i) as [Hai|Hai]; destruct (Nat.eq_dec a j) as [Haj|Haj];
    destruct (Nat.eq_dec c i) as [Hci|Hci]; destruct (Nat.eq_dec c j) as [Hcj|Hcj];
    simpl; auto; apply Hsym.
  - intros a c Hgt.
    rewrite update_mx_diff.
    + rewrite update_mx_diff.
      * apply Hoffband. exact Hgt.
      * destruct (Nat.eq_dec a i) as [Hai|Hai].
        -- right. intro Hc.
           assert (Hai': a = i) by (apply ord_inj; exact Hai).
           rewrite Hai', Hc in Hgt. lia.
        -- left. intro Hc. apply Hai. rewrite Hc. reflexivity.
    + destruct (Nat.eq_dec a j) as [Haj|Haj].
      * right. intro Hc.
        assert (Haj': a = j) by (apply ord_inj; exact Haj).
        rewrite Haj', Hc in Hgt.
        lia.
      * left. intro Hc. apply Haj. rewrite Hc. reflexivity.
Qed.

Lemma banded_repr_double_upd_Znth {T} {InhT: Inhabitant T} (m b: nat) (M: 'M[T]_(m,m)) (i j: 'I_m) (v: T):
  0 <= (Z.of_nat j - Z.of_nat i) <= Z.of_nat b ->
  (b < m)%nat ->
  upd_Znth (Z.of_nat j + (Z.of_nat j - Z.of_nat i) * Z.of_nat m) (@banded_repr T InhT m b M) v
  = @banded_repr T InhT m b (update_mx (update_mx M i j v) j i v).
Proof.
  intros Hd Hb.
  rewrite (banded_repr_upd_Znth m b M i j v Hd Hb).
  destruct (Nat.eq_dec i j) as [Heq|Hneq].
  - assert (Hij: i = j) by (apply ord_inj; exact Heq).
    rewrite <- Hij.
    f_equal.
    symmetry.
    apply update_mx_idem.
  - assert (Hij_lt: (nat_of_ord i < nat_of_ord j)%nat) by lia.
    symmetry.
    apply (banded_repr_lower_update m b (update_mx M i j v) j i v Hij_lt).
Qed.


(** Reusable tactics for [bandmatn_get]/[bandmatn_set]/[bandmatn_addto]-style proofs.
    All rely on [start_function] having bound the names [m, b, M, i, j] exactly as
    our specs destructure them. *)

Ltac bandmat_strip_reptype m b M :=
  try change (reptype_ftype (m * S b) (map val_of_optfloat (banded_repr b M)))
    with (map val_of_optfloat (banded_repr b M));
  try change (reptype_ftype (m * Z.pos (PosDef.Pos.of_succ_nat b)) (map val_of_optfloat (banded_repr b M)))
    with (map val_of_optfloat (banded_repr b M)).

Ltac bandmat_index_range_tac m b i j :=
  entailer!;
  assert (Hj: 0 <= j < m) by (pose proof (ltn_ord j); lia);
  assert (Hi: 0 <= i < m) by (pose proof (ltn_ord i); lia);
  assert (Hjm: j <= m * S b) by nia;
  assert (Hprod: 0 <= (j - i) * m <= m * S b) by nia;
  rewrite (Int.signed_repr j) by rep_lia;
  rewrite (Int.signed_repr ((j - i) * m)) by rep_lia;
  rewrite (Int.signed_repr (j - i)) by rep_lia;
  rewrite (Int.signed_repr m) by rep_lia;
  split; rep_lia.

Ltac bandmat_read_tac m b M i j Heq :=
  bandmat_strip_reptype m b M;
  assert (Hbound2: 0 <= j + (j - i) * m < Zlength (banded_repr b M))
    by (rewrite Zlength_banded_repr by lia; lia);
  rewrite Znth_map by apply Hbound2;
  rewrite banded_repr_Znth by (auto; assert (H2nat: (b < m)%nat) by lia; apply H2nat);
  rewrite Heq.

Ltac bandmat_write_tac m b M i j v Htrmx Hoffband Hband :=
  rewrite (upd_Znth_map val_of_optfloat (j + (j - i) * m) (banded_repr b M) v);
  assert (H2nat: (b < m)%nat) by lia;
  rewrite (banded_repr_double_upd_Znth m b M i j v Hband H2nat);
  unfold bandmatn;
  entailer!;
  apply (bandmatn_invariant_update m b M i j v Htrmx Hoffband Hband).

(** * Supporting infrastructure for [body_dense_to_band] *)

(** [banded_repr] only ever reads [M] at in-band positions [i <= j], so two
    matrices that agree there produce the same physical representation. *)
Lemma banded_repr_ext {T} {InhT: Inhabitant T} (m b: nat) (P M: 'M[T]_(m,m)):
  (forall (i j: 'I_m), 0 <= (Z.of_nat j - Z.of_nat i) <= Z.of_nat b -> P i j = M i j) ->
  banded_repr b P = banded_repr b M.
Proof.
  intros Hext.
  unfold banded_repr.
  f_equal.
  apply map_ext_in; intros j0 _.
  f_equal.
  apply map_ext_in; intros i0 _.
  apply Hext.
  unfold inord_inj, inord_add; simpl.
  pose proof (ltn_ord j0) as Hj0.
  lia.
Qed.

Lemma bandmatn_ext {t: type} (sh: share) (m b: nat) (P M: 'M[option (ftype t)]_(m,m)) (p: val):
  trmx M = M ->
  (forall i j : 'I_m, j > i + b -> M i j = Some (Zconst t 0)) ->
  banded_repr b P = banded_repr b M ->
  bandmatn sh b P p |-- bandmatn sh b M p.
Proof.
  intros Htrmx Hoffband Heq.
  unfold bandmatn.
  rewrite Heq.
  apply andp_derives; [ | apply derives_refl].
  apply prop_derives.
  intros [Hb1 [Hb2 _]].
  destruct Hb1 as [Hb1a Hb1b].
  repeat split; auto.
Qed.

Lemma bandmat_ext (sh: share) (m b: nat) (P M: 'M[option (ftype the_type)]_(m,m)) (p: val):
  trmx M = M ->
  (forall i j : 'I_m, j > i + b -> M i j = Some (Zconst the_type 0)) ->
  banded_repr b P = banded_repr b M ->
  bandmat sh b P p |-- bandmat sh b M p.
Proof.
  intros Htrmx Hoffband Heq.
  unfold bandmat.
  apply sepcon_derives.
  - apply sepcon_derives.
    + apply derives_refl.
    + apply bandmatn_ext; auto.
  - apply derives_refl.
Qed.

(** Reading either of the two positions written by a symmetric double-update
    gives back the written value. *)
Lemma update_mx_sym_same {T} [m] (M: 'M[T]_(m,m)) (a b: 'I_m) (x: T):
  update_mx (update_mx M a b x) b a x a b = x.
Proof.
  destruct (Nat.eq_dec a b) as [Hab|Hab].
  - assert (Hab': a = b) by (apply ord_inj; auto). subst.
    apply update_mx_same.
  - rewrite update_mx_diff.
    + apply update_mx_same.
    + left. intro Hc. apply Hab. rewrite Hc. reflexivity.
Qed.

(** Reading any OTHER position is unaffected by a symmetric double-update. *)
Lemma update_mx_sym_diff {T} [m] (M: 'M[T]_(m,m)) (a b: 'I_m) (x: T) (r c: 'I_m):
  r <> a \/ c <> b ->
  r <> b \/ c <> a ->
  update_mx (update_mx M a b x) b a x r c = M r c.
Proof.
  intros H1 H2.
  rewrite update_mx_diff by exact H2.
  rewrite update_mx_diff by exact H1.
  reflexivity.
Qed.

(** Convenience wrapper: derive an ordinal-level disjoint-pair fact from a
    nat-level one (nat-level is what [lia] can actually discharge). *)
Lemma ord_neq_pair {m} (r i c j: 'I_m):
  (nat_of_ord r <> nat_of_ord i)%nat \/ (nat_of_ord c <> nat_of_ord j)%nat ->
  r <> i \/ c <> j.
Proof.
  intros [H|H].
  - left. intro He. apply H. rewrite He. reflexivity.
  - right. intro He. apply H. rewrite He. reflexivity.
Qed.

(** [dtb_inv bw d j A P0 P]: loop invariant for [dense_to_band]'s double loop.
    [P0] is the starting (all-[None]-in-band) matrix; [A] is the source dense
    matrix being converted. After the outer loop has fully processed bands
    [0..d-1] and the current band [d]'s columns [d..j-1], [P] agrees with [A]
    on every in-band position already visited, and still agrees with [P0] on
    every in-band position not yet visited. Only positions [(r,c)] with
    [c >= r] (upper triangle) are tracked, since that's all [banded_repr]
    (and hence [bandmatn]) ever reads. *)
Definition dtb_inv {m: nat} (bw d j: nat) (A P0 P: 'M[option (ftype the_type)]_(m,m)) : Prop :=
  (forall (r c : 'I_m),
     (0 <= (Z.of_nat c - Z.of_nat r) <= Z.of_nat bw)%Z ->
     ((Z.of_nat c - Z.of_nat r < Z.of_nat d)%Z \/
      ((Z.of_nat c - Z.of_nat r = Z.of_nat d)%Z /\ (c < j)%nat)) ->
     P r c = A r c)
  /\
  (forall (r c : 'I_m),
     (0 <= (Z.of_nat c - Z.of_nat r) <= Z.of_nat bw)%Z ->
     ((Z.of_nat c - Z.of_nat r > Z.of_nat d)%Z \/
      ((Z.of_nat c - Z.of_nat r = Z.of_nat d)%Z /\ (c >= j)%nat)) ->
     P r c = P0 r c).

Lemma dtb_inv_base {m: nat} (bw: nat) (A P0: 'M[option (ftype the_type)]_(m,m)):
  @dtb_inv m bw 0 0 A P0 P0.
Proof.
  split.
  - intros r c Hrange [Hlt | [Heq Hlt]]; lia.
  - intros r c Hrange Hcond. reflexivity.
Qed.

(** Advancing the inner loop by one: writing the single symmetric pair
    [(i_ord,j_ord)] with [j_ord - i_ord = d] extends [dtb_inv] from column
    [j] to column [S j] within the same band [d]. *)
Lemma dtb_inv_step_j {m: nat} (bw d j: nat) (A P0 P: 'M[option (ftype the_type)]_(m,m))
      (i_ord j_ord: 'I_m) (x: ftype the_type):
  dtb_inv bw d j A P0 P ->
  nat_of_ord i_ord = (j - d)%nat ->
  nat_of_ord j_ord = j ->
  (d <= j)%nat -> (j < m)%nat ->
  A i_ord j_ord = Some x ->
  dtb_inv bw d (S j) A P0 (update_mx (update_mx P i_ord j_ord (Some x)) j_ord i_ord (Some x)).
Proof.
  intros [Hdone Hpend] Hi Hj Hdj Hjm HAx.
  split.
  - intros r c Hrange [Hlt | [Heq Hlt]].
    + assert (H1: r <> i_ord \/ c <> j_ord).
      { apply ord_neq_pair.
        destruct (Nat.eq_dec (nat_of_ord r) (nat_of_ord i_ord)) as [Hreq|Hrneq].
        - right. intro Hceq.
          rewrite Hi in Hreq. rewrite Hj in Hceq.
          rewrite Hreq, Hceq in Hlt. lia.
        - left. exact Hrneq. }
      assert (H2: r <> j_ord \/ c <> i_ord).
      { apply ord_neq_pair.
        destruct (Nat.eq_dec (nat_of_ord r) (nat_of_ord j_ord)) as [Hreq|Hrneq].
        - right. intro Hceq.
          rewrite Hj in Hreq. rewrite Hi in Hceq.
          rewrite Hreq, Hceq in Hlt. lia.
        - left. exact Hrneq. }
      rewrite (update_mx_sym_diff P i_ord j_ord (Some x) r c H1 H2).
      apply Hdone; [exact Hrange | left; exact Hlt].
    + destruct (Nat.eq_dec (nat_of_ord c) j) as [Hcj | Hcj].
      * assert (Hreq: r = i_ord) by (apply ord_inj; rewrite Hi; lia).
        assert (Hceq: c = j_ord) by (apply ord_inj; rewrite Hj; exact Hcj).
        subst r c.
        rewrite update_mx_sym_same.
        symmetry. exact HAx.
      * assert (Hclt: (nat_of_ord c < j)%nat) by lia.
        assert (H1: r <> i_ord \/ c <> j_ord).
        { apply ord_neq_pair. right. rewrite Hj. exact Hcj. }
        assert (H2: r <> j_ord \/ c <> i_ord).
        { apply ord_neq_pair.
          destruct (Nat.eq_dec (nat_of_ord r) (nat_of_ord j_ord)) as [Hreq|Hrneq].
          - right. intro Hceq0.
            rewrite Hj in Hreq. rewrite Hi in Hceq0.
            rewrite Hreq, Hceq0 in Heq. lia.
          - left. exact Hrneq. }
        rewrite (update_mx_sym_diff P i_ord j_ord (Some x) r c H1 H2).
        apply Hdone; [exact Hrange | right; split; [exact Heq | exact Hclt] ].
  - intros r c Hrange [Hgt | [Heq Hge]].
    + assert (H1: r <> i_ord \/ c <> j_ord).
      { apply ord_neq_pair.
        destruct (Nat.eq_dec (nat_of_ord r) (nat_of_ord i_ord)) as [Hreq|Hrneq].
        - right. rewrite Hj. rewrite Hi in Hreq. lia.
        - left. exact Hrneq. }
      assert (H2: r <> j_ord \/ c <> i_ord).
      { apply ord_neq_pair.
        destruct (Nat.eq_dec (nat_of_ord r) (nat_of_ord j_ord)) as [Hreq|Hrneq].
        - right. rewrite Hi. rewrite Hj in Hreq. lia.
        - left. exact Hrneq. }
      rewrite (update_mx_sym_diff P i_ord j_ord (Some x) r c H1 H2).
      apply Hpend; [exact Hrange | left; exact Hgt].
    + assert (H1: r <> i_ord \/ c <> j_ord).
      { apply ord_neq_pair. right. rewrite Hj. lia. }
      assert (H2: r <> j_ord \/ c <> i_ord).
      { apply ord_neq_pair.
        destruct (Nat.eq_dec (nat_of_ord r) (nat_of_ord j_ord)) as [Hreq|Hrneq].
        - right. rewrite Hi. rewrite Hj in Hreq. lia.
        - left. exact Hrneq. }
      rewrite (update_mx_sym_diff P i_ord j_ord (Some x) r c H1 H2).
      apply Hpend; [exact Hrange | right; split; [exact Heq | lia] ].
Qed.

(** Advancing the outer loop by one: once the inner loop has fully finished
    band [d] (reached column [m]), the very same [P] also satisfies the
    invariant for band [S d] at its starting column [S d] (nothing has been
    written yet in that band; every position in it is still [c < S d]-vacuous
    on one side and [P0] on the other). No write happens here, just
    reindexing, relying on [c < m] always holding for [c : 'I_m]. *)
Lemma dtb_inv_step_d {m: nat} (bw d: nat) (A P0 P: 'M[option (ftype the_type)]_(m,m)):
  dtb_inv bw d m A P0 P ->
  dtb_inv bw (S d) (S d) A P0 P.
Proof.
  intros [Hdone Hpend].
  split.
  - intros r c Hrange Hcond.
    apply Hdone; [exact Hrange | ].
    pose proof (ltn_ord c) as Hcm.
    destruct Hcond as [Hlt | [Heq Hlt]]; [ | exfalso; lia].
    destruct (Z.eq_dec (Z.of_nat c - Z.of_nat r) (Z.of_nat d)) as [Heqd|Hneqd].
    + right. split; [exact Heqd | lia].
    + left. lia.
  - intros r c Hrange Hcond.
    apply Hpend; [exact Hrange | left].
    destruct Hcond as [Hgt | [Heq Hge]]; lia.
Qed.

(** Closing lemma: once band [bw] (the last one) has been fully processed
    (inner loop reached column [m]), every in-band position agrees with [A]. *)
Lemma dtb_inv_final {m: nat} (bw: nat) (A P0 P: 'M[option (ftype the_type)]_(m,m)):
  dtb_inv bw bw m A P0 P ->
  forall (r c: 'I_m), 0 <= (Z.of_nat c - Z.of_nat r) <= Z.of_nat bw -> P r c = A r c.
Proof.
  intros [Hdone Hpend] r c Hrange.
  apply Hdone; [exact Hrange | ].
  pose proof (ltn_ord c) as Hcm.
  destruct (Z.eq_dec (Z.of_nat c - Z.of_nat r) (Z.of_nat bw)) as [Heqd|Hneqd].
  - right. split; [exact Heqd | lia].
  - left. lia.
Qed.