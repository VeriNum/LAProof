Require Import VST.floyd.functional_base.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Import ListNotations.



Inductive sorted {A} (le: relation A): list A -> Prop := 
| sorted_nil:
    sorted le nil
| sorted_1: forall x,
    sorted le (x::nil)
| sorted_cons: forall x y l,
     le x y -> sorted le (y::l) -> sorted le (x::y::l).

Lemma sorted_e: forall {A} `{d: Inhabitant A} {le: A -> A -> Prop}
       {TR: Transitive le}
        (al: list A), 
      sorted le al -> forall i j, 0 <= i < j -> j < Zlength al -> 
               (le (Znth i al) (Znth j al)).
Proof.
 induction 2; intros.
 list_solve. list_solve.
 destruct (zeq i 0).
 - subst i. autorewrite with sublist. rewrite Znth_pos_cons by lia.
   destruct (zeq (j-1) 0). rewrite e, Znth_0_cons; auto.
   transitivity y; auto.
   specialize (IHsorted 0 (j-1) ltac:(lia) ltac:(list_solve)).
   autorewrite with sublist in IHsorted; auto.
 - rewrite Znth_pos_cons by lia. rewrite (Znth_pos_cons j) by lia.
   apply IHsorted; list_solve.
Qed.

Lemma sorted_i: forall {A} `{d: Inhabitant A} (le: A -> A -> Prop) {TR: Transitive le}
         (al: list A),
         (forall i j, 0 <= i < j -> j < Zlength al -> le (Znth i al) (Znth j al)) ->
         sorted le al.
Proof.
induction al; intros.
constructor.
destruct al. constructor.
constructor.
apply (H 0 1); list_solve.
apply IHal.
intros.
specialize (H (i+1) (j+1) ltac:(lia)).
rewrite !(Znth_pos_cons (_+_)), !Z.add_simpl_r in H by list_solve.
apply H. list_solve.
Qed.

Lemma le1_sorted: forall {A} {le: A -> A -> Prop}
       {TR: Transitive le}
        (a b: A) (al: list A), 
      (le a b) -> sorted le (b::al) -> sorted le (a::al).
Proof.
intros.
revert a b H H0; induction al; simpl; intros.
constructor.
inv H0.
constructor; auto.
transitivity b; auto.
Qed.

Lemma sorted_app:
  forall {A} {le: A->A->Prop} {TRANS: Transitive le}
    pivot al bl,
    sorted le al -> sorted le bl ->
    Forall (fun x => le x pivot) al ->
    Forall (le pivot) bl ->
    sorted le (al++bl).
Proof.
intros.
induction H.
simpl; auto.
simpl.
inv H1. inv H5.
inv H0.
constructor.
inv H2.
constructor.
apply TRANS with pivot; auto.
constructor.
inv H2.
constructor.
apply TRANS with pivot; auto.
constructor; auto.
simpl.
constructor; auto.
apply IHsorted.
inv H1; auto.
Qed.

Lemma sorted_app_e3:
  forall {A} {le: relation A} {TRANS: Transitive le}
    pivot al bl,
    sorted le (al++[pivot]++bl) ->
    sorted le al /\ sorted le bl /\ 
    Forall (fun x => le x pivot) al /\
    Forall (le pivot) bl.
Proof.
 intros.
 induction al.
 simpl in *.
 split. constructor.
 induction bl; inv  H. repeat constructor.
 spec IHbl. destruct bl; inv H4; constructor; auto. 
 eapply TRANS; eassumption.
 split3; auto. destruct IHbl as [? [? ?]]; constructor; auto.
 inv H. destruct al; inv H2. destruct al; inv H1.
 simpl in IHal. spec IHal; auto.
 destruct IHal as [_ [? [_ ?]]].
 split3. constructor. auto. split; auto.
 spec IHal; auto.
 destruct IHal as [? [? [? ?]]].
 split3; auto. constructor; auto.
 split; auto.
 constructor; auto.
 apply TRANS with a0; auto.
 inv H1; auto.
Qed.


Lemma sorted_e1: forall {t} {Inh: Inhabitant t} {le: relation t} (al: list t), sorted le al ->
   forall i,
   0 <= i < Zlength al-1 -> le (Znth i al) (Znth (i+1) al).
Proof.
  induction 1; intros.
  - list_solve.
  - list_solve.
  - destruct (zeq i 0).
   + subst. autorewrite with sublist in *. apply H.
   + rewrite Znth_pos_cons by lia. rewrite (Znth_pos_cons (i+1)) by lia.
     replace (i+1-1) with (i-1+1) by lia.
     apply IHsorted. list_solve.
Qed.


Lemma sorted_sublist: 
  forall (i j: Z) {A} {InhA: Inhabitant A} le (al: list A), 
   0 <= i <= j -> j <= Zlength al -> sorted le al -> sorted le (sublist i j al).
Proof.
 intros.
 revert i j H H0; induction H1; intros.
 rewrite sublist_nil' by list_solve. constructor.
 destruct (zeq i j). autorewrite with sublist. constructor.
 rewrite sublist_one by list_solve. constructor.
 destruct (zeq i 0). subst. 
 destruct (zeq j 0). autorewrite with sublist. constructor.
 rewrite (sublist_split 0 1) by lia. rewrite sublist_one by lia.
 rewrite Znth_0_cons. simpl. rewrite sublist_1_cons by lia.
 destruct (zeq j 1); autorewrite with sublist. constructor.
 rewrite sublist_0_cons by lia.
 constructor; auto.
 replace (y::sublist 0 (j-1-1) l) with (sublist 0 (j-1) (y::l)) by list_solve.
 apply IHsorted; try list_solve.
 rewrite sublist_S_cons by lia.
 apply IHsorted; try list_solve.
Qed.



Class BoolOrder {A: Type} (R: relation A): Type := {
    test : A -> A -> bool;
    test_spec: forall x y, reflect (R x y) (test x y)
}.

Arguments test {A} R {BoolOrder}.

Module BPO.

Local Lemma mkteststrictspec {A} {R: relation A} {B: BoolOrder R}{P: PreOrder R}:
  let strict x y := R x y /\ ~R y x in
  let teststrict x y := andb (test R x y) (negb (test R y x)) in
   forall x y : A, reflect (strict x y) (teststrict x y).
Proof.
intros.
unfold strict, teststrict.
destruct (test_spec x y), (test_spec y x); simpl.
- apply ReflectF. intros [? ?]; contradiction.
- apply ReflectT. split; auto.
- apply ReflectF. intros [? ?]; contradiction.
- apply ReflectF. intros [? ?]; contradiction.
Qed.

Local Lemma StrictOrderstrict {A}{R: relation A}{P: PreOrder R}:
 let strict x y := R x y /\ ~ R y x in
   StrictOrder strict.
Proof.
constructor.
intro x; red; tauto.
intros x y z [??] [??]; split.
   transitivity y; auto.
   contradict H2. transitivity x; auto.
Qed.

Local Lemma mktesteqvspec {A} {R: relation A}{BO: BoolOrder R}: 
  let eqv x y := R x y /\ R y x in
  let testeqv x y := andb (test R x y) (test R y x) in
  forall x y : A, reflect (eqv x y) (testeqv x y).
Proof.
intros.
subst eqv testeqv; simpl.
destruct (test_spec x y), (test_spec y x); simpl; constructor; tauto.
Qed.

Local Lemma mkEqv {A}{R: relation A}{PO: PreOrder R}:
  let eqv x y := R x y /\ R y x in
  Equivalence eqv.
Proof.
intros. subst eqv. constructor; hnf; intros.
- split; reflexivity.
- tauto.
- split; transitivity y; tauto.
Qed.

Class BoolPreOrder {A: Type} (R: relation A) : Type := {
    #[export] BO :: BoolOrder R (* | 2 *)  ;
    #[export] PO :: PreOrder R (* | 2 *);
    lt : relation A := fun x y => R x y /\ ~R y x;
    ltb: A -> A -> bool := fun x y => andb (test R x y) (negb (test R y x));
    ltb_spec: forall x y, reflect (lt x y) (ltb x y) := 
              mkteststrictspec;
    #[export] Strict :: StrictOrder lt := StrictOrderstrict;
    eqv: relation A := fun x y => R x y /\ R y x;
    eqvb: A -> A -> bool := fun x y => andb (test R x y) (test R y x);
    eqvbspec: forall x y, reflect (eqv x y) (eqvb x y) :=
              mktesteqvspec;
    Eqv :: Equivalence eqv := mkEqv
 }.

Arguments lt [A] [R] {_}.
Arguments ltb [A] [R] {_}.
Arguments eqv [A] [R] {_}.
Arguments eqvb [A] [R] {_}.

End BPO.
Import BPO.

(*
#[export] Instance or_eq_trans {A} {R: relation A} {TR: Transitive R} : Transitive (or_eq R).
Proof.
intros x y z ? ?.
destruct H; subst; auto.
destruct H0; subst; auto.
right; auto.
right; eapply TR; eauto.
Qed.
*)
Section SBO.

Context {A: Type} {le: relation A} {SBO: BoolPreOrder le}.
Context {InhA: Inhabitant A}.

Definition count_distinct_aux u v :=
   let '(k,x) := u in (if ltb x v then k+1 else k, v).

Definition count_distinct (al: list A) : Z :=
 match al with
 | nil => 0 
 | a::rest => fst (fold_left count_distinct_aux rest (1,a))
 end.


Lemma count_distinct_bound: forall el: list A, 
  0 <= count_distinct el <= Zlength el.
Proof.
intros.
unfold count_distinct.
destruct el as [| p el]; simpl. list_solve.
rewrite Zlength_cons.
unfold Z.succ.
set (u := 1). 
assert (0<=u) by lia.  clearbody u.
revert p u H; induction el; simpl; intros. list_solve.
destruct (ltb p a); simpl.
specialize (IHel a (u+1)); list_solve.
specialize (IHel a u); list_solve.
Qed.

Lemma count_distinct_bound': forall el, 
  0 < Zlength el ->
  0 < @count_distinct el.
Proof.
intros.
destruct el as [|p el]. list_solve.
clear. unfold count_distinct.
set (u := 1). assert (0<u) by lia. clearbody u.
revert u H p ; induction el; simpl; intros; auto.
destruct (ltb p a); simpl.
apply IHel; lia.
apply IHel; auto.
Qed.

Lemma count_distinct_mono: 
  forall (bl: list A) i,
      count_distinct (sublist 0 i bl) <= count_distinct bl.
Proof.
 intros.
 destruct bl as [|rc bl].
 unfold sublist. simpl. rewrite firstn_nil. simpl. lia.
 unfold count_distinct.
 assert (forall al u p, u <= fst (fold_left count_distinct_aux al (u, p))). {
         clear.
         induction al as [|rca al]; simpl. lia.
         intros u rc.
         destruct (BPO.ltb _ _); simpl; auto. specialize (IHal (u+1) rca); lia.
 } 
 destruct (zlt i 1). 
 replace (sublist 0 i (rc::bl)) with (@nil A).
 transitivity 1; auto. lia.
 unfold sublist; simpl. replace (Z.to_nat i) with O by lia; reflexivity.
 unfold sublist. simpl.
 replace (Z.to_nat i) with (S (Z.to_nat (i-1))) by lia.
 forget (Z.to_nat (i-1)) as i'; clear i g. rename i' into i.
 simpl.
 forget 1 as u.
 revert rc u i; induction bl; intros. destruct i; simpl; auto; lia.
 destruct i; simpl;
 destruct (BPO.ltb _ _); simpl; auto.
 transitivity (u+1); auto; lia.
Qed.

Lemma count_distinct_incr:
  forall (bl: list A) i,
      lt (Znth (i-1) bl) (Znth i bl) ->
      0 < i < Zlength bl ->
      count_distinct (sublist 0 i bl) + 1 = count_distinct (sublist 0 (i+1) bl).
Proof.
intros.
        unfold count_distinct.
        destruct bl as [| rc']. list_solve.
        rewrite sublist_0_cons by lia.
        rewrite (Znth_pos_cons i) in H by rep_lia.
        rewrite Zlength_cons in H0.
        rewrite (sublist_split 0 1 (i+1)) by list_solve.
        rewrite (sublist_one 0 1) by list_solve. autorewrite with sublist.
        simpl. rewrite sublist_1_cons by lia. replace (i+1-1) with (i-1+1) by lia.
        assert (H0': 0 <= i-1 < Zlength bl) by lia; clear H0; rename H0' into H0.
        forget (i-1) as i'; clear i; rename i' into i.
        set (u:=1) at 1 4; clearbody u.
        revert i rc' u H H0; induction bl as [|rc1 bl]; simpl; intros.
        list_solve.
        assert (forall al u p, u <= fst (fold_left count_distinct_aux al (u, p))). {
              clear.
              induction al as [|rca al]; simpl; intros u rc. lia.
              destruct (ltb _ _); simpl; auto. specialize (IHal (u+1) rca); lia.
           } 
        destruct (zeq i 0).
        -- subst. rewrite sublist_nil. simpl.
           rewrite !Znth_0_cons in H.
           destruct (ltb_spec rc' rc1); simpl; auto. contradiction.
        -- rewrite !sublist_0_cons by lia. simpl.
           replace (i+1-1) with (i-1+1) by lia.
           rewrite !(Znth_pos_cons i) in H by lia.
           destruct (ltb rc' rc1); apply IHbl; try list_solve.
Qed.

Lemma count_distinct_incr':
  forall (bl: list A) i,
      lt (Znth (i - 1) bl) (Znth i bl) ->
      0 <= i - 1 < Zlength bl - 1 ->
      count_distinct (sublist 0 i bl) < count_distinct bl.
Proof.
intros.
  pose proof count_distinct_incr bl i H ltac:(lia).
  pose proof count_distinct_mono bl (i+1).
  lia.
Qed.

Lemma count_distinct_noincr:
  forall (al: list A) i,
         0 < i < Zlength al -> 
         ~lt (Znth (i-1) al) (Znth i al) ->
         count_distinct (sublist 0 i al) = count_distinct (sublist 0 (i+1) al).
Proof.
intros * H Hi.
        rewrite (sublist_split 0 i (i+1)) by rep_lia.
        rewrite (sublist_one i (i+1)) by rep_lia.
        replace (Znth (i-1) al) with (Znth (i-1) (sublist 0 i al)) in Hi by list_solve.
        forget (Znth i al) as b.
        assert (i = Zlength (sublist 0 i al)) by list_solve.
        forget (sublist 0 i al) as bl. destruct H. clear - Hi H0 H. subst i.
        destruct bl. list_solve.
        clear H. autorewrite with sublist in *. replace (_ - _) with (Zlength bl) in Hi by lia.
        unfold count_distinct.
        forget 1 as u.
        revert u a Hi; induction bl; simpl; intros.
        autorewrite with sublist in Hi.
        destruct (ltb_spec a b); auto. contradiction.
        autorewrite with sublist in *. rewrite Znth_pos_cons in Hi by rep_lia.
        replace (_ - _) with (Zlength bl) in Hi by lia.
        simpl in IHbl.
        destruct (ltb a0 a) eqn:?H;
        apply IHbl; auto.
Qed.

Lemma count_distinct_aux_mono:
 forall al y u,
   fst (fold_left count_distinct_aux al (u, y)) >= u.
Proof.
induction al; simpl; intros. lia.
destruct (ltb y a). specialize (IHal a (u+1)); lia.
auto.
Qed.

Lemma eqv_cda: forall a x u al, 
  eqv x a ->
  fst (fold_left count_distinct_aux al (u, x)) = 
  fst (fold_left count_distinct_aux al (u, a)).
Proof.
intros.
destruct al; simpl; auto.
destruct (ltb_spec x a0), (ltb_spec a a0); auto; exfalso;
unfold eqv, lt in *;
destruct H,l; apply n; clear n; split.
  etransitivity; eassumption.
  contradict H2. etransitivity; eassumption.
  etransitivity; eassumption.
  contradict H2. etransitivity; eassumption.
Qed.

Lemma count_distinct_aux_lemma:
 forall al y (SOR: sorted le (y::al)) u,
   fst (fold_left count_distinct_aux al (u, y)) <= u ->
   Forall (Basics.compose not (lt y)) al.
Proof.
induction al; intros.
constructor.
inv SOR.
simpl in H.
destruct (ltb_spec y a).
- pose proof (count_distinct_aux_mono al a (u+1)); lia.
- constructor. apply n.
  assert (le a y) 
     by (unfold lt in n; destruct (test_spec a y); tauto).
  eapply IHal with u; auto.
 + apply le1_sorted with a; auto.
 + rewrite (eqv_cda a); auto. split; auto. 
Qed.

Lemma count_distinct_1:
 forall al
   (SOR: sorted le al),
   count_distinct al = 1 -> 
   forall x y, In x al -> In y al -> eqv x y.
Proof.
intros.
unfold count_distinct in H.
destruct al. discriminate.
destruct H0,H1; subst.
- reflexivity.
- revert x y SOR H1 H; induction al; simpl; intros. contradiction.
  destruct H1. subst. destruct (ltb_spec x y); auto. 
  pose proof (count_distinct_aux_mono al y 2); lia.
  inv SOR.
  unfold lt in n.
  split; tauto. 
  destruct (ltb_spec x a).  
  pose proof (count_distinct_aux_mono al a 2); lia.
  inv SOR.
  eapply IHal; eauto.
  apply le1_sorted with a; auto.
  rewrite (eqv_cda a); auto.
  unfold lt in n. split; auto. tauto.
- revert x y SOR H H0; induction al; simpl; intros. contradiction.
  destruct H0.
 + subst.
  destruct (ltb_spec y x).
  pose proof (count_distinct_aux_mono al x 2); lia.
  inv SOR. unfold lt in n; split; tauto.
 + destruct (ltb_spec y a).
  pose proof (count_distinct_aux_mono al a 2); lia.
  inv SOR.
  eapply IHal in H; try eassumption. rewrite H. unfold lt in n; split; tauto.
- revert a SOR H x y H0 H1. 
  induction al; simpl; intros.
  contradiction.
  inv SOR. destruct (ltb a0 a).
  pose proof (count_distinct_aux_mono al a 2); lia.
  clear a0 H4.
  specialize (IHal _ H6 H).
  destruct H0,H1; subst; auto.
  + reflexivity.
  + revert x H6 H y H1; induction al; simpl; intros. contradiction.
    destruct H1.
    * subst. inv H6. split; auto.
      destruct (ltb_spec x y); try contradiction.
      pose proof (count_distinct_aux_mono al y 2); lia.
      unfold lt in n; tauto.
    * inv H6.
      destruct (ltb_spec x a).
      pose proof (count_distinct_aux_mono al a 2); lia.
      assert (eqv x a) by (unfold lt in n; split; tauto). rewrite H1.
      apply IHal; hnf; auto.
  + rename x into x'. rename y into x. rename x' into y.
    rename H0 into H1.
    clear IHal.
    revert x H6 H y H1; induction al; simpl; intros. contradiction.
    destruct H1.
    * subst. inv H6. split; auto.
      destruct (ltb_spec x y); try contradiction.
      pose proof (count_distinct_aux_mono al y 2); lia.
      unfold lt in n; tauto.
    * inv H6.
      destruct (ltb_spec x a).
      pose proof (count_distinct_aux_mono al a 2); lia.
      assert (eqv x a) by (unfold lt in n; split; tauto). rewrite H1.
      apply IHal; hnf; auto.
Qed.

Lemma count_distinct_range_same:
 forall al g h,
        sorted le al -> 0 <= g < h-1 -> h <= Zlength al ->
        BPO.eqv (Znth g al) (Znth (h-1) al) <->
        count_distinct (sublist 0 (g+1) al) = count_distinct (sublist 0 h al).
Proof.
intros.
unfold count_distinct.
destruct al. list_solve.
rewrite !sublist_0_cons by list_solve.
rewrite Z.add_simpl_r.
pose (u:=1). change (1,a) with (u,a). clearbody u.
assert (h-1 <= Zlength al) by list_solve. clear H1.
set (h' := h-1) in *. clearbody h'. clear h. rename h' into h.
replace (sublist 0 g al) with (sublist 0 g (sublist 0 h al)) by list_solve.
assert (sorted le (a::sublist 0 h al)). {
  replace (a:: sublist 0 h al) with (sublist 0 (h+1) (a::al)) by list_solve.
  apply sorted_sublist; list_solve.
}
clear H.
replace (Znth h (a::al)) with (Znth h (a::sublist 0 h al)) by list_solve.
replace (Znth g (a::al)) with (Znth g (a::sublist 0 h al)) by list_solve.
assert (h = Zlength (sublist 0 h al)) by list_solve.
forget (sublist 0 h al) as bl. subst h.
clear al H2.
revert a u g H0 H1; induction bl; intros.
list_solve.
rename a into b; rename a0 into a.
specialize (IHbl b).
inv H1.
autorewrite with sublist.
rewrite (Znth_pos_cons (Z.succ _)) by list_solve.
unfold Z.succ; rewrite Z.add_simpl_r.
destruct (zeq g 0).
-
 subst. autorewrite with sublist.
 simpl.
 destruct (ltb_spec a b).
 + split; intro; exfalso; [ | pose proof (count_distinct_aux_mono bl b (u+1)); lia].
  destruct (zeq (Zlength bl) 0).
  * destruct bl; [ | list_solve]. simpl in *. autorewrite with sublist in H.
    clear - H3 l H SBO. destruct l,H. tauto.
  * 
   assert (le (Znth 0 (b::bl)) (Znth (Zlength bl) (b::bl)))
    by (apply sorted_e; auto; list_solve).
   autorewrite with sublist in H1.
   forget (Znth (Zlength bl) (b::bl)) as c.
   clear - l H H1.
   destruct H,l. assert (le b a) by (transitivity c; auto). tauto.
 + assert (eqv a b). unfold lt in n. unfold eqv. tauto. clear H3 n.
   rewrite H. clear a H.
   destruct (zeq 0 (Zlength bl)). destruct bl; [ | list_solve]; subst. simpl.
   autorewrite with sublist. split; intro; auto.  reflexivity.
   specialize (IHbl u 0 ltac:(list_solve) H5).
   autorewrite with sublist in IHbl. rewrite IHbl. 
   simpl. split; auto.
- rewrite sublist_0_cons by lia.
  simpl.
  rewrite (Znth_pos_cons) by list_solve.
  destruct (ltb_spec a b).
  * rewrite <- (IHbl (u+1) (g-1) ltac:(list_solve) H5); tauto.
  * rewrite <- (IHbl u (g-1) ltac:(list_solve) H5); tauto.
Qed.

End SBO.



