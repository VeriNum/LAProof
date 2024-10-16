Require Import VST.floyd.proofauto.
Require Import vcfloat.FPStdLib.
Require Import vcfloat.FPStdCompCert.
Require Import VSTlib.spec_math.
Require Import LAProof.C.floatlib.
Require Import LAProof.C.cholesky.
Import FPCore FPCompCert.


#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition Gprog: funspecs := [sqrt_spec].

Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

Section WithSTD.
Context {NAN: Nans} {t : type} {STD: is_standard t}.

Definition neg_zero := ftype_of_float (Binary.B754_zero (fprec t) (femax t) true).

Definition sumF := fold_right BPLUS neg_zero.

Fixpoint iota (i j : nat) :=
match j with O => nil | S j' => i :: iota (S i) j' end.

Definition subtract_loop A R (i j k: Z) :=
  fold_left BMINUS
    (map (fun k' => BMULT (R k' i) (R k' j)) (map Z.of_nat (iota 0 (Z.to_nat k))))
     (A i j).

Definition sum_upto (n: Z) (f: Z -> ftype t) :=
  sumF (map (fun k => f (Z.of_nat k)) (iota 0 (Z.to_nat n))).     

Definition cholesky_jik_ij (n: Z) (A R: Z -> Z -> ftype t) (i j: Z) : Prop :=
   (0 <= j < n) ->
     (0 <= i < j -> R i j = BDIV (subtract_loop A R i j j) (R i i))
   /\ (i=j -> R i j = BSQRT _ _ (subtract_loop A R i j j)).


Definition cholesky_jik_spec (n: Z) (A R: Z -> Z -> ftype t) : Prop :=
  forall i j, cholesky_jik_ij n A R i j.

Definition cholesky_jik_upto (n imax jmax : Z) (A R : Z -> Z -> ftype t) : Prop :=
  forall i j, 
    (j<jmax -> forall i, cholesky_jik_ij n A R i j)
   /\ (j=jmax -> i<imax -> cholesky_jik_ij n A R i j).

Definition done_to_ij (n i j: Z) (R: Z -> Z -> ftype Tdouble) (i' j': Z) : val :=
  if zlt i' 0 then Vundef
  else if zlt j' 0 then Vundef
  else if zlt j' i' then Vundef
  else if zlt (j'+1) j
         then Vfloat (float_of_ftype (R i' j')) 
  else if zeq (j'+1) j
       then if zlt i' i
           then Vfloat (float_of_ftype (R i' j')) 
           else Vundef
  else Vundef.

Definition done_to_n (n: Z) := done_to_ij n n n.

End WithSTD.

Definition N : Z := proj1_sig (opaque_constant 1000).
Definition N_eq : N=1000 := proj2_sig (opaque_constant _).
Hint Rewrite N_eq : rep_lia.

Definition matrix := tarray (tarray tdouble N) N.

Definition list_of_fun (n: Z) (f: Z -> val) : list val :=
 map (fun j => f (Z.of_nat j)) (iota 0 (Z.to_nat n)).

Definition lists_of_fun (n: Z) (f: Z -> Z -> val) :=
 map (fun i => list_of_fun n (f (Z.of_nat i))) (iota 0 (Z.to_nat n)).

Definition cholesky_spec {NAN: Nans}:=
 DECLARE _cholesky
 WITH rsh: share, sh: share, n: Z, A: (Z -> Z -> ftype Tdouble), a: val, r: val
 PRE [ tuint , tptr (tarray tdouble N), tptr (tarray tdouble N) ]
    PROP (readable_share rsh; writable_share sh; 0 <= n <= N)
    PARAMS ( Vint (Int.repr n); a; r)
    SEP (data_at rsh matrix (lists_of_fun N (done_to_n n A)) a;
         data_at_ sh matrix r)
 POST [ tvoid ]
   EX R: Z -> Z -> ftype Tdouble,
    PROP (cholesky_jik_spec n A R)
    RETURN ()
    SEP (data_at rsh matrix (lists_of_fun N (done_to_n n A)) a;
         data_at sh matrix (lists_of_fun N (done_to_n n R)) r).


Lemma Znth_i_iota:
  forall lo i hi, 
   0 <= i < Z.of_nat hi -> Znth i (iota lo hi) = (lo+Z.to_nat i)%nat.
Proof.
 intros.
 rewrite <- (Z2Nat.id i) in * by lia.
 rewrite <- nth_Znth'.
 rewrite Nat2Z.id by lia.
 revert lo hi H; induction (Z.to_nat i); destruct hi; simpl; intros; try lia.
 rewrite IHn by lia. lia.
Qed.


Lemma Znth_i_list_of_fun:
  forall d f i n, 0 <= i < n -> @Znth _ d i (list_of_fun n f) = f i.
Proof.
 intros.
 unfold list_of_fun.
 rewrite Znth_map by rep_lia.
 rewrite Znth_i_iota by rep_lia. f_equal; lia.
Qed.

Lemma Zlength_iota:
  forall lo n, Zlength (iota lo n) = Z.of_nat n.
Proof.
intros. revert lo; induction n; simpl; intros; auto.
rewrite Zlength_cons, IHn. lia.
Qed.
 


Lemma Znth_lists_done: forall N n A d d' i j imax jmax,
   n <= N ->
   imax <= n -> jmax <= n ->
   0 <= i ->
   0 <= j < jmax ->
   i <= j ->
   (j+1=jmax -> i<imax) ->
   @Znth _ d j (@Znth _ d' i (lists_of_fun N (done_to_ij n imax jmax A))) = 
   Vfloat (A i j).
Proof.
intros.
unfold lists_of_fun, done_to_ij.
rewrite Znth_map by (rewrite Zlength_iota; lia).
rewrite Znth_i_list_of_fun by rep_lia.
rewrite Znth_i_iota by lia.
rewrite !if_false by rep_lia.
if_tac. simpl; f_equal. f_equal. lia.
if_tac; try lia.
rewrite if_true by lia.
simpl; f_equal. f_equal. lia.
Qed.

Lemma iota_plus1:
  forall lo n, iota lo (n + 1)%nat = iota lo n ++ [(lo+n)%nat].
Proof.
intros.
revert lo; induction n; simpl; intros; auto.
f_equal; lia.
f_equal.
rewrite IHn.
f_equal.
f_equal.
lia.
Qed.

Definition updij {T} (R: Z -> Z -> T) i j x :=
  fun i' j' => if zeq i i' then if zeq j j' then x else R i' j' else R i' j'.


Lemma upd_Znth_lists_of_fun:
  forall d N n R i j x,
   0 <= i <= j -> j < N ->
  
   upd_Znth i (lists_of_fun N (done_to_ij n i (j + 1) R))
     (upd_Znth j (@Znth _ d i (lists_of_fun N (done_to_ij n i (j + 1) R)))
        (Vfloat x))
    = lists_of_fun N (done_to_ij n (i+1) (j+1) (updij R i j x)).
Proof.
intros.
unfold lists_of_fun.
set (f i0 := list_of_fun _ _).
rewrite Znth_map by (rewrite Zlength_iota; lia).
rewrite Znth_i_iota by lia.
simpl.
Admitted.

Lemma update_i_lt_j:
  forall {t: type} {STD: is_standard t} n i j (A R: Z -> Z -> ftype t),
   0 <= i < j -> j < n ->
   cholesky_jik_upto n i j A R ->
   let rij := BDIV (subtract_loop A R i j i) (R i i) in
    cholesky_jik_upto n (i + 1) j A (updij R i j rij).
Admitted.

Lemma subtract_another:
  forall
   {t: type} {STD: is_standard t} i j k (A R: Z -> Z -> ftype t),
    0 <= i <= j -> 0 <= k < j ->
    subtract_loop A R i j (k+1) = 
     BMINUS (subtract_loop A R i j k) (BMULT (R k i) (R k j)).
Proof.
intros.
unfold subtract_loop at 1.
replace (Z.to_nat (k+1)) with (Z.to_nat k + 1)%nat by lia.
rewrite iota_plus1.
simpl.
rewrite !map_app.
simpl map.
rewrite fold_left_app.
simpl.
f_equal.
rewrite Z2Nat.id by lia.
f_equal.
Qed.

Lemma body_cholesky : 
  semax_body Vprog Gprog f_cholesky cholesky_spec.
Proof.
unfold cholesky_spec.
rewrite N_eq.
start_function.
rewrite <- N_eq.
forward_for_simple_bound n 
  (EX j:Z, EX R: Z->Z->ftype Tdouble,
      PROP(cholesky_jik_upto n 0 j A R)
      LOCAL(temp _n (Vint (Int.repr n)); temp _A a; temp _R r)
      SEP(data_at rsh matrix (lists_of_fun N (done_to_n n A)) a;
          data_at sh matrix (lists_of_fun N (done_to_ij n j j R)) r)).
-
Exists (fun _ _ : Z => Zconst _ 0).
set (Aval := lists_of_fun _ _).
set (Rval := lists_of_fun _ _).
entailer!!.
intros i j; split; intros; hnf; intros; split; intros; lia.
 sep_apply data_at__data_at.
 apply derives_refl'; f_equal.
 subst Rval.
 unfold matrix.
 unfold default_val. simpl.
 replace (done_to_ij _ _ _ _) with (fun _ _ :Z => Vundef)
  by (extensionality i j; unfold done_to_ij; repeat (if_tac; try lia); auto). 
 unfold lists_of_fun.
 forget O as i. rewrite <- repeat_Zrepeat.
 revert i; induction (Z.to_nat N); simpl; intros; f_equal; auto.
 unfold list_of_fun.
 clear i IHn0.
 forget O as i. rewrite <- repeat_Zrepeat.
 revert i; induction (Z.to_nat N); simpl; intros; f_equal; auto.
-
rename i into j.
forward_for_simple_bound j 
  (EX i:Z, EX R: Z->Z->ftype Tdouble,
      PROP(cholesky_jik_upto n i j A R)
      LOCAL(temp _j (Vint (Int.repr j)); temp _n (Vint (Int.repr n)); temp _A a; temp _R r)
      SEP(data_at rsh matrix (lists_of_fun N (done_to_n n A)) a;
          data_at sh matrix (lists_of_fun N (done_to_ij n i (j+1) R)) r)).
 + Exists R.
   assert (done_to_ij n 0 (j+1) R = done_to_ij n j j R). {
    extensionality i' j'.
    unfold done_to_ij.
    repeat (if_tac; try lia); auto.
   }
   rewrite H1; clear H1.
   entailer!!.
 + clear R.  rename R0 into R.
   unfold matrix.
   rewrite N_eq; forward;
    change (Vundef :: _ :: _) with (default_val (tarray tdouble 1000));
    rewrite <- N_eq in *. 
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
   change (Vundef :: _ :: _) with (default_val (tarray tdouble 1000)).
   forward_for_simple_bound i
     (EX k:Z, 
      PROP(cholesky_jik_upto n i j A R)
      LOCAL(temp _s (Vfloat (subtract_loop A R i j k) );
            temp _i (Vint (Int.repr i)); temp _j (Vint (Int.repr j)); 
            temp _n (Vint (Int.repr n)); temp _A a; temp _R r)
      SEP(data_at rsh matrix (lists_of_fun N (done_to_n n A)) a;
          data_at sh matrix (lists_of_fun N (done_to_ij n i (j+1) R)) r)).
  * entailer!!.  unfold done_to_n; rewrite Znth_lists_done by rep_lia; auto.
  * rename i0 into k.
    unfold matrix.
    rewrite N_eq in *; forward;
    change (Vundef :: _ :: _) with (default_val (tarray tdouble 1000));
    rewrite <- N_eq in *; fold matrix.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
    unfold matrix.
    rewrite N_eq in *; forward;
    change (Vundef :: _ :: _) with (default_val (tarray tdouble 1000));
    rewrite <- N_eq in *; fold matrix.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
     forward.
     entailer!!.
     unfold done_to_ij, lists_of_fun.
     symmetry.
     rewrite Znth_map by rep_lia.
     rewrite !Znth_i_list_of_fun by rep_lia.
     rewrite Znth_i_iota by rep_lia.
     repeat (if_tac; try rep_lia; [ ] ).
     simpl.
     f_equal.
     unfold subtract_loop.
     change (Float.sub ?x ?y) with (BMINUS x y).
     replace (iota 0 (Z.to_nat (k + 1))) with (iota 0 (Z.to_nat k) ++ [Z.to_nat k]).
     rewrite !map_app, fold_left_app.
     reflexivity.
     replace (Z.to_nat (k + 1)) with (Z.to_nat k + 1)%nat by lia.
     simpl.
      rewrite iota_plus1. f_equal.
    * 
     unfold matrix.
     rewrite N_eq in *; forward; 
     change (Vundef :: _ :: _) with (default_val (tarray tdouble 1000));
     rewrite <- N_eq in *; fold matrix.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
     unfold matrix.
     rewrite N_eq in *.
     rewrite Znth_lists_done by lia.
     set (jj := lists_of_fun _ (done_to_ij _ _ _ _)).
     freeze FR1 := (data_at rsh _ _ _).
     forward.
     thaw FR1.
     set (rij := Float.div _ _).
     subst jj.
     Exists (updij R i j rij).
     rewrite <- N_eq.
     rewrite upd_Znth_lists_of_fun by rep_lia.
     entailer!!.
     change Float.div with BDIV in rij.
     apply update_i_lt_j; auto. lia.
  + clear R. Intros R.
    freeze FR2 := (data_at sh _ _ _).
    unfold matrix.
    rewrite N_eq in *.
    forward.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
    rewrite <- N_eq in *; fold matrix.
    thaw FR2.
    freeze FR3 := (data_at rsh _ _ _).
    deadvars!.
   forward_for_simple_bound j
     (EX k:Z, 
      PROP()
      LOCAL(temp _s (Vfloat (subtract_loop A R j j k) );
            temp _j (Vint (Int.repr j)); 
            temp _n (Vint (Int.repr n)); temp _A a; temp _R r)
      SEP(FRZL FR3;
          data_at sh matrix (lists_of_fun N (done_to_ij n j (j+1) R)) r)).
  * entailer!!.
    unfold done_to_n.
    rewrite Znth_lists_done by lia. reflexivity.
  * 
    unfold matrix.
    rewrite N_eq in *.
    forward.
     entailer!!; unfold done_to_n; rewrite Znth_lists_done by rep_lia; apply I.
    rewrite <- N_eq in *; fold matrix.
    rewrite Znth_lists_done by lia.
    forward.     
    entailer!!.
    f_equal.
    change Float.sub with BMINUS. change Float.mul with BMULT.
    apply subtract_another; lia.
  * forward_call.
    unfold matrix.
    rewrite N_eq in *.
    forward.
    rewrite <- N_eq in *; fold matrix.
    rewrite upd_Znth_lists_of_fun by rep_lia.
    set (R' := updij _ _ _ _).
    Exists R'.
    thaw FR3.
    entailer!!.
    change (Binary.Bsqrt _ _ _ _ _ _ ?x) with (BSQRT _ _  x) in R'.
    intros i' j'.
    destruct (zlt j' (j+1));
      [ | split; intros; [ lia | split; intros; lia]].
    assert (Hsub: forall i j', 0 <= i <= j' -> j'<=j -> subtract_loop A R' i j' j' = subtract_loop A R i j' j'). {
      clear j' l; intros i j' Hi Hj'.
      set (x := BSQRT _ _ _) in R'. clearbody x.
      subst R'. destruct H0.
      clear - H0 Hi Hj'.
      unfold subtract_loop.
      rewrite !map_map.
      pose (f z := BMULT z z ).
      set (g1 := BMULT). set (g2 := BMINUS).
      set (a := A i j'). clearbody a.
      set (n:=j) at 1 2 3 4.
      set (u := O).  assert (Z.of_nat (u+ Z.to_nat j')<=n) by lia. clearbody u. clearbody n.
      revert a u H; induction (Z.to_nat j'); intros; auto.
      simpl. rewrite IHn0 by lia. f_equal. f_equal. f_equal. unfold updij.
      rewrite if_false by lia. auto. unfold updij. rewrite if_false by lia. auto.
    }
    destruct (zlt j' j); split; intros; try lia.
    ++ clear H2 i' l.
      destruct (H1 i j') as [? _].
      specialize (H2 l0 i).
      set (x := BSQRT _ _ _) in R'. clearbody x. clear - Hsub H2 l0 H0.
      intro.  specialize (H2 H). destruct H2.
      split; intros.
      ** rewrite Hsub by lia.
      unfold R', updij. rewrite !if_false by lia. auto. 
      ** rewrite Hsub by lia. 
      unfold R', updij. rewrite !if_false by lia. auto. 
    ++ assert (j'=j) by lia. subst j'. clear l g H2 i'.
       red in H1.
       split; intros.
      **
       destruct (H1 i j) as [_ ?]. specialize (H4 (eq_refl _) ltac:(lia)).
       red in H4. destruct H4 as [? _]; try lia.
       rewrite Hsub by lia.
       unfold R'. unfold updij. rewrite !if_false by lia.
       apply H4; auto. 
      ** subst i. rewrite Hsub by lia. unfold R', updij.
         rewrite !if_true by auto. auto.
 - Intros R. Exists R.
   rewrite <- N_eq in *.
   entailer!!.
   intros i j.
   specialize (H0 i j).   
   destruct (zlt j n);[ | split; intros; lia].
   destruct H0.
   apply H0; auto.
Qed.









