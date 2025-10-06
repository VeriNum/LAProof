From LAProof.accuracy_proofs Require Import preamble common
      dotprod_model sum_model dot_acc float_acc_lems list_lemmas
       gem_defs mv_mathcomp gemv_acc.
From mathcomp Require Import Rstruct.
Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.
Set Warnings "notation-overridden,ambiguous-paths,overwriting-delimiting-key".

Open Scope R_scope.
Open Scope ring_scope.


Import Order.TTheory GRing.Theory ssrnum.Num.Def ssrnum.Num.Theory.

Section SCALE_V_ERROR.
(* mixed error vector scaling *)
Context {NAN: FPCore.Nans} {t : FPStdLib.type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Lemma scaleV_mixed_error :
  forall (v: @vector (ftype t)) (a : ftype t)
    (Hfinv : is_finite_vec (scaleVF a v)),
    let vr:= map FT2R v in
    let m := length v in
  exists (e eta: vector),
  map FT2R (scaleVF a v) =  scaleVR (FT2R a) (vr +v e) +v eta
  /\ (forall i, (i < m)%nat -> exists d,
      List.nth i e 0%Re = ((List.nth i vr 0%Re) * d)%Re
        /\ Rabs d <= g m) 
  /\ (forall e0, In e0 eta -> Rabs e0 <= g1 m m) 
  /\ length e   = length v
  /\ length eta = length v .
Proof.
elim => /= [a _|].
-
rewrite /vec_sumR/vec_sum/map2/=. 
by exists [], [].
-
move => v0 v IH a Hfinv. 
have [HA HB]:  is_finite_vec (scaleVF a v) /\ Binary.is_finite (BMULT a v0).
  by apply is_finite_vec_cons in Hfinv.
destruct (IH a) as (e & eta & Heq & He & Heta) => //.
clear IH. rewrite Heq. clear Heq.
destruct (BMULT_accurate a v0) as (del & eps & HD & HE & HF & Heq).
by apply is_finite_BMULT_no_overflow.
rewrite Heq. clear Heq.
remember ((FT2R v0) * del)%Re as d.
exists (d :: e), (eps :: eta); repeat split; try (simpl; lia).
+ rewrite /scaleVR/vec_sumR/vec_sum/map2 /= Heqd. (*-RmultE.*)
  f_equal; nra.
+ move => i Hi.
 rewrite Heqd.
  destruct i => /=.
  * exists del; split; [nra|].
    eapply Rle_trans.
    apply HE => /=. 
    rewrite -Nat.add_1_r; auto with commonDB.
  * have Hi': (i < length v)%nat by lia.
    destruct (He i Hi') as (x & He' & Hx).
    rewrite He'.
    exists x; split => //=.
    eapply Rle_trans; [apply Hx | ].
    auto with commonDB.
+ move => e0 [Hin| Hin].
  * rewrite -Hin.
    eapply Rle_trans; [apply HF|].
    apply e_le_g1; lia.
  * eapply Rle_trans; [apply Heta => // | ].
    apply g1n_le_g1Sn'.
Qed.

End SCALE_V_ERROR.

Section VECSUMERROR.
(* mixed error matrix addition *)
Context {NAN: FPCore.Nans} {t : FPStdLib.type} .

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Lemma vec_sumF_mixed_error :
  forall (u v: @vector (ftype t))
    (Hfinv : is_finite_vec (vec_sumF u v))
    (Hlen : length u = length v),
    let vr:= map FT2R v in
    let ur:= map FT2R u in
    let m := length v in
  exists (e1 e2 : vector),
  map FT2R (vec_sumF u v) = vec_sumR (ur +v e1) (vr +v e2)
  /\ (forall i, (i < m)%nat -> exists d,
      List.nth i e1 0 = (List.nth i ur 0%R) * d
        /\ Rabs d <= @default_rel t)
  /\ (forall i, (i < m)%nat -> exists d,
      List.nth i e2 0 = (List.nth i vr 0%R) * d
        /\ Rabs d <= @default_rel t)
  /\ length e1   = length u
  /\ length e2   = length v.
Proof.
move => u. 
(* main induction on right vector *)
elim u. 
{ move => v /=; intros. 
exists [], [] => /=; repeat split => //=.
rewrite -Hlen. intros => //.
rewrite -Hlen. intros => //. }  
clear u; move => u0 u IH v.
(* main induction *)
case: v => //. 
move => v0 v. intros. 
rewrite /vec_sumF vec_sum_cons.
have Hfin:  is_finite_vec (vec_sum BPLUS u v) /\
  (Binary.is_finite (BPLUS u0 v0) = true).
simpl in Hfinv. rewrite /vec_sumF vec_sum_cons in Hfinv.  
apply is_finite_vec_cons in Hfinv.
destruct Hfinv => //.
destruct Hfin as (H1f & H2f).
rewrite /vec_sumF in IH. 
destruct (IH v) as (e1 & e2 & Heq & H) => //; clear IH.
simpl in Hlen; lia.
simpl; rewrite Heq.
destruct (BPLUS_accurate' u0 v0) as (del & Hd & H1) => //.
rewrite H1; clear H1.
rewrite !CommonSSR.map_map_equiv/=.
exists (((FT2R u0) * del) :: e1), (((FT2R v0) * del) :: e2);
  repeat split. 
{ rewrite /ur/vr/=/vec_sumR !vec_sum_cons.
f_equal. 
rewrite -!RmultE; nra. }
{ move => i Hi; destruct i => /=.
exists del; auto.
destruct H as (H & H1).
elim: (H i). 
clear H; move => d' Hd'.
destruct Hd' as (Hd' & Hd'').
exists d'; split => //=.
unfold m in Hi. simpl in Hi. lia. } 
{ move => i Hi; destruct i => /=.
exists del; split => //=.
destruct H as (_ & H1 & _).
elim: (H1 i). 
clear H1; move => d' Hd'.
destruct Hd' as (Hd' & Hd'').
exists d'; split => //=.
unfold m in Hi; simpl in Hi; lia. } 
all : simpl; lia. 
Qed.

Lemma Svec_sumF_mixed_error :
  forall (u v: @vector (ftype t)) (a b : ftype t)
    (Hfinv : is_finite_vec (vec_sumF (scaleVF a u) (scaleVF b v)))
    (Hlen : length u = length v),
    let vr:= map FT2R v in
    let ur:= map FT2R u in
    let m := length v in
  exists (e1 e2 e3 e4 e5 e6: vector),
  map FT2R (vec_sumF (scaleVF a u) (scaleVF b v)) = 
        vec_sumR 
            (scaleVR (FT2R a) (ur +v e1) +v e2 +v e3) 
            (scaleVR (FT2R b) (vr +v e4) +v e5 +v e6)
  /\ (forall i, (i < m)%nat -> exists d,
      List.nth i e1 0 = (List.nth i ur 0%R) * d
        /\ Rabs d <= g m )
  /\ (forall i, (i < m)%nat -> exists d,
      List.nth i e4 0 = (List.nth i vr 0%R) * d
        /\ Rabs d <= g m )
  /\ (forall i : nat, (i < m)%nat -> exists d,
      List.nth i e3 0 =  (List.nth i (scaleVR (FT2R a) (ur +v e1) +v e2) 0%R) * d 
        /\ Rabs d <= @default_rel t) 
  /\ (forall i : nat, (i < m)%nat -> exists d,
      List.nth i e6 0 =  (List.nth i (scaleVR (FT2R b) (vr +v e4) +v e5) 0%R) * d 
        /\ Rabs d <= @default_rel t)  
  (* absolute error terms *)
  /\ (forall k : R, In k e5 -> Rabs k <= g1 m m)
  /\ (forall k : R, In k e2 -> Rabs k <= g1 m m)
  (* length info is kept *)
  /\ length e1 = m
  /\ length e2 = m
  /\ length e3 = m
  /\ length e4 = m
  /\ length e5 = m
  /\ length e6 = m.
Proof.
intros.
have Hu : (length u = m) by lia.
destruct (vec_sumF_mixed_error (scaleVF a u) (scaleVF b v)) as
  (Du & Dv & Heq & HD) => //.
by rewrite !map_length.
apply is_finite_vec_sum in Hfinv; destruct Hfinv.
destruct (scaleV_mixed_error u a) as 
  (ae & aeta & Heqa & Hea & Haeta & HA1 & HA2) => //.
destruct (scaleV_mixed_error v b) as 
  (be & beta & Heqb & Heb & Hbeta & HB1 & HB2) => //.
rewrite Heq. rewrite Heqb Heqa.
rewrite Heqa Heqb in HD. clear Heq Heqa Heqb.
destruct HD as (HDu & HDv & HD1 & HD2).
rewrite !CommonSSR.map_map_equiv.
exists ae, aeta ,Du, be, beta, Dv; repeat split => //; try lia.
{ intros; destruct (Hea i) . 
rewrite Hu; lia.
exists x; rewrite Hu in H2; apply H2. }
{ intros; destruct (HDu i) .
rewrite !map_length. fold m; lia.
fold m in H2; exists x; apply H2. }
{ intros; destruct (HDv i) .
rewrite !map_length. fold m; lia.
rewrite !CommonSSR.map_map_equiv in H2.
fold m in H2; exists x. apply H2. }
rewrite -Hu.
by apply Haeta. 
rewrite !map_length in HD1; lia.
rewrite !map_length in HD2; lia.
all: by rewrite !map_length.
Qed. 

End VECSUMERROR.


Section SCALEFMV. 
(* mixed error bounds over lists *)
Context {NAN: FPCore.Nans} {t : FPStdLib.type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A: @matrix (ftype t)).
Variable (v: @vector (ftype t)).
Variable (b: ftype t).

Notation n := (length v).
Notation m := (length A).
Notation Ar := (map_mat FT2R A).
Notation vr := (map FT2R v).

Hypothesis Hfin : is_finite_vec (scaleVF b (A *f v)).
Hypothesis Hlen: forall row, In row A -> length row = length v.

Lemma Smat_vec_mul_mixed_error:
  exists (E : matrix) (e eta1 eta2 : vector),
    map FT2R (scaleVF b (A *f v)) =  
        scaleVR (FT2R b) ((Ar +m E) *r vr +v eta1 +v e) +v eta2 
    /\ (forall i j, (i < m)%nat -> (j < n)%nat -> 
      Rabs (E _(i,j)) <= g n * Rabs (Ar _(i,j))) 
    /\ (forall k, In k eta2 -> Rabs k <= g1 m m) 
    /\ eq_size E A 
    /\ length eta2 = m
    /\ (forall i : nat, (i < m)%nat ->
        exists d : R,
        (List.nth i e 0 = List.nth i (A *fr v) 0 * d /\
           (Rabs d) <= g m))
    /\ (forall k : R,
       (In k eta1) -> is_true (Rabs k <= g1 n n)%O) 
    /\ length eta1= m.
Proof.
(* proof follows from previous bounds for scaling
and multiplication *)
destruct (scaleV_mixed_error (A *f v) b)
  as (e & eta & Heq & H) => //.
rewrite Heq. clear Heq.
destruct (mat_vec_mul_mixed_error A v)
  as (E & eta1 & Heq1 & H1).
{ apply (is_finite_scaleV b) => //. } 
{ intros; by apply Hlen. } 
rewrite !CommonSSR.map_map_equiv.
change @map with @List.map in Heq1.
rewrite Heq1. 
rewrite !CommonSSR.map_map_equiv in H.
rewrite Heq1 in H. clear Heq1.
have Hlen1: (length (A *f v)) = m  by rewrite !length_map.
exists E, e, eta1, eta; repeat split => //.
-
destruct H1.  
intros; apply H0 => //.
-
destruct H as (_ & H & _); intros.
rewrite Hlen1 in H. by apply H.
-
destruct H1 as (_ & _ &H1 & _).
destruct H1; lia.
-
destruct H1 as (_ & _ &H1 & _).
destruct H1; intros. by apply H1.
-
destruct H as (_ & H).
destruct H as ( _ & H ).
destruct H;intros.
by rewrite H0 !length_map.
-
change @List.map with @map in H|-*.
rewrite !CommonSSR.map_map_equiv in H.
destruct H as (H & _); intros. 
destruct (H i). by rewrite Hlen1.
exists x; destruct H2; split => //.
by rewrite Hlen1 in H3.
-
destruct H1 as (_ & H1 & _).
intros; apply /RleP; by apply H1.
-
destruct H1 as (_ & _ & H2).
by apply H2.
Qed.

End SCALEFMV. 

Section GEMV. 
(* mixed error bounds over lists *)
Context {NAN: FPCore.Nans} {t : type}.

Notation g := (@common.g t).
Notation g1 := (@common.g1 t).

Variable (A: @matrix (ftype t)).
Variable (x y: @vector (ftype t)).
Variable (s1 s2: ftype t).

Notation n := (length x).
Notation m := (length A).
Notation Ar := (map_mat FT2R A).
Notation xr := (map FT2R x).
Notation yr := (map FT2R y).

Hypothesis Hfin : is_finite_vec 
  (vec_sumF (scaleVF s1 (A *f x)) (scaleVF s2 y)).
Hypothesis Hlen: forall row, In row A -> length row = length x.
Hypothesis Hleny: length y = m.

Lemma gemv_error:
  exists (e1 : matrix) (e2 e3 e4 e5 e6 e7 e8: vector),
    map FT2R (vec_sumF (scaleVF s1 (A *f x)) (scaleVF s2 y)) =  
  ((scaleVR (FT2R s1) ((((Ar +m e1) *r xr) +v e2) +v e3) +v e4) +v e5) +v
  ((scaleVR (FT2R s2) (List.map FT2R y +v e6) +v e7) +v e8)

  /\ (forall i j : nat, (i < m)%nat -> (j < n)%nat ->
      Rabs (matrix_index 0%Re e1 i j) <= g n * Rabs (matrix_index 0%Re Ar i j)) 
  /\ (forall k : R, In k e2 -> Rabs k <= g1 n n) 
  /\ (forall i : nat, (i < m)%nat -> exists d,
        List.nth i e3 0 = List.nth i (((Ar +m e1) *r xr) +v e2) 0%Re * d 
        /\ Rabs d <= g m ) 
  /\ (forall i : nat, (i < m)%nat -> exists d,
        List.nth i e6 0 = List.nth i (List.map FT2R y) 0%Re * d 
        /\ Rabs d <= g m) 
  /\ (forall i : nat, (i < m)%nat -> exists d,
        List.nth i e5 0 = List.nth i (scaleVR (FT2R s1) ((((Ar +m e1) *r xr) +v e2) +v e3) +v e4) 0%Re * d 
        /\ Rabs d <= @default_rel t) 
  /\ (forall i : nat, (i < m)%nat -> exists d ,
        List.nth i e8 0 = List.nth i (scaleVR (FT2R s2) (List.map FT2R y +v e6) +v e7) 0%Re * d 
        /\ Rabs d <= @default_rel t) 
  /\ (forall k : R, In k e7 -> Rabs k <= g1 m m)
  /\ (forall k0 : R, In k0 e4 -> Rabs k0 <= g1 m m).

Proof.
(* proof follows from previous bounds for axpby and mul *)
destruct (Svec_sumF_mixed_error (A *f x) y s1 s2)
  as (e3 & e4 & e5 & e6 & e7 & e8 & Heq1 & H1) => //.
{ by symmetry; rewrite !map_length.  }
rewrite Heq1.
rewrite !CommonSSR.map_map_equiv.
destruct (mat_vec_mul_mixed_error A x)
  as (e1 & e2 & Heq2 & H2).
{ apply is_finite_vec_sum in Hfin; destruct Hfin.
by apply is_finite_scaleV in H.
all: rewrite !map_length; by rewrite Hleny. }
{ by intros; apply Hlen. }
change @List.map with @map.
rewrite Heq2. 
rewrite Heq2 in H1. rewrite Hleny in H1, H2.
destruct H2 as (He1 & He2 & _).
destruct H1 as (He3 & He4 & He5 & He6 & He7 & He8 & _).
exists e1, e2, e3, e4, e5, e6, e7, e8; repeat split => //.
Qed.

End GEMV.




