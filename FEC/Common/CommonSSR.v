(* Copyright 2021 Joshua M. Cohen

Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and limitations under the License.
*)

(** Generic Results about mathcomp and ssreflect functions, some used in multiple places*)
Require Import Coq.Lists.List.
From mathcomp Require Import all_ssreflect.
Require Import mathcomp.algebra.matrix.
Require Import mathcomp.algebra.ssralg.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(*Used only for other tactics*)
Ltac case_view E P H :=
  destruct E eqn : H; [ apply (elimT P) in H | apply (elimF P) in H].

(** Lemmas about Nats*)

Lemma ltn_total: forall (n1 n2: nat),
  (n1 < n2) || (n1 == n2) || (n2 < n1).
Proof.
  move => n1 n2. case: (orP (leq_total n1 n2)); rewrite leq_eqVlt.
  - move => le_n12; case (orP le_n12) => [Heq | Hlt].  rewrite Heq /=.
    by rewrite orbT orTb. by rewrite Hlt !orTb.
  - move => le_n21; case (orP le_n21) => [Heq | Hlt]. rewrite eq_sym Heq /=.
    by rewrite orbT orTb. by rewrite Hlt !orbT.
Qed. 

Lemma ltn_leq_trans: forall [n m p : nat], m < n -> n <= p -> m < p.
Proof.
  move => m n p Hmn. rewrite leq_eqVlt => /orP[/eqP Hmp | Hmp]. by subst.
  move : Hmn Hmp. apply ltn_trans.
Qed.

Lemma ltn_pred: forall m n,
  0 < n ->
  (m < n) = (m <= n.-1).
Proof.
  move => m n Hpos. have: n.-1 == (n - 1)%N by rewrite eq_sym subn1. move => /eqP Hn1. by rewrite Hn1 leq_subRL.
Qed.

Lemma pred_lt: forall n, 0 < n -> n.-1 < n.
Proof.
  move => n Hn. by rewrite ltn_predL.
Qed.

Lemma ltn_leq_total: forall n m,
  (n < m) || (m <= n).
Proof.
  move => m n.   
  pose proof (ltn_total m n). move : H => /orP[/orP[Hlt | Heq] | Hgt].
  + by rewrite Hlt.
  + by rewrite (leq_eqVlt n) eq_sym Heq orbT.
  + by rewrite (leq_eqVlt n) Hgt !orbT.
Qed. 

Lemma ltn_add2rl: forall n1 n2 m1 m2,
  n1 < n2 ->
  m1 < m2 ->
  n1 + m1 < n2 + m2.
Proof.
  move => n1 n2 m1 m2 Hn Hm. have Hleft: n1 + m1 < n1 + m2 by rewrite ltn_add2l.
  have Hright: n1 + m2 < n2 + m2 by rewrite ltn_add2r. by apply (ltn_trans Hleft Hright).
Qed.

Lemma pred_leq: forall (n m: nat),
  (n.-1 <= m) = (n <= m.+1).
Proof.
  move => n m. by rewrite -subn1 -addn1 add0n leq_subLR addnC addn1.
Qed.

(** Lemmas about Ordinals*)

Definition pred_ord (n: nat) (Hn: 0 < n) : 'I_n := Ordinal (pred_lt Hn).

(*Working with enums of ordinals*)
Lemma ordinal_enum_size: forall n,
  size (Finite.enum (ordinal_finType n)) = n.
Proof.
  move => n. have: size ([seq val i | i <- enum 'I_n]) = n. rewrite val_enum_ord. by apply: size_iota.
  rewrite size_map. unfold enum. rewrite size_map //.
Qed.

Lemma ordinal_enum: forall {n: nat} (x: 'I_n) y,
  nth y (Finite.enum (ordinal_finType n)) x = x.
Proof.
  move => n x y. have nth_ord := (nth_ord_enum y x). unfold enum in nth_ord. move: nth_ord.
  rewrite (@nth_map _ y) //. by rewrite ordinal_enum_size.
Qed. 

Lemma size_ord_enum: forall n, size (ord_enum n) = n.
Proof.
  move => n. 
  have : size (ord_enum n) = size ([seq val i | i <- ord_enum n]) by rewrite size_map.
  by rewrite val_ord_enum size_iota.
Qed.

Lemma nth_ord_enum: forall n (i: 'I_n) x, nth x (ord_enum n) i = i.
Proof.
  move => n i x. have Hv := val_ord_enum n.  have Hmap :=  @nth_map 'I_n x nat x val i (ord_enum n).
  move : Hmap. rewrite Hv size_ord_enum nth_iota =>[//=|//]. rewrite add0n. move => H.
  (*some annoying stuff about equality of ordinals vs nats*)
  have : nat_of_ord ( nth x (ord_enum n) i) == nat_of_ord i. rewrite {2}H. by []. by [].
  move => Hnatord. have : nth x (ord_enum n) i == i by []. 
  by move => /eqP Heq.
Qed.

Lemma index_ord_enum: forall (n: nat), (index_enum (ordinal_finType n)) = ord_enum n.
Proof.
  move => n. have: 0 <= n by []. rewrite leq_eqVlt => /orP[/eqP Hn0 | Hnpos].
  - subst. rewrite /ord_enum /= /index_enum /=. apply size0nil. apply ordinal_enum_size.
  - apply (eq_from_nth (x0:=pred_ord Hnpos)).
    + by rewrite ordinal_enum_size size_ord_enum.
    + move => i. rewrite ordinal_enum_size => Hi.
      have->: i = nat_of_ord (Ordinal Hi) by [].
      by rewrite ordinal_enum nth_ord_enum.
Qed.

(*If an 'I_m exists, then 0 < m*)
Lemma ord_nonzero {m} (r: 'I_m) : 0 < m.
Proof.
  case : r. move => m'. case (orP (ltn_total m 0)) => [/orP[Hlt // | /eqP Heq] | Hgt //].
  by subst.
Qed.

Lemma remove_widen: forall {m n} (x: 'I_m) (H: m <= n),
  nat_of_ord (widen_ord H x) = nat_of_ord x.
Proof.
  by [].
Qed.

Lemma widen_ord_inj: forall {m n: nat} (H: m <= n) x y, widen_ord H x = widen_ord H y -> x = y.
Proof.
  move => m n H x y Hw. apply (elimT eqP).
  have: nat_of_ord (widen_ord H x) == x by []. have: nat_of_ord (widen_ord H y) == y by [].
  move => /eqP Hy /eqP Hx. rewrite Hw in Hx. have: nat_of_ord x == nat_of_ord y by rewrite -Hx -Hy. by [].
Qed.

Lemma eq_leqn: forall m n,
  m = n ->
  (m <= n)%N.
Proof.
  move => m n ->. by rewrite leqnn.
Qed. 

Definition eq_ord m n (Hmn: m = n) (x: 'I_m) : 'I_n  := widen_ord (eq_leqn Hmn) x.

Lemma nat_of_ord_eq: forall n (x y : 'I_n),
  (nat_of_ord x == nat_of_ord y) = (x == y).
Proof.
  move => n x y. case Hxy: (x == y).
  apply (elimT eqP) in Hxy. by rewrite Hxy eq_refl.
  case Hxynat: (nat_of_ord x == nat_of_ord y) =>[|//]. apply (elimT eqP) in Hxynat.
  have: x == y by (apply /eqP; apply ord_inj). by rewrite Hxy.
Qed.

Lemma nat_of_ord_neq: forall {m} (x y : 'I_m),
  x != y ->
  nat_of_ord x != nat_of_ord y.
Proof.
  move => m x y Hxy. by rewrite nat_of_ord_eq.
Qed.

(** Lemmas about [iota]*)

Lemma iota_plus_1: forall x y,
  iota x (y.+1) = iota x y ++ [ :: (x + y)%N].
Proof.
  move => x y. by rewrite -addn1 iotaD /=.
Qed.

Lemma last_iota: forall n m k,
  (0 < n)%N ->
  last k (iota m n) = (m+n).-1.
Proof.
  move => n. elim : n => [/= m k | /=n IH m k Hn].
  - by rewrite ltnn.
  - apply ltnSE in Hn. move: Hn; rewrite leq_eqVlt => /orP[/eqP Hn0 | Hnpos].
    + by rewrite -Hn0 /= addn1 -pred_Sn.
    + by rewrite IH // addSnnS.
Qed.


(** Other lemmas*)

Lemma rwN: forall [P: Prop] [b: bool], reflect P b -> ~ P <-> ~~ b.
Proof.
  move => P b Hr. split. by apply introN. by apply elimN.
Qed.

Lemma rem_impl: forall b : Prop,
  (true -> b) -> b.
Proof.
  move => b. move => H. by apply H.
Qed.

Lemma isSome_none: forall {T: eqType} (o: option T),
  ~~ (isSome o) = (o == None).
Proof.
  move => T o. by case : o.
Qed.

(*The lemma in the ssreflect library is not generic enough*)
Lemma some_inj: forall {A: Type},
  injective (@Some A).
Proof.
  move => A x y Hop. by case : Hop.
Qed.

(** Lemmas about [find] *)

(*Results about [find] that mostly put the library lemmas into a more convenient form*)

Lemma find_iff: forall {T: eqType} (a: pred T) (s: seq T) (r : nat) (t: T),
  r < size s ->
  find a s = r <-> (forall x, a (nth x s r)) /\ forall x y, y < r -> (a (nth x s y) = false).
Proof.
  move => T a s r t Hsz. split.
  - move => Hfind. subst. split. move => x. apply nth_find. by rewrite has_find.
    move => x. apply before_find.
  - move => [Ha Hbef]. have Hfind := (findP a s). case : Hfind.
    + move => Hhas. have H := (rwN (@hasP T a s)). rewrite Hhas in H.
      have:~ (exists2 x : T, x \in s & a x) by rewrite H. move : H => H{H} Hex.
      have : nth t s r \in s by apply mem_nth. move => Hnthin. 
      have: (exists2 x : T, x \in s & a x) by exists (nth t s r). by [].
    + move => i Hisz Hanth Hprev.
      have Hlt := ltn_total i r. move : Hlt => /orP[H1 | Hgt].
      move : H1 => /orP[Hlt | /eqP Heq].
      * have : a (nth t s i) by apply Hanth. by rewrite Hbef.
      * by subst.
      * have : a (nth t s r) by apply Ha. by rewrite Hprev.
Qed.

(*Similar for None case*)
Lemma find_none_iff: forall {T: eqType} (a: pred T) (s: seq T),
  find a s = size s <-> (forall x, x \in s -> ~~ (a x)).
Proof.
  move => T a s. split.
  - move => Hfind. have: ~~ has a s. case Hhas : (has a s). 
    move : Hhas. rewrite has_find Hfind ltnn. by []. by [].
    move => Hhas. by apply (elimT hasPn).
  - move => Hnotin. apply hasNfind. apply (introT hasPn). move => x. apply Hnotin. 
Qed.

(** [find] but for values rather than indices*)

Definition find_val_option {T: Type} (p: pred T) (s: seq T) : option T :=
  match (filter p s) with
  | nil => None
  | h :: _ => Some h
  end.

Definition find_val {T: Type} (p: pred T) (s: seq T) (d: T) : T :=
  match (find_val_option p s) with
  | None => d
  | Some h => h
  end.

Lemma find_val_option_none: forall {T: Type} (p: pred T) s,
  all (fun x => ~~ p x) s = ~~ (isSome (find_val_option p s)).
Proof.
  move => T p s. elim : s => [//= | h t /=].
  rewrite /find_val_option /= => IH.
  case Hh: (p h) =>[//|/=].
  by rewrite IH.
Qed.

Lemma find_val_none: forall {T: Type} (p: pred T) s d,
  all (fun x => ~~ p x) s ->
  find_val p s d = d.
Proof.
  move => T p s d. rewrite find_val_option_none /find_val.
  by case (find_val_option).
Qed.

Lemma find_val_option_some_in: forall {T: eqType} (p: pred T) s h,
  (find_val_option p s) = Some h ->
  h \in s.
Proof.
  move => T p s. elim : s =>[// | x t /=].
  rewrite /find_val_option/= => IH h. case Hx: (p x) => [/= |/=].
  move => [Hxh]. subst. by rewrite in_cons eq_refl. move => Hh. apply IH in Hh.
  by rewrite in_cons Hh orbT.
Qed.

Lemma find_val_option_some: forall {T: Type} (p: pred T) s h,
  (find_val_option p s) = Some h ->
  p h.
Proof.
  move => T p s. elim : s =>[// | x t /=].
  rewrite /find_val_option/= => IH h. case Hx: (p x) => [/= |/=].
  move => [Hxh]. by subst. apply IH.
Qed.

Lemma find_val_option_exists: forall {T: eqType} (p: pred T) s,
  (exists x, (x \in s) && p x) ->
  exists h, ((find_val_option p s == Some h) && p h).
Proof.
  move => T p s. elim : s => [//= | h t /=].
  rewrite /find_val_option/= => IH [x /andP[Hin Hpx]].
  move: Hin; rewrite in_cons => /orP[/eqP Hxh | Hxt].
  - subst. rewrite Hpx. exists h. by rewrite Hpx eq_refl.
  - case Hh: (p h). exists h. by rewrite Hh eq_refl. apply IH.
    exists x. by rewrite Hxt Hpx.
Qed.

Lemma find_val_exists: forall {T: eqType} (p: pred T) s d,
  (exists x, (x \in s) && p x) ->
  p (find_val p s d).
Proof.
  move => T p s d Hex. rewrite /find_val. apply find_val_option_exists in Hex.
  case : Hex => [h /andP[/eqP Hfind Hph]]. by rewrite Hfind Hph.
Qed.

(** Lemmas about [all]*)

Lemma all_in: forall {A: eqType} (l: seq A) (p: pred A),
  all p l <-> forall x, x \in l -> p x.
Proof.
  move => A l. elim: l =>[p // | h t IH p /=].
  split. move => /andP[Hh Htl x]. rewrite in_cons => /orP[/eqP Hxh | Hxt].
  by subst. by apply IH.
  move => Hall. rewrite Hall. rewrite IH. move => x Hint. apply Hall. by rewrite in_cons Hint orbT.
  by rewrite in_cons eq_refl.
Qed.

(** Lemmas about [rem]*)
Lemma rem_in_neq: forall {A: eqType} (l : seq A) (y: A) (x: A),
  x != y ->
  (x \in (rem y l)) = (x \in l).
Proof.
  move => A l y x Hxy. elim : l => [//= | h t IH /=].
  case: (h == y) /eqP => Hhy.
  - rewrite in_cons. subst. have->: (x == y = false). move : Hxy. by case (x == y).
    by [].
  - rewrite !in_cons. by rewrite IH.
Qed. 

(** Lemmas about [pmap]*)
Lemma nth_pmap: forall (aT rT: eqType) (f: aT -> option rT) (s: seq aT) (i: nat) (a: aT) (r: rT),
  all f s ->
  (i < size s)%N ->
  Some (nth r (pmap f s) i) = f (nth a s i).
Proof.
  move => aT rT f s i a r. move: i. elim : s =>[//= | h t /= IH i /andP[Hh Hall]]. rewrite ltnS => Hi.
  move : Hh. case Hh: (f h) => [h' /= | //=]. move => Htriv. 
  have: (0 <= i)%N by []. rewrite leq_eqVlt => /orP[/eqP Hi0 | Hi'].
  - subst. by rewrite /= Hh.
  - have->: (i = (i.-1).+1)%N by rewrite (ltn_predK Hi'). rewrite /=. rewrite IH //.
    have Hi1: (i.-1 < i)%N by apply pred_lt. by apply (ltn_leq_trans Hi1).
Qed.

Lemma index_pmap: forall (aT rT: eqType) (f: aT -> option rT) (g: rT -> aT) (s: seq aT) (x: rT),
  pcancel g f ->
  (forall x x' y, f x = Some y -> f x' = Some y -> x = x') ->
  all f s ->
  index (g x) s = index x (pmap f s).
Proof.
  move => aT rT f g s x Hcancel Hinj. elim : s => [//= | h t /= IH /andP[Hh Hall]]. 
  move: Hh. case Hfh : (f h) => [o /= | //]. move => _.
  case : (h == g x) /eqP => [Hhg | Hhg].
  - rewrite Hhg in Hfh. rewrite Hcancel in Hfh. case : Hfh => [->]. by rewrite eq_refl.
  - case: (o == x) /eqP => [Hox /= | Hox /=].
    + subst. have: h = g x. apply (Hinj _ _ x). by []. apply Hcancel. by [].
    + by rewrite IH.
Qed.

Lemma rev_pmap: forall {aT rT} (f: aT -> option rT) (s: seq aT),
  rev (pmap f s) = pmap f (rev s).
Proof.
  move => aT rT f s. elim : s => [// | h t /= IH].
  rewrite rev_cons -cats1 pmap_cat /= -IH.
  case Hf: (f h) =>[/= u|/=].
  - by rewrite rev_cons -cats1.
  - by rewrite cats0.
Qed.

(** Lemmas about [index]*)

Lemma index_notin: forall {T: eqType} (x: T) (s: seq T), (index x s == size s) = (x \notin s).
Proof.
  move => T x s. case Hin: (x \in s).
  - move: Hin. rewrite -index_mem. case : (index x s == size s) /eqP => [->// |//]. by rewrite ltnn.
  - rewrite memNindex. by rewrite eq_refl. by rewrite Hin.
Qed.

(*Don't need f to be injective fully, only on some predicate that encompases list and x (for us,
  dealing with only positive integers)*)
Lemma index_map': forall [T1 T2 : eqType] [f : T1 -> T2] (s: seq T1) (a: pred T1),
  (forall x y, a x -> a y -> f x = f y -> x = y) ->
  all a s ->
  forall (x : T1), a x -> index (f x) [seq f i | i <- s] = index x s.
Proof.
  move => T1 T2 f s a Hinj Hall x Hx. move: Hinj Hall. elim : s => [//= | h t /= IH Hinj /andP[Hah Hat]].
  case : (h == x) /eqP => [Hhx/= | Hhx/=].
  - subst. by rewrite eq_refl.
  - case : (f h == f x) /eqP => [Hfxh /= | Hfxh /=].
    + have: h = x. by apply Hinj. by [].
    + by rewrite IH.
Qed.

(** Relating ssreflect and standard library functions*)


Lemma in_mem_In: forall {A: eqType} (l: list A) x,
  x \in l <-> In x l.
Proof.
  move => A l x. elim: l => [//| h t IH /=].
  rewrite in_cons -IH eq_sym. split => [/orP[/eqP Hx | Ht]| [Hx | Hlt]]. by left. by right.
  subst. by rewrite eq_refl. by rewrite Hlt orbT.
Qed.

Lemma uniq_NoDup: forall {A: eqType} (l: list A),
  uniq l <-> NoDup l.
Proof.
  move => A l. elim : l => [//=|h t IH].
  - split =>[H{H}|//]. by apply NoDup_nil.
  - rewrite /=. split => [/andP[Hnotin Hun]| ].
    constructor. rewrite -in_mem_In. move => Hin. by move : Hin Hnotin ->.
    by apply IH.
    move => Hnod. inversion Hnod as [|x l Hnotin Hnodup] ; subst.
    have->: h \notin t. case Hin: (h\in t). have: h\in t by []. by rewrite in_mem_In =>{} Hin.
    by []. by rewrite IH.
Qed. 

Lemma size_length: forall {A : Type} (l: list A),
  size l = Datatypes.length l.
Proof.
  move => A l. elim: l => [//|h t IH /=].
  by rewrite IH.
Qed.

Lemma nth_nth: forall {A: Type} (d: A) (l: seq A) (n: nat),
  nth d l n = List.nth n l d.
Proof.
  move => A d l. elim : l => [//= n | //= h t IH n].
  - by case : n.
  - case: n. by []. move => n. by rewrite /= IH.
Qed.

Lemma concat_flatten: forall {A: Type} (l: seq (seq A)),
  concat l = flatten l.
Proof.
  move => A l. by [].
Qed.

Lemma rev_rev: forall {A: Type} (s: seq A),
  rev s = List.rev s.
Proof. 
  move => A s. elim : s => [// | h t /= IH].
  by rewrite rev_cons IH -cats1.
Qed.

Lemma map_map_equiv: forall {A B: Type} (f: A -> B) (s: seq A),
  map f s = List.map f s.
Proof.
  by [].
Qed.

Lemma filter_filter: forall {A: Type} (f: A -> bool) (s: seq A),
  filter f s = List.filter f s.
Proof.
  by [].
Qed.

(** Other list lemmas*)

Lemma cat_extra: forall {A: Type} (s1 s2 : seq A),
  s1 ++ s2 = s1 ->
  s2 = [::].
Proof.
  move => A s1 s2. elim : s1 => [//= | /= h t IH [Happ]]. by apply IH.
Qed.

Lemma size_not_nil: forall {A: Type} (l: seq A),
  (0 < size l) = ~~ (nilp l).
Proof.
  move => A l. case Hsz: (size l) => [/= | n /=].
  - apply size0nil in Hsz. by subst.
  - move: Hsz. by case : l.
Qed.

Lemma larger_not_nil: forall {A: Type} (l1 l2: seq A),
  ~~ nilp l2 ->
  (size l1 < size l2) = false ->
  ~~ nilp l1.
Proof.
  move => A l1 l2 Hl2 Hsz. rewrite ltnNge in Hsz. apply negbFE in Hsz. move : Hl2;
  rewrite -!size_not_nil => Hl2. by apply (ltn_leq_trans Hl2).
Qed.

(** Stuff about finTypes*)

Lemma bijective_card: forall {T T': finType} (f: T -> T'),
  bijective f ->
  #|T| = #|T'|.
Proof.
  move => T T' f Hb. have Htt': #|T| <= #|T'|. apply (leq_card f). by apply bij_inj.
  case : Hb => g Hfg Hgf. have Htt'': #|T'| <= #|T|. apply (leq_card g). apply (can_inj Hgf).
  apply /eqP. by rewrite eqn_leq Htt' Htt''.
Qed.

Lemma tuple_eq: forall {A: Type} (n: nat) (t1 t2: n.-tuple A),
  tval t1 = tval t2 ->
  t1 = t2.
Proof.
  move => A n [l1 Hl1] [l2 Hl2]. rewrite /= => Hl12. subst. f_equal. apply bool_irrelevance.
Qed. 

Lemma in_enum: forall {T: finType} (x: T),
  x \in (enum T).
Proof.
  move => T x. rewrite enumT. pose proof (@enumP T) as Hfin. move: Hfin; rewrite /Finite.axiom => /(_ x) Hx.
  case Hin: (x \in Finite.enum T) => [// | ].
  have / count_memPn Hnotin: (x \notin Finite.enum T) by rewrite Hin. by rewrite Hnotin in Hx.
Qed.


(** Seqs of subTypes *)

(*We want to transform a seq T into a seq sT if we know that all elements in s satisfy the predicate P.
  We can do so with the following function, which is computable, unlike [pmap insub]*)

Lemma all_cons_hd: forall {T: Type} (P: pred T) (h: T) t,
  all P (h :: t) ->
  P h.
Proof.
  by move => T P h t /= /andP[Hh Ht].
Qed.

Lemma all_cons_tl: forall {T: Type} (P: pred T) (h: T) t,
  all P (h :: t) ->
  all P t.
Proof.
  by move => T P h t /= /andP[Hh Ht].
Qed.

Definition sub_seq {T: Type} (P: pred T) (st: subType P) (s: seq T) (Hs: all P s) : seq st.
move: Hs; elim s => [Hall | h t /= IH Hall].
apply nil.
apply cons. apply (Sub h (all_cons_hd Hall)). apply (IH (all_cons_tl Hall)).
Defined.

Lemma sub_seq_in: forall {T: eqType} (P: pred T) (st: subType P) (s: seq T) (Hs: all P s) (x: st),
  x \in (sub_seq st Hs) = ((val x) \in s).
Proof.
  move => T P st s Hs x. move: Hs. elim : s => [//= | h t /= IH Hs].
  rewrite !in_cons /=. f_equal.
  - by rewrite -val_eqE /= SubK.
  - apply IH.
Qed.

(** [dropWhileEnd - remove all elts from end that satisfy predicate (from Haskell)*)

(* function (from Haskell) to remove all values from end of list that satisfy a predicate. *)
Definition dropWhileEnd {A: Type} (p: pred A) (l: seq A) : seq A :=
  foldr (fun x acc => if (nilp acc) && (p x) then nil else x :: acc) nil l.

Lemma dropWhileEnd_nil: forall {A} p (l: seq A),
  reflect (dropWhileEnd p l = nil) (all p l).
Proof.
  move => A p l. apply Bool.iff_reflect. elim : l => [//= | h t /= IH].
  case Hnil: (nilp (dropWhileEnd p t)) => [/= | /=].
  - case Hp: (p h) => [//= | //=]. rewrite -IH. apply (elimT nilP) in Hnil. by rewrite Hnil.
  - split; move => Hcon.
    + by [].
    + move: Hcon => /andP[Hph Ht]. have: all p t = true by rewrite Ht. rewrite -IH => Htl.
      by rewrite Htl in Hnil.
Qed.

Lemma dropWhileEnd_end: forall {A: Type} p (l1 l2: seq A),
  all p l2 ->
  dropWhileEnd p (l1 ++ l2) = dropWhileEnd p l1.
Proof.
  move => A p l1. elim : l1 => [//= l2 Hall | h t /= IH l2 Hall].
  - by apply /dropWhileEnd_nil.
  - by rewrite IH.
Qed.

Lemma dropWhileEnd_spec: forall {A: eqType} p (l: seq A) (x: A) res,
  dropWhileEnd p l = res <->
  (exists l1, l = res ++ l1 /\ forall x, x \in l1 -> p x) /\ (~~nilp res -> ~~p(last x res)).
Proof.
  move => A p l x. elim : l => [//= | h t /= IH res]; split.
  - move <-. split. by exists nil. by [].
  - move => [[l1 [Hl1 Hall]] Hlast]. move: Hl1 Hlast. by case : res.
  - case Hdrop: (nilp (dropWhileEnd p t)) => [//= | //=].
    + case Hph : ( p h) => [/= | /=].
      * move <-. rewrite /=. split. exists (h :: t). split. by [].
        have Ht: forall x, x \in t -> p x. apply all_in. apply /dropWhileEnd_nil. by apply /nilP.
        move => y. rewrite in_cons => /orP[/eqP Hyh | Hyt]. by subst. by apply Ht. by [].
      * case : res => [// | r1 t1 /= [Hhr1 Htl]]. rewrite Hhr1. move: Htl; rewrite IH => [[[l1 [Hl1 Hinl1]] Hlast]].
        subst. split. by exists l1. move => {Hdrop} {IH}. move: Hlast. case : t1 => [//= | //=].
        move => Htriv Htriv1. by rewrite Hph.
    + case : res => [//= | r1 t1 /= [Hhr1 Hdt1]]. rewrite Hhr1.
      move: Hdt1; rewrite IH => [[[l1 [Hl1 Hinl1]] Hlast]]. subst. split. by exists l1.
      move: Hdrop. rewrite dropWhileEnd_end. move : Hlast => {IH}. by case : t1. by rewrite all_in.
  - move => [[l1 [Hl1 Hinl1]] Hlast]. move: Hl1 Hlast. case : res => [//= Hl1 | r1 t1 /=[Hhr1 Ht]].
    + subst. move => Htriv. rewrite Hinl1. rewrite andbT.
      have->: nilp (dropWhileEnd p t). apply /nilP. apply /dropWhileEnd_nil. rewrite all_in.
      move => y Hy. apply Hinl1. by rewrite in_cons Hy orbT. by []. by rewrite in_cons eq_refl.
    + move => Hlast. subst. have Hdrop: dropWhileEnd p (t1 ++ l1) = t1. apply IH. split.
      by exists l1. move: Hlast {IH}. by case : t1.
      rewrite Hdrop. case Hnil: (nilp t1) => [/= | //=].
      * apply (elimT nilP) in Hnil. subst. move: Hlast; rewrite /= => Hpr1.
        have->: p r1 = false. apply (elimT negPf). by apply Hpr1. by [].
Qed.

Lemma dropWhileEnd_size: forall {A: eqType} (p: pred A) (l: seq A),
  size (dropWhileEnd p l) <= size l.
Proof.
  move => A pr l. elim : l => [//= | h t /= IH ].
  case : (nilp (dropWhileEnd pr t) && pr h) => [//|/=].
  by rewrite ltnS.
Qed.

Lemma dropWhileEnd_last: forall {A: eqType} (p: pred A) (l: seq A) (x: A),
  ~~ p (last x l) ->
  dropWhileEnd p l = l.
Proof.
  move => A pr l x Hlast. rewrite (dropWhileEnd_spec pr l x). split. exists nil. split. by rewrite cats0.
  by []. by rewrite Hlast.
Qed. 

Require Import mathcomp.algebra.poly.

(** [remTrailZeroes] - used for polynomial construction*)
Section RemZeroes.

Variable F : fieldType.

Local Open Scope ring_scope.

Definition rem_trail_zero (s: seq F) : seq F := dropWhileEnd (fun x => x == 0) s.

Lemma rem_trail_zero_wf: forall s,
  last 1 (rem_trail_zero s) != 0.
Proof.
  move => s. rewrite /rem_trail_zero.
  have: (dropWhileEnd (eq_op^~ 0) s) = (dropWhileEnd (eq_op^~ 0) s) by [].
  rewrite (dropWhileEnd_spec _ _ 1) => [[[l1 [Hl1 Hinl1]] Hlast]].
  case Hdrop: (dropWhileEnd (eq_op^~ 0) s) => [/= | h t /=].
  - apply GRing.oner_neq0.
  - rewrite Hdrop in Hlast. by apply Hlast.
Qed.

Lemma rem_trail_zero_nth: forall s i,
  nth 0 s i = nth 0 (rem_trail_zero s) i.
Proof.
  move => s i. rewrite /rem_trail_zero.
  have: (dropWhileEnd (eq_op^~ 0) s) = (dropWhileEnd (eq_op^~ 0) s) by [].
  rewrite (dropWhileEnd_spec _ _ 1) => [[[l1 [Hl1 Hinl1]] Hlast]].
  rewrite {1}Hl1 nth_cat. 
  case Hi: (i < size (dropWhileEnd (eq_op^~ 0) s)).
  - by [].
  - rewrite (@nth_default _ 0 (dropWhileEnd (eq_op^~ 0) s) i). 
    case Hi': (i - size (dropWhileEnd (eq_op^~ 0) s) < size l1).
    + move: Hinl1. rewrite -all_in => /all_nthP Hall. apply /eqP. by apply Hall.
    + by rewrite nth_default // leqNgt Hi'.
    + by rewrite leqNgt Hi.
Qed.

Lemma rem_trail_zero_polyseq: forall (l: seq F),
  polyseq (Poly (rem_trail_zero l)) = (rem_trail_zero l).
Proof.
  move => l. have: polyseq (Poly (Polynomial (rem_trail_zero_wf l))) = rem_trail_zero l by rewrite polyseqK /=.
  by [].
Qed.

Lemma rem_trail_zero_size: forall (l: seq F),
  size (rem_trail_zero l) <= size l.
Proof.
  move => l. apply dropWhileEnd_size.
Qed. 

End RemZeroes.