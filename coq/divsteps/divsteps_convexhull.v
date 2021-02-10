Require Import List.
Require Import QArith.
Require Import Qpower.
Require Import Orders.
Require Import Sorted.
Require Import divsteps_base.
Import ListNotations.

Lemma Dadd_Q : forall x y, Dadd x y == x + y.
Proof.
intros x y.
unfold Dadd.
assert (Hxy := Dalign_lr x y).
destruct (Dalign x y) as [[xm ym] e].
destruct Hxy as [<- <-].
unfold inject_D; simpl.
rewrite inject_Z_plus.
ring.
Qed.

Lemma Dsub_Q : forall x y, Dsub x y == x - y.
Proof.
intros x y.
unfold Dsub.
assert (Hxy := Dalign_lr x y).
destruct (Dalign x y) as [[xm ym] e].
destruct Hxy as [<- <-].
unfold inject_D, Z.sub; simpl.
rewrite inject_Z_plus, inject_Z_opp.
ring.
Qed.

Lemma Dmult_Q : forall x y, Dmult x y == x * y.
Proof.
intros x y.
unfold Dmult, inject_D; simpl.
rewrite inject_Z_mult, Qpower_plus by discriminate.
ring.
Qed.

Lemma Dhalf_Q : forall x, Dhalf x == x / 2.
Proof.
intros x.
unfold Dhalf, inject_D, Z.pred; simpl.
rewrite Qpower_plus, Qmult_assoc by discriminate.
reflexivity.
Qed.

Lemma Dltb_Q : forall x y, Dltb x y = true -> x < y.
Proof.
intros a b.
unfold Dltb, D_as_TTLT.leb, D_as_OrderedTypeAlt.compare.
rewrite D_as_OrderedTypeAlt.compare_sym, Dcompare_Q, Qlt_alt.
case (a ?= b);try discriminate;reflexivity.
Qed.

Definition QQ : Set := Q * Q.
Definition Qsum := fold_right Qplus 0.
Definition Qcombine := 
  fold_right (fun (qp : Q * DD) a =>
             (fst a + fst qp * fst (snd qp), snd a + fst qp * snd (snd qp)))
             (0,0).
Definition QQplus p1 p2 := (fst p1 + fst p2, snd p1 + snd p2).
Definition QQscale c p := (c * fst p, c * snd p).
Definition QQavg c p1 p2 := QQplus (QQscale c p1) (QQscale (1-c) p2).
Definition QQeq (p q : QQ) := fst p == fst q /\ snd p == snd q.
Definition inject_DD (p : DD) : QQ := (inject_D (fst p), inject_D (snd p)).
Coercion inject_DD : DD >-> QQ.

Lemma QQeq_sym : forall p q, QQeq p q -> QQeq q p.
Proof.
intros p q [H0 H1].
unfold QQeq.
auto with *.
Qed.

Hint Rewrite Dcompare_Q Dadd_Q Dmult_Q Dsub_Q : DQ.

Lemma Qsum_app : forall l1 l2, Qsum (l1 ++ l2) == Qsum l1 + Qsum l2.
Proof.
intros l1 l2.
unfold Qsum.
rewrite fold_right_app.
generalize (fold_right Qplus 0 l2); intros q.
induction l1;simpl;[ring|].
rewrite IHl1.
ring.
Qed.

Lemma Qsum_pos : forall l, (forall x, In x l -> 0 <= x) ->
 0 <= Qsum l.
Proof.
induction l;simpl;auto with *.
intros H.
change 0 with (0 + 0).
auto using Qplus_le_compat.
Qed.

Lemma Qsum_mult : forall c l, Qsum (map (Qmult c) l) == c * Qsum l.
Proof.
induction l;simpl;try rewrite IHl; ring.
Qed.

Lemma QQscale_1 : forall p, QQeq (QQscale 1 p) p.
Proof.
intros p.
split;simpl;ring.
Qed.

Lemma QQscale_mult : forall a b p,
  QQeq (QQscale a (QQscale b p)) (QQscale (a*b) p).
Proof.
intros a b p.
split;simpl;ring.
Qed.

Lemma Qcombine_app : forall l1 l2,
  QQeq (Qcombine (l1 ++ l2)) 
       (QQplus (Qcombine l1) (Qcombine l2)).
Proof.
intros l1 l2.
unfold Qcombine.
rewrite fold_right_app.
set (f := fun qp a => _).
generalize (fold_right f (0,0) l2); intros q.
induction l1;simpl;[split;simpl;ring|].
unfold QQeq; simpl.
destruct IHl1 as [-> ->]; simpl.
split;ring.
Qed.

Lemma Qcombine_scale : forall c l,
  QQeq (QQscale c (Qcombine l)) (Qcombine (map (fun x => (c * fst x, snd x)) l)).
Proof.
intros c l.
unfold QQeq; simpl.
induction l;[split;simpl;ring|].
simpl.
destruct IHl as [<- <-].
split;ring.
Qed.

Definition Deq (a b : D) : Prop := Dcompare a b = Eq.
Definition DDeq (a b : DD) : Prop := 
  Deq (fst a) (fst b) /\ Deq (snd a) (snd b).

Lemma Deq_Q : forall x y, Deq x y <-> x == y.
Proof.
intros x y.
unfold Deq.
rewrite Dcompare_Q.
symmetry.
apply Qeq_alt.
Qed.

Lemma DDeq_Q : forall p q : DD, DDeq p q -> QQeq p q.
Proof.
intros [x1 y1] [x2 y2] [H1 H2].
rewrite Deq_Q in *.
split; simpl in *; congruence.
Qed.

Module DD_as_OTF <: OrderedTypeFull := OT_to_Full DDOrder.

(*Opaque point*)
Definition null : DD.
exact (0:D,0:D)%Z.
Qed.

Definition DDreverse x y := DDOrder.lt y x.

Definition Qdet (p1 p2 p3 : QQ) := 
let (x1, y1) := p1 in
let (x2, y2) := p2 in
let (x3, y3) := p3 in
 (x1 * y2 - y1 * x2) +
 (x2 * y3 - y2 * x3) +
 (x3 * y1 - y3 * x1).

Lemma Qdet_opp : forall p q r, - Qdet p q r == Qdet p r q.
Proof.
intros [x1 y1] [x2 y2] [x3 y3].
simpl.
ring.
Qed.

Lemma orientation_det : forall p1 p2 p3,
orientation p1 p2 p3 = (Qdet p1 p2 p3 ?= 0).
Proof.
intros [x1 y1] [x2 y2] [x3 y3].
simpl.
autorewrite with DQ.
destruct Qcompare_spec with
  (x1 * y2 - y1 * x2 + (x2 * y3 - y2 * x3) + (x3 * y1 - y3 * x1)) 0.
* apply Qeq_alt.
  apply Qplus_inj_r with (-((y1 - y3) * (x2 - x3))).
  rewrite Qplus_opp_r.
  rewrite <- H; ring.
* apply -> Qlt_alt.
  apply Qplus_lt_l with (-((y1 - y3) * (x2 - x3))).
  rewrite Qplus_opp_r.
  eapply Qlt_compat;[|reflexivity|apply H].
  ring.
* apply -> Qgt_alt.
  apply <- Qlt_minus_iff.
  eapply Qlt_compat;[reflexivity| |apply H].
  ring.
Qed.

Lemma orientation_dup : forall p q, orientation p q q = Eq.
Proof.
intros [x1 y1] [x2 y2].
rewrite orientation_det, <- Qeq_alt.
simpl.
ring.
Qed.

Lemma orientation_rot : forall p q r,
 orientation p q r = orientation r p q.
Proof.
intros [x1 y1] [x2 y2] [x3 y3].
rewrite !orientation_det.
simpl.
set (a := _ + _).
set (b := _ + _).
setoid_replace a with b; [reflexivity|].
unfold a, b.
ring.
Qed.

Lemma orientation_opp : forall p q r, CompOpp (orientation p q r) = orientation p r q.
Proof.
intros p q r.
rewrite !orientation_det.
rewrite <- Qdet_opp.
generalize (Qdet p r q).
clear p q r.
intros x.
rewrite Qcompare_antisym.
destruct (Qcompare_spec x 0).
* apply Qeq_alt.
  rewrite H.
  ring.
* apply -> Qlt_alt.
  setoid_replace (-x) with (0 + - x) by ring.
  apply -> Qlt_minus_iff.
  assumption.
* apply -> Qgt_alt.
  apply Qlt_minus_iff.
  ring_simplify.
  assumption.
Qed.

Add Morphism orientation with signature DDOrder.eq ==> DDOrder.eq ==> DDOrder.eq ==> eq as orientation_morph.
intros [x1 y1] [x2 y2] [H12a H12b].
intros [x3 y3] [x4 y4] [H34a H34b].
intros [x5 y5] [x6 y6] [H56a H56b].
rewrite !orientation_det; simpl.
apply Deq_Q in H12a,H12b,H34a,H34b,H56a,H56b.
rewrite H12a,H12b,H34a,H34b,H56a,H56b.
reflexivity.
Qed.

Lemma In_DDSet_fromList : forall l (p : DD),
 DDSet.In p (DDSet_fromList l) <->
 exists q : DD, DDeq p q /\ In q l.
Proof.
intros l p.
unfold DDSet_fromList.
rewrite <- fold_left_rev_right.
transitivity (exists q :DD, DDeq p q /\ In q (rev l));
 [|split; intros [q Hq];exists q; assert (H0 := in_rev l q);firstorder].
change DDSet.elt with DD.
induction (rev l);[|split].
* simpl; split; [|intros [q [Hq []]]].
  intros H.
  apply DDSet.empty_spec in H.
  elim H.
* intros Hp.
  apply DDSet.add_spec in Hp.
  destruct Hp as [Hp|Hp].
  exists a;auto with *.
  apply IHl0 in Hp.
  destruct Hp as [q [Hpq Hp]].
  exists q;auto with *.
* intros [q [Hpq Hp]].
  apply DDSet.add_spec.
  destruct Hp as [->|Hp];[left;assumption|right].
  apply IHl0.
  exists q;tauto.
Qed.

Definition make_upper l :=
  fold_right addUpperPoint nil l.
Definition make_lower l :=
  fold_right addLowerPoint nil l.

Definition convexHull_alt : forall s,
 convexHull s =
 DDSet_fromList (make_upper (rev (DDSet.elements s))
              ++ make_lower (rev (DDSet.elements s))).
Proof.
intros s.
unfold convexHull.
apply f_equal.
rewrite !DDSet.fold_spec.
rewrite <- !fold_left_rev_right.
reflexivity.
Qed.

Lemma hd_addUpperPoint : forall a l, 
 addUpperPoint a l = a :: tl (addUpperPoint a l).
Proof.
intros a l.
induction l.
 reflexivity.
simpl.
destruct l as [|b l].
* case (DDOrder.compare _ _); reflexivity.
* case (orientation _ _ _); try reflexivity; apply IHl.
Qed.

Lemma hd_make_upper : forall l, hd null (make_upper l) = hd null l.
Proof.
intros [|a l]; try reflexivity.
simpl.
rewrite hd_addUpperPoint.
reflexivity.
Qed.

Lemma hd_addLowerPoint : forall a l, 
  addLowerPoint a l = a :: tl (addLowerPoint a l).
Proof.
intros a l.
induction l.
 reflexivity.
simpl.
destruct l as [|b l].
* case (DDOrder.compare _ _); reflexivity.
* case (orientation _ _ _); try reflexivity; apply IHl.
Qed.

Lemma hd_make_lower : forall l, hd null (make_lower l) = hd null l.
Proof.
intros [|a l]; try reflexivity.
simpl.
rewrite hd_addLowerPoint.
reflexivity.
Qed.

Fixpoint addUpperPoint_ris (p : DD) (l : list DD) : list DD :=
match l with
| [] => []
| q :: l0 => match l0 with
   | [] => match DDOrder.compare p q with
           | Eq => [q]
           | _ => []
           end
   | r :: _ => match orientation p q r with
                 | Gt => []
                 | _ => q :: addUpperPoint_ris p l0
               end
   end
end.

Fixpoint addLowerPoint_ris (p : DD) (l : list DD) : list DD :=
match l with
| [] => []
| q :: l0 => match l0 with
   | [] => match DDOrder.compare p q with
           | Eq => [q]
           | _ => []
           end
   | r :: _ => match orientation p q r with
                 | Lt => []
                 | _ => q :: addLowerPoint_ris p l0
                 end
   end
end.

Lemma tl_addUpperPoint : forall a l, 
 l = addUpperPoint_ris a l ++ tl (addUpperPoint a l).
Proof.
intros a.
induction l; auto.
simpl.
destruct l as [|b l].
* case (DDOrder.compare _ _); reflexivity.
* case (orientation _ _ _); auto; cbn [app]; congruence.
Qed.

Lemma tl_addLowerPoint : forall a l, 
 l = addLowerPoint_ris a l ++ tl (addLowerPoint a l).
Proof.
intros a.
induction l; auto.
simpl.
destruct l as [|b l].
* case (DDOrder.compare _ _); reflexivity.
* case (orientation _ _ _); auto; cbn [app]; congruence.
Qed.

Lemma SSorted_app : forall A R (l1 l2 : list A),
 StronglySorted R (l1 ++ l2) ->
 StronglySorted R l1 /\ StronglySorted R l2.
Proof.
intros A R l1 l2.
induction l1; simpl; intros H.
* split;auto;constructor.
* inversion_clear H.
  destruct (IHl1 H0) as [Hl1 Hl2].
  split;try constructor;auto.
  apply Forall_app in H1.
  tauto.
Qed.

Lemma Sorted_rev : forall A R (l : list A),
 Sorted R l -> Sorted (fun x y => R y x) (rev l).
Proof.
intros A R.
set (R' := fun x y => _).
assert (H : forall l l' a,
 Sorted R l -> Sorted R' l' -> HdRel R a l -> HdRel R' a l' ->
 Sorted R' (rev l ++ [a] ++ l')).
 intros l.
 induction l; try constructor;auto.
 intros l' a0 Hl Hl' Hal Hal'.
 simpl.
 rewrite <- app_assoc.
 apply IHl.
 inversion_clear Hl; auto.
 constructor; auto.
 inversion_clear Hl; auto.
 constructor; inversion_clear Hal; auto.
intros [|a l] Hl; try constructor.
simpl.
inversion_clear Hl.
apply H; try constructor; auto.
Qed.

Lemma incl_make_upper : forall l,
 incl (make_upper l) l.
Proof.
intros l.
induction l; intros x Hx; auto.
simpl in *.
rewrite hd_addUpperPoint in Hx.
destruct Hx as [<-| Hx];auto.
right.
apply IHl.
rewrite (tl_addUpperPoint a (make_upper l)).
apply in_or_app.
tauto.
Qed.

Lemma incl_make_lower : forall l,
 incl (make_lower l) l.
Proof.
intros l.
induction l; intros x Hx; auto.
simpl in *.
rewrite hd_addLowerPoint in Hx.
destruct Hx as [<-| Hx];auto.
right.
apply IHl.
rewrite (tl_addLowerPoint a (make_lower l)).
apply in_or_app.
tauto.
Qed.

Lemma SSorted_make_upper : forall R l,
 StronglySorted R l ->
 StronglySorted R (make_upper l).
Proof.
intros R l.
induction l; auto.
intros H.
inversion_clear H.
specialize (IHl H0).
simpl.
rewrite hd_addUpperPoint.
rewrite (tl_addUpperPoint a) in IHl.
apply SSorted_app in IHl.
constructor;try tauto.
eapply incl_Forall;[|apply H1].
eapply incl_tran;[|apply incl_make_upper].
rewrite (tl_addUpperPoint a).
auto with *.
Qed.

Lemma SSorted_make_lower : forall R l,
 StronglySorted R l ->
 StronglySorted R (make_lower l).
Proof.
intros R l.
induction l; auto.
intros H.
inversion_clear H.
specialize (IHl H0).
simpl.
rewrite hd_addLowerPoint.
rewrite (tl_addLowerPoint a) in IHl.
apply SSorted_app in IHl.
constructor;try tauto.
eapply incl_Forall;[|apply H1].
eapply incl_tran;[|apply incl_make_lower].
rewrite (tl_addLowerPoint a).
auto with *.
Qed.

Definition in_between p a b := 
 exists c, 0 <= c <= 1 /\ QQeq p (QQavg c a b).

Definition in_convex_hull (x : QQ) (s : DDSet.t) : Prop :=
exists l : list (Q * DD),
 (forall q p, In (q, p) l -> 0 <= q /\ DDSet.In p s) /\
 Qsum (map fst l) == 1 /\
 QQeq (Qcombine l) x.

Lemma in_convex_hull_Empty : forall {x}, ~in_convex_hull x DDSet.empty.
Proof.
intros s [[|[q d]] [H0 [H1 [H2 H3]]]];[discriminate|].
destruct (H0 q d); auto with *.
auto using (@DDSet.empty_spec d).
Qed.

Lemma in_convex_hull_morph1 : forall p1 p2 s,
 QQeq p1 p2 ->
 in_convex_hull p1 s ->
 in_convex_hull p2 s.
Proof.
intros p1 p2 s [Hp1 Hp2] [l Hl].
exists l.
split; try tauto.
split; try tauto.
unfold QQeq.
rewrite <- Hp1, <- Hp2.
fold (QQeq (Qcombine l) p1).
tauto.
Qed.

Lemma in_convex_hull_morph2 : forall p s1 s2,
 DDSet.eq s1 s2 ->
 in_convex_hull p s1 ->
 in_convex_hull p s2.
Proof.
intros p s1 s2 Hs [l Hl].
exists l.
split; try tauto.
intros a b H.
destruct Hl as [Hl _].
destruct (Hl a b H).
split; try tauto.
apply Hs.
assumption.
Qed.

Lemma in_in_convex_hull : forall (p:DD) s,
 DDSet.In p s -> in_convex_hull p s.
Proof.
intros p s Hp.
exists ((1,p)::nil);split;[|split].
* intros q0 p0 [Hqp|[]].
  injection Hqp; intros <- <-; clear Hqp.
  split; auto with *.
* reflexivity.
* unfold QQeq in *.
  simpl;split;ring.
Qed.

Lemma in_convex_hull_subset : forall q s1 s2,
 DDSet.Subset s1 s2 -> in_convex_hull q s1 ->
 in_convex_hull q s2.
Proof.
intros q s1 s2 Hs [l H].
unfold DDSet.Subset in Hs.
exists l;split;[|split]; firstorder.
Qed.

Lemma in_convex_hull_singleton : forall q (p:DD),
 in_convex_hull q (DDSet.add p DDSet.empty) ->
 QQeq q p.
Proof.
intros q p [l [H0 [H1 H2]]].
unfold QQeq.
destruct H2 as [<- <-].
setoid_replace (fst p:Q) with (1*(fst p)) by ring.
setoid_replace (snd p:Q) with (1*(snd p)) by ring.
rewrite <- H1; clear H1.
induction l;simpl;[split;ring|].
destruct IHl as [-> ->]; auto with *.
specialize (H0 (fst a) (snd a) (or_introl (surjective_pairing a))).
destruct H0 as [_ H0].
apply DDSet.add_spec in H0.
destruct H0 as [[H0 H1]|H0];
 [apply Deq_Q in H0, H1; rewrite H0, H1; split; ring|].
apply DDSet.mem_spec in H0.
discriminate.
Qed.

Lemma QQavg_in_convex_hull : forall c p1 p2 s,
  0 <= c <= 1 ->
  in_convex_hull p1 s ->
  in_convex_hull p2 s ->
  in_convex_hull (QQavg c p1 p2) s.
Proof.
intros c p1 p2 s Hc [l1 Hp1] [l2 Hp2].
pose (f := fun c (x : Q * DD) => (c * fst x, snd x)).
pose (l1' := map (f c) l1).
pose (l2' := map (f (1-c)) l2).
exists (l1' ++ l2').
split;[|split].
assert (Hc' : 0 <= 1 - c) by
 (apply -> Qle_minus_iff; tauto).
* intros q p Hqp.
  apply in_app_or in Hqp.
  destruct Hp1 as [Hp1 _].
  destruct Hp2 as [Hp2 _].
  destruct Hqp as [Hqp|Hqp];split;
    apply in_map_iff in Hqp;
    destruct Hqp as [[x y] [Hx1 Hx2]];
    injection Hx1; intros <- <-;
    try apply Qmult_le_0_compat; firstorder.
* destruct Hp1 as [_ [Hp1 _]].
  destruct Hp2 as [_ [Hp2 _]].
  rewrite map_app.
  unfold l1', l2'.
  rewrite !map_map.
  change (fun x => fst (f c x)) with (fun x : Q * DD => c * fst x).
  change (fun x => fst (f (1 - c) x)) with (fun x : Q * DD => (1 - c) * fst x).
  rewrite <- (map_map _ (Qmult (1-c))), <- map_map.
  rewrite Qsum_app, !Qsum_mult, Hp1, Hp2.
  ring.
* unfold QQeq; simpl.
  destruct Hp1 as [_ [_ [<- <-]]].
  destruct Hp2 as [_ [_ [<- <-]]].
  destruct (Qcombine_app l1' l2') as [-> ->].
  simpl.
  destruct (Qcombine_scale c l1) as [-> ->].
  destruct (Qcombine_scale (1-c) l2) as [-> ->].
  fold (f c) (f (1-c)) l1' l2'.
  split; ring.
Qed.

Inductive OnPath (p : QQ) : list DD -> Prop :=
| OnPathTl : forall a l, OnPath p l -> OnPath p (a::l)
| OnPathBetween : forall (a b : DD) l, in_between p (a:QQ) (b:QQ) -> OnPath p (a::b::l).

Lemma incl_DDSet_fromList : forall l1 l2,
 incl l1 l2 ->
 DDSet.Subset (DDSet_fromList l1) (DDSet_fromList l2).
Proof.
intros p l1 l2 H Hq.
rewrite In_DDSet_fromList in *.
destruct Hq as [r [Hqr Hr]].
exists r;split;auto with *.
Qed.

Lemma OnPathConvex : forall p l,
  OnPath p l -> in_convex_hull p (DDSet_fromList l).
Proof.
intros p l H.
induction H.
* eapply in_convex_hull_subset;[|apply IHOnPath].
  apply incl_DDSet_fromList.
  auto with *.
* destruct H as [c [Hc Hp]].
  exists [(c,a);((1-c),b)];split;[intros q r [Hqr|[Hqr|[]]];injection Hqr; intros <- <-; clear Hqr|split].
  + split; try tauto.
    rewrite In_DDSet_fromList.
    exists a;repeat split;auto with *.
  + split;[apply -> Qle_minus_iff;tauto|].
    rewrite In_DDSet_fromList.
    exists b;repeat split;auto with *.
  + simpl;ring.
  + unfold QQeq;destruct Hp as [-> ->].
    simpl;split;ring.
Qed.

Definition under p l := exists q, OnPath q l /\ fst p == fst q /\ snd p <= snd q.

Lemma in_under : forall (p : DD) (l : list DD),
 In p l -> under (p:QQ) l \/ l = [p].
Proof.
intros p l.
induction l;try contradiction.
intros [->|H].
* destruct l;[right;reflexivity|].
  left.
  exists p; repeat split; auto with *.
  apply OnPathBetween.
  exists 1; repeat split;auto with *;simpl;ring.
* left.
  specialize (IHl H).
  destruct IHl as [[q H0]| ->].
   exists q;split;[apply OnPathTl|]; tauto.
  exists p; repeat split; auto with *.
  apply OnPathBetween.
  exists 0; repeat split;auto with *;simpl;ring.
Qed.

Lemma DDorder_fst : forall a b, DDOrder.lt a b -> fst a <= fst b.
Proof.
intros a b H.
rewrite Qle_lteq.
destruct H as [H|[H _]];[left|right].
* rewrite Qlt_alt, <- Dcompare_Q; auto.
* rewrite Qeq_alt, <- Dcompare_Q; auto.
Qed.

Lemma DDorder_snd : forall a b, DDOrder.lt a b -> fst a == fst b -> snd a < snd b.
Proof.
intros a b H H0.
destruct H as [H|[H H']].
* change (Dcompare (fst a) (fst b) = Lt) in H.
  rewrite Dcompare_Q, <- Qlt_alt in H.
  apply Qlt_not_eq in H.
  contradiction.
* rewrite Qlt_alt, <- Dcompare_Q; auto.
Qed.

Lemma under_addUpperPoint : forall p a l,
 StronglySorted DDreverse (a :: l) ->
 under p (a::l) -> under p (addUpperPoint a l).
Proof.
intros p a l.
induction l.
* intros Hsort [q [HPath [Hpq1 Hpq2]]].
  inversion_clear HPath;inversion H.
* rename a0 into b.
  intros Hsort H.
  simpl.
  destruct l as [|c l].
   simpl.
   destruct (DDOrder.compare_spec a b); auto.
   inversion_clear Hsort.
   inversion_clear H2.
   change (DDOrder.lt b a) in H3.
   rewrite H0 in H3.
   destruct DDOrder.lt_strorder.
   elim (StrictOrder_Irreflexive b H3).
  compare (orientation a b c) Gt;[intros ->; auto|].
   intros Horient.
   cut (under p (addUpperPoint a (c :: l))).
    intros;case (orientation a b c);try contradiction; auto.
   apply IHl.
    inversion_clear Hsort.
    inversion_clear H0.
    inversion_clear H1.
    constructor; auto.
   destruct H as [q [HPath [Hpq1 Hpq2]]].
     cut (under q (a :: c :: l)).
     intros [r [Hr [Heq1 Heq2]]].
     exists r;repeat split;auto;eauto with *.
    clear Hpq1 Hpq2 p IHl.
    change DD in a,b,c.
    assert (Hb : under (b:QQ) [a;c]).
     inversion_clear Hsort.
     inversion_clear H0.
     inversion_clear H2.
     clear H3.
     inversion_clear H.
     clear H2.
     inversion_clear H3.
     clear H2. 
     assert (Hac : fst c <= fst a).
      apply DDorder_fst.
      assumption.
     rewrite Qle_lteq in Hac.
     destruct Hac as [Hac|Hac].
     + rewrite Qlt_minus_iff in Hac.
       pose (d := ((fst b - fst c)/(fst a - fst c))).
       assert (Hd0 : 0 <= d).
        apply Qle_shift_div_l; auto.
        ring_simplify (0 * (fst a - fst c)).
        apply -> Qle_minus_iff.
        auto using DDorder_fst.
       assert (Hd1 : d <= 1).
        apply Qle_shift_div_r; auto.
        ring_simplify (1 * (fst a - fst c)).
        apply Qle_minus_iff.
        ring_simplify.
        apply -> Qle_minus_iff.
        auto using DDorder_fst.
       exists (QQavg d (a:QQ) (c:QQ)).
       simpl; repeat split.
         apply OnPathBetween.
         exists d;repeat split;auto.
        unfold d;field;auto with *.
       rewrite orientation_rot in Horient.
       destruct a as [a1 a2]; destruct b as [b1 b2]; destruct c as [c1 c2].
       unfold orientation in Horient.
       autorewrite with DQ in Horient.
       rewrite <- Qle_alt in Horient.
       simpl in *.
       setoid_replace (d * a2 + (1 - d) * c2) with (((b1 - c1)*a2 + (a1 - b1)*c2)/(a1 - c1)) 
         by (unfold d;field;auto with *).
       apply Qle_shift_div_l; auto with *.
       rewrite Qle_minus_iff in *.
       eapply Qle_trans;[apply Horient|].
       rewrite Qle_minus_iff.
       ring_simplify.
       auto with *.
     + exists a.
       split.
        apply OnPathBetween.
        exists 1;repeat split;simpl;auto with *; ring.
       assert (Hab : fst b == fst a).
        apply Qle_antisym.
         apply DDorder_fst; auto.
        rewrite <- Hac.
        apply DDorder_fst; auto.
       split;auto.
       apply Qlt_le_weak.
       apply DDorder_snd; auto.
  + destruct Hb as [r [Hr [Hr1 Hr2]]].
    inversion_clear Hr;[inversion_clear H; inversion_clear H0|].
    inversion_clear HPath;[inversion_clear H0|].
    - exists q;split;auto with *.
      apply OnPathTl; assumption.
    - destruct H as [x [Hx Hr]].
      destruct H1 as [y [Hy Hq]].
      exists (QQavg y (r:QQ) (c:QQ)); split;simpl.
        apply OnPathBetween.
        destruct Hx as [Hx0 Hx1].
        destruct Hy as [Hy0 Hy1].
        exists (x*y).
        unfold QQeq; simpl.
        destruct Hr as [-> ->]; simpl.
        repeat split; try ring; auto using Qmult_le_0_compat.
        rewrite Qle_lteq in Hx0.
        destruct Hx0 as [Hx0|<-];[|ring_simplify;auto with *].
        rewrite <- (Qmult_le_l _ _ x) in Hy1 by assumption.
        ring_simplify in Hy1.
        eauto with *.
       destruct Hq as [-> ->]; simpl.
       split;[rewrite Hr1;ring|].
       rewrite Qle_minus_iff in Hr2|-*.
       ring_simplify.
       setoid_replace (y * snd r + -1 * y * snd b) with (y * (snd r + - snd b)) by ring.
       destruct Hy;apply Qmult_le_0_compat; auto with *.
    - destruct H as [x [Hx Hr]].
      destruct H0 as [y [Hy Hq]].
      exists (QQavg y (a:QQ) (r:QQ)); split;simpl.
        apply OnPathBetween.
        destruct Hx as [Hx0 Hx1].
        destruct Hy as [Hy0 Hy1].
        exists (x + y*(1 - x)).
        unfold QQeq; simpl.
        destruct Hr as [-> ->]; simpl.
        repeat split; try ring.
         change 0 with (0 + 0).
         apply Qplus_le_compat; auto.
         apply Qmult_le_0_compat; auto.
         rewrite Qle_minus_iff in Hx1; auto.
        rewrite Qle_minus_iff.
        setoid_replace (1 + - (x + y * (1 - x))) with ((1 - x)*(1 - y)) by ring.
        rewrite Qle_minus_iff in Hx1, Hy1.
        apply Qmult_le_0_compat; auto.
       destruct Hq as [-> ->]; simpl.
       split;[rewrite Hr1;ring|].
       rewrite Qle_minus_iff in Hr2|-*.
       ring_simplify.
       setoid_replace (-1 * y * snd r + y * snd b + snd r + -1 * snd b) with ((1-y) * (snd r + - snd b)) by ring.
       destruct Hy as [Hy0 Hy1].
       rewrite Qle_minus_iff in Hy1.
       apply Qmult_le_0_compat; auto with *.
Qed.

Lemma under_make_upper : forall (p:DD) l,
 StronglySorted DDreverse l ->
 In p l ->
 under (p:QQ) (make_upper l) \/ l = [p].
Proof.
intros p.
induction l; try contradiction.
intros Hsort H.
simpl.
destruct l as [|b l].
 destruct H as [->|[]].
 right;reflexivity.
left.
apply under_addUpperPoint.
 inversion_clear Hsort.
 constructor; auto using SSorted_make_upper.
 eapply incl_Forall;[|apply H1].
 apply incl_make_upper.
destruct l as [|c l].
 simpl.
 apply in_under in H.
 destruct H;auto;discriminate.
destruct H as [->|H].
 assert (H0 : In p (p :: make_upper (b :: c :: l))) by auto with *.
 apply in_under in H0.
 destruct H0 as [H0|H0];auto.
 simpl in H0.
 rewrite hd_addUpperPoint in H0.
 discriminate.
inversion_clear Hsort.
specialize (IHl H0 H).
destruct IHl as [[q Hq]|IHl];try discriminate.
exists q;split;[apply OnPathTl|]; tauto.
Qed.

Definition over p l := exists q, OnPath q l /\ fst p == fst q /\ snd q <= snd p.

Lemma in_over : forall (p : DD) (l : list DD),
 In p l -> over (p:QQ) l \/ l = [p].
Proof.
intros p l.
induction l;try contradiction.
intros [->|H].
* destruct l;[right;reflexivity|].
  left.
  exists p; repeat split; auto with *.
  apply OnPathBetween.
  exists 1; repeat split;auto with *;simpl;ring.
* left.
  specialize (IHl H).
  destruct IHl as [[q H0]| ->].
   exists q;split;[apply OnPathTl|]; tauto.
  exists p; repeat split; auto with *.
  apply OnPathBetween.
  exists 0; repeat split;auto with *;simpl;ring.
Qed.

Lemma over_addLowerPoint : forall p a l,
 StronglySorted DDreverse (a :: l) ->
 over p (a::l) -> over p (addLowerPoint a l).
Proof.
intros p a l.
induction l.
* intros Hsort [q [HPath [Hpq1 Hpq2]]].
  inversion_clear HPath;inversion H.
* rename a0 into b.
  intros Hsort H.
  simpl.
  destruct l as [|c l].
   simpl.
   destruct (DDOrder.compare_spec a b); auto.
   inversion_clear Hsort.
   inversion_clear H2.
   change (DDOrder.lt b a) in H3.
   rewrite H0 in H3.
   destruct DDOrder.lt_strorder.
   elim (StrictOrder_Irreflexive b H3).
  compare (orientation a b c) Lt;[intros ->; auto|].
   intros Horient.
   cut (over p (addLowerPoint a (c :: l))).
    intros;case (orientation a b c);try contradiction; auto.
   apply IHl.
    inversion_clear Hsort.
    inversion_clear H0.
    inversion_clear H1.
    constructor; auto.
   destruct H as [q [HPath [Hpq1 Hpq2]]].
     cut (over q (a :: c :: l)).
     intros [r [Hr [Heq1 Heq2]]].
     exists r;repeat split;auto;eauto with *.
    clear Hpq1 Hpq2 p IHl.
    change DD in a,b,c.
    assert (Hb : over (b:QQ) [a;c]).
     inversion_clear Hsort.
     inversion_clear H0.
     inversion_clear H2.
     clear H3.
     inversion_clear H.
     clear H2.
     inversion_clear H3.
     clear H2. 
     assert (Hac : fst c <= fst a).
      apply DDorder_fst.
      assumption.
     rewrite Qle_lteq in Hac.
     destruct Hac as [Hac|Hac].
     + rewrite Qlt_minus_iff in Hac.
       pose (d := ((fst b - fst c)/(fst a - fst c))).
       assert (Hd0 : 0 <= d).
        apply Qle_shift_div_l; auto.
        ring_simplify (0 * (fst a - fst c)).
        apply -> Qle_minus_iff.
        auto using DDorder_fst.
       assert (Hd1 : d <= 1).
        apply Qle_shift_div_r; auto.
        ring_simplify (1 * (fst a - fst c)).
        apply Qle_minus_iff.
        ring_simplify.
        apply -> Qle_minus_iff.
        auto using DDorder_fst.
       exists (QQavg d (a:QQ) (c:QQ)).
       simpl; repeat split.
         apply OnPathBetween.
         exists d;repeat split;auto.
        unfold d;field;auto with *.
       rewrite orientation_rot in Horient.
       destruct a as [a1 a2]; destruct b as [b1 b2]; destruct c as [c1 c2].
       unfold orientation in Horient.
       autorewrite with DQ in Horient.
       rewrite <- Qge_alt in Horient.
       simpl in *.
       setoid_replace (d * a2 + (1 - d) * c2) with (((b1 - c1)*a2 + (a1 - b1)*c2)/(a1 - c1)) 
         by (unfold d;field;auto with *).
       apply Qle_shift_div_r; auto with *.
       rewrite Qle_minus_iff in *.
       eapply Qle_trans;[apply Horient|].
       rewrite Qle_minus_iff.
       ring_simplify.
       auto with *.
     + exists c.
       split.
        apply OnPathBetween.
        exists 0;repeat split;simpl;auto with *; ring.
       assert (Hab : fst c == fst b).
        apply Qle_antisym.
         apply DDorder_fst; auto.
        rewrite Hac.
        apply DDorder_fst; auto.
       split;auto with *.
       apply Qlt_le_weak.
       apply DDorder_snd; auto.
  + destruct Hb as [r [Hr [Hr1 Hr2]]].
    inversion_clear Hr;[inversion_clear H; inversion_clear H0|].
    inversion_clear HPath;[inversion_clear H0|].
    - exists q;split;auto with *.
      apply OnPathTl; assumption.
    - destruct H as [x [Hx Hr]].
      destruct H1 as [y [Hy Hq]].
      exists (QQavg y (r:QQ) (c:QQ)); split;simpl.
        apply OnPathBetween.
        destruct Hx as [Hx0 Hx1].
        destruct Hy as [Hy0 Hy1].
        exists (x*y).
        unfold QQeq; simpl.
        destruct Hr as [-> ->]; simpl.
        repeat split; try ring; auto using Qmult_le_0_compat.
        rewrite Qle_lteq in Hx0.
        destruct Hx0 as [Hx0|<-];[|ring_simplify;auto with *].
        rewrite <- (Qmult_le_l _ _ x) in Hy1 by assumption.
        ring_simplify in Hy1.
        eauto with *.
       destruct Hq as [-> ->]; simpl.
       split;[rewrite Hr1;ring|].
       rewrite Qle_minus_iff in Hr2|-*.
       ring_simplify.
       setoid_replace (y * snd b + -1 * y * snd r) with (y * (snd b + - snd r)) by ring.
       destruct Hy;apply Qmult_le_0_compat; auto with *.
    - destruct H as [x [Hx Hr]].
      destruct H0 as [y [Hy Hq]].
      exists (QQavg y (a:QQ) (r:QQ)); split;simpl.
        apply OnPathBetween.
        destruct Hx as [Hx0 Hx1].
        destruct Hy as [Hy0 Hy1].
        exists (x + y*(1 - x)).
        unfold QQeq; simpl.
        destruct Hr as [-> ->]; simpl.
        repeat split; try ring.
         change 0 with (0 + 0).
         apply Qplus_le_compat; auto.
         apply Qmult_le_0_compat; auto.
         rewrite Qle_minus_iff in Hx1; auto.
        rewrite Qle_minus_iff.
        setoid_replace (1 + - (x + y * (1 - x))) with ((1 - x)*(1 - y)) by ring.
        rewrite Qle_minus_iff in Hx1, Hy1.
        apply Qmult_le_0_compat; auto.
       destruct Hq as [-> ->]; simpl.
       split;[rewrite Hr1;ring|].
       rewrite Qle_minus_iff in Hr2|-*.
       ring_simplify.
       setoid_replace (-1 * y * snd b + y * snd r + snd b + -1 * snd r) with 
         ((1-y) * (snd b + - snd r)) by ring.
       destruct Hy as [Hy0 Hy1].
       rewrite Qle_minus_iff in Hy1.
       apply Qmult_le_0_compat; auto with *.
Qed.

Lemma over_make_lower : forall (p:DD) l,
 StronglySorted DDreverse l ->
 In p l ->
 over (p:QQ) (make_lower l) \/ l = [p].
Proof.
intros p.
induction l; try contradiction.
intros Hsort H.
simpl.
destruct l as [|b l].
 destruct H as [->|[]].
 right;reflexivity.
left.
apply over_addLowerPoint.
 inversion_clear Hsort.
 constructor; auto using SSorted_make_lower.
 eapply incl_Forall;[|apply H1].
 apply incl_make_lower.
destruct l as [|c l].
 simpl.
 apply in_over in H.
 destruct H;auto;discriminate.
destruct H as [->|H].
 assert (H0 : In p (p :: make_lower (b :: c :: l))) by auto with *.
 apply in_over in H0.
 destruct H0 as [H0|H0];auto.
 simpl in H0.
 rewrite hd_addLowerPoint in H0.
 discriminate.
inversion_clear Hsort.
specialize (IHl H0 H).
destruct IHl as [[q Hq]|IHl];try discriminate.
exists q;split;[apply OnPathTl|]; tauto.
Qed.

Lemma over_under : forall p l1 l2,
 under p l1 ->
 over p l2 ->
 in_convex_hull p (DDSet_fromList (l1 ++ l2)).
Proof.
intros p l1 l2 [p1 [Hl1 [Hp11 Hp12]]] [p2 [Hl2 [Hp21 Hp22]]].
apply OnPathConvex in Hl1.
apply OnPathConvex in Hl2.
pose (c := (snd p - snd p2)/(snd p1 - snd p2)).
assert (Hp0 := Qle_trans _ _ _ Hp22 Hp12).
apply Qle_lt_or_eq in Hp0.
assert (Hp : QQeq (QQavg c p1 p2) p).
 unfold QQeq; simpl.
 rewrite <- Hp11, <- Hp21.
 split;[ring|].
 destruct Hp0 as [Hp0|Hp0].
  rewrite Qlt_minus_iff in Hp0.
  unfold c; field; auto with *.
 unfold c; simpl.
 rewrite Hp0; ring_simplify.
 apply Qle_antisym; auto.
 rewrite <- Hp0.
 auto.
eapply in_convex_hull_morph1;[apply Hp|].
apply QQavg_in_convex_hull.
* destruct Hp0 as [Hp0|Hp0].
   rewrite Qlt_minus_iff in Hp0.
   unfold c;split.
    apply Qle_shift_div_l; auto.
    ring_simplify (0 * (snd p1 - snd p2)).
    apply -> Qle_minus_iff; auto.
   apply Qle_shift_div_r; auto.
   rewrite Qle_minus_iff in * .
   ring_simplify.
   assumption.
  unfold c.
  rewrite Hp0.
  setoid_replace (snd p1 - snd p1) with 0 by ring.
  unfold Qdiv.
  change (/0) with 0.
  split;ring_simplify; auto with *.
* eapply in_convex_hull_subset;[|apply Hl1].
  apply incl_DDSet_fromList; auto with *.
* eapply in_convex_hull_subset;[|apply Hl2].
  apply incl_DDSet_fromList; auto with *.
Qed.

Lemma convexHull_sound : forall s (p : DD), DDSet.In p s ->
  in_convex_hull p (convexHull s).
Proof.
intros s p H.
apply DDSet.elements_spec1 in H.
apply SetoidList.InA_rev in H.
apply SetoidList.InA_alt in H.
destruct H as [p0 [Hp H]].
symmetry in Hp.
change DD in p0.
destruct Hp as [Hp0 Hp1].
apply Deq_Q in Hp0,Hp1.
apply in_convex_hull_morph1 with (p0:QQ);[split;auto|].
clear -H.
rename p0 into p.
rewrite convexHull_alt.
assert (HSorted0 := DDSet.elements_spec2 s).
change (Sorted (DDOrder.lt) (DDSet.elements s)) in HSorted0.
assert (HSorted1 := Sorted_rev _ _ _ HSorted0).
set (l := (rev _)) in *.
set (l1 := make_upper _).
set (l2 := make_lower _).
change (Sorted DDreverse l) in HSorted1.
clear HSorted0.
destruct l as [|a [|b l]]; try contradiction.
 apply in_in_convex_hull.
 destruct H as [->|[]].
 simpl.
 apply In_DDSet_fromList.
 exists p;split;auto with *.
 change (DDOrder.eq p p).
 reflexivity.
set (l0 := a :: b :: l) in *.
apply Sorted_StronglySorted in HSorted1;
[|intros x y z Hx Hy;unfold DDreverse in *;simpl;transitivity y;auto].
assert (Hunder := under_make_upper p l0 HSorted1 H).
assert (Hover := over_make_lower p l0 HSorted1 H).
destruct Hunder as [Hunder|Hunder];try discriminate.
destruct Hover as [Hover|Hover];try discriminate.
apply over_under; auto.
Qed.
