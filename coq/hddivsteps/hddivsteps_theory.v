Require Import List.
Require MSetProperties.
Require FMapFacts.
Require Import NArith.
Require Import ZArith.
Require Import QArith.
Require Import Qpower.
Require Import hddivsteps_base.
Require Import hddivsteps_def.
Require Import hddivsteps_convexhull.

Lemma Dred_eq : forall x, Deq (Dred x) x.
Proof.
intros x.
unfold Deq.
rewrite Dcompare_Q.
rewrite <- Qeq_alt.
destruct x as [[|m|m] e]; try reflexivity; simpl;
(revert e; induction m; try reflexivity;
 intros e; simpl;
 rewrite IHm;
 unfold inject_D; simpl;
 rewrite <- Z.add_1_l, Qpower_plus by discriminate; simpl;
 change 2 with (inject_Z 2);
 rewrite Qmult_assoc, <- inject_Z_mult, Z.mul_comm;
 reflexivity).
Qed.

Module DDSetProperties := MSetProperties.OrdProperties DDSet.

Lemma Qsum_map_partition : forall {A} f l (g : A -> Q),
 Qsum (map g l) == Qsum (map g (fst (partition f l))) + Qsum (map g (snd (partition f l))).
Proof.
intros A f l g.
induction l;[reflexivity|].
assert (Hl := surjective_pairing (partition f l)).
simpl (Qsum (map g (a :: l))).
rewrite IHl.
case (f a) eqn:H;
[rewrite (partition_cons1 f a l Hl H)
|rewrite (partition_cons2 f a l Hl H)
];simpl;ring.
Qed.

Lemma Qcombine_partition : forall f l,
 QQeq (Qcombine l) (QQplus (Qcombine (fst (partition f l))) (Qcombine (snd (partition f l)))).
Proof.
intros f l.
induction l;[split;reflexivity|].
assert (Hl := surjective_pairing (partition f l)).
simpl (Qcombine (a :: l)).
unfold QQeq.
destruct IHl as [-> ->].
cbn -[partition].
case (f a) eqn:H;
[rewrite (partition_cons1 f a l Hl H)
|rewrite (partition_cons2 f a l Hl H)
];simpl;split;ring.
Qed.

Lemma in_fst_partition : forall {A} f l (x : A),
  In x (fst (partition f l)) -> f x = true.
Proof.
intros A f l x.
induction l;[intros []|].
simpl.
destruct (partition f l) as [l1 l2].
case (f a) eqn:H;[intros [Hx|Hx]|]; auto.
congruence.
Qed.

Lemma in_snd_partition : forall {A} f l (x : A),
  In x (snd (partition f l)) -> f x = false.
Proof.
intros A f l x.
induction l;[intros []|].
simpl.
destruct (partition f l) as [l1 l2].
case (f a) eqn:H;[|intros [Hx|Hx]]; auto.
congruence.
Qed.

Lemma in_nonempty_convex_hull : forall a s (p : QQ),
  in_convex_hull p (DDSet.add a s) ->
  QQeq p (inject_DD a) \/ (exists c, exists q, 0 <= c <= 1 /\ in_convex_hull q s
                           /\ QQeq p (QQavg c (inject_DD a) q)).
Proof.
intros a s p [l [H0 [H1 H2]]].
pose (f := (fun p:Q * DD => if DDOrder.eq_dec (snd p) a then true else false)).
rewrite (Qsum_map_partition f) in H1.
assert (H2' : QQeq 
        (QQplus (Qcombine (fst (partition f l)))
           (Qcombine (snd (partition f l)))) p)
 by (unfold QQeq;destruct (Qcombine_partition f l) as [<- <-]; auto).
set (l1 := fst (partition f l)) in *.
set (l2 := snd (partition f l)) in *.
set (c := Qsum (map fst l1)) in *.
set (d := Qsum (map fst l2)) in *.
assert (Hl := elements_in_partition f l (surjective_pairing (partition f l))).
assert (H0' : forall q, In q (map fst l2) -> 0 <= q).
 intros q.
 rewrite in_map_iff.
 intros [[x y] [Hx Hx0]].
 eapply or_intror in Hx0.
 apply Hl in Hx0.
 simpl in Hx.
 rewrite Hx in Hx0.
 specialize (H0 _ _ Hx0).
 tauto.
assert (Hl1 : QQeq (Qcombine l1) (QQscale c (inject_DD a))).
 unfold QQeq, QQscale.
 clear.
 assert (Hl1 := in_fst_partition f l).
 fold l1 in Hl1.
 induction l1 as [|[d p] l1 IHl1];[split;reflexivity|].
 unfold c.
 simpl.
 rewrite (Qplus_comm d), !Qmult_plus_distr_l.
 destruct (IHl1 (fun x H => Hl1 x (or_intror H))) as [-> ->].
 specialize (Hl1 _ (or_introl (refl_equal _))).
 unfold f in Hl1.
 destruct (DDOrder.eq_dec _) as [[He Hf]|];[|discriminate].
 apply Deq_Q in He.
 apply Deq_Q in Hf.
 rewrite He, Hf.
 split; reflexivity.

case (Qeq_dec d 0);intros Hd;[left|right].
* unfold QQeq.
  destruct H2' as [<- <-].
  simpl.
  rewrite Hd, Qplus_0_r in H1.
  assert (Hl1' : QQeq (Qcombine l1) (inject_DD a)).
   unfold QQeq.
   setoid_replace (fst (inject_DD a)) with (1 * fst (inject_DD a)) by ring.
   setoid_replace (snd (inject_DD a)) with (1 * snd (inject_DD a)) by ring.
   rewrite <- H1.
   apply Hl1.
  fold l1 l2 in Hl.
  assert (Hl2 : QQeq (Qcombine l2) (0,0)).
   clear -H0' Hd.
   induction l2;[split;reflexivity|].
   unfold QQeq.
   unfold d in Hd; simpl in *.
   assert (H1 : 0 <= fst a0) by firstorder.
   assert (H2 : 0 <= Qsum (map fst l2)) by firstorder using Qsum_pos.
   setoid_replace (fst a0) with 0;
    [rewrite !Qmult_0_l, !Qplus_0_r;
     apply IHl2; try firstorder|];
   apply Qle_antisym;try assumption;
   rewrite <- Hd;
   apply Qle_minus_iff;
   ring_simplify;
   assumption.
   unfold QQeq.
   destruct Hl1' as [-> ->].
   destruct Hl2 as [-> ->].
   simpl; split; ring.
* exists c.
  exists (QQscale (/d) (Qcombine l2)).
  assert (Hd0 : 0 <= d).
   apply Qsum_pos.
   intros z.
   rewrite in_map_iff.
   intros [[z1 z2] [<- Hz]].
   specialize (H0 z1 z2).
   rewrite (elements_in_partition f _ (surjective_pairing (partition f l))) in H0.
   tauto.
  split;[split|split].
+ apply Qsum_pos.
  intros z.
  rewrite in_map_iff.
  intros [[z1 z2] [<- Hz]].
  specialize (H0 z1 z2).
  rewrite (elements_in_partition f _ (surjective_pairing (partition f l))) in H0.
  tauto.
+ rewrite <- H1.
  setoid_replace c with (c + 0) at 1 by ring.
  apply Qplus_le_r.
  assumption.
+ pose (g := fun x => (/ d * fst x, snd x : DD)).
  exists (map g l2).
  apply Qle_lt_or_eq in Hd0.
  destruct Hd0 as [Hd0|Hd0];[|symmetry in Hd0;contradiction].
  split;[|split].
  - clear - H0 Hd0.
    intros q p.
    rewrite in_map_iff.
    intros [[x y] [Hxy Hqp]].
    injection Hxy; intros <- <-; clear Hxy.

    specialize (H0 x y).
    rewrite (elements_in_partition f _ (surjective_pairing (partition f l))) in H0.
    specialize (H0 (or_intror Hqp)).
    split;
     [rewrite Qmult_comm; apply Qle_shift_div_l; auto;
      ring_simplify; tauto|].
    destruct H0 as [_ H0].
    rewrite DDSet.add_spec in H0.
    destruct H0 as [H0|H0];[|assumption].
    apply in_snd_partition in Hqp.
    unfold f in Hqp.
    destruct (DDOrder.eq_dec _) as [Hy|Hy];[discriminate|].
    elim Hy.
    assumption.
  - clearbody l2; clear - Hd.
    rewrite map_map.
    pose (f := fun x => / d * x).
    change (fun x => _) with (fun x : Q * DD => f (fst x)).
    rewrite <- map_map.
    setoid_replace 1 with (d/d) by field;auto.
    unfold d at 1.
    clearbody d; clear - Hd.
    unfold f.
    rewrite Qsum_mult.
    rewrite Qmult_comm.
    reflexivity.
  - clearbody l2 d; clear.
    induction l2;[split;simpl;ring|].
    unfold QQeq; simpl.
    destruct IHl2 as [-> ->];simpl.
    unfold Qdiv.
    split; ring.
+ cut (QQeq (QQplus (Qcombine l1) (Qcombine l2)) 
       (QQavg c (inject_DD a) (QQscale (/ d) (Qcombine l2)))).
   destruct H2' as [H2'1 H2'2].
   symmetry in H2'1.
   symmetry in H2'2.
   intros [Ha Hb].
   split; eauto using Qeq_trans.
  unfold QQavg, QQeq.
  simpl.
  destruct Hl1 as [-> ->]; simpl.
  rewrite <- H1.
  split;field;auto.
Qed.

Lemma in_nested_convex_hull : forall s1 s2 (p : QQ),
  in_convex_hull p s1 ->
  (forall (q :DD) q', QQeq q q' -> DDSet.In q s1 -> in_convex_hull q' s2) ->
  in_convex_hull p s2.
Proof.
intros s1.
induction s1 as [H|s0 s1 IH a _ Hadd] using DDSetProperties.P.set_induction;
[intros;
 eelim in_convex_hull_Empty;
 eapply in_convex_hull_morph2;[|eassumption];
 firstorder using DDSet.empty_spec
|].
intros s2 p H1 H2.
apply DDSetProperties.P.Add_Equal in Hadd.
assert (Hp : in_convex_hull p (DDSet.add a s0)) by
 (eapply in_convex_hull_morph2;[apply Hadd|apply H1]).
apply in_nonempty_convex_hull in Hp.
destruct Hp as [Hp|[c [q [Hc [Hq Hp]]]]].
* apply H2 with a;
   [destruct Hp;split;symmetry;assumption|].
  rewrite Hadd.
  apply DDSet.add_spec; left; reflexivity.
* assert (H2' : forall (q : DD) (q' : QQ),
     QQeq q q' -> DDSet.In q s0 -> in_convex_hull q' s2).
   intros q0 q' Hq0 Hq0s.
   apply H2 with q0; auto.
   rewrite Hadd.
   apply DDSet.add_spec;right; assumption.
  specialize (IH s2 _ Hq H2').
  assert (Ha : in_convex_hull (inject_DD a) s2).
   apply H2 with a;[split;reflexivity|].
   rewrite Hadd.
   apply DDSet.add_spec; left; reflexivity.
  apply in_convex_hull_morph1 with (QQavg c (inject_DD a) q);
   [unfold QQeq in *; split; symmetry; tauto|].
  apply QQavg_in_convex_hull; auto.
Qed.

Lemma in_convex_hull_convexHull : forall s q p,
  in_convex_hull p (DDSet.add q s) ->
  in_convex_hull p (DDSet.add q (convexHull s)).
Proof.
intros s q p H.
apply in_nonempty_convex_hull in H.
destruct H as [H|[c [r [Hc [Hr Hp]]]]].
* apply QQeq_sym in H.
  eapply in_convex_hull_morph1;[apply H|].
  apply in_in_convex_hull;apply DDSet.add_spec;left;reflexivity.
* assert (H : in_convex_hull r (convexHull s)).
   apply in_nested_convex_hull with s;auto.
   intros t0 t1 Ht H.
   eapply in_convex_hull_morph1;[apply Ht|].
   auto using convexHull_sound.
  change DD in q.
  assert (Hp' : QQeq (QQavg c (q:QQ) r) p) by
   (destruct Hp;split;symmetry;assumption).
  eapply in_convex_hull_morph1;[apply Hp'|].
  apply QQavg_in_convex_hull;auto.
  + apply in_in_convex_hull;apply DDSet.add_spec;left;reflexivity.
  + apply in_convex_hull_subset with (convexHull s); auto.
    apply DDSetProperties.P.subset_add_2.
    apply DDSetProperties.P.subset_refl.
Qed.

Definition State_lookup (i : Z) (m : State) :=
  match (ZMap.find i m) with
  | None => DDSet.empty
  | Some s => s
  end.

Lemma State_lookup_join2 : forall p delta i q m,
DDSet.In p (State_lookup delta m) ->
DDSet.In p
  (State_lookup delta (State_join i q m)).
Proof.
intros p delta i q m.
unfold State_lookup.
case (ZMap.find _ _) as [t|] eqn:Hi;
[|intros H; apply DDSet.empty_spec in H; contradiction].
unfold State_join.
destruct (OrdersEx.Z_as_DT.eq_decidable i delta) as [->|Hdelta].
+ rewrite Hi,
          (ZMap.find_1 (ZMap.add_1 _ _ (refl_equal delta))),
          DDSet.union_spec.
  auto.
+ apply ZMap.find_2 in Hi.
  eapply (ZMap.add_2 _ Hdelta) in Hi.
  rewrite (ZMap.find_1 Hi).
  auto.
Qed.

Lemma State_lookup_fromList : forall l q p delta s,
 DDSet.In p (DDSet.add q s) ->
 In (delta, s) l ->
 DDSet.In p (DDSet.add q (State_lookup delta (State_fromList l))).
Proof.
intros l q p delta s Hps Hsl.
rewrite DDSet.add_spec in *.
destruct Hps as [Hps|Hps];[left;assumption|right].
unfold State_fromList.
rewrite <- fold_left_rev_right.
rewrite in_rev in Hsl.
induction (rev l);[contradiction|].
simpl.
destruct Hsl as [->|Hsl];[|auto using State_lookup_join2].
simpl.
unfold State_lookup, State_join.
rewrite (ZMap.find_1 (ZMap.add_1 _ _ (refl_equal delta))).
destruct (ZMap.find _ _);[rewrite DDSet.union_spec|];auto.
Qed.

Lemma State_in_convex_hull_fromList1 : forall l q p delta s,
 in_convex_hull p (DDSet.add q s) ->
 In (delta, s) l ->
 in_convex_hull p (DDSet.add q (State_lookup delta (State_fromList l))).
Proof.
intros l q p delta s [c [Hps1 [Hps2 [Hps3 Hps4]]]] Hsl.
exists c;split;[|repeat split;auto].
intros q' p' Hqp'.
destruct (Hps1 q' p' Hqp') as [Hps11 Hps12].
split; eauto using State_lookup_fromList.
Qed.

Definition Matrix : Set := D * D * D * D.
Definition even_matrix : Matrix :=
  (Dhalf 1, 0:D, 0:D, 1:D)%Z.
Definition odd_pos_matrix : Matrix :=
  (Dhalf 1, Dhalf (-1), 1:D, 0:D)%Z.
Definition odd_nonpos_matrix : Matrix :=
  (Dhalf 1, Dhalf 1, 0:D, 1:D)%Z.
Definition linearD_of (m : Matrix) (p : DD) : DD :=
  let '(a,b,c,d) := m in
  (Dadd (Dmult a (fst p)) (Dmult b (snd p))
  ,Dadd (Dmult c (fst p)) (Dmult d (snd p))).
Definition linearQ_of (m : Matrix) (p : QQ) : QQ :=
  let '(a,b,c,d) := m in
  (a * (fst p) + b * (snd p), c * (fst p) + d * (snd p)).

Lemma even_trans_matrix : forall p,
  DDeq (even_trans p) (linearD_of even_matrix p).
Proof.
intros [x y].
unfold DDeq; simpl.
rewrite !Deq_Q, !Dadd_Q, !Dmult_Q, !Dhalf_Q.
change (inject_D 1%Z:Q) with 1.
change (inject_D 0%Z:Q) with 0.
split;field.
Qed.

Lemma odd_pos_trans_matrix : forall p,
  DDeq (odd_pos_trans p) (linearD_of odd_pos_matrix p).
Proof.
intros [x y].
unfold DDeq, odd_pos_trans.
rewrite Dred_eq; simpl.
rewrite !Deq_Q, !Dadd_Q, !Dmult_Q, !Dhalf_Q, Dsub_Q.
change (inject_D (-1)%Z:Q) with (-1).
change (inject_D 1%Z:Q) with 1.
change (inject_D 0%Z:Q) with 0.
split;field.
Qed.

Lemma odd_nonpos_trans_matrix : forall p,
  DDeq (odd_nonpos_trans p) (linearD_of odd_nonpos_matrix p).
Proof.
intros [x y].
unfold DDeq, odd_nonpos_trans.
rewrite Dred_eq; simpl.
rewrite !Deq_Q, !Dadd_Q, !Dmult_Q, !Dhalf_Q, Dadd_Q.
change (inject_D 1%Z:Q) with 1.
change (inject_D 0%Z:Q) with 0.
split;field.
Qed.

Lemma linearD_of_morph : forall m q1 q2, 
  DDeq q1 q2 -> DDeq (linearD_of m q1) (linearD_of m q2).
Proof.
intros [[[a b] c] d] [x1 y1] [x2 y2] [Hx Hy].
unfold DDeq.
simpl in *.
rewrite !Deq_Q, !Dadd_Q, !Dmult_Q, Hx, Hy in *.
split;reflexivity.
Qed.

Lemma in_DDSet_map : forall trans p s,
 (forall q1 q2, DDeq q1 q2 -> DDeq (trans q1) (trans q2)) ->
 DDSet.In p s ->
 DDSet.In (trans p) (DDSet_map trans s).
Proof.
intros trans [x y] s trans_morph Hps.
unfold DDSet_map.
rewrite DDSet.fold_spec, <- fold_left_rev_right.
rewrite <- DDSet.elements_spec1, <- SetoidList.InA_rev in Hps.
fold DDSet.elt in Hps.
induction (rev (DDSet.elements s));
 [rewrite SetoidList.InA_nil in Hps;elim Hps|simpl].
rewrite DDSet.add_spec.
rewrite SetoidList.InA_cons in Hps.
destruct Hps as [Hps|Hps];[|right;auto].
left.
apply trans_morph.
assumption.
Qed.

Lemma in_convex_hull_map_ext : forall trans m p q s,
 (forall p, DDeq (trans p) (linearD_of m p)) ->
 QQeq (linearQ_of m p) q ->
 in_convex_hull p (DDSet.add (0:D,0:D)%Z s) ->
 in_convex_hull q (DDSet.add (0:D,0:D)%Z (DDSet_map trans s)).
Proof.
intros trans m p p' s trans_ext Hp [l [Hl1 [Hl2 [Hl3 Hl4]]]].
assert (trans_morph : forall q1 q2, DDeq q1 q2 -> DDeq (trans q1) (trans q2)).
 intros q1 q2 Hq.
 destruct (trans_ext q1) as [trans_ext11 trans_ext12].
 destruct (trans_ext q2) as [trans_ext21 trans_ext22].
 unfold DDeq.
 rewrite !Deq_Q in *.
 rewrite trans_ext11, trans_ext21, trans_ext12, trans_ext22.
 rewrite <-!Deq_Q.
 apply (linearD_of_morph m _ _ Hq).
exists (map (fun cp => (fst cp, linearD_of m (snd cp))) l);split;[|split].
* intros q [f g] H.
  apply in_map_iff in H.
  destruct H as [[x y] [Hx1 Hx2]].
  simpl in Hx1.
  injection Hx1; intros <- <-.
  destruct (Hl1 _ _ Hx2).
  specialize (trans_ext y).
  change (DDOrder.eq (trans y) (linearD_of m y)) in trans_ext.
  rewrite <- trans_ext.
  split;auto.
  rewrite DDSet.add_spec in *.
  destruct H0 as [[H0l H0r]|H0];[left|right;auto using in_DDSet_map].
  destruct y as [yl yr].
  apply Deq_Q in H0l; apply Deq_Q in H0r.
  simpl in *.
  rewrite trans_ext.
  set (trans' := linearD_of m).
  change (Deq (fst (trans' (yl, yr))) 0%Z /\ Deq (snd (trans' (yl, yr))) 0%Z).
  destruct m as [[[ma mb] mc] md].
  simpl.
  rewrite !Deq_Q, !Dadd_Q, !Dmult_Q, H0l, H0r.
  change (0%Z:Q) with 0.
  split; ring.
* rewrite <- Hl2.
  clear - l.
  induction l;[reflexivity|].
  simpl.
  rewrite IHl.
  reflexivity.
* clear - Hl3 Hl4 Hp.
  destruct p as [x y].
  destruct Hp as [Hp1 Hp2].
  destruct m as [[[a b] c] d].
  unfold QQeq.
  simpl in *.
  rewrite <- Hp1, <- Hp2, <- Hl3, <- Hl4; clear Hp1 Hp2 Hl3 Hl4.
  induction l;simpl;[split; ring|].
  destruct IHl as [-> ->].
  rewrite !Dadd_Q, !Dmult_Q.
  split; ring.
Qed.

Lemma inject_Z_half : forall a : Z, Z.Even a -> inject_Z (a / 2)%Z == inject_Z a / 2.
Proof.
intros a Ha.
rewrite <- Zeven_equiv in Ha.
rewrite (Zeven_div2 _ Ha) at 2.
rewrite inject_Z_mult.
change (inject_Z 2) with 2.
rewrite <- Qmult_comm, Qdiv_mult_l, Z.div2_div by discriminate.
reflexivity.
Qed.

Lemma inject_Z_D_Q : forall a : Z, (a:D) == inject_Z a.
intros a.
unfold inject_D.
simpl.
ring.
Qed.

Lemma Zodd_opp : forall a : Z, Zodd a -> Zodd (-a).
Proof.
intros.
rewrite Zodd_ex_iff in *.
destruct H as [m ->].
exists (-m-1)%Z.
ring.
Qed.

Lemma in_narrow : forall (M g f : Z) s,
 (0 < M)%Z ->
 narrow M s = true ->
 in_convex_hull (g / M, f / M) (DDSet.add (0:D,0:D)%Z s) ->
 g = 0%Z.
Proof.
intros M g f s HM Hs Hg.
rewrite Zlt_Qlt, <- !inject_Z_D_Q in HM.
change (0%Z:Q) with 0 in HM.
cut (-1 < M * (g / M) /\ M * (g / M) < 1).
  rewrite Qmult_div_r by auto with *.
  change (-1) with ((-1)%Z:Q).
  change 1 with (1%Z:Q).
  rewrite !inject_Z_D_Q, <- !Zlt_Qlt.
  auto with *.
set (zero := (0:D,0:D)%Z).
assert (Hnarrow : forall x y, DDSet.In (x, y) (DDSet.add zero s) -> -1 < M*x /\ M*x < 1).
 apply Qlt_le_weak in HM.
 intros x y Hxy.
 apply DDSet.add_spec in Hxy.
 destruct Hxy as [[Hxyl Hxyr]|Hxy].
  apply Deq_Q in Hxyl, Hxyr; simpl in *.
  rewrite Hxyl.
  change (0%Z:Q) with 0.
  rewrite Qmult_0_r, !Qlt_alt.
  split;reflexivity.
 unfold narrow in Hs.
 case (DDSet.min_elt s) as [[l l0]|] eqn:Hmin;
  [|apply DDSet.min_elt_spec3 in Hmin;elim (Hmin _ Hxy)].
 case (DDSet.max_elt s) as [[h h0]|] eqn:Hmax;
  [|apply DDSet.max_elt_spec3 in Hmax;elim (Hmax _ Hxy)].
 apply (fun H => DDSet.min_elt_spec2 H Hxy) in Hmin.
 apply (fun H => DDSet.max_elt_spec2 H Hxy) in Hmax.
 apply andb_prop in Hs.
 destruct Hs as [Hs1 Hs2].
 change (~(Dcompare x l = Lt \/ (Dcompare x l = Eq /\ Dcompare y l0 = Lt))) in Hmin.
 change (~(Dcompare h x = Lt \/ (Dcompare h x = Eq /\ Dcompare h0 y = Lt))) in Hmax.
 apply Dltb_Q in Hs1.
 apply Dltb_Q in Hs2.
 change ((-1)%Z:Q) with (-1) in Hs1.
 change ((1)%Z:Q) with 1 in Hs2.
 rewrite Dmult_Q, !Dcompare_Q, <- Qeq_alt, <- !Qlt_alt in *.
 assert (Hmin' : l <= x) by (apply Qnot_lt_le; tauto).
 assert (Hmax' : x <= h) by (apply Qnot_lt_le; tauto).
 apply (fun H => Qmult_le_compat_r _ _ _ H HM) in Hmin'.
 apply (fun H => Qmult_le_compat_r _ _ _ H HM) in Hmax'.
 rewrite (Qmult_comm M) in *.
 split; eauto using Qle_lt_trans, Qlt_le_trans.
clear Hs.
destruct Hg as [l [Hl1 [Hl2 [Hl3 _]]]].
simpl in Hl3.
rewrite <- Hl3.
pose (l' := filter (fun x => negb (Qle_bool (fst x) 0)) l).
assert (Hl1' : forall (q : Q) (p : DD), In (q, p) l' -> 0 < q /\ q <= 1 /\ DDSet.In p (DDSet.add zero s)).
 intros q p Hqp.
 unfold l' in Hqp.
 rewrite filter_In in Hqp.
 destruct Hqp as [Hqp Hfilter].
 destruct (Hl1 _ _ Hqp).
 repeat split; try tauto;
 [apply in_split in Hqp;
  case (Qlt_le_dec 0 q); auto;
  intros H1;
  rewrite <- Qle_bool_iff in H1;
  simpl in Hfilter;
  rewrite H1 in Hfilter;
  discriminate
 |].
 rewrite <- Hl2.
 clear -Hl1 Hqp.
 apply in_split in Hqp.
 destruct Hqp as [l1 [l2 ->]].
 rewrite map_app, Qsum_app; simpl.
 setoid_replace q with (0 + (q + 0)) at 1 by ring.
 repeat apply Qplus_le_compat; auto with *;
 apply Qsum_pos;
 intros x Hx;
 rewrite in_map_iff in Hx;
 destruct Hx as [[y1 y2] [<- Hy]];
 specialize (Hl1 y1 y2);
 assert (H := in_or_app l1 ((q,p)::l2) (y1, y2));
 simpl in H;
 tauto.
assert (Hl2' : Qsum (map fst l') == 1 /\ fst (Qcombine l') == fst (Qcombine l)).
 rewrite <- Hl2.
 clear -Hl1.
 induction l;[split;reflexivity|].
 unfold l'; simpl.
 destruct IHl as [<- <-];[firstorder|].
 specialize (Hl1 (fst a) (snd a)).
 rewrite <-surjective_pairing in Hl1.
 specialize (Hl1 (or_introl (refl_equal _))).
 destruct Hl1 as [Hl1 _].
 case (Qle_bool (fst a) 0) eqn:Ha;[|split;reflexivity].
 rewrite Qle_bool_iff in Ha.
 simpl.
 rewrite (Qle_antisym _ _ Ha Hl1).
 split;ring.
change (-1) with (Qopp 1).
destruct Hl2' as [Hl2' <-].
rewrite <- Hl2'.
case l' as [|a' l'];[discriminate|].
clear Hl1 Hl2 Hl3 Hl2'.
simpl.
rewrite Qopp_plus, Qmult_plus_distr_r, (Qplus_comm (M*_)).
cut (- Qsum (map fst l') <= M * fst (Qcombine l') <= Qsum (map fst l')).
 intros [H1 H2].
 rewrite (Qmult_comm (fst a')).
 setoid_replace (-fst a') with (-1 * fst a') by ring.
 setoid_replace (fst a') with (1 * fst a') at 4 by ring.
 rewrite Qmult_assoc.
 specialize (Hl1' (fst a') (snd a')).
 rewrite <- surjective_pairing in Hl1'.
 destruct Hl1' as [Ha1 [_ Ha2]];auto with *.
 rewrite (surjective_pairing (snd a')) in Ha2.
 specialize (Hnarrow _ _ Ha2).
 split;
 apply Qplus_lt_le_compat; auto;
 apply Qmult_lt_compat_r; tauto.
assert (Hl1 : forall (q : Q) (p : DD),
       In (q, p) l' -> 0 < q /\ q <= 1 /\ DDSet.In p (DDSet.add zero s)) by firstorder.
clear -Hnarrow Hl1.
induction l' as [|[c p] l IHl];simpl;[rewrite Qmult_0_r;auto with *|].
rewrite (Qplus_comm c), Qopp_plus, Qmult_plus_distr_r.
specialize (IHl (fun q p H => Hl1 q p (or_intror H))).
rewrite (Qmult_comm c).
setoid_replace (-c) with (-1 * c) by ring.
setoid_replace c with (1 * c) at 4 by ring.
rewrite Qmult_assoc.
specialize (Hl1 c p (or_introl (refl_equal _))).
destruct Hl1 as [Hc0 [Hc1 Hp]].
rewrite (surjective_pairing p) in Hp.
specialize (Hnarrow _ _ Hp).
split;
apply Qplus_le_compat; try tauto;
apply Qmult_le_compat_r; auto with *;
apply Qlt_le_weak; tauto.
Qed.

Definition in_State (M : Z) (ds : hddivsteps.State) (s : State) : Prop :=
  hddivsteps.g ds = 0%Z \/
  in_convex_hull (hddivsteps.g ds / M, hddivsteps.f ds / M)
   (DDSet.add (0:D,0:D)%Z (State_lookup (hddivsteps.delta ds) s)).

Lemma in_State_step : forall M ds st, (0 < M)%Z -> Z.Odd (hddivsteps.f ds) ->
 in_State M ds st -> in_State M (hddivsteps.step ds) (processDivstep M st).
Proof.
intros M [delta f g] st HM Hf [Hst|Hst];[left; auto using hddivsteps.zero_step|].
rewrite <- Zodd_equiv in Hf.
simpl in *.
set (ds' := hddivsteps.step _).
pose (delta' := hddivsteps.delta ds').
pose (f' := hddivsteps.f ds').
pose (g' := hddivsteps.g ds').
unfold processDivstep.
set (fm2 := fun kv => _).
set (fm1 := fun kv => _).
set (st1 := State_fromList (flat_map fm1 _)).
set (st2 := State_fromList (flat_map fm2 _)).
case (Z.eq_dec g 0) as [Hg0|Hg0];
 [left;unfold ds'; auto using hddivsteps.zero_step|].
case (Z.eq_dec g' 0) as [Hg'0|Hg'0];
 [left;auto|].
assert (H : {s | ZMap.MapsTo delta s st}).
  clear - Hst Hg0 HM.
  unfold State_lookup in Hst.
  case (ZMap.find delta st) as [s|] eqn:Hfind;
    [exists s; auto using ZMap.find_2|].
  apply in_convex_hull_singleton in Hst.
  destruct Hst as [Hst _].
  simpl in Hst.
  rewrite <- inject_Z_injective in Hg0.
  rewrite Zlt_Qlt in HM.
  rewrite <- !inject_Z_D_Q in *.
  apply Qinv_lt_0_compat in HM.
  apply Qmult_integral_l in Hst; auto.
  rewrite Hst in HM.
  discriminate.
destruct H as [s Hs].
pose (divstep_trans :=
  if Z.even g then even_trans
              else if (0 <? delta)%Z then odd_pos_trans else odd_nonpos_trans).
pose (divstep_matrix :=
  if Z.even g then even_matrix
              else if (0 <? delta)%Z then odd_pos_matrix else odd_nonpos_matrix).
set (zero := (0%Z:D,0%Z:D)) in *.
assert (Hst' : in_convex_hull (g' / M, f' / M) (DDSet.add zero (State_lookup delta' st1))).
  assert (Hx := ZMap.elements_1 Hs).
  apply SetoidList.InA_altdef in Hx.
  apply Exists_exists in Hx.
  destruct Hx as [x [Hx1 Hx2]].
  apply State_in_convex_hull_fromList1 with (DDSet_map divstep_trans (snd x)).
  * apply in_convex_hull_map_ext with divstep_matrix (g / M, f / M).
    - intros p. clear.
      case (Z.even g) in *;[apply even_trans_matrix|].
      case (0 <? delta)%Z in *;[apply odd_pos_trans_matrix|].
      apply odd_nonpos_trans_matrix.
    - clear -Hf.
      unfold QQeq, g', f', ds', hddivsteps.step; simpl.
      case (Z.even g) eqn:Hg in *;[apply Zeven_bool_iff in Hg
                                  |apply (f_equal negb) in Hg;
                                   rewrite Z.negb_even in Hg;
                                   apply Zodd_bool_iff in Hg;
                                   case (0 <? delta)%Z in *];simpl;
        rewrite !Dhalf_Q;
        change (inject_D (-1)%Z:Q) with (-1);
        change (inject_D 1%Z:Q) with 1;
        change (inject_D 0%Z:Q) with 0;
        split; try ring;
        unfold Z.sub;
        rewrite !inject_Z_D_Q, inject_Z_half, ?inject_Z_plus, ?inject_Z_opp;
        try (unfold Qdiv; ring);
        apply Zeven_equiv;
        auto using Zodd_plus_Zodd, Zodd_opp.
    - clear -Hst Hs Hx2.
      destruct Hx2 as [_ Hx2].
      replace (snd x) with s.
      unfold State_lookup in Hst.
      rewrite (ZMap.find_1 Hs) in Hst.
      assumption.
  * apply in_flat_map.
    exists x; split; auto.
    clear -Hx2; destruct x; destruct Hx2 as [Hx1 Hx2].
    unfold hddivsteps.step in ds'; cbn -[Z.ltb Z.add Z.sub] in *.
    rewrite <- Hx1.
    case (Z.even g) in *;[left;reflexivity|].
    right;left.
    case (0 <? delta)%Z in *;
    reflexivity.
* clear s Hs.
  assert (H : {s | ZMap.MapsTo delta' s st1}).
   clear - Hst' Hg'0 HM.
   unfold State_lookup in Hst'.
   case (ZMap.find delta' st1) as [s|] eqn:Hfind;
     [exists s; auto using ZMap.find_2|].
   apply in_convex_hull_singleton in Hst'.
   destruct Hst' as [Hst' _].
   simpl in Hst'.
   rewrite <- inject_Z_injective in Hg'0.
   rewrite Zlt_Qlt in HM.
   rewrite <- !inject_Z_D_Q in *.
   apply Qinv_lt_0_compat in HM.
   apply Qmult_integral_l in Hst'; auto.
   rewrite Hst' in HM.
   discriminate.
  destruct H as [s Hs].
  assert (Hx := ZMap.elements_1 Hs).
  apply SetoidList.InA_altdef in Hx.
  apply Exists_exists in Hx.
  destruct Hx as [x [Hx1 Hx2]].
  unfold State_lookup in Hst'.
  rewrite (ZMap.find_1 Hs) in Hst'.
  case (narrow M s) eqn:Hnarrow;
  [left;
   apply (in_narrow _ _ _ _ HM Hnarrow Hst')
  |].
  right.
  fold g' f' delta'.
  apply State_in_convex_hull_fromList1 with (convexHull s).
    auto using in_convex_hull_convexHull.
  apply in_flat_map.
  exists x.
  split; try tauto.
  destruct x as [x0 x1].
  destruct Hx2 as [Hx2 Hx3]; simpl in *.
  rewrite <- Hx2, <- Hx3, Hnarrow.
  auto with *.
Qed.

Module ZMapProperties := FMapFacts.OrdProperties ZMap.

Theorem processDivstep_correct : forall N M f g,
  Z.Odd f ->
  (f <= M)%Z -> (0 <= g <= f)%Z -> 
  ZMap.Empty (N.iter N (processDivstep M) state0) ->
  hddivsteps.g (N.iter N hddivsteps.step (hddivsteps.init f g)) = 0%Z.
Proof.
intros N M f g HM Hf Hg H.
rewrite N2Nat.inj_iter.
rewrite <- N2Nat.inj_iter.
assert (HM0 : (0 < M)%Z).
 eapply Z.lt_le_trans;[|apply Hf].
 apply Z.le_neq.
 split; auto with *.
 intros <-.
 rewrite <- Zodd_equiv in HM.
 contradiction.
assert (HM2 : 0 < M).
 rewrite inject_Z_D_Q.
 change 0 with (inject_Z 0).
 rewrite <- Zlt_Qlt.
 assumption.
cut (in_State M (N.iter N hddivsteps.step (hddivsteps.init f g)) (N.iter N (processDivstep M) state0)).
 intros [H0|H0];auto.
 set (p := (_,_)) in *.
 set (st' := N.iter N hddivsteps.step _) in *.
 unfold State_lookup in H0.
 case (ZMap.find _ _) eqn:Hfind.
  apply ZMap.find_2 in Hfind.
  apply ZMap.elements_1 in Hfind.
  apply ZMapProperties.P.elements_Empty in H.
  rewrite H in Hfind.
  apply SetoidList.InA_nil in Hfind.
  contradiction.
 apply in_convex_hull_singleton in H0.
 destruct H0 as [H0 _].
 simpl in *.
 apply inject_Z_injective.
 rewrite <- !inject_Z_D_Q.
 change (0%Z:Q) with 0 in *.
 apply Qmult_integral in H0.
 destruct H0 as [H0|H0]; auto.
 apply Qinv_lt_0_compat in HM2.
 rewrite H0 in HM2.
 discriminate.
clear H.
cut (in_State M (hddivsteps.init f g) state0).
 intros H.
 apply proj2 with (Z.Odd (hddivsteps.f (N.iter N hddivsteps.step (hddivsteps.init f g)))).
 elim N using N.induction;[intros x y ->| |];try tauto.
 intros n.
 intros H0.
 rewrite !N.iter_succ.
 split;[apply hddivsteps.odd_step;tauto|].
 apply in_State_step;auto with *; try tauto.
right.
unfold State_lookup; simpl.
pose (l := ((1-f/M),(0:D,0:D)%Z)
         ::(g / M,(1:D,1:D)%Z)
         ::((f - g)/M,(0:D,1:D)%Z)
         ::nil : list (Q*DD)).
exists l.
do 2 (try split).
* destruct H as [H|[H|[H|[]]]];inversion H.
  + apply -> Qle_minus_iff.
    apply Qle_shift_div_r; auto with *.
    ring_simplify.
    rewrite !inject_Z_D_Q.
    change 0 with (inject_Z 0).
    rewrite <- Zle_Qle.
    auto with *.
  + apply Qle_shift_div_l;auto with *.
    ring_simplify.
    rewrite inject_Z_D_Q.
    change 0 with (inject_Z 0).
    rewrite <- Zle_Qle.
    auto with *.
  + apply Qle_shift_div_l;auto with *.
    ring_simplify (0 * M).
    apply -> Qle_minus_iff.
    rewrite !inject_Z_D_Q.
    rewrite <- Zle_Qle.
    auto with *.
* destruct H as [H|[H|[H|[]]]];
    inversion H;
    apply DDSet.mem_spec;
    reflexivity.
* simpl; field.
  auto with *.
* simpl.
  change (0%Z:Q) with 0.
  change (1%Z:Q) with 1.
  split; simpl; try ring.
  field.
  auto with *.
Qed.

Corollary processDivstep_gcd : forall N M f g,
  Z.Odd f ->
  (f <= M)%Z -> (0 <= g <= f)%Z -> 
  ZMap.Empty (N.iter N (processDivstep M) state0) ->
  Znumtheory.Zis_gcd f g
   (hddivsteps.f (N.iter N hddivsteps.step (hddivsteps.init f g))).
Proof.
intros N M f g HM Hf Hg H.
rewrite N2Nat.inj_iter.
apply (hddivsteps.gcd_spec _ (hddivsteps.init f g)); auto.
rewrite <- N2Nat.inj_iter.
eapply processDivstep_correct; eauto.
Qed.

Corollary processDivstep_inverse : forall N M f g,
  Z.Odd f ->
  (f <= M)%Z -> (0 <= g <= f)%Z -> 
  Znumtheory.rel_prime f g ->
  ZMap.Empty (N.iter N (processDivstep M) state0) ->
  let st' := N.iter N hddivsteps.step (hddivsteps.init f g) in
  Z.abs (hddivsteps.f st') = 1%Z /\
  eqm f ((hddivsteps.d st' * hddivsteps.f st') * g) 1.
Proof.
intros N M f g Hodd HM Hgf Hprime Hempty st'.
unfold st'; clear st'.
rewrite N2Nat.inj_iter.
apply hddivsteps.modulo_spec; auto using hddivsteps.modulo_init.
rewrite <- N2Nat.inj_iter.
eapply processDivstep_correct; eauto.
Qed.

Corollary processDivstep_prime_inverse : forall N M f g,
  Z.Odd f ->
  (g < f <= M)%Z ->
  Znumtheory.prime f ->
  ZMap.Empty (N.iter N (processDivstep M) state0) ->
  let st' := N.iter N hddivsteps.step (hddivsteps.init f g) in
  (g = 0 -> hddivsteps.d st' = 0)%Z /\
  (0 < g -> Z.abs (hddivsteps.f st') = 1 /\
            eqm f ((hddivsteps.d st' * hddivsteps.f st') * g) 1)%Z.
Proof.
intros N M f g Hodd Hgf Hprime Hempty st'.
split.
* intros Hg.
  rewrite Hg in *.
  unfold st'.
  rewrite N2Nat.inj_iter, hddivsteps.d_zero_spec; rewrite Hg; reflexivity.
* intros Hg.
  eapply (processDivstep_inverse N M); eauto with *.
  apply Znumtheory.prime_rel_prime; auto.
  intros Hfg.
  apply Z.divide_pos_le in Hfg; auto with *.
Qed.
