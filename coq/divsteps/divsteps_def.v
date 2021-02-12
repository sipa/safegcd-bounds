Require Import ZArith.

Definition INC : Z := 1.

Module divsteps.

Record State : Set :=
 { delta : Z
 ; f : Z
 ; g : Z
 ; d : Z
 ; e : Z
 ; modulus : Z
 }.

Definition init f g := 
{| delta := 1
 ; f := f
 ; g := g
 ; d := 0
 ; e := 1
 ; modulus := f
 |}.

Section Step.

Let div2M (M x : Z) : Z :=
 (if Z.odd x then x + M else x) / 2.

Definition step (st : State) : State :=
if Z.even (g st)
  then {| delta := INC + delta st
        ; f := f st
        ; g := g st / 2
        ; d := d st
        ; e := div2M (modulus st) (e st)
        ; modulus := modulus st
        |}
  else if (0 <? delta st)%Z
         then {| delta := INC - delta st
               ; f := g st
               ; g := (g st - f st) / 2
               ; d := e st
               ; e := div2M (modulus st) (e st - d st)
               ; modulus := modulus st
               |}
         else {| delta := INC + delta st
               ; f := f st
               ; g := (g st + f st) / 2
               ; d := d st
               ; e := div2M (modulus st) (e st + d st)
               ; modulus := modulus st
               |}.

Lemma modulus_step : forall st, modulus (step st) = modulus st.
Proof.
intros [delta f g d e modulus].
unfold step.
cbn -[Z.ltb Z.add Z.sub] in *.
case (Z.even g) eqn:Hg;[|case (0 <? delta)%Z];auto.
Qed.

Lemma odd_step : forall st, Z.Odd (f st) ->
   Z.Odd (f (step st)).
Proof.
intros [delta f g] Hf.
unfold step.
cbn -[Z.ltb Z.add Z.sub] in *.
case (Z.even g) eqn:Hg;[|case (0 <? delta)%Z];auto.
simpl.
rewrite <- Z.odd_spec, Zodd_even_bool, Hg.
reflexivity.
Qed.

Lemma zero_step : forall st, g st = 0%Z ->
   g (step st) = 0%Z.
Proof.
intros [delta f g]; simpl.
intros ->.
reflexivity.
Qed.

Lemma d_zero_spec : forall (n:nat) st,
  g st = 0%Z ->
  d (Nat.iter n step st) = d st.
Proof.
intros n [delta f g d e M]; simpl.
set (st := Build_State _ _ _ _ _ _).
intros ->.
cut (divsteps.g (Nat.iter n step st) = 0%Z /\ divsteps.d (Nat.iter n step st) = d).
 tauto.
induction n; auto.
simpl.
destruct IHn as [IHn1 IHn2].
split;auto using zero_step.
unfold step at 1.
rewrite IHn1.
assumption.
Qed.

Definition gcd (st : State) : Z := 
  Z.gcd (f st) (g st).

Lemma gcd_step : forall st, Z.Odd (f st) ->
  gcd (step st) = gcd st.
Proof.
assert (Hgcd : forall f g, Z.Odd f -> Z.Even g -> Z.gcd f (g / 2) = Z.gcd f g).
  intros f g Hf Hg.
  rewrite <- Zdiv2_div.
  replace g with (2 * Z.div2 g)%Z at 2 by
   (symmetry;
    apply Zeven_div2;
    rewrite Zeven_equiv;
    assumption).
  generalize (Z.div2 g); intros g'.
  symmetry.
  apply Znumtheory.Zis_gcd_gcd;[apply Z.gcd_nonneg|].
  constructor;[apply Z.gcd_divide_l|apply Z.divide_mul_r; apply Z.gcd_divide_r|].
  intros x Hxf Hxg'.
  apply Z.gcd_greatest; auto.
  apply Znumtheory.Gauss with 2%Z; auto.
  apply Znumtheory.rel_prime_sym.
  apply Znumtheory.prime_rel_prime;[apply Znumtheory.prime_2|].
  intros H2x.
  apply Z.Even_Odd_False with f; auto.
  rewrite <-Zeven_equiv, Zeven_ex_iff.
  exists (f / 2)%Z.
  apply Znumtheory.Zdivide_Zdiv_eq; auto with *.
  apply Z.divide_transitive with x; auto.
intros [delta f g] Hf.
unfold step, gcd.
cbn -[Z.ltb Z.add Z.sub] in *.
case (Z.even g) eqn:Hg;[|case (0 <? delta)%Z];cbn -[Z.add Z.sub].
* rewrite Z.even_spec in Hg.
  apply Hgcd; auto.
* rewrite (Z.gcd_comm f g), <- (Z.gcd_sub_diag_r g f).
  replace (f - g)%Z with (-(g - f))%Z by ring.
  rewrite Z.gcd_opp_r.
  apply Hgcd;
  [ rewrite <- Z.odd_spec, <- Z.negb_even, Hg; reflexivity
  | rewrite <- Z.odd_spec in Hf;
    rewrite <- Z.even_spec, Z.even_sub, Hg, Zeven.Zeven_odd_bool, Hf
  ]; reflexivity.
* rewrite <- (Z.gcd_add_diag_r f g).
  apply Hgcd; auto.
  rewrite <- Z.odd_spec in Hf.
  rewrite <- Z.even_spec, Z.even_add, Hg, Zeven.Zeven_odd_bool, Hf.
  reflexivity.
Qed.

Lemma gcd_spec : forall (n:nat) st,
  Z.Odd (f st) ->
  g (Nat.iter n step st) = 0%Z ->
  Znumtheory.Zis_gcd (f st) (g st) (f (Nat.iter n step st)).
Proof.
intros n [delta f g] Hf Hg; simpl in *.
set (d := divsteps.f _).
cut (Znumtheory.Zis_gcd f g (Z.abs d) /\ Z.Odd d).
  destruct (Z.abs_eq_or_opp d) as [-> | ->];intros [H _];[auto|].
  replace d with (- - d)%Z by ring.
  auto using Znumtheory.Zis_gcd_sym, Znumtheory.Zis_gcd_opp.
rewrite <- Z.gcd_0_r, <- Hg.
clear Hg.
induction n;[auto using Znumtheory.Zgcd_is_gcd|].
destruct IHn as [IHn1 IHn2].
split;[|apply odd_step; auto].
unfold d; simpl.
set (st' := (Nat.iter n _ _ )) in *.
fold (gcd (step st')).
rewrite (gcd_step st'); auto.
Qed.

Let modulo_invariant (x : Z) (st : State) :=
 eqm (modulus st) (f st) (d st * x) /\ 
 eqm (modulus st) (g st) (e st * x).

Definition inv2M (M : Z) : Z := 
 let 'Znumtheory.Euclid_intro _ _ u _ d _ _ := Znumtheory.euclid 2 M in (d*u).

Lemma mul_inv2M : forall M, Z.Odd M -> eqm M (inv2M M * 2) 1.
Proof.
intros M HM.
unfold inv2M.
destruct (Znumtheory.euclid 2 M) as [u v d Hd Hgcd].
assert (H : Znumtheory.rel_prime 2 M).
 apply Znumtheory.prime_rel_prime.
  apply Znumtheory.prime_2.
 intros Heven.
 apply (Zeven_not_Zodd M).
 rewrite Znumtheory.Zdivide_Zdiv_eq with 2%Z M; auto with *.
  apply Zeven_2p.
 apply Zodd_equiv; auto.
destruct (Znumtheory.Zis_gcd_uniqueness_apart_sign _ _ _ _ Hgcd H) as [Heq|Heq];
 rewrite Heq in *;
[|apply (f_equal Z.opp) in Hd;rewrite Z.opp_involutive in Hd;
  replace (- (u * 2 + v * M))%Z with (- u*2 + (-v) * M)%Z in Hd by ring];
 rewrite <- Hd at 2;
 unfold eqm;
 rewrite <- Zplus_mod_idemp_r, <- (Zmult_mod_idemp_r M), Z_mod_same_full,
         Z.mul_0_r, Z.add_0_r;
 f_equal.
ring.
Qed.

Lemma mul_inv2M_even : forall M x, Z.Odd M -> Z.Even x ->
 eqm M (x / 2) (inv2M M * x).
Proof.
intros M x HM Hx.
rewrite <- Z.div2_div.
rewrite (Zeven_div2 x) at 2; [|apply Zeven_equiv;auto].
rewrite Zmult_assoc.
replace (Z.div2 x) with (1*Z.div2 x)%Z at 1 by ring.
apply Zmult_eqm;try reflexivity.
auto using eqm_sym, mul_inv2M.
Qed.

Lemma eqm_div2M : forall M x, Z.Odd M -> eqm M (div2M M x) (inv2M M * x).
Proof.
intros M x HM.
rewrite <- (Z.mul_1_l (div2M M x)).
apply eqm_trans with ((inv2M M * 2) * div2M M x)%Z.
 apply Zmult_eqm; try reflexivity.
 apply eqm_sym.
 apply mul_inv2M; auto.
rewrite <- Zmult_assoc.
apply Zmult_eqm; try reflexivity.
unfold div2M.
case (Z.odd x) eqn:Hx.
* apply Zodd_bool_iff in Hx.
  apply Zodd_equiv in HM.
  rewrite <- Zdiv2_div, <- Zeven_div2; auto using Zodd_plus_Zodd.
  unfold eqm; rewrite Zplus_mod. 
  rewrite <- (Zmod_eqm M M), Z_mod_same_full, Z.add_0_r.
  apply Zmod_mod.
* apply (f_equal negb) in Hx.
  rewrite Z.negb_odd in Hx.
  apply Zeven_bool_iff in Hx.
  rewrite <- Zdiv2_div, <- Zeven_div2; auto.
  reflexivity.
Qed.

Lemma eqm_div2M' : forall M x y, Z.Odd M -> 
 eqm M (inv2M M * (x * y)) (div2M M x * y).
Proof.
intros M x y HM.
rewrite Zmult_assoc.
apply Zmult_eqm;try reflexivity.
auto using eqm_div2M, eqm_sym.
Qed.

Lemma modulo_step : forall x st, Z.Odd (modulus st) -> Z.Odd (f st) ->
  modulo_invariant x st ->
  modulo_invariant x (step st).
Proof.
intros x [delta f g d e M] HM Hf [Heqf Heqg].
unfold modulo_invariant.
rewrite modulus_step.
simpl in *.
destruct (Z.eq_dec M 1%Z) as [->|HM1].
 unfold eqm.
 rewrite !Z.mod_1_r; auto with *.
destruct (Z.eq_dec M (-1)%Z) as [->|HM1'].
 unfold eqm.
 rewrite !(Z_mod_zero_opp_r _ _ (Z.mod_1_r _)); auto with *.
assert (HM0 : M <> 0%Z).
 rewrite <- Z.odd_spec in HM.
 intros HM0.
 rewrite HM0 in HM.
 discriminate.
assert (HM2 : (2 mod M)%Z <> 0%Z).
 rewrite <- Z.odd_spec in HM.
 intros H.
 apply Znumtheory.Zmod_divide in H; auto with *.
 apply Znumtheory.prime_divisors in H; auto using Znumtheory.prime_2.
 destruct H as [H|[H|[H|H]]]; try contradiction; rewrite H in HM; discriminate.
unfold step.
cbn -[Z.ltb Z.add Z.sub] in *.
case (Z.even g) eqn:Hg;[|case (0 <? delta)%Z];simpl;split;auto.
* apply Zeven_bool_iff in Hg.
  apply Zeven_equiv in Hg.
  eapply eqm_trans;[apply mul_inv2M_even;auto|].
  eapply eqm_trans;[|apply eqm_div2M';auto].
  apply Zmult_eqm;try reflexivity.
  assumption.
* apply (f_equal negb) in Hg.
  rewrite Z.negb_even in Hg.
  rewrite Zodd_bool_iff in Hg.
  apply Zodd_equiv in Hg.
  eapply eqm_trans;[apply mul_inv2M_even;auto|].
   apply Zeven_equiv.
   apply Zodd_plus_Zodd; apply Zodd_equiv; auto.
   apply Z.odd_spec.
   rewrite Z.odd_opp.
   apply Z.odd_spec.
   assumption.
  eapply eqm_trans;[|apply eqm_div2M';auto].
  apply Zmult_eqm;try reflexivity.
  replace ((e - d)*x)%Z with (e * x - d * x)%Z by ring.
  apply Zminus_eqm; auto.
* apply (f_equal negb) in Hg.
  rewrite Z.negb_even in Hg.
  rewrite Zodd_bool_iff in Hg.
  apply Zodd_equiv in Hg.
  eapply eqm_trans;[apply mul_inv2M_even;auto|].
   apply Zeven_equiv.
   apply Zodd_plus_Zodd; apply Zodd_equiv; auto.
  eapply eqm_trans;[|apply eqm_div2M';auto].
  apply Zmult_eqm;try reflexivity.
  replace ((e + d)*x)%Z with (e * x + d * x)%Z by ring.
  apply Zplus_eqm; auto.
Qed.

Lemma modulo_spec : forall (n:nat) st x,
  Z.Odd (modulus st) ->
  Z.Odd (f st) ->
  modulo_invariant x st ->
  Znumtheory.rel_prime (f st) (g st) ->
  let st' := (Nat.iter n step st) in
  g st' = 0%Z ->
  Z.abs (f st') = 1%Z /\
  eqm (modulus st) ((d st' * f st') * x) 1.
Proof.
intros n st x HM Hf Hinv Hprime st' Hg.
assert (HMeq : modulus st = modulus st').
 clear.
 induction n;try reflexivity.
 unfold st'.
 rewrite IHn.
 simpl.
 rewrite modulus_step.
 reflexivity.
assert (Hinv' : modulo_invariant x st').
 clear -HM Hf Hinv.
 cut (Z.Odd (modulus st') /\ (Z.Odd (f st') /\ modulo_invariant x st'));[tauto|].
 induction n; auto.
 destruct IHn as [IHn1 [IHn2 IHn3]].
 unfold st'.
 simpl.
 split;[rewrite modulus_step;auto|].
 split;[apply odd_step;auto|].
 apply modulo_step; auto.
destruct Hinv' as [Hinv' _].
rewrite (Zmult_comm (d st') _), <- Zmult_assoc.
rewrite <- HMeq in Hinv'.
assert (Hgcd := gcd_spec n st Hf Hg).
fold st' in Hgcd.
assert (H1 : Z.abs (f st') = 1%Z).
destruct (Znumtheory.Zis_gcd_uniqueness_apart_sign _ _ _ _ Hgcd Hprime) as [->| ->];
 auto.
split; auto.
change 1%Z with (1 * 1)%Z.
rewrite <- H1.
rewrite Z.abs_square.
apply eqm_sym.
apply Zmult_eqm; auto; reflexivity.
Qed.

Lemma modulo_init : forall f g, modulo_invariant g (init f g).
Proof.
intros f g.
split; unfold init; cbn -[Zmult]; unfold eqm.
* rewrite Z_mod_same_full, Z.mul_0_l, Zmod_0_l; reflexivity.
* rewrite Z.mul_1_l; reflexivity.
Qed.

End Step.
End divsteps.
