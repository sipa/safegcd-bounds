Require Import ZArith.
Require Import hddivsteps590.
Require Import hddivsteps_def.
Require Import hddivsteps_theory.

Theorem hddivsteps590_gcd : forall f g,
  Z.Odd f ->
  (f <= 0x101c840faed222b9ef3bfe933011b277f84ee3d3f6dc8b496d8cd75b8315afec2)%Z ->
  (0 <= g <= f)%Z -> 
  Znumtheory.Zis_gcd f g
    (hddivsteps.f (N.iter 590 hddivsteps.step (hddivsteps.init f g))).
Proof.
intros f g Hf HM Hg.
eapply processDivstep_gcd; try assumption; try apply HM.
apply example590.
Qed.

Check hddivsteps590_gcd.
Print Assumptions hddivsteps590_gcd.

Theorem hddivsteps590_inverse : forall f g,
  Z.Odd f ->
  (f <= 0x101c840faed222b9ef3bfe933011b277f84ee3d3f6dc8b496d8cd75b8315afec2)%Z ->
  (0 <= g <= f)%Z -> 
  Znumtheory.rel_prime f g ->
  let st := N.iter 590 hddivsteps.step (hddivsteps.init f g) in
  Z.abs (hddivsteps.f st) = 1%Z /\
   eqm f ((hddivsteps.d st * hddivsteps.f st) * g) 1.
Proof.
intros f g Hf HM Hg Hprime.
eapply processDivstep_inverse; try assumption; try apply HM.
apply example590.
Qed.

Check hddivsteps590_inverse.
Print Assumptions hddivsteps590_inverse.

Theorem hddivsteps590_prime_inverse : forall f g,
  Z.Odd f ->
  Znumtheory.prime f ->
  (g < f <= 0x101c840faed222b9ef3bfe933011b277f84ee3d3f6dc8b496d8cd75b8315afec2)%Z ->
  let st := N.iter 590 hddivsteps.step (hddivsteps.init f g) in
  (g = 0 -> hddivsteps.d st = 0)%Z /\
  (0 < g -> Z.abs (hddivsteps.f st) = 1 /\
            eqm f ((hddivsteps.d st * hddivsteps.f st) * g) 1)%Z.
Proof.
intros f g Hf Hprime HM Hg.
eapply processDivstep_prime_inverse; try assumption; try apply HM.
apply example590.
Qed.

Check hddivsteps590_prime_inverse.
Print Assumptions hddivsteps590_prime_inverse.
