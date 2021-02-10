Require Import ZArith.
Require Import divsteps724.
Require Import divsteps_def.
Require Import divsteps_theory.

Theorem divsteps724_gcd : forall f g,
  Z.Odd f ->
  (f <= 0x1030596cf6d817d1357f908ef70cdb00b38d047fbba852139babb6c8646fb15b2)%Z ->
  (0 <= g <= f)%Z -> 
  Znumtheory.Zis_gcd f g
    (divsteps.f (N.iter 724 divsteps.step (divsteps.init f g))).
Proof.
intros f g Hf HM Hg.
eapply processDivstep_gcd; try assumption; try apply HM.
apply example724.
Qed.

Check divsteps724_gcd.
Print Assumptions divsteps724_gcd.

Theorem divsteps724_inverse : forall f g,
  Z.Odd f ->
  (f <= 0x1030596cf6d817d1357f908ef70cdb00b38d047fbba852139babb6c8646fb15b2)%Z ->
  (0 <= g <= f)%Z -> 
  Znumtheory.rel_prime f g ->
  let st := N.iter 724 divsteps.step (divsteps.init f g) in
  Z.abs (divsteps.f st) = 1%Z /\
   eqm f ((divsteps.d st * divsteps.f st) * g) 1.
Proof.
intros f g Hf HM Hg Hprime.
eapply processDivstep_inverse; try assumption; try apply HM.
apply example724.
Qed.

Check divsteps724_inverse.
Print Assumptions divsteps724_inverse.

Theorem divsteps724_prime_inverse : forall f g,
  Z.Odd f ->
  Znumtheory.prime f ->
  (g < f <= 0x1030596cf6d817d1357f908ef70cdb00b38d047fbba852139babb6c8646fb15b2)%Z ->
  let st := N.iter 724 divsteps.step (divsteps.init f g) in
  (g = 0 -> divsteps.d st = 0)%Z /\
  (0 < g -> Z.abs (divsteps.f st) = 1 /\
            eqm f ((divsteps.d st * divsteps.f st) * g) 1)%Z.
Proof.
intros f g Hf Hprime HM Hg.
eapply processDivstep_prime_inverse; try assumption; try apply HM.
apply example724.
Qed.

Check divsteps724_prime_inverse.
Print Assumptions divsteps724_prime_inverse.
