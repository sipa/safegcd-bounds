Require Import ZArith.
Require Import hddivsteps_base.

Lemma example50 : ZMap.Empty (N.iter 50 (processDivstep 0x30ef80) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example60 : ZMap.Empty (N.iter 60 (processDivstep 0x3cfab01) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example70 : ZMap.Empty (N.iter 70 (processDivstep 0x4ed603ad) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example80 : ZMap.Empty (N.iter 80 (processDivstep 0x62079d724) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example90 : ZMap.Empty (N.iter 90 (processDivstep 0x7ae312bf9f) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example100 : ZMap.Empty (N.iter 100 (processDivstep 0x9eb8bb022c3) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example120 : ZMap.Empty (N.iter 120 (processDivstep 0xf91d7384fec8f) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example140 : ZMap.Empty (N.iter 140 (processDivstep 0x190c14a6b68d1755) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example160 : ZMap.Empty (N.iter 160 (processDivstep 0x28adca2f6746850761) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example180 : ZMap.Empty (N.iter 180 (processDivstep 0x41164837dba63cc865f5) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example200 : ZMap.Empty (N.iter 200 (processDivstep 0x6800e4d2ac85589f17d4b0) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example250 : ZMap.Empty (N.iter 250 (processDivstep 0x14fe91f2a268cc215f1586a78f32) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example300 : ZMap.Empty (N.iter 300 (processDivstep 0x454ce3c97f2e8f66511db7c277de001ab) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example350 : ZMap.Empty (N.iter 350 (processDivstep 0xe18e996a73c8649b67a59b136a03ae874088da) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example400 : ZMap.Empty (N.iter 400 (processDivstep 0x2e2aa07e7688b076c9b312eb5c8afb58bcca81e09729) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example450 : ZMap.Empty (N.iter 450 (processDivstep 0x96ac54f418d8174b771b32d8ec83d1a044f3543df0418cf70) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Lemma example500 : ZMap.Empty (N.iter 500 (processDivstep 0x1e7c8ce70bede0e24be604945c3e4cc5d99270cd57644386f873692) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.
