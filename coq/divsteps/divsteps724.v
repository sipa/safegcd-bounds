Require Import ZArith.
Require Import divsteps_base.

Lemma example724 : ZMap.Empty (N.iter 724 (processDivstep 0x1030596cf6d817d1357f908ef70cdb00b38d047fbba852139babb6c8646fb15b2) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.
