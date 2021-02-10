Require Import ZArith.
Require Import hddivsteps_base.

Lemma example590 : ZMap.Empty (N.iter 590 (processDivstep 0x101c840faed222b9ef3bfe933011b277f84ee3d3f6dc8b496d8cd75b8315afec2) state0).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

