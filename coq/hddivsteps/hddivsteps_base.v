Require Import Orders.
Require Import OrdersEx.
Require Import OrdersAlt.
Require Import ZArith.
Require Import QArith.
Require Import Qpower.
Require Import MSets.
Require Import List.
Import ListNotations.

Definition INC : Z := 2.

Record D := Dmake {Dmantissa : Z; Dexponent : Z }.

Definition D_from_Z (a : Z) := Dmake a 0.
Coercion D_from_Z : Z >-> D.

Definition inject_D (a : D) := (inject_Z (Dmantissa a) * 2 ^ Dexponent a)%Q.
Coercion inject_D : D >-> Q.

Fixpoint DredH (p : positive) (z : Z) : positive*Z :=
match p with
| xO x => DredH x (Z.succ z)
| _ => (p, z)
end.

Definition Dred (a : D) : D :=
let (m, e) := a in
match m with
| Z0 => 0%Z
| Zpos p => let (p', e') := DredH p e in Dmake (Zpos p') e'
| Zneg p => let (p', e') := DredH p e in Dmake (Zneg p') e'
end.

Definition Dalign (a b : D) : Z * Z * Z :=
match (Dexponent a - Dexponent b)%Z with
| Zpos d => (Z.shiftl (Dmantissa a) (Zpos d), Dmantissa b, Dexponent b)
| Z0 => (Dmantissa a, Dmantissa b, Dexponent b)
| Zneg d => (Dmantissa a, Z.shiftl (Dmantissa b) (Zpos d), Dexponent a)%Z
end.

Lemma Dalign_lr : forall x y, let '(xm', ym', e') := Dalign x y in
  inject_D (Dmake xm' e') == inject_D x /\ 
  inject_D (Dmake ym' e') == inject_D y.
Proof.
intros [xm xe] [ym ye].
cbv beta iota delta [Dalign Dexponent Dmantissa inject_D].
case (xe - ye)%Z as [|p|p] eqn:He; [rewrite (Zminus_eq _ _ He); split; reflexivity| |];
split;try reflexivity;
rewrite Z.shiftl_mul_pow2, inject_Z_mult, Zpower_Qpower; auto with *;
rewrite <- Qmult_assoc, <- Qpower_plus; try discriminate.
* rewrite <- He, Z_as_OT.sub_add; reflexivity.
* rewrite <- (Pos2Z.opp_neg p), <- He.
  replace (-(xe - ye) + xe)%Z with ye by ring.
  reflexivity.
Qed.

Definition Dadd (a b : D) : D :=
let '(a',b',e') := Dalign a b in Dmake (a' + b') e'.

Definition Dsub (a b : D) : D :=
let '(a',b',e') := Dalign a b in Dmake (a' - b') e'.

Definition Dmult (a b : D) : D :=
 Dmake (Dmantissa a * Dmantissa b) (Dexponent a + Dexponent b).

Definition Dhalf (a : D) : D :=
 Dmake (Dmantissa a) (Z.pred (Dexponent a)).

Definition Dcompare (a b : D) : comparison :=
let '(a',b',_) := Dalign a b in (a' ?= b')%Z.

Lemma Dcompare_Q : forall x y, Dcompare x y = (x ?= y)%Q.
Proof.
intros x y.
unfold Dcompare.
assert (Hxy := Dalign_lr x y).
destruct (Dalign x y) as [[xm' ym'] e'].
destruct Hxy as [<- <-].
unfold Qcompare.
simpl.
rewrite <- !Zmult_assoc.
apply Zmult_compare_compat_r.
apply Z.lt_gt.
assert (Hp : forall p, (0 < Z.pow_pos 2 p)%Z).
 intros p;
 apply Zpow_facts.Zpower_pos_pos; auto with *.
apply Zmult_lt_0_compat;
destruct e'; simpl; auto with *;
rewrite Qpower_decomp; simpl; auto with *.
unfold Qinv; simpl.
specialize (Hp p).
destruct (Z.pow_pos 2 p)%Z; try discriminate; auto with *.
Qed. 

Lemma Dcompare_antisym : forall x y, Dcompare y x = CompOpp (Dcompare x y).
Proof.
intros x y.
rewrite !Dcompare_Q, Qcompare_antisym.
reflexivity.
Qed.

Lemma Dcompare_trans : forall c x y z,
 Dcompare x y = c -> Dcompare y z = c -> Dcompare x z = c.
Proof.
intros c x y z <-.
rewrite !Dcompare_Q.
destruct (Qcompare_spec x y).
* rewrite H; auto.
* rewrite <- !Qlt_alt.
  eauto using Qlt_trans.
* rewrite <- !Qgt_alt.
  eauto using Qlt_trans.
Qed.

Module D_as_OrderedTypeAlt <: OrderedTypeAlt.
 Definition t := D.
 Definition compare := Dcompare.
 Definition compare_sym := Dcompare_antisym.
 Definition compare_trans := Dcompare_trans.
End D_as_OrderedTypeAlt.

Module D_as_OT <: OrderedType := OT_from_Alt D_as_OrderedTypeAlt.
Module D_as_OTF <: OrderedTypeFull := OT_to_Full D_as_OT.
Module D_as_TTLT <: TotalTransitiveLeBool := OTF_to_TTLB D_as_OTF.

Definition Dltb (a b : D) := negb (D_as_TTLT.leb b a).

Module DDOrder <: OrderedType := PairOrderedType D_as_OT D_as_OT.

Definition DD := DDOrder.t.

(* | x1 y1 1 |
 * | x2 y2 1 | ?= 0
 * | x3 y3 1 |
 *)
Definition orientation (p1 p2 p3 : DD) : comparison :=
let (x1, y1) := p1 in
let (x2, y2) := p2 in
let (x3, y3) := p3 in
(* (x1*y2 - y1*x2) + (x2*y3 - y2*x3) ?= x1*y3-y1*x3. *)
Dcompare (Dmult (Dsub x1  x3) (Dsub y2 y3)) (Dmult (Dsub y1 y3) (Dsub x2 x3)).

Fixpoint addLowerPoint (p : DD) (l : list DD) : list DD :=
match l with
| [] => [p]
| q :: l0 => match l0 with
   | [] => match DDOrder.compare p q with
           | Eq => [p]
           | _ => [p; q]
           end
   | r :: _ => match orientation p q r with
                 | Lt => p :: l
                 | _ => addLowerPoint p l0
                 end
   end
end.

Fixpoint addUpperPoint (p : DD) (l : list DD) : list DD :=
match l with
| [] => [p]
| q :: l0 => match l0 with
   | [] => match DDOrder.compare p q with
           | Eq => [p]
           | _ => [p; q]
           end
   | r :: _ => match orientation p q r with
                 | Gt => p :: l
                 | _ => addUpperPoint p l0
                 end
   end
end.

Module DDSet := MSetAVL.Make DDOrder.
Definition DDSet_fromList (l : list DD) :=
 fold_left (fun s a => DDSet.add a s) l DDSet.empty.
Definition DDSet_map (f : DD -> DD) (s : DDSet.t) :=
 DDSet.fold (fun a s => DDSet.add (f a) s) s DDSet.empty.

Definition convexHull (s : DDSet.t) : DDSet.t :=
 DDSet_fromList
   ((DDSet.fold addUpperPoint s []) ++ (DDSet.fold addLowerPoint s [])).

Definition narrow (M : Z) (s : DDSet.t) : bool :=
match (DDSet.min_elt s, DDSet.max_elt s) with
| (Some (l, _), Some (h, _)) => andb (Dltb (-1)%Z (Dmult M l)) (Dltb (Dmult M h) 1%Z)
| _ => true
end.

Definition odd_pos_trans (p : DD) : DD :=
let (g, f) := p in
 (Dred (Dhalf (Dsub g f)), g) (* ((g - f) / 2), g) *).
Definition odd_nonpos_trans (p : DD) : DD :=
let (g, f) := p in
 (Dred (Dhalf (Dadd g f)), f) (* ((g + f) / 2), f) *).
Definition even_trans (p : DD) : DD :=
let (g, f) := p in
 (Dhalf g, f) (* (g / 2), f) *).

Definition even_map (kv : Z * DDSet.t) : Z * DDSet.t :=
let (k, v) := kv in ((INC + k)%Z, DDSet_map even_trans v).
Definition odd_map (kv : Z * DDSet.t) : Z * DDSet.t :=
let (k, v) := kv in
if (0 <? k)%Z
 then ((INC - k)%Z, DDSet_map odd_pos_trans v)
 else ((INC + k)%Z, DDSet_map odd_nonpos_trans v).

Require FMapAVL.

Module ZMap := FMapAVL.Make OrderedTypeEx.Z_as_OT.

Definition State := ZMap.t DDSet.t.
Definition empty : State := ZMap.empty DDSet.t.
Definition State_join (k : Z) (v : DDSet.t) (m : State) : State :=
  ZMap.add k (match ZMap.find k m with
              | None =>  v
              | Some v0 => DDSet.union v v0
              end)
           m.
Definition State_fromList (l : list (Z * DDSet.t)) :=
 fold_left (fun s kv => State_join (fst kv) (snd kv) s) l empty.

Definition processDivstep (M : Z) (s : State) : State :=
 let f kv := [even_map kv; odd_map kv] in
 let s1 := (State_fromList (flat_map f (ZMap.elements s))) in
 let g kv := let (k, v) := kv : Z * DDSet.t in
             if narrow M v then [] else [(k, convexHull v)]
 in State_fromList (flat_map g (ZMap.elements s1)).

Definition set0 : DDSet.t := DDSet_fromList [(0:D,1:D); (1:D,1:D)]%Z.
Definition state0 : State := ZMap.add 1%Z set0 empty.

Lemma example_0x1dff_30 : ZMap.Empty (N.iter 30 (processDivstep 0x1dff) state0).
Proof.
apply ZMap.is_empty_2.
Time vm_compute.
auto.
Qed.

Lemma example_0x1e00_30 : ~ZMap.Empty (N.iter 30 (processDivstep 0x1e00) state0).
Proof.
intros H.
apply ZMap.is_empty_1 in H.
Time vm_compute in H.
discriminate.
Qed.

Lemma example_0x1dff_29 : ~ZMap.Empty (N.iter 29 (processDivstep 0x1dff) state0).
Proof.
intros H.
apply ZMap.is_empty_1 in H.
Time vm_compute in H.
discriminate.
Qed.