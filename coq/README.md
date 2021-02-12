# Coq proof of bounds on divsteps iterations in safegcd

This directory contains Coq proofs that establish upper bounds on the number of iterations needed for divsteps and hddivsteps to cover 256-bit input values.
The `divsteps` directory contains the proof that 724 iterations of `divstep` is sufficient for 256-bit inputs. 
The `hddivsteps` directory contains the proof that 590 iterations of `hddivstep` is sufficient for 256-bit inputs. 

## Building

The proof has been developed using [Coq 8.13](https://coq.inria.fr/news/coq-8-13-0-is-out.html) and this is a requirement (although the proof could be backported to work with earlier version of Coq).

To build the proof, run the following commands in either the `divsteps` or `hddivsteps` directory, depending on which proof you wish to build.

```
$ coq_makefile -f _CoqProject -o Makefile

$ make -j2
```

Then wait for about 2.5 days or so.

## Results

The `divsteps/divsteps724_proof.v` or `hddivsteps/hddivsteps590_proof.v` file contains the final proofs of this development.
During the build these files will each print three variants of the main theorem and then print any assumptions that these theorems depend on.
For example, when building the `hddivsteps` project, the following output should be printed:

```
hddivsteps590_gcd
     : forall f g : Z,
       Z.Odd f ->
       (f <=
        116598219975581070071883298065196158969310383137833836574946009125721210552002)%Z ->
       (0 <= g <= f)%Z ->
       Znumtheory.Zis_gcd f g
         (hddivsteps.f (N.iter 590 hddivsteps.step (hddivsteps.init f g)))
Closed under the global context
hddivsteps590_inverse
     : forall f g : Z,
       Z.Odd f ->
       (f <=
        116598219975581070071883298065196158969310383137833836574946009125721210552002)%Z ->
       (0 <= g <= f)%Z ->
       Znumtheory.rel_prime f g ->
       let st := N.iter 590 hddivsteps.step (hddivsteps.init f g) in
       Z.abs (hddivsteps.f st) = 1%Z /\
       eqm f (hddivsteps.d st * hddivsteps.f st * g) 1
Closed under the global context
hddivsteps590_prime_inverse
     : forall f g : Z,
       Z.Odd f ->
       Znumtheory.prime f ->
       (g < f <=
        116598219975581070071883298065196158969310383137833836574946009125721210552002)%Z ->
       let st := N.iter 590 hddivsteps.step (hddivsteps.init f g) in
       (g = 0%Z -> hddivsteps.d st = 0%Z) /\
       ((0 < g)%Z ->
        Z.abs (hddivsteps.f st) = 1%Z /\
        eqm f (hddivsteps.d st * hddivsteps.f st * g) 1)
Closed under the global context
```

The first theorem concludes under the conditions that `f` is odd, bounded and `0 <= g <= f`, that the `hddivsteps.f` field of the state after iterating `hddivsteps.step` 590 times from the `hddivsteps.init f g` state is a GCD of `f` and `g`.

The second theorem concludes under the conditions that `f` is odd, bounded and `0 <= g <= f`, `f` and `g` are relatively prime, and `st` is the state after iterating `hddivsteps.step` 590 times from the `hddivsteps.init f g`, that the absolute value of the `hddivsteps.f` field of `st` is 1 and that the product of the `hddivsteps.d` field of `st`, the `hddivsteps.f` field of `st`, and `g` equals `1` modulo `f`.

The thrid theorem states under the conditions that `f` is odd, prime, and bounded and `g <= f` and `st` is the state after iterating `hddivsteps.step` 590 times from the `hddivsteps.init f g`, that
1. if `g = 0` then the `hddivsteps.d` field `st` is 0.
2. if `0 < g` then the absolute value of the `hddivsteps.f` field of `st` is 1 and that the product of the `hddivsteps.d` field of `st`, the `hddivsteps.f` field of `st`, and `g` equals `1` modulo `f`.

The formal definitions of the `hddivsteps.State` the `hddivsteps.step` function and the initial `hddivsteps.init` state can be found at the top of the `hddivsteps/hddivsteps_def.v` file.  They are
```
Module hddivsteps.

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
```

The `Closed under the global context` statements mean that Coq has verified these theorems to hold without the use of any assumptions.

Similar output is produced when building the `divsteps` project.
