# Generic formula for hddivsteps

Here we derive and give a proof for a generic formula for the number of iterations required for hddivsteps.

## Introduction

The algorithm under consideration is this:

```python
def hddivstep(f, g, delta):
    if delta > 0 and g & 1:
        return 1 - delta, g, (g - f) >> 1
    elif g & 1:
        return 1 + delta, f, (g + f) >> 1
    else:
        return 1 + delta, f, (g    ) >> 1

def gcd(f, g):
    assert f & 1
    delta = 1/2
    while g != 0:
        f, g, delta = hddivstep(f, g, delta)
    return abs(f)
```

To create a constant-time version of this algorithm, we are interested in knowing an upper
bound on the number of hddivstep iterations in function of `f` and `g`.

## Formula

If *0 &leq; f &leq; M*, *0 &leq; g &leq; M*, then no more than *&lfloor;(45907 log<sub>2</sub>(M) + 30179) / 19929&rfloor;* hddivsteps are needed for input *(f,g)*.

If additionally *g &leq; f*, then no more than *&lfloor;(45907 log<sub>2</sub>(M) + 26313) / 19929&rfloor;* hddivsteps are needed for input *(f,g)*.

## Proof

Define the function *hull*, which takes a set *S* of points *&in; &reals;<sup>2</sup>* and returns their convex hull (the set of all convex combinations
of points in *S*).

In what follows, multiplications between scalars or matrices and sets of points are defined as the set of that multiplication applied to all its points;
*[[a,b],[c,d]]S* is defined as *{(af+bg,cf+dg) | (f,g) &isin; S}*.

Define:
* *D = 273548757304312537*
* *&alpha; = ((1591853137 + 3&radic;D)/2<sup>55</sup>)<sup>1/54</sup> &approx; 0.740146723852948...*

Define the sets *H<sub>&delta;</sub>*, for every *&delta;* that is an integer plus *1/2*, as follows. The constant point sets *P<sub>1/2</sub>* and *P<sub>-1/2</sub>* are defined in the appendix below.
* *H<sub>-1/2</sub> = hull(P<sub>-1/2</sub>)*
* *H<sub>1/2</sub> = hull(P<sub>1/2</sub>)*
* *&forall;&delta;<-1*: *H<sub>&delta;</sub> = [[0,2<sup>&delta;-1/2</sup>],[-1/2,2<sup>&delta;-3/2</sup>]]&alpha;<sup>&delta;-3/2</sup>H<sub>1/2</sub>*
* *&forall;&delta;>1*: *H<sub>&delta;</sub> = [[1,0],[0,2<sup>1/2-&delta;</sup>]]&alpha;<sup>1/2-&delta;</sup>H<sub>1/2</sub>*

To simplify analysis of the `hddivstep` function above, we generalize it to operate on *f* and *g* in *&reals;*.
As the concept of *g*'s parity no longer exist then, we treat it as a function whose exact behavior is not fully defined.
Instead, we always consider the possibility that either the "g is even" or "g is odd" branches are taken, regardless of the actual value of *g*.
We know about *hddivstep*:
* *hddivstep(f,g,&delta;)* where *&delta;<0*: either
  * (a) *(1+&delta;,f,g/2)*
  * (b) *(1+&delta;,f,(g+f)/2)*
* *hddivstep(f,g,&delta;)* where *&delta;>0*: either
  * (c) *(1+&delta;,f,g/2)*
  * (d) *(1-&delta;,g,(g-f)/2)*

This is a strict generalization, and thus any conclusions about restrictions on the domains after application of this function should apply
to `hddivstep` as well. Furthermore, we know that whenever *|g|<1*, `gcd`
would have terminated, as the restriction to integers there together with *|g|<1* implies *g=0*.

---

**Theorem 1** The collection of hulls defined by *H* has the property of being mapped to an *&alpha;*-scaled version of itself by *hddivstep*.
*&forall;&delta;, (f,g) &isin; H<sub>&delta;</sub>*: if *(f',g',&delta;') = hddivstep(f,g,&delta;)*, then *(f',g') &isin; &alpha;H<sub>&delta;'</sub>*.

This can be written as follows:
* (a) *&forall;&delta;<0, (f,g) &isin; H<sub>&delta;</sub>*: *(f,g/2) &isin; &alpha;H<sub>1+&delta;</sub>*
* (b) *&forall;&delta;<0, (f,g) &isin; H<sub>&delta;</sub>*: *(f,(g+f)/2) &isin; &alpha;H<sub>1+&delta;</sub>*
* (c) *&forall;&delta;>0, (f,g) &isin; H<sub>&delta;</sub>*: *(f,g/2) &isin; &alpha;H<sub>1+&delta;</sub>*
* (d) *&forall;&delta;>0, (f,g) &isin; H<sub>&delta;</sub>*: *(g,(g-f)/2) &isin; &alpha;H<sub>1-&delta;</sub>*

These relations can be verified directly for any specific *&delta;*. We do so for all *-2<&delta;<2*. None of the
remaining cases involve *H<sub>-1/2</sub>*:
* (a) *&forall;&delta;<-2*: *[[1,0],[0,1/2]]H<sub>&delta;</sub> &sube; &alpha;H<sub>1+&delta;</sub>*
* (b) *&forall;&delta;<-2*: *[[1,0],[1/2,1/2]]H<sub>&delta;</sub> &sube; &alpha;H<sub>1+&delta;</sub>*
* (c) *&forall;&delta;>2*: *[[1,0],[0,1/2]]H<sub>&delta;</sub> &sube; &alpha;H<sub>1+&delta;</sub>*
* (d) *&forall;&delta;>2*: *[[0,1],[-1/2,1/2]]H<sub>&delta;</sub> &sube; &alpha;H<sub>1-&delta;</sub>*

By substituting the definitions of *H<sub>&delta;</sub>*, and left-dividing to make the right hand side equal to *H<sub>1/2</sub>*, we obtain:
* (a) *&forall;&delta;<-2*: *[[1/2,2<sup>&delta;-3/2</sup>],[0,1/2]]&alpha;<sup>-2</sup>H<sub>1/2</sub> &sube; H<sub>1/2</sub>*
* (b) *&forall;&delta;<-2*: *[[1/2,-2<sup>-&delta;-3/2</sup>],[0,1/2]]&alpha;<sup>-2</sup>H<sub>1/2</sub> &sube; H<sub>1/2</sub>*
* (c) *&forall;&delta;>2*: *H<sub>1/2</sub> &sube; H<sub>1/2</sub>*
* (d) *&forall;&delta;>2*: *H<sub>1/2</sub> &sube; H<sub>1/2</sub>*

(c) and (d) are trivially true. (a) and (b) can be verified computationally for *|&delta;| = 5/2*. From this we can
conclude that for any point *p &isin; H<sub>1/2</sub>*, *[[1/2,&plusmn;1/16],[0,1/2]]&alpha;<sup>-2</sup>p* &isin; *H<sub>1/2</sub>*.
Now observe that for higher *|&delta;|* (a) and (b) demand that for any such point *p*,
*[[1/2,&plusmn;1/2<sup>|&delta;|+3/2</sup>],[0,1/2]]&alpha;<sup>-2</sup>p &isin; H<sub>1/2</sub>* as well. These points are on the line connecting
the two *[[1/2,&plusmn;1/16],[0,1/2]]&alpha;<sup>-2</sup>p* points, and because *H<sub>1/2</sub>* is a convex hull,
any line connecting two points in the hull is entirely in the hull itself. Thus, from (a) and (b) holding for *|&delta;| = 5/2* (which they do)
we conclude they also hold for every higher *|&delta;|*.

---

**Theorem 2** There are simple bounds on *|g|* on *H<sub>&delta;</sub>* for positive *&delta;
*.*&forall;&delta;>0, (f,g) &isin; H<sub>&delta;</sub>*: *|g| &leq; (2&alpha;)<sup>1/2-&delta;</sup>*.

For *&delta; = 1/2* this can be verified directly for points in *P<sub>1/2</sub>*.
For all other *&delta;* values it follows from the definition of *H<sub>&delta;</sub>*.

---

For a given computation starting with *f = f<sub>0</sub>*, *g = g<sub>0</sub>*, and *&delta; = &delta;<sub>0</sub> = 1/2*, define
*(f<sub>k</sub>, g<sub>k</sub>, &delta;<sub>k</sub>) = hddivstep<sup>k</sup>(f<sub>0</sub>,g<sub>0</sub>,1/2)*. Assume further that *(f<sub>0</sub>, g<sub>0</sub>) &isin; qH<sub>1/2</sub>*
for some known hull scaling factor *q>0*.

**Theorem 3** *(f<sub>k</sub>, g<sub>k</sub>) &isin; q&alpha;<sup>k</sup>H<sub>&delta;<sub>k</sub>*.

This holds for *k=0* because *(f<sub>0</sub>, g<sub>0</sub>) &isin; qH<sub>1/2</sub>* is given. If it holds for *k-1&geq;0*, it also
holds for *k* because of Theorem 1.

---

**Theorem 4** For all *k&geq;0*, either:
* (1) There exists a *0&leq;j&leq;k* for which *|g<sub>j</sub>|<1*
* (2) *q&alpha;<sup>k</sup>(2&alpha;)<sup>1/2-|&delta;<sub>k</sub>|</sup> &geq; 1*

This holds for *k=0*. We know *q &geq; |g<sub>0</sub>|* because by Theorem 2, every point in *qH<sub>1/2</sub>* has *|g| &leq; q(2&alpha;)<sup>0</sup> = q*.
If *|g<sub>0</sub>|<1*, then (1) holds. If not, *q&geq;1* and (2) *q&alpha;<sup>0</sup>(2&alpha;)<sup>0</sup> &geq; 1* holds.

Assuming the theorem is true for *k-1*, we show it is also true for *k*. It is either the case that:
* (1) held for *k-1*, and a *0&leq;j&leq;k-1* existed for which *|g<sub>j</sub>|<1*. In this case (1) holds for *k* as well, with the same *j*.
* *|g<sub>k</sub>|<1*, and (1) holds with *j=k*.
* Neither of the above applies, we know (2) held for *k-1*, *|g<sub>k</sub>|&geq;1*, and either:
  * *&delta;<sub>k</sub> > 0*: by Theorem 3 we know *(f<sub>k</sub>,g<sub>k</sub>) &isin; q&alpha;<sup>k</sup>H<sub>&delta;<sub>k</sub></sub>*.
    Applying Theorem 2 we get that *|g<sub>k</sub>| &leq; q&alpha;<sup>k</sup>(2&alpha;)<sup>1/2-&delta;<sub>k</sub></sup>*,
    and combining that with *|g<sub>k</sub>|&geq;1* leads to (2) *q&alpha;<sup>k</sup>(2&alpha;)<sup>1/2-|&delta;<sub>k</sub>|</sup> &geq; 1*.
  * *&delta;<sub>k</sub> < 0*: to reach a negative *&delta;*, there are two possibilities. Either:
    * *&delta;<sub>k-1</sub> > 0* and step *k* was a (d) transition. In that case we know *&delta;<sub>k</sub> = 1-&delta;<sub>k-1</sub>* and
      *q&alpha;<sup>k-1</sup>(2&alpha;)<sup>1/2-&delta;<sub>k-1</sub></sup> &geq; 1* (from (2) holding for *k-1*), and thus *q&alpha;<sup>k-1</sup>(2&alpha;)<sup>&delta;<sub>k</sub>-1/2</sup> &geq; 1*.
    * *&delta;<sub>k-1</sub> < 0* and step *k* was an (a) or (b) transition. In that case we know *&delta;<sub>k</sub> = 1+&delta;<sub>k-1</sub>* and
      *q&alpha;<sup>k-1</sup>(2&alpha;)<sup>1/2+&delta;<sub>k-1</sub></sup> &geq; 1* (from (2) holding for *k-1*) and thus *q&alpha;<sup>k-1</sup>(2&alpha;)<sup>&delta;<sub>k</sub>-1/2</sup> &geq; 1*

    In both cases we conclude *q&alpha;<sup>k-1</sup>(2&alpha;)<sup>-1/2-|&delta;<sub>k</sub>|</sup> &geq; 1*, which implies
    *2&alpha;<sup>2</sup>q&alpha;<sup>k-1</sup>(2&alpha;)<sup>-1/2-|&delta;<sub>k</sub>|</sup> &geq; 2&alpha;<sup>2</sup>* or
    *q&alpha;<sup>k</sup>(2&alpha;)<sup>1/2-|&delta;<sub>k</sub>|</sup> &geq; 2&alpha;<sup>2</sup> &approx; 1.0956 &geq; 1*, and (2) holds.

Intuitively, what Theorem 4 says is that the range of possible *&delta;* values one traverses through without hitting *|g|<1* shrinks with every iteration
of hddivstep. When that range shrinks to nothing, *|g|<1* must have been hit at least once, and the real `gcd` algorithm would have stopped
at that point.

---

**Theorem 5** If *q&alpha;<sup>k</sup> < 1*, then there exists a *0&leq;j&leq;k* for which *|g<sub>j</sub>|<1*.

For every *&delta;* in the domain (integers plus *1/2*), *(2&alpha;)<sup>1/2-|&delta;|</sup> &leq; 1* because *2&alpha; > 1* and
*1/2-|&delta;| &leq; 0*. From this it follows that condition (2) in Theorem 4 is impossible if *q&alpha;<sup>k</sup> < 1*.

---

**Theorem 6** If *0 &leq; f &leq; M* and *0 &leq; q &leq; M* and *C<sub>sq</sub>M&alpha;<sup>k</sup> < 1* (see appendix for *C<sub>sq</sub>*), then
there exists a *0&leq;j&leq;k* for which *|g<sub>j</sub>|<1*.

It can be verified that *hull([(0,0),(0,1),(1,0),(1,1)]) &sube; C<sub>sq</sub>H<sub>1/2</sub>* by checking the statement for all 4 vertices.
Multiplying both sides by *M*, we get that *&forall; 0 &leq; g &leq; M, 0 &leq; f &leq; M*: *(f,g) &isin; C<sub>sq</sub>MH<sub>1/2</sub>*.
Applying Theorem 5 with *q=C<sub>sq</sub>M* we get that if *C<sub>sq</sub>M&alpha;<sup>k</sup> < 1*, then there exists a *0&leq;j&leq;k* for which *|g<sub>j</sub>|<1*.

---

**Theorem 7** If *0 &leq; g &leq; f &leq; M* and *C<sub>tri</sub>M&alpha;<sup>k</sup> < 1* (see appendix for *C<sub>tri</sub>*), then
there exists a *0&leq;j&leq;k* for which *|g<sub>j</sub>|<1*.

It can be verified that *hull([(0,0),(0,1),(1,1)]) &sube; C<sub>sq</sub>H<sub>1/2</sub>* by checking the statement for all 3 vertices.
Multiplying both sides by *M*, we get that *&forall; 0 &leq; g &leq; f M*: *(f,g) &isin; C<sub>tri</sub>MH<sub>1/2</sub>*.
Applying Theorem 5 with *q=C<sub>tri</sub>M* we get that if *C<sub>tri</sub>M&alpha;<sup>k</sup> < 1*, then there exists a *0&leq;j&leq;k* for which *|g<sub>j</sub>|<1*.

---

The formulas to be proven follow from Theorem 6 and Theorem 7, by taken the *2*-logarithm of both sides, and adding a rational approximation.

## Appendix: C<sub>tri</sub>, C<sub>sq</sub>, P<sub>1/2</sub>, and P<sub>-1/2</sub>

In the expressions below:
* `s` means *&radic;D*
* `r` means *1/&alpha;*.

```
P_{1/2} = [(-r, -237081*r/1329130), ((-0x13bfebb9e0ad7*s-0x267ee7f3548cf845e4ad)*r/0x4cfdcfe6a919f08bc95a, (-0x72e949a2eca3*s-0xdbbb320b1355420b531)*r/0x99fb9fcd5233e11792b4), ((-0x56dd8f90680f-179997*s)*r**53/(132913<<53), (-0xd7b1e5486327-446949*s)*r**53/(664565<<54)), ((-0x347c554bdf9453329fe9*s-0x66437f6cb23f008e62e21941d93)*r**53/(0x267ee7f3548cf845e4ad<<53), (-0x1a4a09b4c5db19d9351d*s-0x3337477bc642862225f78aeda0f)*r**53/(0x267ee7f3548cf845e4ad<<54)), ((-0x8e90449b5819*s-0x1160a8805db99bbb8aa3)*r/0x267ee7f3548cf845e4ad, (-0x11e9432cb9a33*s-0x22a33a688957acf70361)*r/0x99fb9fcd5233e11792b4), (-106930971*r**16/10888232960, -221024137*r**16/43552931840), ((-0xc6943eabc5f3d9*s-0x18321ae6b4db0f4569f7e3)*r**16/0x133f73f9aa467c22f2568000, (-0x19b5396aeb86373*s-0x320316c3b4936e67003d21)*r**16/0x4cfdcfe6a919f08bc95a0000), ((-36612622151-69*s)*r**31/(664565<<30), (-90735628809-171*s)*r**31/(664565<<32)), ((-0x104cca1d5aaa7217d*s-0x1fc39c56d3069a98399ec82f)*r**31/(0x267ee7f3548cf845e4ad<<30), (-0x29d24049b9d0536f3*s-0x517536dc4e425cebb47a8ba1)*r**31/(0x267ee7f3548cf845e4ad<<32)), ((-0xb9d95022a87-24069*s)*r**46/(664565<<45), (-0x1f1f7aee51c9-64491*s)*r**46/(664565<<47)), ((-0x16620c881dd55353c3d*s-0x2b9d07c0edb10d8248138b9a6f)*r**46/(0x267ee7f3548cf845e4ad<<45), (-0x3c7f260bd92346be033*s-0x75dd09d68af8adc5e76c5e6561)*r**46/(0x267ee7f3548cf845e4ad<<47)), ((-0x478e2019161-9267*s)*r**44/(664565<<43), (-0x1893da20fb5-3183*s)*r**44/(60415<<45)), ((-0x899fcaf6f32e4d953b*s-0x10c2b353bb1338e6e28dc67d39)*r**44/(0x267ee7f3548cf845e4ad<<43), (-0x20d69c9a8c49682f8fd*s-0x3ffa55780141a4bd35322e82af)*r**44/(0x267ee7f3548cf845e4ad<<45)), (-1050997*r**5/5316520, -868971*r**5/4253216), ((-0x1f23f1b553f57*s-0x3ce1590d611766506e2d)*r**5/0x267ee7f3548cf845e4ad0, (-0x816cd0ac0c66d*s-0xfbae52c8d1be77df2d7f)*r**5/0x99fb9fcd5233e11792b40), ((-1591853137-3*s)*r**24/(664565<<23), (-1591853137-3*s)*r**24/(132913<<25)), ((-0xacdf0540da6da1d*s-0x1511e97a7991d85ef9f410f)*r**24/(0x267ee7f3548cf845e4ad<<23), (-0x3a1f0a67147ac587*s-0x7138d3332148f783ee1953d)*r**24/(0x267ee7f3548cf845e4ad<<25)), ((-495066325607-933*s)*r**39/(664565<<38), (-587393807553-1107*s)*r**39/(132913<<40)), ((-0xdafa618bf0d6ce0dd*s-0x1aac48e90e2274c97e571f74f)*r**39/(0x267ee7f3548cf845e4ad<<38), (-0x52e13293f6f89a11c7*s-0xa17a119778a9bb482f7fe9ffd)*r**39/(0x267ee7f3548cf845e4ad<<40)), (-427484/664565, -1), ((-0x648ab8fd8f1a*s-0xc619a6951abd21297be)/0x267ee7f3548cf845e4ad, (-0x13bfebb9e0ad7*s-0x267ee7f3548cf845e4ad)/0x4cfdcfe6a919f08bc95a), ((-0x36a87a226949-113259*s)*r**52/(664565<<51), (-0x56dd8f90680f-179997*s)*r**52/(132913<<53)), ((-0x68c92e5c66e4e565ab3*s-0xcc30dfc3aff1e9b0f3aa3950e1)*r**52/(0x267ee7f3548cf845e4ad<<51), (-0x347c554bdf9453329fe9*s-0x66437f6cb23f008e62e21941d93)*r**52/(0x267ee7f3548cf845e4ad<<53)), (-12471097*r**13/1361029120, -106930971*r**13/5444116480), ((-0x170d24aa932f03*s-0x2d2673e0d3fb7ed27b551)*r**13/0x267ee7f3548cf845e4ad000, (-0xc6943eabc5f3d9*s-0x18321ae6b4db0f4569f7e3)*r**13/0x99fb9fcd5233e11792b4000), ((-4775559411-9*s)*r**28/(664565<<28), (-36612622151-69*s)*r**28/(664565<<29)), ((-0x1c50783958bc0b61*s-0x375678a0ab45cb73e18733b)*r**28/(0x267ee7f3548cf845e4ad<<28), (-0x104cca1d5aaa7217d*s-0x1fc39c56d3069a98399ec82f)*r**28/(0x267ee7f3548cf845e4ad<<29)), ((-0xee51060b73-1929*s)*r**43/(664565<<43), (-0xb9d95022a87-24069*s)*r**43/(664565<<44)), ((-0x1a9bfe320172ccf521*s-0x33e835b0f869eb03c33911a7b)*r**43/(0x267ee7f3548cf845e4ad<<43), (-0x16620c881dd55353c3d*s-0x2b9d07c0edb10d8248138b9a6f)*r**43/(0x267ee7f3548cf845e4ad<<44)), ((956703735337+1803*s)*r**41/(664565<<41), (-0x478e2019161-9267*s)*r**41/(664565<<42)), ((0x1c229a30fac2e68e53*s+0x36c8edf3401fe82236236c2c1)*r**41/(0x267ee7f3548cf845e4ad<<41), (-0x899fcaf6f32e4d953b*s-0x10c2b353bb1338e6e28dc67d39)*r**41/(0x267ee7f3548cf845e4ad<<42)), (148983*r**2/664565, -1050997*r**2/2658260), ((0x4801f718210d*s+0x8a148f415cf089dbc5f)*r**2/0x4cfdcfe6a919f08bc95a, (-0x1f23f1b553f57*s-0x3ce1590d611766506e2d)*r**2/0x133f73f9aa467c22f2568), ((1591853137+3*s)*r**21/(664565<<22), (-1591853137-3*s)*r**21/(664565<<22)), ((0x19b5396aeb86373*s+0x320316c3b4936e67003d21)*r**21/0x133f73f9aa467c22f25680000, (-0xacdf0540da6da1d*s-0x1511e97a7991d85ef9f410f)*r**21/(0x267ee7f3548cf845e4ad<<22)), ((90735628809+171*s)*r**36/(664565<<34), (-495066325607-933*s)*r**36/(664565<<37)), ((0x29d24049b9d0536f3*s+0x517536dc4e425cebb47a8ba1)*r**36/(0x267ee7f3548cf845e4ad<<34), (-0xdafa618bf0d6ce0dd*s-0x1aac48e90e2274c97e571f74f)*r**36/(0x267ee7f3548cf845e4ad<<37)), ((0x1f1f7aee51c9+64491*s)*r**51/(664565<<49), (-0x9ab9d53456a7-320613*s)*r**51/(664565<<52)), ((0x3c7f260bd92346be033*s+0x75dd09d68af8adc5e76c5e6561)*r**51/(0x267ee7f3548cf845e4ad<<49), (-0x129a1a2760431ee7e39d*s-0x243f3723850182a5e99cc5b418f)*r**51/(0x267ee7f3548cf845e4ad<<52)), ((0x1893da20fb5+3183*s)*r**49/(60415<<47), (-0x36a87a226949-113259*s)*r**49/(664565<<50)), ((0x20d69c9a8c49682f8fd*s+0x3ffa55780141a4bd35322e82af)*r**49/(0x267ee7f3548cf845e4ad<<47), (-0x68c92e5c66e4e565ab3*s-0xcc30dfc3aff1e9b0f3aa3950e1)*r**49/(0x267ee7f3548cf845e4ad<<50)), (868971*r**10/17012864, -12471097*r**10/680514560), ((0x816cd0ac0c66d*s+0xfbae52c8d1be77df2d7f)*r**10/0x267ee7f3548cf845e4ad00, (-0x170d24aa932f03*s-0x2d2673e0d3fb7ed27b551)*r**10/0x133f73f9aa467c22f256800), (868971*r**8/8506432, -4063121*r**8/170128640), ((0x816cd0ac0c66d*s+0xfbae52c8d1be77df2d7f)*r**8/0x133f73f9aa467c22f25680, (-0x77b2bcfe9344b*s-0xeb5c75a236fcbaa443e9)*r**8/0x4cfdcfe6a919f08bc95a00), ((1591853137+3*s)*r**27/(132913<<26), (-4775559411-9*s)*r**27/(664565<<28)), ((0x3a1f0a67147ac587*s+0x7138d3332148f783ee1953d)*r**27/(0x267ee7f3548cf845e4ad<<26), (-0x1c50783958bc0b61*s-0x375678a0ab45cb73e18733b)*r**27/(0x267ee7f3548cf845e4ad<<28)), ((587393807553+1107*s)*r**42/(132913<<41), (-0xee51060b73-1929*s)*r**42/(664565<<43)), ((0x52e13293f6f89a11c7*s+0xa17a119778a9bb482f7fe9ffd)*r**42/(0x267ee7f3548cf845e4ad<<41), (-0x1a9bfe320172ccf521*s-0x33e835b0f869eb03c33911a7b)*r**42/(0x267ee7f3548cf845e4ad<<43)), ((587393807553+1107*s)*r**40/(132913<<40), (956703735337+1803*s)*r**40/(664565<<41)), ((0x52e13293f6f89a11c7*s+0xa17a119778a9bb482f7fe9ffd)*r**40/(0x267ee7f3548cf845e4ad<<40), (0x1c229a30fac2e68e53*s+0x36c8edf3401fe82236236c2c1)*r**40/(0x267ee7f3548cf845e4ad<<41)), (r, 237081*r/1329130), ((0x13bfebb9e0ad7*s+0x267ee7f3548cf845e4ad)*r/0x4cfdcfe6a919f08bc95a, (0x72e949a2eca3*s+0xdbbb320b1355420b531)*r/0x99fb9fcd5233e11792b4), ((0x56dd8f90680f+179997*s)*r**53/(132913<<53), (0xd7b1e5486327+446949*s)*r**53/(664565<<54)), ((0x347c554bdf9453329fe9*s+0x66437f6cb23f008e62e21941d93)*r**53/(0x267ee7f3548cf845e4ad<<53), (0x1a4a09b4c5db19d9351d*s+0x3337477bc642862225f78aeda0f)*r**53/(0x267ee7f3548cf845e4ad<<54)), ((0x8e90449b5819*s+0x1160a8805db99bbb8aa3)*r/0x267ee7f3548cf845e4ad, (0x11e9432cb9a33*s+0x22a33a688957acf70361)*r/0x99fb9fcd5233e11792b4), (106930971*r**16/10888232960, 221024137*r**16/43552931840), ((0xc6943eabc5f3d9*s+0x18321ae6b4db0f4569f7e3)*r**16/0x133f73f9aa467c22f2568000, (0x19b5396aeb86373*s+0x320316c3b4936e67003d21)*r**16/0x4cfdcfe6a919f08bc95a0000), ((36612622151+69*s)*r**31/(664565<<30), (90735628809+171*s)*r**31/(664565<<32)), ((0x104cca1d5aaa7217d*s+0x1fc39c56d3069a98399ec82f)*r**31/(0x267ee7f3548cf845e4ad<<30), (0x29d24049b9d0536f3*s+0x517536dc4e425cebb47a8ba1)*r**31/(0x267ee7f3548cf845e4ad<<32)), ((0xb9d95022a87+24069*s)*r**46/(664565<<45), (0x1f1f7aee51c9+64491*s)*r**46/(664565<<47)), ((0x16620c881dd55353c3d*s+0x2b9d07c0edb10d8248138b9a6f)*r**46/(0x267ee7f3548cf845e4ad<<45), (0x3c7f260bd92346be033*s+0x75dd09d68af8adc5e76c5e6561)*r**46/(0x267ee7f3548cf845e4ad<<47)), ((0x478e2019161+9267*s)*r**44/(664565<<43), (0x1893da20fb5+3183*s)*r**44/(60415<<45)), ((0x899fcaf6f32e4d953b*s+0x10c2b353bb1338e6e28dc67d39)*r**44/(0x267ee7f3548cf845e4ad<<43), (0x20d69c9a8c49682f8fd*s+0x3ffa55780141a4bd35322e82af)*r**44/(0x267ee7f3548cf845e4ad<<45)), (1050997*r**5/5316520, 868971*r**5/4253216), ((0x1f23f1b553f57*s+0x3ce1590d611766506e2d)*r**5/0x267ee7f3548cf845e4ad0, (0x816cd0ac0c66d*s+0xfbae52c8d1be77df2d7f)*r**5/0x99fb9fcd5233e11792b40), ((1591853137+3*s)*r**24/(664565<<23), (1591853137+3*s)*r**24/(132913<<25)), ((0xacdf0540da6da1d*s+0x1511e97a7991d85ef9f410f)*r**24/(0x267ee7f3548cf845e4ad<<23), (0x3a1f0a67147ac587*s+0x7138d3332148f783ee1953d)*r**24/(0x267ee7f3548cf845e4ad<<25)), ((495066325607+933*s)*r**39/(664565<<38), (587393807553+1107*s)*r**39/(132913<<40)), ((0xdafa618bf0d6ce0dd*s+0x1aac48e90e2274c97e571f74f)*r**39/(0x267ee7f3548cf845e4ad<<38), (0x52e13293f6f89a11c7*s+0xa17a119778a9bb482f7fe9ffd)*r**39/(0x267ee7f3548cf845e4ad<<40)), (427484/664565, 1), ((0x648ab8fd8f1a*s+0xc619a6951abd21297be)/0x267ee7f3548cf845e4ad, (0x13bfebb9e0ad7*s+0x267ee7f3548cf845e4ad)/0x4cfdcfe6a919f08bc95a), ((0x36a87a226949+113259*s)*r**52/(664565<<51), (0x56dd8f90680f+179997*s)*r**52/(132913<<53)), ((0x68c92e5c66e4e565ab3*s+0xcc30dfc3aff1e9b0f3aa3950e1)*r**52/(0x267ee7f3548cf845e4ad<<51), (0x347c554bdf9453329fe9*s+0x66437f6cb23f008e62e21941d93)*r**52/(0x267ee7f3548cf845e4ad<<53)), (12471097*r**13/1361029120, 106930971*r**13/5444116480), ((0x170d24aa932f03*s+0x2d2673e0d3fb7ed27b551)*r**13/0x267ee7f3548cf845e4ad000, (0xc6943eabc5f3d9*s+0x18321ae6b4db0f4569f7e3)*r**13/0x99fb9fcd5233e11792b4000), ((4775559411+9*s)*r**28/(664565<<28), (36612622151+69*s)*r**28/(664565<<29)), ((0x1c50783958bc0b61*s+0x375678a0ab45cb73e18733b)*r**28/(0x267ee7f3548cf845e4ad<<28), (0x104cca1d5aaa7217d*s+0x1fc39c56d3069a98399ec82f)*r**28/(0x267ee7f3548cf845e4ad<<29)), ((0xee51060b73+1929*s)*r**43/(664565<<43), (0xb9d95022a87+24069*s)*r**43/(664565<<44)), ((0x1a9bfe320172ccf521*s+0x33e835b0f869eb03c33911a7b)*r**43/(0x267ee7f3548cf845e4ad<<43), (0x16620c881dd55353c3d*s+0x2b9d07c0edb10d8248138b9a6f)*r**43/(0x267ee7f3548cf845e4ad<<44)), ((-956703735337-1803*s)*r**41/(664565<<41), (0x478e2019161+9267*s)*r**41/(664565<<42)), ((-0x1c229a30fac2e68e53*s-0x36c8edf3401fe82236236c2c1)*r**41/(0x267ee7f3548cf845e4ad<<41), (0x899fcaf6f32e4d953b*s+0x10c2b353bb1338e6e28dc67d39)*r**41/(0x267ee7f3548cf845e4ad<<42)), (-148983*r**2/664565, 1050997*r**2/2658260), ((-0x4801f718210d*s-0x8a148f415cf089dbc5f)*r**2/0x4cfdcfe6a919f08bc95a, (0x1f23f1b553f57*s+0x3ce1590d611766506e2d)*r**2/0x133f73f9aa467c22f2568), ((-1591853137-3*s)*r**21/(664565<<22), (1591853137+3*s)*r**21/(664565<<22)), ((-0x19b5396aeb86373*s-0x320316c3b4936e67003d21)*r**21/0x133f73f9aa467c22f25680000, (0xacdf0540da6da1d*s+0x1511e97a7991d85ef9f410f)*r**21/(0x267ee7f3548cf845e4ad<<22)), ((-90735628809-171*s)*r**36/(664565<<34), (495066325607+933*s)*r**36/(664565<<37)), ((-0x29d24049b9d0536f3*s-0x517536dc4e425cebb47a8ba1)*r**36/(0x267ee7f3548cf845e4ad<<34), (0xdafa618bf0d6ce0dd*s+0x1aac48e90e2274c97e571f74f)*r**36/(0x267ee7f3548cf845e4ad<<37)), ((-0x1f1f7aee51c9-64491*s)*r**51/(664565<<49), (0x9ab9d53456a7+320613*s)*r**51/(664565<<52)), ((-0x3c7f260bd92346be033*s-0x75dd09d68af8adc5e76c5e6561)*r**51/(0x267ee7f3548cf845e4ad<<49), (0x129a1a2760431ee7e39d*s+0x243f3723850182a5e99cc5b418f)*r**51/(0x267ee7f3548cf845e4ad<<52)), ((-0x1893da20fb5-3183*s)*r**49/(60415<<47), (0x36a87a226949+113259*s)*r**49/(664565<<50)), ((-0x20d69c9a8c49682f8fd*s-0x3ffa55780141a4bd35322e82af)*r**49/(0x267ee7f3548cf845e4ad<<47), (0x68c92e5c66e4e565ab3*s+0xcc30dfc3aff1e9b0f3aa3950e1)*r**49/(0x267ee7f3548cf845e4ad<<50)), (-868971*r**10/17012864, 12471097*r**10/680514560), ((-0x816cd0ac0c66d*s-0xfbae52c8d1be77df2d7f)*r**10/0x267ee7f3548cf845e4ad00, (0x170d24aa932f03*s+0x2d2673e0d3fb7ed27b551)*r**10/0x133f73f9aa467c22f256800), (-868971*r**8/8506432, 4063121*r**8/170128640), ((-0x816cd0ac0c66d*s-0xfbae52c8d1be77df2d7f)*r**8/0x133f73f9aa467c22f25680, (0x77b2bcfe9344b*s+0xeb5c75a236fcbaa443e9)*r**8/0x4cfdcfe6a919f08bc95a00), ((-1591853137-3*s)*r**27/(132913<<26), (4775559411+9*s)*r**27/(664565<<28)), ((-0x3a1f0a67147ac587*s-0x7138d3332148f783ee1953d)*r**27/(0x267ee7f3548cf845e4ad<<26), (0x1c50783958bc0b61*s+0x375678a0ab45cb73e18733b)*r**27/(0x267ee7f3548cf845e4ad<<28)), ((-587393807553-1107*s)*r**42/(132913<<41), (0xee51060b73+1929*s)*r**42/(664565<<43)), ((-0x52e13293f6f89a11c7*s-0xa17a119778a9bb482f7fe9ffd)*r**42/(0x267ee7f3548cf845e4ad<<41), (0x1a9bfe320172ccf521*s+0x33e835b0f869eb03c33911a7b)*r**42/(0x267ee7f3548cf845e4ad<<43)), ((-587393807553-1107*s)*r**40/(132913<<40), (-956703735337-1803*s)*r**40/(664565<<41)), ((-0x52e13293f6f89a11c7*s-0xa17a119778a9bb482f7fe9ffd)*r**40/(0x267ee7f3548cf845e4ad<<40), (-0x1c229a30fac2e68e53*s-0x36c8edf3401fe82236236c2c1)*r**40/(0x267ee7f3548cf845e4ad<<41))]]
P_{-1/2} = [(-r**2/2, 190403*r**2/2658260), ((-0x13bfebb9e0ad7*s-0x267ee7f3548cf845e4ad)*r**2/0x99fb9fcd5233e11792b4, (0x562c28583191*s+0xb0781b1f22250047a4b)*r**2/0x133f73f9aa467c22f2568), (-119998/132913, 2029/664565), ((-0x8e90449b5819*s-0x1160a8805db99bbb8aa3)/0x267ee7f3548cf845e4ad, (-0x173a994ea01*s+0x1e1698321b8a8011e5)/0x4cfdcfe6a919f08bc95a), (-106930971*r**15/10888232960, -1432439*r**15/4355293184), ((-0xc6943eabc5f3d9*s-0x18321ae6b4db0f4569f7e3)*r**15/0x133f73f9aa467c22f2568000, (-0xe2b19572c7bc1*s-0x19ee0f64add4fdc2c4d5b)*r**15/0x267ee7f3548cf845e4ad0000), ((-36612622151-69*s)*r**30/(664565<<30), (-1591853137-3*s)*r**30/(60415<<31)), ((-0x104cca1d5aaa7217d*s-0x1fc39c56d3069a98399ec82f)*r**30/(0x267ee7f3548cf845e4ad<<30), (-0x938ac0f047b6f3f9*s-0x11edfe2ea83527bb413cfb43)*r**30/(0x267ee7f3548cf845e4ad<<31)), ((-0xb9d95022a87-24069*s)*r**45/(664565<<45), (-0x7e450e9fcbb-16353*s)*r**45/(664565<<46)), ((-0x16620c881dd55353c3d*s-0x2b9d07c0edb10d8248138b9a6f)*r**45/(0x267ee7f3548cf845e4ad<<45), (-0xfbb0cfb9d78a0167b9*s-0x1ea2fa54af9692c15745473083)*r**45/(0x267ee7f3548cf845e4ad<<46)), ((-0x478e2019161-9267*s)*r**43/(664565<<43), (-0x7f3e1f38a05-16479*s)*r**43/(664565<<44)), ((-0x899fcaf6f32e4d953b*s-0x10c2b353bb1338e6e28dc67d39)*r**43/(0x267ee7f3548cf845e4ad<<43), (-0xfa2a33bade39e7ce87*s-0x1e74eed08b1b32ef7016a1883d)*r**43/(0x267ee7f3548cf845e4ad<<44)), (-1050997*r**4/5316520, -2242861*r**4/10633040), ((-0x1f23f1b553f57*s-0x3ce1590d611766506e2d)*r**4/0x267ee7f3548cf845e4ad0, (-0x4324ed41647bf*s-0x81eba0ae0f8fab3e5125)*r**4/0x4cfdcfe6a919f08bc95a0), ((-1591853137-3*s)*r**23/(664565<<23), (-4775559411-9*s)*r**23/(664565<<24)), ((-0xacdf0540da6da1d*s-0x1511e97a7991d85ef9f410f)*r**23/(0x267ee7f3548cf845e4ad<<23), (-0x248329bef92d114d*s-0x4715003e2e2546c5fa3131f)*r**23/(0x267ee7f3548cf845e4ad<<24)), ((-495066325607-933*s)*r**38/(664565<<38), (-0x1c5487dc2f7-3669*s)*r**38/(664565<<39)), ((-0xdafa618bf0d6ce0dd*s-0x1aac48e90e2274c97e571f74f)*r**38/(0x267ee7f3548cf845e4ad<<38), (-0x3781e66278ddc0500d*s-0x6c217fc55c64d1b532d1ab15f)*r**38/(0x267ee7f3548cf845e4ad<<39)), ((-0x9ab9d53456a7-320613*s)*r**53/(664565<<53), (-0x28cb184197337-1352469*s)*r**53/(664565<<54)), ((-0x129a1a2760431ee7e39d*s-0x243f3723850182a5e99cc5b418f)*r**53/(0x267ee7f3548cf845e4ad<<53), (-0x4f194033396665a5e6cd*s-0x9a1c40fa0ffa306bd109241979f)*r**53/(0x267ee7f3548cf845e4ad<<54)), ((-0x36a87a226949-113259*s)*r**51/(664565<<51), (-0x14502d98d35b9-673467*s)*r**51/(664565<<52)), ((-0x68c92e5c66e4e565ab3*s-0xcc30dfc3aff1e9b0f3aa3950e1)*r**51/(0x267ee7f3548cf845e4ad<<51), (-0x27632f8052b7b685ea83*s-0x4cbd63743c40c358446cd217bd1)*r**51/(0x267ee7f3548cf845e4ad<<52)), (-12471097*r**12/1361029120, -81988777*r**12/2722058240), ((-0x170d24aa932f03*s-0x2d2673e0d3fb7ed27b551)*r**12/0x267ee7f3548cf845e4ad000, (-0x9879f5569f95d3*s-0x128d4c6a9a5b9f6b1a8d41)*r**12/0x4cfdcfe6a919f08bc95a000), (-4063121*r**10/340257280, -38821961*r**10/680514560), ((-0x77b2bcfe9344b*s-0xeb5c75a236fcbaa443e9)*r**10/0x99fb9fcd5233e11792b400, (-0x48319425ef67b3*s-0x8c8cf0be8c4f0799dafe1)*r**10/0x133f73f9aa467c22f256800), ((-4775559411-9*s)*r**29/(664565<<29), (-1591853137-3*s)*r**29/(15455<<30)), ((-0x1c50783958bc0b61*s-0x375678a0ab45cb73e18733b)*r**29/(0x267ee7f3548cf845e4ad<<29), (-0x1ed48cb71fc923799*s-0x3c11d1239b58d87935251d23)*r**29/(0x267ee7f3548cf845e4ad<<30)), ((-0xee51060b73-1929*s)*r**44/(664565<<44), (-0x164cd8fe499b-46209*s)*r**44/(664565<<45)), ((-0x1a9bfe320172ccf521*s-0x33e835b0f869eb03c33911a7b)*r**44/(0x267ee7f3548cf845e4ad<<44), (-0x2b1a592d1b9379d8359*s-0x53fb8c26cbdb7c5453f3861a63)*r**44/(0x267ee7f3548cf845e4ad<<45)), ((956703735337+1803*s)*r**42/(664565<<42), (-0x9d083ffa0eb-20337*s)*r**42/(664565<<43)), ((0x1c229a30fac2e68e53*s+0x36c8edf3401fe82236236c2c1)*r**42/(0x267ee7f3548cf845e4ad<<42), (-0x12f62301ee11f81b8c9*s-0x24f1f586aa28704fe87dc3bd33)*r**42/(0x267ee7f3548cf845e4ad<<43)), (237081*r**3/2658260, -2421179*r**3/5316520), ((0x72e949a2eca3*s+0xdbbb320b1355420b531)*r**3/0x133f73f9aa467c22f2568, (-0x47d11a4d53eb9*s-0x8c3fecaca0fe8cf6dd83)*r**3/0x267ee7f3548cf845e4ad0), (148983*r/664565, -1050997*r/1329130), ((0x4801f718210d*s+0x8a148f415cf089dbc5f)*r/0x4cfdcfe6a919f08bc95a, (-0x1f23f1b553f57*s-0x3ce1590d611766506e2d)*r/0x99fb9fcd5233e11792b4), (221024137*r**20/174211727360, -1489871399*r**20/(664565<<20)), ((0x19b5396aeb86373*s+0x320316c3b4936e67003d21)*r**20/0x133f73f9aa467c22f25680000, (-0xacdf0540da6da1d*s-0x1511e97a7991d85ef9f410f)*r**20/(0x267ee7f3548cf845e4ad<<21)), ((90735628809+171*s)*r**35/(664565<<34), (-495066325607-933*s)*r**35/(664565<<36)), ((0x29d24049b9d0536f3*s+0x517536dc4e425cebb47a8ba1)*r**35/(0x267ee7f3548cf845e4ad<<34), (-0xdafa618bf0d6ce0dd*s-0x1aac48e90e2274c97e571f74f)*r**35/(0x267ee7f3548cf845e4ad<<36)), ((0x1f1f7aee51c9+64491*s)*r**50/(664565<<49), (-0x9ab9d53456a7-320613*s)*r**50/(664565<<51)), ((0x3c7f260bd92346be033*s+0x75dd09d68af8adc5e76c5e6561)*r**50/(0x267ee7f3548cf845e4ad<<49), (-0x129a1a2760431ee7e39d*s-0x243f3723850182a5e99cc5b418f)*r**50/(0x267ee7f3548cf845e4ad<<51)), ((0x1893da20fb5+3183*s)*r**48/(60415<<47), (-0x36a87a226949-113259*s)*r**48/(664565<<49)), ((0x20d69c9a8c49682f8fd*s+0x3ffa55780141a4bd35322e82af)*r**48/(0x267ee7f3548cf845e4ad<<47), (-0x68c92e5c66e4e565ab3*s-0xcc30dfc3aff1e9b0f3aa3950e1)*r**48/(0x267ee7f3548cf845e4ad<<49)), (868971*r**9/17012864, -12471097*r**9/340257280), ((0x816cd0ac0c66d*s+0xfbae52c8d1be77df2d7f)*r**9/0x267ee7f3548cf845e4ad00, (-0x170d24aa932f03*s-0x2d2673e0d3fb7ed27b551)*r**9/0x99fb9fcd5233e11792b400), (868971*r**7/8506432, -4063121*r**7/85064320), ((0x816cd0ac0c66d*s+0xfbae52c8d1be77df2d7f)*r**7/0x133f73f9aa467c22f25680, (-0x77b2bcfe9344b*s-0xeb5c75a236fcbaa443e9)*r**7/0x267ee7f3548cf845e4ad00), ((1591853137+3*s)*r**26/(132913<<26), (-4775559411-9*s)*r**26/(664565<<27)), ((0x3a1f0a67147ac587*s+0x7138d3332148f783ee1953d)*r**26/(0x267ee7f3548cf845e4ad<<26), (-0x1c50783958bc0b61*s-0x375678a0ab45cb73e18733b)*r**26/(0x267ee7f3548cf845e4ad<<27)), ((587393807553+1107*s)*r**41/(132913<<41), (-0xee51060b73-1929*s)*r**41/(664565<<42)), ((0x52e13293f6f89a11c7*s+0xa17a119778a9bb482f7fe9ffd)*r**41/(0x267ee7f3548cf845e4ad<<41), (-0x1a9bfe320172ccf521*s-0x33e835b0f869eb03c33911a7b)*r**41/(0x267ee7f3548cf845e4ad<<42)), (r**2/2, -190403*r**2/2658260), ((0x13bfebb9e0ad7*s+0x267ee7f3548cf845e4ad)*r**2/0x99fb9fcd5233e11792b4, (-0x562c28583191*s-0xb0781b1f22250047a4b)*r**2/0x133f73f9aa467c22f2568), (119998/132913, -2029/664565), ((0x8e90449b5819*s+0x1160a8805db99bbb8aa3)/0x267ee7f3548cf845e4ad, (0x173a994ea01*s-0x1e1698321b8a8011e5)/0x4cfdcfe6a919f08bc95a), (106930971*r**15/10888232960, 1432439*r**15/4355293184), ((0xc6943eabc5f3d9*s+0x18321ae6b4db0f4569f7e3)*r**15/0x133f73f9aa467c22f2568000, (0xe2b19572c7bc1*s+0x19ee0f64add4fdc2c4d5b)*r**15/0x267ee7f3548cf845e4ad0000), ((36612622151+69*s)*r**30/(664565<<30), (1591853137+3*s)*r**30/(60415<<31)), ((0x104cca1d5aaa7217d*s+0x1fc39c56d3069a98399ec82f)*r**30/(0x267ee7f3548cf845e4ad<<30), (0x938ac0f047b6f3f9*s+0x11edfe2ea83527bb413cfb43)*r**30/(0x267ee7f3548cf845e4ad<<31)), ((0xb9d95022a87+24069*s)*r**45/(664565<<45), (0x7e450e9fcbb+16353*s)*r**45/(664565<<46)), ((0x16620c881dd55353c3d*s+0x2b9d07c0edb10d8248138b9a6f)*r**45/(0x267ee7f3548cf845e4ad<<45), (0xfbb0cfb9d78a0167b9*s+0x1ea2fa54af9692c15745473083)*r**45/(0x267ee7f3548cf845e4ad<<46)), ((0x478e2019161+9267*s)*r**43/(664565<<43), (0x7f3e1f38a05+16479*s)*r**43/(664565<<44)), ((0x899fcaf6f32e4d953b*s+0x10c2b353bb1338e6e28dc67d39)*r**43/(0x267ee7f3548cf845e4ad<<43), (0xfa2a33bade39e7ce87*s+0x1e74eed08b1b32ef7016a1883d)*r**43/(0x267ee7f3548cf845e4ad<<44)), (1050997*r**4/5316520, 2242861*r**4/10633040), ((0x1f23f1b553f57*s+0x3ce1590d611766506e2d)*r**4/0x267ee7f3548cf845e4ad0, (0x4324ed41647bf*s+0x81eba0ae0f8fab3e5125)*r**4/0x4cfdcfe6a919f08bc95a0), ((1591853137+3*s)*r**23/(664565<<23), (4775559411+9*s)*r**23/(664565<<24)), ((0xacdf0540da6da1d*s+0x1511e97a7991d85ef9f410f)*r**23/(0x267ee7f3548cf845e4ad<<23), (0x248329bef92d114d*s+0x4715003e2e2546c5fa3131f)*r**23/(0x267ee7f3548cf845e4ad<<24)), ((495066325607+933*s)*r**38/(664565<<38), (0x1c5487dc2f7+3669*s)*r**38/(664565<<39)), ((0xdafa618bf0d6ce0dd*s+0x1aac48e90e2274c97e571f74f)*r**38/(0x267ee7f3548cf845e4ad<<38), (0x3781e66278ddc0500d*s+0x6c217fc55c64d1b532d1ab15f)*r**38/(0x267ee7f3548cf845e4ad<<39)), ((0x9ab9d53456a7+320613*s)*r**53/(664565<<53), (0x28cb184197337+1352469*s)*r**53/(664565<<54)), ((0x129a1a2760431ee7e39d*s+0x243f3723850182a5e99cc5b418f)*r**53/(0x267ee7f3548cf845e4ad<<53), (0x4f194033396665a5e6cd*s+0x9a1c40fa0ffa306bd109241979f)*r**53/(0x267ee7f3548cf845e4ad<<54)), ((0x36a87a226949+113259*s)*r**51/(664565<<51), (0x14502d98d35b9+673467*s)*r**51/(664565<<52)), ((0x68c92e5c66e4e565ab3*s+0xcc30dfc3aff1e9b0f3aa3950e1)*r**51/(0x267ee7f3548cf845e4ad<<51), (0x27632f8052b7b685ea83*s+0x4cbd63743c40c358446cd217bd1)*r**51/(0x267ee7f3548cf845e4ad<<52)), (12471097*r**12/1361029120, 81988777*r**12/2722058240), ((0x170d24aa932f03*s+0x2d2673e0d3fb7ed27b551)*r**12/0x267ee7f3548cf845e4ad000, (0x9879f5569f95d3*s+0x128d4c6a9a5b9f6b1a8d41)*r**12/0x4cfdcfe6a919f08bc95a000), (4063121*r**10/340257280, 38821961*r**10/680514560), ((0x77b2bcfe9344b*s+0xeb5c75a236fcbaa443e9)*r**10/0x99fb9fcd5233e11792b400, (0x48319425ef67b3*s+0x8c8cf0be8c4f0799dafe1)*r**10/0x133f73f9aa467c22f256800), ((4775559411+9*s)*r**29/(664565<<29), (1591853137+3*s)*r**29/(15455<<30)), ((0x1c50783958bc0b61*s+0x375678a0ab45cb73e18733b)*r**29/(0x267ee7f3548cf845e4ad<<29), (0x1ed48cb71fc923799*s+0x3c11d1239b58d87935251d23)*r**29/(0x267ee7f3548cf845e4ad<<30)), ((0xee51060b73+1929*s)*r**44/(664565<<44), (0x164cd8fe499b+46209*s)*r**44/(664565<<45)), ((0x1a9bfe320172ccf521*s+0x33e835b0f869eb03c33911a7b)*r**44/(0x267ee7f3548cf845e4ad<<44), (0x2b1a592d1b9379d8359*s+0x53fb8c26cbdb7c5453f3861a63)*r**44/(0x267ee7f3548cf845e4ad<<45)), ((-956703735337-1803*s)*r**42/(664565<<42), (0x9d083ffa0eb+20337*s)*r**42/(664565<<43)), ((-0x1c229a30fac2e68e53*s-0x36c8edf3401fe82236236c2c1)*r**42/(0x267ee7f3548cf845e4ad<<42), (0x12f62301ee11f81b8c9*s+0x24f1f586aa28704fe87dc3bd33)*r**42/(0x267ee7f3548cf845e4ad<<43)), (-237081*r**3/2658260, 2421179*r**3/5316520), ((-0x72e949a2eca3*s-0xdbbb320b1355420b531)*r**3/0x133f73f9aa467c22f2568, (0x47d11a4d53eb9*s+0x8c3fecaca0fe8cf6dd83)*r**3/0x267ee7f3548cf845e4ad0), (-148983*r/664565, 1050997*r/1329130), ((-0x4801f718210d*s-0x8a148f415cf089dbc5f)*r/0x4cfdcfe6a919f08bc95a, (0x1f23f1b553f57*s+0x3ce1590d611766506e2d)*r/0x99fb9fcd5233e11792b4), (-221024137*r**20/174211727360, 1489871399*r**20/(664565<<20)), ((-0x19b5396aeb86373*s-0x320316c3b4936e67003d21)*r**20/0x133f73f9aa467c22f25680000, (0xacdf0540da6da1d*s+0x1511e97a7991d85ef9f410f)*r**20/(0x267ee7f3548cf845e4ad<<21)), ((-90735628809-171*s)*r**35/(664565<<34), (495066325607+933*s)*r**35/(664565<<36)), ((-0x29d24049b9d0536f3*s-0x517536dc4e425cebb47a8ba1)*r**35/(0x267ee7f3548cf845e4ad<<34), (0xdafa618bf0d6ce0dd*s+0x1aac48e90e2274c97e571f74f)*r**35/(0x267ee7f3548cf845e4ad<<36)), ((-0x1f1f7aee51c9-64491*s)*r**50/(664565<<49), (0x9ab9d53456a7+320613*s)*r**50/(664565<<51)), ((-0x3c7f260bd92346be033*s-0x75dd09d68af8adc5e76c5e6561)*r**50/(0x267ee7f3548cf845e4ad<<49), (0x129a1a2760431ee7e39d*s+0x243f3723850182a5e99cc5b418f)*r**50/(0x267ee7f3548cf845e4ad<<51)), ((-0x1893da20fb5-3183*s)*r**48/(60415<<47), (0x36a87a226949+113259*s)*r**48/(664565<<49)), ((-0x20d69c9a8c49682f8fd*s-0x3ffa55780141a4bd35322e82af)*r**48/(0x267ee7f3548cf845e4ad<<47), (0x68c92e5c66e4e565ab3*s+0xcc30dfc3aff1e9b0f3aa3950e1)*r**48/(0x267ee7f3548cf845e4ad<<49)), (-868971*r**9/17012864, 12471097*r**9/340257280), ((-0x816cd0ac0c66d*s-0xfbae52c8d1be77df2d7f)*r**9/0x267ee7f3548cf845e4ad00, (0x170d24aa932f03*s+0x2d2673e0d3fb7ed27b551)*r**9/0x99fb9fcd5233e11792b400), (-868971*r**7/8506432, 4063121*r**7/85064320), ((-0x816cd0ac0c66d*s-0xfbae52c8d1be77df2d7f)*r**7/0x133f73f9aa467c22f25680, (0x77b2bcfe9344b*s+0xeb5c75a236fcbaa443e9)*r**7/0x267ee7f3548cf845e4ad00), ((-1591853137-3*s)*r**26/(132913<<26), (4775559411+9*s)*r**26/(664565<<27)), ((-0x3a1f0a67147ac587*s-0x7138d3332148f783ee1953d)*r**26/(0x267ee7f3548cf845e4ad<<26), (0x1c50783958bc0b61*s+0x375678a0ab45cb73e18733b)*r**26/(0x267ee7f3548cf845e4ad<<27)), ((-587393807553-1107*s)*r**41/(132913<<41), (0xee51060b73+1929*s)*r**41/(664565<<42)), ((-0x52e13293f6f89a11c7*s-0xa17a119778a9bb482f7fe9ffd)*r**41/(0x267ee7f3548cf845e4ad<<41), (0x1a9bfe320172ccf521*s+0x33e835b0f869eb03c33911a7b)*r**41/(0x267ee7f3548cf845e4ad<<42))]
C_{tri} = ((0xedbee290c57d5e2f07b5708c7dbbb75*s-0x1d018296a605b6fd26db98c74a27ce040510557)/r**44+(149208097289600249806643527680*s-300401370399750633778348248661638512640)/r**5)/(0xe567fd0e3791bb433842709<<34)
C_{sq} = ((0x6009e6b579e62430024d3ea49ff*s-0xbb30b957adbc92f5a51ca9a639cfea8de5)/r**43+(2467686814853616087805909073920*s-1296436581718759240950871850120779857920)/r**41)/(0x6e60adbbc7ed6ce1f8d<<31)
```

This stable hull was constructed by Daniel J. Bernstein and Bo-Yin Yang, by repeatedly adding transformed and rescaled points to a hull, and finding what it converges to.
