import functools

# Define number field with sqrtD = sqrt(D) and
# shrinkage = ((1591853137+3*sqrt(D))/2^55)^(1/54).
print("Defining number field...")
proof.all(False)
D = 273548757304312537
K.<sqrtD> = NumberField(x^2-D)
Kz.<z> = K[]
L.<shrinkage> = NumberField(z^54-(1591853137+3*sqrtD)/2^55)


# Define embedding phi of L into reals with 1024 bit precision.
print("Finding embedding...")
bits = 1024
RR = RealField(bits)
for em in L.embeddings(RR):
  if em(shrinkage) > 0:
    if em((shrinkage^54)*2^55-1591853137) > 0:
      if em(sqrtD) > 0:
        phi = em
        break

print(em(shrinkage))

def convex_hull(points):
    """Computes the convex hull of a set of 2D points.

    Input: an iterable sequence of (x, y) pairs representing the points.
    Output: a list of vertices of the convex hull in counter-clockwise order,
      starting from the vertex with the lexicographically smallest coordinates.
    Implements Andrew's monotone chain algorithm. O(n log n) complexity.
    """
    def cross(o, a, b):
        """2D cross product of the OA and OB vectors, i.e. the z-component of
        their 3D cross product.

        Returns a positive value if OAB makes a counter-clockwise turn,
        negative for clockwise turn, and zero if the points are collinear.
        """
        return ((a[0] - o[0]) * (b[1] - o[1])) - ((a[1] - o[1]) * (b[0] - o[0]))

    def compare_points(a, b):
        """Compare two points a and b, using the phi embedding."""
        diff = (a[0] - b[0], a[1] - b[1])
        if diff[0] != 0:
            return phi(diff[0])
        if diff[1] != 0:
            return phi(diff[1])
        return 0

    # Boring case: no points.
    if len(points) <= 1:
        return points
    # Sort the points lexicographically.
    points = sorted(points, key=functools.cmp_to_key(compare_points))
    # Build lower hull.
    lower = [points[0]]
    for p in points[1:]:
        while len(lower) >= 2 and phi(cross(lower[-2], lower[-1], p)) <= 0:
            lower.pop()
        if lower[-1] != p:
            lower.append(p)
    if (len(lower) == 1):
        return lower
    # Build upper hull.
    upper = [points[-1]]
    for p in reversed(points[:-1]):
        while len(upper) >= 2 and phi(cross(upper[-2], upper[-1], p)) <= 0:
            upper.pop()
        if upper[-1] != p:
            upper.append(p)
    # Concatenation of the lower and upper hulls gives the convex hull.
    # The Last point of each list is omitted because it is repeated at the beginning
    # of the other list. 
    return lower[:-1] + upper[:-1]

# Define the fixed delta=1/2 and delta=-1/2 hulls.
print("Defining delta=1/2 and delta=-1/2 hulls...")
s = sqrtD
r = 1/shrinkage
HULL_POS_HALF = [(-r, -237081*r/1329130), ((-0x13bfebb9e0ad7*s-0x267ee7f3548cf845e4ad)*r/0x4cfdcfe6a919f08bc95a, (-0x72e949a2eca3*s-0xdbbb320b1355420b531)*r/0x99fb9fcd5233e11792b4), ((-0x56dd8f90680f-179997*s)*r**53/(132913<<53), (-0xd7b1e5486327-446949*s)*r**53/(664565<<54)), ((-0x347c554bdf9453329fe9*s-0x66437f6cb23f008e62e21941d93)*r**53/(0x267ee7f3548cf845e4ad<<53), (-0x1a4a09b4c5db19d9351d*s-0x3337477bc642862225f78aeda0f)*r**53/(0x267ee7f3548cf845e4ad<<54)), ((-0x8e90449b5819*s-0x1160a8805db99bbb8aa3)*r/0x267ee7f3548cf845e4ad, (-0x11e9432cb9a33*s-0x22a33a688957acf70361)*r/0x99fb9fcd5233e11792b4), (-106930971*r**16/10888232960, -221024137*r**16/43552931840), ((-0xc6943eabc5f3d9*s-0x18321ae6b4db0f4569f7e3)*r**16/0x133f73f9aa467c22f2568000, (-0x19b5396aeb86373*s-0x320316c3b4936e67003d21)*r**16/0x4cfdcfe6a919f08bc95a0000), ((-36612622151-69*s)*r**31/(664565<<30), (-90735628809-171*s)*r**31/(664565<<32)), ((-0x104cca1d5aaa7217d*s-0x1fc39c56d3069a98399ec82f)*r**31/(0x267ee7f3548cf845e4ad<<30), (-0x29d24049b9d0536f3*s-0x517536dc4e425cebb47a8ba1)*r**31/(0x267ee7f3548cf845e4ad<<32)), ((-0xb9d95022a87-24069*s)*r**46/(664565<<45), (-0x1f1f7aee51c9-64491*s)*r**46/(664565<<47)), ((-0x16620c881dd55353c3d*s-0x2b9d07c0edb10d8248138b9a6f)*r**46/(0x267ee7f3548cf845e4ad<<45), (-0x3c7f260bd92346be033*s-0x75dd09d68af8adc5e76c5e6561)*r**46/(0x267ee7f3548cf845e4ad<<47)), ((-0x478e2019161-9267*s)*r**44/(664565<<43), (-0x1893da20fb5-3183*s)*r**44/(60415<<45)), ((-0x899fcaf6f32e4d953b*s-0x10c2b353bb1338e6e28dc67d39)*r**44/(0x267ee7f3548cf845e4ad<<43), (-0x20d69c9a8c49682f8fd*s-0x3ffa55780141a4bd35322e82af)*r**44/(0x267ee7f3548cf845e4ad<<45)), (-1050997*r**5/5316520, -868971*r**5/4253216), ((-0x1f23f1b553f57*s-0x3ce1590d611766506e2d)*r**5/0x267ee7f3548cf845e4ad0, (-0x816cd0ac0c66d*s-0xfbae52c8d1be77df2d7f)*r**5/0x99fb9fcd5233e11792b40), ((-1591853137-3*s)*r**24/(664565<<23), (-1591853137-3*s)*r**24/(132913<<25)), ((-0xacdf0540da6da1d*s-0x1511e97a7991d85ef9f410f)*r**24/(0x267ee7f3548cf845e4ad<<23), (-0x3a1f0a67147ac587*s-0x7138d3332148f783ee1953d)*r**24/(0x267ee7f3548cf845e4ad<<25)), ((-495066325607-933*s)*r**39/(664565<<38), (-587393807553-1107*s)*r**39/(132913<<40)), ((-0xdafa618bf0d6ce0dd*s-0x1aac48e90e2274c97e571f74f)*r**39/(0x267ee7f3548cf845e4ad<<38), (-0x52e13293f6f89a11c7*s-0xa17a119778a9bb482f7fe9ffd)*r**39/(0x267ee7f3548cf845e4ad<<40)), (-427484/664565, -1), ((-0x648ab8fd8f1a*s-0xc619a6951abd21297be)/0x267ee7f3548cf845e4ad, (-0x13bfebb9e0ad7*s-0x267ee7f3548cf845e4ad)/0x4cfdcfe6a919f08bc95a), ((-0x36a87a226949-113259*s)*r**52/(664565<<51), (-0x56dd8f90680f-179997*s)*r**52/(132913<<53)), ((-0x68c92e5c66e4e565ab3*s-0xcc30dfc3aff1e9b0f3aa3950e1)*r**52/(0x267ee7f3548cf845e4ad<<51), (-0x347c554bdf9453329fe9*s-0x66437f6cb23f008e62e21941d93)*r**52/(0x267ee7f3548cf845e4ad<<53)), (-12471097*r**13/1361029120, -106930971*r**13/5444116480), ((-0x170d24aa932f03*s-0x2d2673e0d3fb7ed27b551)*r**13/0x267ee7f3548cf845e4ad000, (-0xc6943eabc5f3d9*s-0x18321ae6b4db0f4569f7e3)*r**13/0x99fb9fcd5233e11792b4000), ((-4775559411-9*s)*r**28/(664565<<28), (-36612622151-69*s)*r**28/(664565<<29)), ((-0x1c50783958bc0b61*s-0x375678a0ab45cb73e18733b)*r**28/(0x267ee7f3548cf845e4ad<<28), (-0x104cca1d5aaa7217d*s-0x1fc39c56d3069a98399ec82f)*r**28/(0x267ee7f3548cf845e4ad<<29)), ((-0xee51060b73-1929*s)*r**43/(664565<<43), (-0xb9d95022a87-24069*s)*r**43/(664565<<44)), ((-0x1a9bfe320172ccf521*s-0x33e835b0f869eb03c33911a7b)*r**43/(0x267ee7f3548cf845e4ad<<43), (-0x16620c881dd55353c3d*s-0x2b9d07c0edb10d8248138b9a6f)*r**43/(0x267ee7f3548cf845e4ad<<44)), ((956703735337+1803*s)*r**41/(664565<<41), (-0x478e2019161-9267*s)*r**41/(664565<<42)), ((0x1c229a30fac2e68e53*s+0x36c8edf3401fe82236236c2c1)*r**41/(0x267ee7f3548cf845e4ad<<41), (-0x899fcaf6f32e4d953b*s-0x10c2b353bb1338e6e28dc67d39)*r**41/(0x267ee7f3548cf845e4ad<<42)), (148983*r**2/664565, -1050997*r**2/2658260), ((0x4801f718210d*s+0x8a148f415cf089dbc5f)*r**2/0x4cfdcfe6a919f08bc95a, (-0x1f23f1b553f57*s-0x3ce1590d611766506e2d)*r**2/0x133f73f9aa467c22f2568), ((1591853137+3*s)*r**21/(664565<<22), (-1591853137-3*s)*r**21/(664565<<22)), ((0x19b5396aeb86373*s+0x320316c3b4936e67003d21)*r**21/0x133f73f9aa467c22f25680000, (-0xacdf0540da6da1d*s-0x1511e97a7991d85ef9f410f)*r**21/(0x267ee7f3548cf845e4ad<<22)), ((90735628809+171*s)*r**36/(664565<<34), (-495066325607-933*s)*r**36/(664565<<37)), ((0x29d24049b9d0536f3*s+0x517536dc4e425cebb47a8ba1)*r**36/(0x267ee7f3548cf845e4ad<<34), (-0xdafa618bf0d6ce0dd*s-0x1aac48e90e2274c97e571f74f)*r**36/(0x267ee7f3548cf845e4ad<<37)), ((0x1f1f7aee51c9+64491*s)*r**51/(664565<<49), (-0x9ab9d53456a7-320613*s)*r**51/(664565<<52)), ((0x3c7f260bd92346be033*s+0x75dd09d68af8adc5e76c5e6561)*r**51/(0x267ee7f3548cf845e4ad<<49), (-0x129a1a2760431ee7e39d*s-0x243f3723850182a5e99cc5b418f)*r**51/(0x267ee7f3548cf845e4ad<<52)), ((0x1893da20fb5+3183*s)*r**49/(60415<<47), (-0x36a87a226949-113259*s)*r**49/(664565<<50)), ((0x20d69c9a8c49682f8fd*s+0x3ffa55780141a4bd35322e82af)*r**49/(0x267ee7f3548cf845e4ad<<47), (-0x68c92e5c66e4e565ab3*s-0xcc30dfc3aff1e9b0f3aa3950e1)*r**49/(0x267ee7f3548cf845e4ad<<50)), (868971*r**10/17012864, -12471097*r**10/680514560), ((0x816cd0ac0c66d*s+0xfbae52c8d1be77df2d7f)*r**10/0x267ee7f3548cf845e4ad00, (-0x170d24aa932f03*s-0x2d2673e0d3fb7ed27b551)*r**10/0x133f73f9aa467c22f256800), (868971*r**8/8506432, -4063121*r**8/170128640), ((0x816cd0ac0c66d*s+0xfbae52c8d1be77df2d7f)*r**8/0x133f73f9aa467c22f25680, (-0x77b2bcfe9344b*s-0xeb5c75a236fcbaa443e9)*r**8/0x4cfdcfe6a919f08bc95a00), ((1591853137+3*s)*r**27/(132913<<26), (-4775559411-9*s)*r**27/(664565<<28)), ((0x3a1f0a67147ac587*s+0x7138d3332148f783ee1953d)*r**27/(0x267ee7f3548cf845e4ad<<26), (-0x1c50783958bc0b61*s-0x375678a0ab45cb73e18733b)*r**27/(0x267ee7f3548cf845e4ad<<28)), ((587393807553+1107*s)*r**42/(132913<<41), (-0xee51060b73-1929*s)*r**42/(664565<<43)), ((0x52e13293f6f89a11c7*s+0xa17a119778a9bb482f7fe9ffd)*r**42/(0x267ee7f3548cf845e4ad<<41), (-0x1a9bfe320172ccf521*s-0x33e835b0f869eb03c33911a7b)*r**42/(0x267ee7f3548cf845e4ad<<43)), ((587393807553+1107*s)*r**40/(132913<<40), (956703735337+1803*s)*r**40/(664565<<41)), ((0x52e13293f6f89a11c7*s+0xa17a119778a9bb482f7fe9ffd)*r**40/(0x267ee7f3548cf845e4ad<<40), (0x1c229a30fac2e68e53*s+0x36c8edf3401fe82236236c2c1)*r**40/(0x267ee7f3548cf845e4ad<<41)), (r, 237081*r/1329130), ((0x13bfebb9e0ad7*s+0x267ee7f3548cf845e4ad)*r/0x4cfdcfe6a919f08bc95a, (0x72e949a2eca3*s+0xdbbb320b1355420b531)*r/0x99fb9fcd5233e11792b4), ((0x56dd8f90680f+179997*s)*r**53/(132913<<53), (0xd7b1e5486327+446949*s)*r**53/(664565<<54)), ((0x347c554bdf9453329fe9*s+0x66437f6cb23f008e62e21941d93)*r**53/(0x267ee7f3548cf845e4ad<<53), (0x1a4a09b4c5db19d9351d*s+0x3337477bc642862225f78aeda0f)*r**53/(0x267ee7f3548cf845e4ad<<54)), ((0x8e90449b5819*s+0x1160a8805db99bbb8aa3)*r/0x267ee7f3548cf845e4ad, (0x11e9432cb9a33*s+0x22a33a688957acf70361)*r/0x99fb9fcd5233e11792b4), (106930971*r**16/10888232960, 221024137*r**16/43552931840), ((0xc6943eabc5f3d9*s+0x18321ae6b4db0f4569f7e3)*r**16/0x133f73f9aa467c22f2568000, (0x19b5396aeb86373*s+0x320316c3b4936e67003d21)*r**16/0x4cfdcfe6a919f08bc95a0000), ((36612622151+69*s)*r**31/(664565<<30), (90735628809+171*s)*r**31/(664565<<32)), ((0x104cca1d5aaa7217d*s+0x1fc39c56d3069a98399ec82f)*r**31/(0x267ee7f3548cf845e4ad<<30), (0x29d24049b9d0536f3*s+0x517536dc4e425cebb47a8ba1)*r**31/(0x267ee7f3548cf845e4ad<<32)), ((0xb9d95022a87+24069*s)*r**46/(664565<<45), (0x1f1f7aee51c9+64491*s)*r**46/(664565<<47)), ((0x16620c881dd55353c3d*s+0x2b9d07c0edb10d8248138b9a6f)*r**46/(0x267ee7f3548cf845e4ad<<45), (0x3c7f260bd92346be033*s+0x75dd09d68af8adc5e76c5e6561)*r**46/(0x267ee7f3548cf845e4ad<<47)), ((0x478e2019161+9267*s)*r**44/(664565<<43), (0x1893da20fb5+3183*s)*r**44/(60415<<45)), ((0x899fcaf6f32e4d953b*s+0x10c2b353bb1338e6e28dc67d39)*r**44/(0x267ee7f3548cf845e4ad<<43), (0x20d69c9a8c49682f8fd*s+0x3ffa55780141a4bd35322e82af)*r**44/(0x267ee7f3548cf845e4ad<<45)), (1050997*r**5/5316520, 868971*r**5/4253216), ((0x1f23f1b553f57*s+0x3ce1590d611766506e2d)*r**5/0x267ee7f3548cf845e4ad0, (0x816cd0ac0c66d*s+0xfbae52c8d1be77df2d7f)*r**5/0x99fb9fcd5233e11792b40), ((1591853137+3*s)*r**24/(664565<<23), (1591853137+3*s)*r**24/(132913<<25)), ((0xacdf0540da6da1d*s+0x1511e97a7991d85ef9f410f)*r**24/(0x267ee7f3548cf845e4ad<<23), (0x3a1f0a67147ac587*s+0x7138d3332148f783ee1953d)*r**24/(0x267ee7f3548cf845e4ad<<25)), ((495066325607+933*s)*r**39/(664565<<38), (587393807553+1107*s)*r**39/(132913<<40)), ((0xdafa618bf0d6ce0dd*s+0x1aac48e90e2274c97e571f74f)*r**39/(0x267ee7f3548cf845e4ad<<38), (0x52e13293f6f89a11c7*s+0xa17a119778a9bb482f7fe9ffd)*r**39/(0x267ee7f3548cf845e4ad<<40)), (427484/664565, 1), ((0x648ab8fd8f1a*s+0xc619a6951abd21297be)/0x267ee7f3548cf845e4ad, (0x13bfebb9e0ad7*s+0x267ee7f3548cf845e4ad)/0x4cfdcfe6a919f08bc95a), ((0x36a87a226949+113259*s)*r**52/(664565<<51), (0x56dd8f90680f+179997*s)*r**52/(132913<<53)), ((0x68c92e5c66e4e565ab3*s+0xcc30dfc3aff1e9b0f3aa3950e1)*r**52/(0x267ee7f3548cf845e4ad<<51), (0x347c554bdf9453329fe9*s+0x66437f6cb23f008e62e21941d93)*r**52/(0x267ee7f3548cf845e4ad<<53)), (12471097*r**13/1361029120, 106930971*r**13/5444116480), ((0x170d24aa932f03*s+0x2d2673e0d3fb7ed27b551)*r**13/0x267ee7f3548cf845e4ad000, (0xc6943eabc5f3d9*s+0x18321ae6b4db0f4569f7e3)*r**13/0x99fb9fcd5233e11792b4000), ((4775559411+9*s)*r**28/(664565<<28), (36612622151+69*s)*r**28/(664565<<29)), ((0x1c50783958bc0b61*s+0x375678a0ab45cb73e18733b)*r**28/(0x267ee7f3548cf845e4ad<<28), (0x104cca1d5aaa7217d*s+0x1fc39c56d3069a98399ec82f)*r**28/(0x267ee7f3548cf845e4ad<<29)), ((0xee51060b73+1929*s)*r**43/(664565<<43), (0xb9d95022a87+24069*s)*r**43/(664565<<44)), ((0x1a9bfe320172ccf521*s+0x33e835b0f869eb03c33911a7b)*r**43/(0x267ee7f3548cf845e4ad<<43), (0x16620c881dd55353c3d*s+0x2b9d07c0edb10d8248138b9a6f)*r**43/(0x267ee7f3548cf845e4ad<<44)), ((-956703735337-1803*s)*r**41/(664565<<41), (0x478e2019161+9267*s)*r**41/(664565<<42)), ((-0x1c229a30fac2e68e53*s-0x36c8edf3401fe82236236c2c1)*r**41/(0x267ee7f3548cf845e4ad<<41), (0x899fcaf6f32e4d953b*s+0x10c2b353bb1338e6e28dc67d39)*r**41/(0x267ee7f3548cf845e4ad<<42)), (-148983*r**2/664565, 1050997*r**2/2658260), ((-0x4801f718210d*s-0x8a148f415cf089dbc5f)*r**2/0x4cfdcfe6a919f08bc95a, (0x1f23f1b553f57*s+0x3ce1590d611766506e2d)*r**2/0x133f73f9aa467c22f2568), ((-1591853137-3*s)*r**21/(664565<<22), (1591853137+3*s)*r**21/(664565<<22)), ((-0x19b5396aeb86373*s-0x320316c3b4936e67003d21)*r**21/0x133f73f9aa467c22f25680000, (0xacdf0540da6da1d*s+0x1511e97a7991d85ef9f410f)*r**21/(0x267ee7f3548cf845e4ad<<22)), ((-90735628809-171*s)*r**36/(664565<<34), (495066325607+933*s)*r**36/(664565<<37)), ((-0x29d24049b9d0536f3*s-0x517536dc4e425cebb47a8ba1)*r**36/(0x267ee7f3548cf845e4ad<<34), (0xdafa618bf0d6ce0dd*s+0x1aac48e90e2274c97e571f74f)*r**36/(0x267ee7f3548cf845e4ad<<37)), ((-0x1f1f7aee51c9-64491*s)*r**51/(664565<<49), (0x9ab9d53456a7+320613*s)*r**51/(664565<<52)), ((-0x3c7f260bd92346be033*s-0x75dd09d68af8adc5e76c5e6561)*r**51/(0x267ee7f3548cf845e4ad<<49), (0x129a1a2760431ee7e39d*s+0x243f3723850182a5e99cc5b418f)*r**51/(0x267ee7f3548cf845e4ad<<52)), ((-0x1893da20fb5-3183*s)*r**49/(60415<<47), (0x36a87a226949+113259*s)*r**49/(664565<<50)), ((-0x20d69c9a8c49682f8fd*s-0x3ffa55780141a4bd35322e82af)*r**49/(0x267ee7f3548cf845e4ad<<47), (0x68c92e5c66e4e565ab3*s+0xcc30dfc3aff1e9b0f3aa3950e1)*r**49/(0x267ee7f3548cf845e4ad<<50)), (-868971*r**10/17012864, 12471097*r**10/680514560), ((-0x816cd0ac0c66d*s-0xfbae52c8d1be77df2d7f)*r**10/0x267ee7f3548cf845e4ad00, (0x170d24aa932f03*s+0x2d2673e0d3fb7ed27b551)*r**10/0x133f73f9aa467c22f256800), (-868971*r**8/8506432, 4063121*r**8/170128640), ((-0x816cd0ac0c66d*s-0xfbae52c8d1be77df2d7f)*r**8/0x133f73f9aa467c22f25680, (0x77b2bcfe9344b*s+0xeb5c75a236fcbaa443e9)*r**8/0x4cfdcfe6a919f08bc95a00), ((-1591853137-3*s)*r**27/(132913<<26), (4775559411+9*s)*r**27/(664565<<28)), ((-0x3a1f0a67147ac587*s-0x7138d3332148f783ee1953d)*r**27/(0x267ee7f3548cf845e4ad<<26), (0x1c50783958bc0b61*s+0x375678a0ab45cb73e18733b)*r**27/(0x267ee7f3548cf845e4ad<<28)), ((-587393807553-1107*s)*r**42/(132913<<41), (0xee51060b73+1929*s)*r**42/(664565<<43)), ((-0x52e13293f6f89a11c7*s-0xa17a119778a9bb482f7fe9ffd)*r**42/(0x267ee7f3548cf845e4ad<<41), (0x1a9bfe320172ccf521*s+0x33e835b0f869eb03c33911a7b)*r**42/(0x267ee7f3548cf845e4ad<<43)), ((-587393807553-1107*s)*r**40/(132913<<40), (-956703735337-1803*s)*r**40/(664565<<41)), ((-0x52e13293f6f89a11c7*s-0xa17a119778a9bb482f7fe9ffd)*r**40/(0x267ee7f3548cf845e4ad<<40), (-0x1c229a30fac2e68e53*s-0x36c8edf3401fe82236236c2c1)*r**40/(0x267ee7f3548cf845e4ad<<41))]
HULL_NEG_HALF = [(-r**2/2, 190403*r**2/2658260), ((-0x13bfebb9e0ad7*s-0x267ee7f3548cf845e4ad)*r**2/0x99fb9fcd5233e11792b4, (0x562c28583191*s+0xb0781b1f22250047a4b)*r**2/0x133f73f9aa467c22f2568), (-119998/132913, 2029/664565), ((-0x8e90449b5819*s-0x1160a8805db99bbb8aa3)/0x267ee7f3548cf845e4ad, (-0x173a994ea01*s+0x1e1698321b8a8011e5)/0x4cfdcfe6a919f08bc95a), (-106930971*r**15/10888232960, -1432439*r**15/4355293184), ((-0xc6943eabc5f3d9*s-0x18321ae6b4db0f4569f7e3)*r**15/0x133f73f9aa467c22f2568000, (-0xe2b19572c7bc1*s-0x19ee0f64add4fdc2c4d5b)*r**15/0x267ee7f3548cf845e4ad0000), ((-36612622151-69*s)*r**30/(664565<<30), (-1591853137-3*s)*r**30/(60415<<31)), ((-0x104cca1d5aaa7217d*s-0x1fc39c56d3069a98399ec82f)*r**30/(0x267ee7f3548cf845e4ad<<30), (-0x938ac0f047b6f3f9*s-0x11edfe2ea83527bb413cfb43)*r**30/(0x267ee7f3548cf845e4ad<<31)), ((-0xb9d95022a87-24069*s)*r**45/(664565<<45), (-0x7e450e9fcbb-16353*s)*r**45/(664565<<46)), ((-0x16620c881dd55353c3d*s-0x2b9d07c0edb10d8248138b9a6f)*r**45/(0x267ee7f3548cf845e4ad<<45), (-0xfbb0cfb9d78a0167b9*s-0x1ea2fa54af9692c15745473083)*r**45/(0x267ee7f3548cf845e4ad<<46)), ((-0x478e2019161-9267*s)*r**43/(664565<<43), (-0x7f3e1f38a05-16479*s)*r**43/(664565<<44)), ((-0x899fcaf6f32e4d953b*s-0x10c2b353bb1338e6e28dc67d39)*r**43/(0x267ee7f3548cf845e4ad<<43), (-0xfa2a33bade39e7ce87*s-0x1e74eed08b1b32ef7016a1883d)*r**43/(0x267ee7f3548cf845e4ad<<44)), (-1050997*r**4/5316520, -2242861*r**4/10633040), ((-0x1f23f1b553f57*s-0x3ce1590d611766506e2d)*r**4/0x267ee7f3548cf845e4ad0, (-0x4324ed41647bf*s-0x81eba0ae0f8fab3e5125)*r**4/0x4cfdcfe6a919f08bc95a0), ((-1591853137-3*s)*r**23/(664565<<23), (-4775559411-9*s)*r**23/(664565<<24)), ((-0xacdf0540da6da1d*s-0x1511e97a7991d85ef9f410f)*r**23/(0x267ee7f3548cf845e4ad<<23), (-0x248329bef92d114d*s-0x4715003e2e2546c5fa3131f)*r**23/(0x267ee7f3548cf845e4ad<<24)), ((-495066325607-933*s)*r**38/(664565<<38), (-0x1c5487dc2f7-3669*s)*r**38/(664565<<39)), ((-0xdafa618bf0d6ce0dd*s-0x1aac48e90e2274c97e571f74f)*r**38/(0x267ee7f3548cf845e4ad<<38), (-0x3781e66278ddc0500d*s-0x6c217fc55c64d1b532d1ab15f)*r**38/(0x267ee7f3548cf845e4ad<<39)), ((-0x9ab9d53456a7-320613*s)*r**53/(664565<<53), (-0x28cb184197337-1352469*s)*r**53/(664565<<54)), ((-0x129a1a2760431ee7e39d*s-0x243f3723850182a5e99cc5b418f)*r**53/(0x267ee7f3548cf845e4ad<<53), (-0x4f194033396665a5e6cd*s-0x9a1c40fa0ffa306bd109241979f)*r**53/(0x267ee7f3548cf845e4ad<<54)), ((-0x36a87a226949-113259*s)*r**51/(664565<<51), (-0x14502d98d35b9-673467*s)*r**51/(664565<<52)), ((-0x68c92e5c66e4e565ab3*s-0xcc30dfc3aff1e9b0f3aa3950e1)*r**51/(0x267ee7f3548cf845e4ad<<51), (-0x27632f8052b7b685ea83*s-0x4cbd63743c40c358446cd217bd1)*r**51/(0x267ee7f3548cf845e4ad<<52)), (-12471097*r**12/1361029120, -81988777*r**12/2722058240), ((-0x170d24aa932f03*s-0x2d2673e0d3fb7ed27b551)*r**12/0x267ee7f3548cf845e4ad000, (-0x9879f5569f95d3*s-0x128d4c6a9a5b9f6b1a8d41)*r**12/0x4cfdcfe6a919f08bc95a000), (-4063121*r**10/340257280, -38821961*r**10/680514560), ((-0x77b2bcfe9344b*s-0xeb5c75a236fcbaa443e9)*r**10/0x99fb9fcd5233e11792b400, (-0x48319425ef67b3*s-0x8c8cf0be8c4f0799dafe1)*r**10/0x133f73f9aa467c22f256800), ((-4775559411-9*s)*r**29/(664565<<29), (-1591853137-3*s)*r**29/(15455<<30)), ((-0x1c50783958bc0b61*s-0x375678a0ab45cb73e18733b)*r**29/(0x267ee7f3548cf845e4ad<<29), (-0x1ed48cb71fc923799*s-0x3c11d1239b58d87935251d23)*r**29/(0x267ee7f3548cf845e4ad<<30)), ((-0xee51060b73-1929*s)*r**44/(664565<<44), (-0x164cd8fe499b-46209*s)*r**44/(664565<<45)), ((-0x1a9bfe320172ccf521*s-0x33e835b0f869eb03c33911a7b)*r**44/(0x267ee7f3548cf845e4ad<<44), (-0x2b1a592d1b9379d8359*s-0x53fb8c26cbdb7c5453f3861a63)*r**44/(0x267ee7f3548cf845e4ad<<45)), ((956703735337+1803*s)*r**42/(664565<<42), (-0x9d083ffa0eb-20337*s)*r**42/(664565<<43)), ((0x1c229a30fac2e68e53*s+0x36c8edf3401fe82236236c2c1)*r**42/(0x267ee7f3548cf845e4ad<<42), (-0x12f62301ee11f81b8c9*s-0x24f1f586aa28704fe87dc3bd33)*r**42/(0x267ee7f3548cf845e4ad<<43)), (237081*r**3/2658260, -2421179*r**3/5316520), ((0x72e949a2eca3*s+0xdbbb320b1355420b531)*r**3/0x133f73f9aa467c22f2568, (-0x47d11a4d53eb9*s-0x8c3fecaca0fe8cf6dd83)*r**3/0x267ee7f3548cf845e4ad0), (148983*r/664565, -1050997*r/1329130), ((0x4801f718210d*s+0x8a148f415cf089dbc5f)*r/0x4cfdcfe6a919f08bc95a, (-0x1f23f1b553f57*s-0x3ce1590d611766506e2d)*r/0x99fb9fcd5233e11792b4), (221024137*r**20/174211727360, -1489871399*r**20/(664565<<20)), ((0x19b5396aeb86373*s+0x320316c3b4936e67003d21)*r**20/0x133f73f9aa467c22f25680000, (-0xacdf0540da6da1d*s-0x1511e97a7991d85ef9f410f)*r**20/(0x267ee7f3548cf845e4ad<<21)), ((90735628809+171*s)*r**35/(664565<<34), (-495066325607-933*s)*r**35/(664565<<36)), ((0x29d24049b9d0536f3*s+0x517536dc4e425cebb47a8ba1)*r**35/(0x267ee7f3548cf845e4ad<<34), (-0xdafa618bf0d6ce0dd*s-0x1aac48e90e2274c97e571f74f)*r**35/(0x267ee7f3548cf845e4ad<<36)), ((0x1f1f7aee51c9+64491*s)*r**50/(664565<<49), (-0x9ab9d53456a7-320613*s)*r**50/(664565<<51)), ((0x3c7f260bd92346be033*s+0x75dd09d68af8adc5e76c5e6561)*r**50/(0x267ee7f3548cf845e4ad<<49), (-0x129a1a2760431ee7e39d*s-0x243f3723850182a5e99cc5b418f)*r**50/(0x267ee7f3548cf845e4ad<<51)), ((0x1893da20fb5+3183*s)*r**48/(60415<<47), (-0x36a87a226949-113259*s)*r**48/(664565<<49)), ((0x20d69c9a8c49682f8fd*s+0x3ffa55780141a4bd35322e82af)*r**48/(0x267ee7f3548cf845e4ad<<47), (-0x68c92e5c66e4e565ab3*s-0xcc30dfc3aff1e9b0f3aa3950e1)*r**48/(0x267ee7f3548cf845e4ad<<49)), (868971*r**9/17012864, -12471097*r**9/340257280), ((0x816cd0ac0c66d*s+0xfbae52c8d1be77df2d7f)*r**9/0x267ee7f3548cf845e4ad00, (-0x170d24aa932f03*s-0x2d2673e0d3fb7ed27b551)*r**9/0x99fb9fcd5233e11792b400), (868971*r**7/8506432, -4063121*r**7/85064320), ((0x816cd0ac0c66d*s+0xfbae52c8d1be77df2d7f)*r**7/0x133f73f9aa467c22f25680, (-0x77b2bcfe9344b*s-0xeb5c75a236fcbaa443e9)*r**7/0x267ee7f3548cf845e4ad00), ((1591853137+3*s)*r**26/(132913<<26), (-4775559411-9*s)*r**26/(664565<<27)), ((0x3a1f0a67147ac587*s+0x7138d3332148f783ee1953d)*r**26/(0x267ee7f3548cf845e4ad<<26), (-0x1c50783958bc0b61*s-0x375678a0ab45cb73e18733b)*r**26/(0x267ee7f3548cf845e4ad<<27)), ((587393807553+1107*s)*r**41/(132913<<41), (-0xee51060b73-1929*s)*r**41/(664565<<42)), ((0x52e13293f6f89a11c7*s+0xa17a119778a9bb482f7fe9ffd)*r**41/(0x267ee7f3548cf845e4ad<<41), (-0x1a9bfe320172ccf521*s-0x33e835b0f869eb03c33911a7b)*r**41/(0x267ee7f3548cf845e4ad<<42)), (r**2/2, -190403*r**2/2658260), ((0x13bfebb9e0ad7*s+0x267ee7f3548cf845e4ad)*r**2/0x99fb9fcd5233e11792b4, (-0x562c28583191*s-0xb0781b1f22250047a4b)*r**2/0x133f73f9aa467c22f2568), (119998/132913, -2029/664565), ((0x8e90449b5819*s+0x1160a8805db99bbb8aa3)/0x267ee7f3548cf845e4ad, (0x173a994ea01*s-0x1e1698321b8a8011e5)/0x4cfdcfe6a919f08bc95a), (106930971*r**15/10888232960, 1432439*r**15/4355293184), ((0xc6943eabc5f3d9*s+0x18321ae6b4db0f4569f7e3)*r**15/0x133f73f9aa467c22f2568000, (0xe2b19572c7bc1*s+0x19ee0f64add4fdc2c4d5b)*r**15/0x267ee7f3548cf845e4ad0000), ((36612622151+69*s)*r**30/(664565<<30), (1591853137+3*s)*r**30/(60415<<31)), ((0x104cca1d5aaa7217d*s+0x1fc39c56d3069a98399ec82f)*r**30/(0x267ee7f3548cf845e4ad<<30), (0x938ac0f047b6f3f9*s+0x11edfe2ea83527bb413cfb43)*r**30/(0x267ee7f3548cf845e4ad<<31)), ((0xb9d95022a87+24069*s)*r**45/(664565<<45), (0x7e450e9fcbb+16353*s)*r**45/(664565<<46)), ((0x16620c881dd55353c3d*s+0x2b9d07c0edb10d8248138b9a6f)*r**45/(0x267ee7f3548cf845e4ad<<45), (0xfbb0cfb9d78a0167b9*s+0x1ea2fa54af9692c15745473083)*r**45/(0x267ee7f3548cf845e4ad<<46)), ((0x478e2019161+9267*s)*r**43/(664565<<43), (0x7f3e1f38a05+16479*s)*r**43/(664565<<44)), ((0x899fcaf6f32e4d953b*s+0x10c2b353bb1338e6e28dc67d39)*r**43/(0x267ee7f3548cf845e4ad<<43), (0xfa2a33bade39e7ce87*s+0x1e74eed08b1b32ef7016a1883d)*r**43/(0x267ee7f3548cf845e4ad<<44)), (1050997*r**4/5316520, 2242861*r**4/10633040), ((0x1f23f1b553f57*s+0x3ce1590d611766506e2d)*r**4/0x267ee7f3548cf845e4ad0, (0x4324ed41647bf*s+0x81eba0ae0f8fab3e5125)*r**4/0x4cfdcfe6a919f08bc95a0), ((1591853137+3*s)*r**23/(664565<<23), (4775559411+9*s)*r**23/(664565<<24)), ((0xacdf0540da6da1d*s+0x1511e97a7991d85ef9f410f)*r**23/(0x267ee7f3548cf845e4ad<<23), (0x248329bef92d114d*s+0x4715003e2e2546c5fa3131f)*r**23/(0x267ee7f3548cf845e4ad<<24)), ((495066325607+933*s)*r**38/(664565<<38), (0x1c5487dc2f7+3669*s)*r**38/(664565<<39)), ((0xdafa618bf0d6ce0dd*s+0x1aac48e90e2274c97e571f74f)*r**38/(0x267ee7f3548cf845e4ad<<38), (0x3781e66278ddc0500d*s+0x6c217fc55c64d1b532d1ab15f)*r**38/(0x267ee7f3548cf845e4ad<<39)), ((0x9ab9d53456a7+320613*s)*r**53/(664565<<53), (0x28cb184197337+1352469*s)*r**53/(664565<<54)), ((0x129a1a2760431ee7e39d*s+0x243f3723850182a5e99cc5b418f)*r**53/(0x267ee7f3548cf845e4ad<<53), (0x4f194033396665a5e6cd*s+0x9a1c40fa0ffa306bd109241979f)*r**53/(0x267ee7f3548cf845e4ad<<54)), ((0x36a87a226949+113259*s)*r**51/(664565<<51), (0x14502d98d35b9+673467*s)*r**51/(664565<<52)), ((0x68c92e5c66e4e565ab3*s+0xcc30dfc3aff1e9b0f3aa3950e1)*r**51/(0x267ee7f3548cf845e4ad<<51), (0x27632f8052b7b685ea83*s+0x4cbd63743c40c358446cd217bd1)*r**51/(0x267ee7f3548cf845e4ad<<52)), (12471097*r**12/1361029120, 81988777*r**12/2722058240), ((0x170d24aa932f03*s+0x2d2673e0d3fb7ed27b551)*r**12/0x267ee7f3548cf845e4ad000, (0x9879f5569f95d3*s+0x128d4c6a9a5b9f6b1a8d41)*r**12/0x4cfdcfe6a919f08bc95a000), (4063121*r**10/340257280, 38821961*r**10/680514560), ((0x77b2bcfe9344b*s+0xeb5c75a236fcbaa443e9)*r**10/0x99fb9fcd5233e11792b400, (0x48319425ef67b3*s+0x8c8cf0be8c4f0799dafe1)*r**10/0x133f73f9aa467c22f256800), ((4775559411+9*s)*r**29/(664565<<29), (1591853137+3*s)*r**29/(15455<<30)), ((0x1c50783958bc0b61*s+0x375678a0ab45cb73e18733b)*r**29/(0x267ee7f3548cf845e4ad<<29), (0x1ed48cb71fc923799*s+0x3c11d1239b58d87935251d23)*r**29/(0x267ee7f3548cf845e4ad<<30)), ((0xee51060b73+1929*s)*r**44/(664565<<44), (0x164cd8fe499b+46209*s)*r**44/(664565<<45)), ((0x1a9bfe320172ccf521*s+0x33e835b0f869eb03c33911a7b)*r**44/(0x267ee7f3548cf845e4ad<<44), (0x2b1a592d1b9379d8359*s+0x53fb8c26cbdb7c5453f3861a63)*r**44/(0x267ee7f3548cf845e4ad<<45)), ((-956703735337-1803*s)*r**42/(664565<<42), (0x9d083ffa0eb+20337*s)*r**42/(664565<<43)), ((-0x1c229a30fac2e68e53*s-0x36c8edf3401fe82236236c2c1)*r**42/(0x267ee7f3548cf845e4ad<<42), (0x12f62301ee11f81b8c9*s+0x24f1f586aa28704fe87dc3bd33)*r**42/(0x267ee7f3548cf845e4ad<<43)), (-237081*r**3/2658260, 2421179*r**3/5316520), ((-0x72e949a2eca3*s-0xdbbb320b1355420b531)*r**3/0x133f73f9aa467c22f2568, (0x47d11a4d53eb9*s+0x8c3fecaca0fe8cf6dd83)*r**3/0x267ee7f3548cf845e4ad0), (-148983*r/664565, 1050997*r/1329130), ((-0x4801f718210d*s-0x8a148f415cf089dbc5f)*r/0x4cfdcfe6a919f08bc95a, (0x1f23f1b553f57*s+0x3ce1590d611766506e2d)*r/0x99fb9fcd5233e11792b4), (-221024137*r**20/174211727360, 1489871399*r**20/(664565<<20)), ((-0x19b5396aeb86373*s-0x320316c3b4936e67003d21)*r**20/0x133f73f9aa467c22f25680000, (0xacdf0540da6da1d*s+0x1511e97a7991d85ef9f410f)*r**20/(0x267ee7f3548cf845e4ad<<21)), ((-90735628809-171*s)*r**35/(664565<<34), (495066325607+933*s)*r**35/(664565<<36)), ((-0x29d24049b9d0536f3*s-0x517536dc4e425cebb47a8ba1)*r**35/(0x267ee7f3548cf845e4ad<<34), (0xdafa618bf0d6ce0dd*s+0x1aac48e90e2274c97e571f74f)*r**35/(0x267ee7f3548cf845e4ad<<36)), ((-0x1f1f7aee51c9-64491*s)*r**50/(664565<<49), (0x9ab9d53456a7+320613*s)*r**50/(664565<<51)), ((-0x3c7f260bd92346be033*s-0x75dd09d68af8adc5e76c5e6561)*r**50/(0x267ee7f3548cf845e4ad<<49), (0x129a1a2760431ee7e39d*s+0x243f3723850182a5e99cc5b418f)*r**50/(0x267ee7f3548cf845e4ad<<51)), ((-0x1893da20fb5-3183*s)*r**48/(60415<<47), (0x36a87a226949+113259*s)*r**48/(664565<<49)), ((-0x20d69c9a8c49682f8fd*s-0x3ffa55780141a4bd35322e82af)*r**48/(0x267ee7f3548cf845e4ad<<47), (0x68c92e5c66e4e565ab3*s+0xcc30dfc3aff1e9b0f3aa3950e1)*r**48/(0x267ee7f3548cf845e4ad<<49)), (-868971*r**9/17012864, 12471097*r**9/340257280), ((-0x816cd0ac0c66d*s-0xfbae52c8d1be77df2d7f)*r**9/0x267ee7f3548cf845e4ad00, (0x170d24aa932f03*s+0x2d2673e0d3fb7ed27b551)*r**9/0x99fb9fcd5233e11792b400), (-868971*r**7/8506432, 4063121*r**7/85064320), ((-0x816cd0ac0c66d*s-0xfbae52c8d1be77df2d7f)*r**7/0x133f73f9aa467c22f25680, (0x77b2bcfe9344b*s+0xeb5c75a236fcbaa443e9)*r**7/0x267ee7f3548cf845e4ad00), ((-1591853137-3*s)*r**26/(132913<<26), (4775559411+9*s)*r**26/(664565<<27)), ((-0x3a1f0a67147ac587*s-0x7138d3332148f783ee1953d)*r**26/(0x267ee7f3548cf845e4ad<<26), (0x1c50783958bc0b61*s+0x375678a0ab45cb73e18733b)*r**26/(0x267ee7f3548cf845e4ad<<27)), ((-587393807553-1107*s)*r**41/(132913<<41), (0xee51060b73+1929*s)*r**41/(664565<<42)), ((-0x52e13293f6f89a11c7*s-0xa17a119778a9bb482f7fe9ffd)*r**41/(0x267ee7f3548cf845e4ad<<41), (0x1a9bfe320172ccf521*s+0x33e835b0f869eb03c33911a7b)*r**41/(0x267ee7f3548cf845e4ad<<42))]

def mat_for_delta(d):
    """Compute the hull transformation from delta=1/2 to delta=d, d != -1/2."""
    assert d != -1/2
    if d >= 1/2:
        return Matrix([[1, 0], [0, 2**(1/2-d)]]) * shrinkage**(1/2-d)
    elif d <= -3/2:
        return Matrix([[0, 2**(d-1/2)], [-1/2, 2**(d-3/2)]]) * shrinkage**(d-3/2)
    else:
        # The delta=-1/2 hull cannot be written as a linear transformation of the 1/2 one.
        assert(False)

@functools.lru_cache(maxsize=None)
def hull_for_delta(d):
    if d == 1/2:
        return HULL_POS_HALF
    elif d == -1/2:
        return HULL_NEG_HALF
    else:
        mat = mat_for_delta(d)
        return [tuple(mat * vector(point)) for point in HULL_POS_HALF]

# (hd)divsteps transformation matrix for even g.
MAT_EVEN_G = Matrix([[1, 0], [0, 1/2]])
# (hd)divsteps transformation matrix for odd g, when delta <= 0.
MAT_ODD_G_LOW_DELTA = Matrix([[1, 0], [1/2, 1/2]])
# (hd)divsteps transformation matrix for odd g, when delta > 0.
MAT_ODD_G_HIGH_DELTA = Matrix([[0, 1], [-1/2, 1/2]])

def verify_hddivsteps_stable(d):
    """Verify that applying hddivsteps to hull_for_delta output gives a shrunken version of itself."""

    # First gather all the delta=d points that can result from applying hddivsteps
    # to the hulls generated by hull_for_delta (specifically, it uses input hulls for
    # delta=1-d and delta=d-1.
    points1 = []
    points1 += [tuple(MAT_EVEN_G * vector(p)) for p in hull_for_delta(d - 1)]
    if d - 1 <= 0:
        points1 += [tuple(MAT_ODD_G_LOW_DELTA * vector(p)) for p in hull_for_delta(d - 1)]
    if 1 - d > 0:
        points1 += [tuple(MAT_ODD_G_HIGH_DELTA * vector(p)) for p in hull_for_delta(1 - d)]

    # Then take the delta=d hull itself and shrink it by factor shrinkage.
    points2 = [tuple(shrinkage * vector(p)) for p in hull_for_delta(d)]

    # Verify that the application of hddivsteps gives a subset of the shrunking hull.
    assert(convex_hull(points1 + points2) == convex_hull(points2))

#for d in [1/2, -1/2, 3/2, -3/2, 5/2, -5/2, 7/2, -7/2, 9/2, -9/2, 11/2, -11/2, 13/2, -13/2, 15/2, -15/2, 17/2, -17/2]:
#    print("Verifying hull stability for delta=%s..." % d)
#    verify_hddivsteps_stable(d)

def find_condition(d):
    if d == -1/2 or (d - 1) == -1/2:
        print("Stability for delta=%s involves HULL_NEG_HALF.")
        return

    # Do the same as verify_hddivsteps_stable, but express it as a condition on HULL_POS_HALF.
    mats1 = []
    mats1 += [MAT_EVEN_G * mat_for_delta(d - 1)]
    if d - 1 <= 0:
        mats1 += [MAT_ODD_G_LOW_DELTA * mat_for_delta(d - 1)]
    if 1 - d > 0:
        mats1 += [MAT_ODD_G_HIGH_DELTA * mat_for_delta(1 - d)]

    mat2 = shrinkage * mat_for_delta(d)

    print("Conditions for stability at delta=%s (H = HULL_POS_HALF):" % d)
    for eq in [(1/mat2) * m for m in mats1]:
        sm = eq * shrinkage**2
        print("* For every p in H, [[%s,%s],[%s,%s]]/shrinkage**2 * p is also in H" % (sm[0][0], sm[0][1], sm[1][0], sm[1][1]))
        assert convex_hull(HULL_POS_HALF + [tuple(eq * vector(p)) for p in HULL_POS_HALF]) == convex_hull(HULL_POS_HALF)


#for d in [1/2, -1/2, 3/2, -3/2, 5/2, -5/2, 7/2, -7/2, 9/2, -9/2, 11/2, -11/2, 13/2, -13/2, 15/2, -15/2, 17/2, -17/2]:
for d in [1/2, -1/2, 3/2, -3/2, 5/2, -5/2]:
    find_condition(d)

def intersect_x0(p1, p2):
    ex1, ex2, ey1, ey2 = em(p1[0]), em(p2[0]), em(p1[1]), em(p2[1])
    if ex1 < 0 and ex2 < 0:
        return None
    if ex1 > 0 and ex2 > 0:
        return None
    if ex1 == 0 and ex2 == 0:
        return p1
    m = (-p1[0]) / (p2[0]-p1[0])
    return (0, m*(p2[1] - p1[1]) + p1[1])

def intersect_y0(p1, p2):
    tp1 = (p1[1], p1[0])
    tp2 = (p2[1], p2[0])
    i = intersect_x0(tp1, tp2)
    if i is None:
        return None
    return (i[1], i[0])

def intersect_xy(p1, p2):
    tp1 = (p1[0] - p1[1], p1[1])
    tp2 = (p2[0] - p2[1], p2[1])
    i = intersect_x0(tp1, tp2)
    if i is None:
        return None
    return (i[0] + i[1], i[1])


IX0 = [p for p in [intersect_x0(HULL_POS_HALF[i], HULL_POS_HALF[i-1]) for i in range(len(HULL_POS_HALF))] if p is not None]
IY0 = [p for p in [intersect_y0(HULL_POS_HALF[i], HULL_POS_HALF[i-1]) for i in range(len(HULL_POS_HALF))] if p is not None]
IXY = [p for p in [intersect_xy(HULL_POS_HALF[i], HULL_POS_HALF[i-1]) for i in range(len(HULL_POS_HALF))] if p is not None]

print("Intersections f=0: (%s)/(2^31*32577732460384302800781)" % [(2**31*32577732460384302800781)/p[1] for p in IX0])
print("Intersections f=g: (%s)/(2^34*4437361351842943627264534281)" % [(2**34*4437361351842943627264534281)/p[0] for p in IXY])

print("Approx 0 <= g <= f <= M: n >= ceil(%s + %s*log2(M))" % (log(abs(em(1/IXY[0][0])))/log(em(1/shrinkage)), 1/log(em(1/shrinkage),2)))
print("Approx 0 <= f <= M, 0 <= g <= M: n >= ceil(%s + %s*log2(M))" % (log(abs(em(1/IX0[0][1])))/log(em(1/shrinkage)), 1/log(em(1/shrinkage),2)))

pworst=None
worst=None
for i in range(len(HULL_POS_HALF)):
    p1 = HULL_POS_HALF[i - 1]
    p2 = HULL_POS_HALF[i]
    scale = (p1[0]*p2[1] - p2[0]*p1[1]) / (p1[0] - p2[0] - p1[1] + p2[1])
    pscale = phi(scale)
    xcoef = (scale - p1[0]) / (p2[0] - p1[0])
    ycoef = (scale - p1[1]) / (p2[1] - p1[1])
    linetest = xcoef - ycoef
    assert(linetest == 0)
    if pscale > 0 and (worst is None or pscale < pworst) and (0 <= phi(xcoef) <= 1):
        pworst = pscale
        worst = scale

gs = [g for _, g in HULL_POS_HALF] + [-g for _, g in HULL_POS_HALF]
gs.sort(key = phi)
factor = gs[-1] / worst

print(gs[-1])
print(1/worst)


exit()

# formula: factor*modulus*shrinkage**steps < 1
# modulus < shrinkage**(-steps)/factor
invshrinkage = 1/shrinkage
invfactor = 1/factor
for steps in range(600):
    m = int(phi(invshrinkage**steps * invfactor))
    print("%i: 0x%x (%.15f)" % (steps, m, log(m,2)))
