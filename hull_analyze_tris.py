import argparse, sys, random, math
from fractions import Fraction

EXPLICIT_LIMIT = 1000

def line_eq(p1, p2):
    xd = p2[0] - p1[0]
    yd = p2[1] - p1[1]
    return (-yd, xd, yd * p1[0] - xd * p1[1])

def cross(o, a, b):
    """2D cross product of the OA and OB vectors, i.e. the z-component of
    their 3D cross product.

    Returns a positive value if OAB makes a counter-clockwise turn,
    negative for clockwise turn, and zero if the points are collinear.
    """
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

def gmin(a, b):
    if a is None:
        return b
    return min(a, b)

def gmax(a, b):
    if a is None:
        return b
    return max(a, b)

def convex_hull(points):
    """Computes the convex hull of a set of 2D points.

    Input: an iterable sequence of (x, y) pairs representing the points.
    Output: a list of vertices of the convex hull in counter-clockwise order,
      starting from the vertex with the lexicographically smallest coordinates.
    Implements Andrew's monotone chain algorithm. O(n log n) complexity.
    """
    # Boring case: no points.
    if len(points) <= 1:
        return points
    # Sort the points lexicographically (tuples are compared lexicographically).
    points = sorted(points)
    # Build lower hull.
    lower = [points[0]]
    for p in points[1:]:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        if lower[-1] != p:
            lower.append(p)
    if (len(lower) == 1):
        return lower
    # Build upper hull.
    upper = [points[-1]]
    for p in reversed(points[:-1]):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        if upper[-1] != p:
            upper.append(p)
    # Concatenation of the lower and upper hulls gives the convex hull.
    # The Last point of each list is omitted because it is repeated at the beginning
    # of the other list. 
    return lower[:-1] + upper[:-1]

def in_convex_hull(hull, point):
    """Determine if a point is in a convex hull (returned by convex_hull)."""
    if len(hull) == 0:
        # Empty set.
        return False
    elif len(hull) == 1:
        # Single point.
        return hull[0] == point
    elif len(hull) == 2:
        # Two points: test for colinearity, plus whether the point is between the vertices.
        return cross(hull[0], hull[1], point) == 0 and hull[0][0] <= point[0] <= hull[1][0] and (hull[0][0] != hull[1][0] or hull[0][1] <= point[1] <= hull[1][1])
    else:
        # Three or more points: point needs to be left of every edge, when traversing in 
        # counter-clockwise order.
        if cross(hull[-1], hull[0], point) < 0:
            return False
        for n in range(1, len(hull)):
            if cross(hull[n-1], hull[n], point) < 0:
                return False
        return True

def convex_hull_intersect_y_line(hull, y):
    if len(hull) == 0:
        return []
    elif len(hull) == 1:
        if hull[0][1] == y:
            return hull
        else:
            return []
    else:
        min_x = None
        max_x = None
        for i in range(len(hull)):
            i2 = 0 if i + 1 == len(hull) else i + 1
            p1 = hull[i]
            p2 = hull[i2]
            if (y < p1[1] and y < p2[1]) or (y > p1[1] and y > p2[1]):
                continue
            elif p1[1] == p2[1]:
                return [p1, p2]
            else:
                a, b, c = line_eq(p1, p2)
                n = -c - b*y
                r = n / a
                max_x = gmax(max_x, r)
                min_x = gmin(min_x, r)
        if min_x is None:
            return []
        elif min_x == max_x:
            return [(min_x, y)]
        else:
            return [(min_x, y), (max_x, y)]

def convex_hull_intersect_x_line(hull, x):
    if len(hull) == 0:
        return []
    elif len(hull) == 1:
        if hull[0][0] == x:
            return hull
        else:
            return []
    else:
        min_y = None
        max_y = None
        for i in range(len(hull)):
            i2 = 0 if i + 1 == len(hull) else i + 1
            p1 = hull[i]
            p2 = hull[i2]
            if (x < p1[0] and x < p2[0]) or (x > p1[0] and x > p2[0]):
                continue
            elif p1[0] == p2[0]:
                return [p1, p2]
            else:
                a, b, c = line_eq(p1, p2)
                n = -c - a*x
                r = n / b
                max_y = gmax(max_y, r)
                min_y = gmin(min_y, r)
        if min_y is None:
            return []
        elif min_y == max_y:
            return [(x, min_y)]
        else:
            return [(x, min_y), (x, max_y)]

#for N in range(10000):
#    lst = []
#    for _ in range(random.randrange(0, 17)):
#        lst.append((2*random.randrange(-4, 4) + 1, random.randrange(-8, 8)))
#    hull = convex_hull(lst)
#    for p in lst:
#        i = in_convex_hull(hull, p)
#        if not i:
#            print(lst, hull, p)
#        assert in_convex_hull(hull, p)
#    for g in range(-9, 9):
#        intersection = convex_hull_intersect_y_line(hull, g)
#        assert all(f & 1 for f, _ in intersection)
#        assert all(gg == g for _, gg in intersection)
#        assert len(intersection) <= 2
#        for f in range(-11, 12, 2):
#             expect = len(intersection) and f >= intersection[0][0] and f <= intersection[-1][0]
#             real = in_convex_hull(hull, (f, g))
#             assert expect == in_convex_hull(hull, (f, g))
#
#h1 = convex_hull([(0,0),(3,0),(0,3),(3,3)])
#assert convex_hull_intersect_y_line(h1, -1) == []
#assert convex_hull_intersect_y_line(h1, 0) == [(0,0), (3,0)]
#assert convex_hull_intersect_y_line(h1, 1) == [(0,1), (3,1)]
#assert convex_hull_intersect_y_line(h1, 3) == [(0,3), (3,3)]
#assert convex_hull_intersect_y_line(h1, 4) == []
#h2 = convex_hull([(1,0), (0,1), (1,2), (2,1)])
#assert convex_hull_intersect_y_line(h2, -1) == []
#assert convex_hull_intersect_y_line(h2, 0) == [(1,0)]
#assert convex_hull_intersect_y_line(h2, 1) == [(0,1), (2,1)]
#assert convex_hull_intersect_y_line(h2, 2) == [(1,2)]
#assert convex_hull_intersect_y_line(h2, 3) == []
#h3 = convex_hull([(0,2), (1,0), (2,1), (3,3)])
#assert convex_hull_intersect_y_line(h3, -1) == []
#assert convex_hull_intersect_y_line(h3, 0) == [(1,0)]
#assert convex_hull_intersect_y_line(h3, 1) == [(1,1), (2,1)]
#assert convex_hull_intersect_y_line(h3, 2) == [(0,2), (2,2)]
#assert convex_hull_intersect_y_line(h3, 3) == [(3,3)]
#assert convex_hull_intersect_y_line(h3, 4) == []
#h4 = convex_hull([(0,2), (1,0), (3,3)])
#assert convex_hull_intersect_y_line(h4, -1) == []
#assert convex_hull_intersect_y_line(h4, 0) == [(1,0)]
#assert convex_hull_intersect_y_line(h4, 1) == [(1,1)]
#assert convex_hull_intersect_y_line(h4, 2) == [(0,2), (2,2)]
#assert convex_hull_intersect_y_line(h4, 3) == [(3,3)]
#assert convex_hull_intersect_y_line(h4, 4) == []

def floor_frac(frac):
    i = int(frac)
    if i > frac:
        i -= 1
    assert i == frac or (i < frac and (i + 1 > frac))
    return i

def ceil_frac(frac):
    i = int(frac)
    if i < frac:
        i += 1
    assert i == frac or (i > frac and (i - 1 < frac))
    return i

def count_divsteps(f, g, delta=1):
    """Compute the number of divsteps safegcd needs with a given input."""
    assert f & 1
    it = 0
    while g != 0:
        it += 1
        if g & 1:
            if delta > 0:
                delta, f, g = 2-delta, g, (g-f)>>1
            else:
                delta, g = 2+delta, (g+f)>>1
        else:
            delta, g = 2+delta, g>>1
    return it

def polygon_area(hull, scale):
    i2 = len(hull) - 1
    ret = Fraction(1)
    iscale = 1/Fraction(scale)
    iscale2 = iscale**2
    for i in range(len(hull)):
        p1 = hull[i]
        p2 = hull[i2]
        ret += iscale2*(p1[1]*p2[0] - p1[0]*p2[1]) * Fraction(1,2)
        ret += max(abs(p1[0]-p2[0]) * Fraction(1,2),abs(p1[1]-p2[1])) * Fraction(1,2) * iscale
        i2 = i
    return ret

MAXFAC = 0.0

def step(state, scale):
    global MAXFAC
    new_state = dict()
    its = 0
    for delta, points in state.items():
        # even step
        n = new_state.setdefault(2+delta, [])
        for f, g in points:
            n.append((f+f,g))
        # odd step
        if delta > 0:
            n = new_state.setdefault(2-delta, [])
            for f, g in points:
                n.append((g+g,g-f))
        else:
            for f, g in points:
                n.append((f+f,g+f))
    pos_scale = Fraction(scale)
    neg_scale = Fraction(-scale)
    for delta in new_state:
        h = convex_hull(new_state[delta])
        rh = [p for p in h if p[1] <= neg_scale or p[1] >= pos_scale]
        rh += convex_hull_intersect_y_line(h, neg_scale)
        rh += convex_hull_intersect_y_line(h, pos_scale)
        h = convex_hull(rh)
#        if len(h) > 0:
#            max_g = floor_frac(max(g for _, g in h) / pos_scale)
#            min_g = ceil_frac(min(g for _, g in h) / pos_scale)
#            max_f = floor_frac(max(f for f, _ in h) / pos_scale)
#            min_f = ceil_frac(min(f for f, _ in h) / pos_scale)
#            max_f -= 1 - (max_f & 1)
#            min_f += 1 - (min_f & 1)
#            size = (max_g - min_g + 1) * (1 + ((max_f - min_f) >> 1))
#            if size < EXPLICIT_LIMIT:
#                for f in range(min_f, max_f + 2, 2):
#                    for g in range(min_g, max_g + 1, 1):
#                        if (in_convex_hull(h, (f * pos_scale, g * pos_scale))):
#                            its = max(its, count_divsteps(f, g, delta))
#                h = []
        if len(h) > 0:
            min_f = ceil_frac(min(f for f, _ in h) / pos_scale)
            max_f = floor_frac(max(f for f, _ in h) / pos_scale)
            min_f += 1 - (min_f & 1)
            max_f -= 1 - (max_f & 1)
            min_g = ceil_frac(min(g for _, g in h) / pos_scale)
            max_g = floor_frac(max(g for _, g in h) / pos_scale)
            area = (((max_f - min_f) >> 1) + 1) * (max_g - min_g + 1)
            if area < 16 * EXPLICIT_LIMIT and area > EXPLICIT_LIMIT:
                area = min(area, floor_frac(polygon_area(h, scale)))
            if area < 16 * EXPLICIT_LIMIT:
                intersect_g = False
                n_points = 0
                intersections = []
                if (max_g - min_g < (max_f - min_f) >> 1):
                    intersect_g = True
                    for g in range(min_g, max_g + 1):
                        ps = convex_hull_intersect_y_line(h, g * pos_scale)
                        if len(ps) == 1:
                            f = int(ps[0][0] / pos_scale)
                            if f * pos_scale == ps[0][0] and f & 1:
                                intersections.append((g, f, f))
                                n_points += 1
                        elif len(ps) == 2:
                            fs = [ps[0][0] / pos_scale, ps[1][0] / pos_scale]
                            fs.sort()
                            fl = ceil_frac(fs[0])
                            fh = floor_frac(fs[1])
                            fl += 1 - (fl & 1)
                            fh -= 1 - (fh & 1)
                            intersections.append((g, fl, fh))
                            n_points += ((fh - fl) >> 1) + 1
                        else:
                            assert False
                else:
                    for f in range(min_f, max_f + 2, 2):
                        ps = convex_hull_intersect_x_line(h, f * pos_scale)
                        if len(ps) == 1:
                            g = int(ps[0][1] / pos_scale)
                            if g * pos_scale == ps[0][1]:
                                intersections.append((f, g, g))
                                n_points += 1
                        elif len(ps) == 2:
                            gs = [ps[0][1] / pos_scale, ps[1][1] / pos_scale]
                            gs.sort()
                            gl = ceil_frac(gs[0])
                            gh = floor_frac(gs[1])
                            intersections.append((f, gl, gh))
                            n_points += (gh - gl) + 1
                        else:
                            assert False
                if n_points < EXPLICIT_LIMIT:
                    print("  * Explicit evaluation for delta=%i hull: points=%i/%i f=%i..%i g=%i..%i g_dir=%s" % (delta, n_points, area, min_f, max_f, min_g, max_g, intersect_g))
                    if intersect_g:
                        for g, fl, fh in intersections:
                            for f in range(fl, fh + 2, 2):
                                its = max(its, count_divsteps(f, g, delta))
                    else:
                        for f, gl, gh in intersections:
                            for g in range(gl, gh + 1):
                                its = max(its, count_divsteps(f, g, delta))
                    h = []
        new_state[delta] = h
    return {k: v for k, v in new_state.items() if len(v) > 0}, its

def analyze(m):
    state = {1: convex_hull([(Fraction(2),Fraction(1)),(Fraction(m),Fraction(1)),(Fraction(m),Fraction(m-1))])}
    it = 0
    its = 0
    while len(state):
        it += 1
        state, nits = step(state, 1 << it)
        its = max(its, it + nits)
        print("- %i: %i deltas, %i points, max %i point/delta" % (it, len(state), sum(len(p) for p in state.values()), max((len(p) for p in state.values()), default=0)))
    return its

LOW = 0xd1289e3d605e833e9622000b11bb29163016743df24f35f9d91d9ba2b7fd1570
HIG = 0xeec9f80577a885d22f8d37c1946187e26805ea27b26c5ae10aa38a02e2ea3157
AIM = 589

#LOW = 0xb0000000
#HIG = 0xe0000000
#AIM = 73

IT = 51
HLOW=False
HHIG=False
while LOW + (1 << IT) < HIG:
    MID = LOW + (1 << IT)
    IT += 8
    print("* LOW = 0x%x" % LOW)
    print("* HIG = 0x%x" % HIG)
    print("* MID = 0x%x" % MID)
    v = analyze(MID)
    print("-> 0x%x: %i" % (MID, v))
    if v == AIM + 1:
        HIG = MID
        HHIG = True
        break
    elif v == AIM:
        LOW = MID
        HLOW = True
    else:
        assert(False)

while HIG > LOW + 1:
    RAN = (HIG - LOW).bit_length()
    print("* LOW = 0x%x" % LOW)
    print("* HIG = 0x%x" % HIG)
    print("* RAN=%i,HLOW=%i,HHIG=%i" % (RAN,HLOW,HHIG))
    MID = (LOW + HIG) // 2
    print("* MID = 0x%x" % MID)
    v = analyze(MID)
    print("-> 0x%x: %i" % (MID, v))
    if v == AIM + 1:
        HIG = MID
        HHIG = True
    elif v == AIM:
        LOW = MID
        HLOW = True
    else:
        assert(False)

print("1 <= g < f <= 0x%x: iterations <= %i" % (LOW, AIM))
