#!/bin/env python

"""Computes how many divsteps iterations are needed for inputs in a given range.

Invoke as:
  python3 divsteps_iters.py [--half-delta] <M>

(or using pypy3, which is significantly faster)

for some integer M > 0. The program will then report the number of iterations
needed for any f and g for which 0 <= g <= f <= M.

When running with --half-delta analysis will be performed for a variant of divsteps
that is equivalent to the original one but with starting value delta=1/2 instead of
delta=1.
"""

import argparse

# When running with --half-delta, we scale delta by a factor 2, and thus always increment
# by 2 instead of 1.
INC = 1

def convex_hull(points):
    """Computes the convex hull of a set of 2D points.

    Input: a list of (x, y) pairs representing the points.
    Output: a list of vertices of the convex hull in counter-clockwise order.

    This implements Andrew's monotone chain algorithm, based on
    https://en.wikibooks.org/wiki/Algorithm_Implementation/Geometry/Convex_hull/Monotone_chain
    """
    # Boring case: 0 or 1 points.
    if len(points) <= 1:
        return points
    # Sort the points lexicographically (tuples are compared lexicographically).
    points.sort()
    # Build lower hull.
    lower = [points[0]]
    for point in points[1:]:
        while len(lower) >= 2 and ((lower[-1][0] - lower[-2][0]) * (point[1] - lower[-2][1]) <=
                                   (lower[-1][1] - lower[-2][1]) * (point[0] - lower[-2][0])):
            lower.pop()
        if lower[-1] != point:
            lower.append(point)
    if len(lower) == 1:
        return lower
    # Build upper hull.
    upper = [points[-1]]
    for point in reversed(points[:-1]):
        while len(upper) >= 2 and ((upper[-1][0] - upper[-2][0]) * (point[1] - upper[-2][1]) <=
                                   (upper[-1][1] - upper[-2][1]) * (point[0] - upper[-2][0])):
            upper.pop()
        if upper[-1] != point:
            upper.append(point)
    # Concatenation of the lower and upper hulls gives the convex hull.
    # The last point of each list is omitted because it is repeated at the beginning
    # of the other list.
    return lower[:-1] + upper[:-1]

def process_divstep(state):
    """Apply one divstep to state.

    state is a dict of the form delta -> points, where points is a set of (f, g)
    coordinates (multiplied by 2**step so that they remain integral) that defines a convex
    hull of possible combinations of f and g.

    Every invocation of this function will compute the new state based on the previous state,
    taking into account that not every transaction is possible for every delta, but always
    exploring both the "odd g" and "even g" variants.
    """

    new_state = dict()
    for delta, points in state.items():
        # Odd g:
        if delta > 0:
            # divsteps^n(delta,f,g) = divsteps^{n-1}(1-delta,g,(g-f)/2)
            n = new_state.setdefault(INC - delta, [])
            for f, g in points:
                n.append((g << 1, g - f))
        else:
            # divsteps^n(delta,f,g) = divsteps^{n-1}(1+delta,f,(f+g)/2)
            n = new_state.setdefault(INC + delta, [])
            for f, g in points:
                n.append((f << 1, g + f))

        # Even g:
        # divsteps^n(delta,f,g) = divsteps^{n-1}(1+delta,f,g/2)
        n = new_state.setdefault(INC + delta, [])
        for f, g in points:
            n.append((f << 1, g))

    for delta in new_state:
        # Minimize the set of points by computing a new convex hull over them.
        new_state[delta] = convex_hull(new_state[delta])

    return new_state


parser = argparse.ArgumentParser(description="Compute the number if divsteps iterations needed for inputs in a specified range.")
parser.add_argument('--half-delta', '-d', action='store_true', default=False, help="Use half-delta divsteps rule")
parser.add_argument('range', type=lambda x: int(x, 0), nargs=1, help="The range M (maximum value for f) to consider")
args = parser.parse_args()
if args.half_delta:
    INC=2
M = args.range[0]
assert(M > 0)

# Define the initial state: a single hull for delta=1, defining the triangle f=0..M g=0..f.
STEP = 0
STATE = {1: [(0, 0), (M, 0), (M, M)]}
while True:
    # Compute next state.
    STATE = process_divstep(STATE)
    STEP += 1
    # Remove all hulls for which all points satisfy |g|<1. In the real algorithm, g is integral
    # and thus |g|<1 implies g==0. Thus, if this is true for all points in a hull, that hull
    # only corresponds to real program states for which g=0, and thus for which the computation
    # would be complete. Such hulls can be removed.
    for delta in list(STATE.keys()):
        if all((abs(g) >> STEP) == 0 for _, g in STATE[delta]):
            del STATE[delta]
    # If no hulls representing unfinished program states are left, we are done.
    if len(STATE) == 0:
        break
# Report how many steps it took.
print(STEP)
