#!/bin/env python

"""Compute ranges of moduli that can be handled with given numbers of divsteps.

Output will include lines like these:

  ...
  721 0x68c99daf6eb26776b8a7a2ace253df30d84c7c4328ac408aa128dc8ca448a777 (2**254.711324)
  722 0x9e4ccd3a0a07119e8a58e4ff434f504ad45434b4af37b913db51296f40fa5a5b (2**255.306518)
  723 0xaa040650e6d9c377b515b9e3d71fbfacc6c7f06f115dd0693166a8a64511ef26 (2**255.409524)
  724 0x1030596cf6d817d1357f908ef70cdb00b38d047fbba852139babb6c8646fb15b2 (2**256.016930)
  ...

indicating that e.g. for any input 1 <= f <= 0x9e4c..5a5b and 0 <= g <= f, 722 divstep
iterations is sufficient to reach g=0. That means 722 divsteps is sufficient for computing
modular inverses for any 255-bit modulus, and 724 is sufficient for any 256-bit modulus.

This code runs significantly faster in Pypy.
"""

import math


def convex_hull(points):
    """Computes the convex hull of a set of 2D points.

    Input: a list of (x, y) pairs representing the points.
    Output: a list of vertices of the convex hull in counter-clockwise order.

    This implements Andrew's monotone chain algorithm, based on
    https://en.wikibooks.org/wiki/Algorithm_Implementation/Geometry/Convex_hull/Monotone_chain
    """
    # Boring case: no points.
    if len(points) <= 1:
        return points
    # Sort the points lexicographically (tuples are compared lexicographically).
    points = sorted(points)
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

    state is a dict of the form delta -> [points, abs_g], where points is a set of (f, g)
    coordinates (multiplied by 2**step so that they remain integral) that defines a convex
    hull of possible combinations of f and g. abs_g is the largest abs(g) in points, or
    the largest such value in any of the contributing hulls if that is smaller.

    Every invocation of this function will compute the new state based on the previous state,
    taking into account that not every transaction is possible for every delta, but always
    exploring both the "odd g" and "even g" variants.
    """

    new_state = dict()
    for delta, (points, abs_g) in state.items():
        # Odd g:
        if delta > 0:
            # divsteps^n(delta,f,g) = divsteps^{n-1}(1-delta,g,(g-f)/2)
            new_state.setdefault(1 - delta, [[], 0])
            new_state[1 - delta][0].extend((g << 1, g - f) for f, g in points)
            new_state[1 - delta][1] = max(new_state[1 - delta][1], abs_g << 1)
        else:
            # divsteps^n(delta,f,g) = divsteps^{n-1}(1+delta,f,(f+g)/2)
            new_state.setdefault(1 + delta, [[], 0])
            new_state[1 + delta][0].extend((f << 1, g + f) for f, g in points)
            new_state[1 + delta][1] = max(new_state[1 + delta][1], abs_g << 1)

        # Even g:
        # divsteps^n(delta,f,g) = divsteps^{n-1}(1+delta,f,g/2)
        new_state.setdefault(1 + delta, [[], 0])
        new_state[1 + delta][0].extend((f << 1, g) for f, g in points)
        new_state[1 + delta][1] = max(new_state[1 + delta][1], abs_g << 1)

    for delta in new_state:
        # Minimize the set of points by computing a new convex hull over them.
        new_state[delta][0] = convex_hull(new_state[delta][0])
        # Update abs_g values for every hull.
        new_state[delta][1] = min(new_state[delta][1], max(abs(g) for _, g in new_state[delta][0]))

    return new_state



# Define the initial state: a single hull for delta=1, defining the triangle f=0..1 g=0..f.
STEP = 0
STATE = {1: [[(0, 0), (1, 0), (1, 1)], 1]}
while True:
    # Compute next state.
    STATE = process_divstep(STATE)
    STEP += 1
    # Compute the maximum of all abs_g values over all hulls at the current state.
    # For any input f,g, and any valid sequence of divsteps applied to it, abs(g)
    # must at some point have been less than or equal to that value (divided by 2**STEP).
    max_abs_g = max(abs_g for _, abs_g in STATE.values())
    # Thus, if the input triangle would have been alpha=(2**STEP / abs_g)-epsilon times
    # larger, abs(g) would at some point have been < 1. In the actual algorithm, g is an
    # integer, and thus abs(g)<1 implies g=0, which means the computation would have
    # been complete for any input.
    alpha = ((1 << STEP) - 1) // max_abs_g
    # That scaled triangle is f=0..alpha g=0..f, covering all moduli up alpha, and all
    # inputs up to the modulus.
    print("%i 0x%x (2**%f)" % (STEP, alpha, math.log(alpha, 2)))
