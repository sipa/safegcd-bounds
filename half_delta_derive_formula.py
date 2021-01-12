import re
import math

# Maximum denominator to consider.
MAX_DENOM = 2000

# Only derive a formula for at least this many steps.
MIN_STEPS = 51

# Direction coefficient to use.
COEF = 2.30352752220748858833059897712765371918755

RE = re.compile("^(\d+) 0x([0-9a-f]+) ")

# Minimal observed offset log(threshold)-steps/COEF.
MIN = (1000, None)
# Compute MINODD and MINEVEN from the data.
with open("half_delta_output.txt") as f:
    for line in f:
        match = RE.match(line)
        if match:
            steps = int(match[1]) + 1
            thresh = int(match[2], 16) + 1
            lthresh = math.log2(thresh)
            offset = lthresh - steps / COEF
            if steps >= MIN_STEPS:
                MIN = min(MIN, (offset, steps))

# Find numerator/denominator approximation for COEF.
NUMER = 0
DENOM = 1
DENOMCOEF = 10
for denom in range(1, MAX_DENOM):
    numer = int(math.ceil(COEF * denom))
    coef = numer / denom
    assert coef >= COEF
    if coef < DENOMCOEF:
        NUMER = numer
        DENOM = denom
        DENOMCOEF = coef

# Find the actual formula, combining the fractional approximation with offsets.
TERM = int(math.ceil(-NUMER*(MIN[0])))
print("steps <= floor((%i * lthresh + %i) / %i)" % (NUMER, TERM, DENOM))

# Find as of where the formula holds.
LASTBAD = None
FIRSTGOOD = None

with open("half_delta_output.txt") as f:
    for line in f:
        match = RE.match(line)
        if match:
            for steps, thresh in [(int(match[1]), int(match[2], 16)), (int(match[1]) + 1, int(match[2], 16) + 1)]:
                lthresh = math.log2(thresh)
                csteps = int((lthresh * NUMER + TERM) / DENOM)
                if csteps < steps:
                    LASTBAD = (steps, csteps, thresh)
                    FIRSTGOOD = None
                elif FIRSTGOOD is None:
                    FIRSTGOOD = (steps, csteps, thresh)

assert LASTBAD[0] == FIRSTGOOD[0]
for t in range(LASTBAD[2], FIRSTGOOD[2]+1):
    lt = math.log2(t)
    csteps = int((lt * NUMER + TERM) / DENOM)
    if csteps >= FIRSTGOOD[0]:
        print("Valid as of %i" % t)
        break

# Verify the formula with exact integer arithmetic (slow!).
with open("half_delta_output.txt") as f:
    for line in f:
        match = RE.match(line)
        if match:
            steps = int(match[1]) + 1
            thresh = int(match[2], 16) + 1
            if steps % 100 == 0:
                print("Verifying for steps=%i" % steps)
            if steps >= MIN_STEPS:
                bits = (thresh**(2*NUMER) - 1).bit_length()
                assert steps*DENOM - TERM <= bits
