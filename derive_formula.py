import re
import math

# Maximum denominator to consider.
MAX_DENOM = 1000

# Only derive a formula for at least this many steps.
MIN_STEPS = 512

# Direction coefficient to use.
COEF = 2.8283396311963109128634878

RE = re.compile("^(\d+) 0x([0-9a-f]+) ")

# Minimal observed offset log(threshold)-steps/COEF for odd steps.
MINODD = (1000, None)
# Minimal observed offset log(threshold)-steps/COEF for even steps.
MINEVEN = (1000, None)
# Compute MINODD and MINEVEN from the data.
with open("output.txt") as f:
    for line in f:
        match = RE.match(line)
        if match:
            steps = int(match[1]) + 1
            thresh = int(match[2], 16) + 1
            lthresh = math.log2(thresh)
            offset = lthresh - steps / COEF
            if steps & 1 == 0 and steps >= MIN_STEPS:
                MINEVEN = min(MINEVEN, (offset, steps))
            if steps & 1 == 1 and steps >= MIN_STEPS:
                MINODD = min(MINODD, (offset, steps))

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

# Find the actual formula, combining the fractional approximation with the odd/even offsets.
EVENTERM = int(math.ceil(-NUMER*(MINEVEN[0])))
ODDTERM = int(math.ceil(-NUMER*(MINODD[0])))
print("steps <= max(2*floor((%i * lthresh + %i) / %i), 2*floor((%i * lthresh + %i) / %i)-1)" % (NUMER, EVENTERM, 2*DENOM, NUMER, ODDTERM+DENOM, 2*DENOM))

# Verify the formula with exact integer arithmetic (slow!).
with open("output.txt") as f:
    for line in f:
        match = RE.match(line)
        if match:
            steps = int(match[1]) + 1
            thresh = int(match[2], 16) + 1
            if steps % 100 == 0:
                print("Verifying for steps=%i" % steps)
            if steps >= MIN_STEPS:
                bits = (thresh**(2*NUMER) - 1).bit_length()
                if steps & 1:
                    assert (steps+1)*(2*DENOM) - 2*(ODDTERM+DENOM) <= bits
                else:
                    assert steps*(2*DENOM) - 2*EVENTERM <= bits
