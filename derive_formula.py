import re
import math

MAX_DENOM = 1000

RE = re.compile("^(\d+) 0x([0-9a-f]+) ")

DATA = []

MINODD = (1000, None)
MINEVEN = (1000, None)

COEF = 2.8283396311963109128634878

with open("output.txt") as f:
    for line in f:
        match = RE.match(line)
        if match:
            steps = int(match[1]) + 1
            thresh = int(match[2], 16) + 1
            lthresh = math.log2(thresh)
            offset = lthresh - steps / COEF
            if steps & 1 == 0 and steps > 20:
                MINEVEN = min(MINEVEN, (offset, steps))
            if steps & 1 == 1 and steps > 20:
                MINODD = min(MINODD, (offset, steps))

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

EVENTERM = int(math.ceil(-NUMER*(MINEVEN[0])))
ODDTERM = int(math.ceil(-NUMER*(MINODD[0])))

print("steps <= max(2*floor((%i * lthresh + %i) / %i), 2*floor((%i * lthresh + %i) / %i)-1)" % (NUMER, EVENTERM, 2*DENOM, NUMER, ODDTERM+DENOM, 2*DENOM))
