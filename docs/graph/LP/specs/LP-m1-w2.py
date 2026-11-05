# Track LP, packet LP-m1-w2 (coverage only): the six §1 conclusion items that LP-m1 deferred until the headline nodes
# exist (packets/LP-m1.deferred-coverage.md, which is superseded by this packet and not assembled). Wave 2 maps them to
# the planar theorem and LP1; the spatial targets (lpM:T19, LP2) are added in wave 3 (packet LP-m6 adds no duplicate
# item: the dispositions below are completed there by the writer).
NODES = {}
T = "NODE lpM:T15, lpM:T15#planar_strongAMD_exponentialSafety, lpM:T19, lpM:T19#spatial_strongAMD_exponentialSafety"
NEWCOV = [
    ("lpM:s1:conclusion", "claim", "s1:69-91", T, "the common conclusion is the statement content of Theorems 15 (d = 2) "
     "and 19 (d = 3) and of their anchors LP1, LP2; includes 'initial pair collisions excluded' (L78, lpM:L14#maximal-"
     "solution) and the osculating sentence (L91, Lemma 16, N10)"),
    ("lpM:eq6", "display", "s1:71-73", T, "the premises (6) of Theorems 15 and 19 and LP1/LP2"),
    ("lpM:eq7", "display", "s1:75-77", T + ", lpM:T15#planar_strongAMD_exponentialSafety_halfInteger, "
     "lpM:T19#spatial_strongAMD_exponentialSafety_halfInteger", "the horizon (7), a = 1/(2(τ+1)); 1/(2n+1) in the "
     "half-integer anchors"),
    ("lpM:eq8", "display", "s1:79-86", T, "the drift and margin conclusions (8)"),
    ("lpM:eq9", "display", "s1:87-90", T, "the canonical annulus separation (9)"),
    ("lpM:s1:no-crossing", "claim", "s1:93-93", T, "meaning of 'no orbit crossing': strict ordering of the radial annuli "
     "(9), canonical and osculating; interpretive part of the conclusion"),
]
