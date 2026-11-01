ITEM: lpM:L5
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L162-L175
DISPOSITION: NODE lpM:L5
REASON: the d-generic Lemma 5; LP0 is its planar instance, the anchor node lpM:L5#planar_strongAMD_barrier (slice LP-athm, own coverage item)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L5#gap-positive
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L166-L166
DISPOSITION: NODE lpM:L5#gap-positive
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; a nonpositive gap would be feasible, then L3 (13) gives C>=B_{i,i+1}>=B
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L5#Km-compact
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L166-L170
DISPOSITION: NODE lpM:L5#Km-compact
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; K_m compact by L4 continuity; d_pair = minimum of the gaps; display at L167-L169
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L5#empty-case
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L170-L170
DISPOSITION: NODE lpM:L5#empty-case
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; K_m empty: assertions vacuous
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L5#perihelion
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L170-L175
DISPOSITION: NODE lpM:L5#perihelion
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; (16): sqrt(1-e^2)>=m/I_max and a(1-e)>=d_star; amendment N11 (define d_star first)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:eq16
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L171-L174
DISPOSITION: NODE lpM:L5#perihelion
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; display (16)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L5#bounds
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L175-L175
DISPOSITION: NODE lpM:L5#bounds
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; |q_i|<=2a_max, |p_i|<=nu_i sqrt(2/d_star) by (12)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L5#pair-distances
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L175-L175
DISPOSITION: NODE lpM:L5#pair-distances
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; ordered radial intervals give |q_j-q_i|>=d_pair for all i<j
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L5#compact-physical
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L175-L175
DISPOSITION: NODE lpM:L5#compact-physical
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; energy <= -1/(2a_max); compact nonsingular physical set
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L5#projection
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L175-L175
DISPOSITION: NODE lpM:L5#projection
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; H_i>=m by L3
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L5#ext-compact-min
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L170-L170
DISPOSITION: NODE lpM:ext-compact-min
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; minimum of finitely many positive continuous gaps over a compact set (candidate external)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L6
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L177-L189
DISPOSITION: NODE lpM:L6
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; moving threshold (17) and continuation, both time directions
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:eq17
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L184-L186
DISPOSITION: NODE lpM:L6#moving-threshold
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; display (17)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L6#shared-U
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:L6#shared-U
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; compact neighborhood U and modulus Omega_B -> 0; amendment N2 makes U the one set shared with L8 and L14
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L6#moving-threshold
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:L6#moving-threshold
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; (17) from (13) and the modulus
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L6#local-existence
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:L6#local-existence
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; bounded field and derivative on a neighborhood of the L5 set; Picard contraction; uniqueness
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L6#continuation
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:L6#continuation
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; limit at a finite endpoint in the compact set, local solution there, gluing; ellipticity cannot be lost
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L6#backward
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:L6#backward
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; negated field gives the backward assertion
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L6#ext-picard
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:ext-picard
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; Picard iteration / contraction mapping (candidate external)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b

ITEM: lpM:L6#ext-gronwall
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:ext-gronwall
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; uniqueness by iterating the integral inequality (candidate external)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2b
