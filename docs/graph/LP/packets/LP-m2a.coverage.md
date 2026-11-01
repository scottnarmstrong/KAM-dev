ITEM: lpM:h:s2
KIND: heading
SOURCE: docs/tracks/LP/source/MAIN.md#s2@L95-L95
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m2a; section heading
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L1
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L1@L97-L108
DISPOSITION: NODE lpM:L1
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; normalization and Newtonian reconstruction (frozen IsNewtonSolutionOn/barycentric maps); LP0 reaches it only through lpM:L3#conservation if L3 stays one node (SPEC Q3)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L1#reduction
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L1@L101-L102
DISPOSITION: NODE lpM:L1#reduction
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; translation reduction and division by mu give (1)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L1#reconstruction
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L1@L104-L108
DISPOSITION: NODE lpM:L1#reconstruction
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; explicit inverse, velocities (10), Newton's equations
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq10
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L1@L105-L107
DISPOSITION: NODE lpM:L1#velocity
REASON: display (10) is its own node: Lemma 3 (recoil) and Lemma 16 (V_i) consume it
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L2
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L2@L110-L128
DISPOSITION: NODE lpM:L2
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; orbital identities (11)-(12), including e=1; CHAR: sourceKepler_ecc_le_one, sourceKeplerPeri_le_planeLength, planeLength_le_sourceKeplerApo and the spatial ecc/angular-momentum/peri/apo characterizations
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq11
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L2@L113-L116
DISPOSITION: NODE lpM:L2
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; display (11)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq12
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L2@L118-L121
DISPOSITION: NODE lpM:L2
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; display (12)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L2#ecc-identity
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
DISPOSITION: NODE lpM:L2#ecc-identity
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; expansion of |e|^2 and substitution 2E=-1/a give (11)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L2#radial-bounds
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L128
DISPOSITION: NODE lpM:L2#radial-bounds
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; radial/tangential decomposition, completing the square: (12)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L3
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L130-L139
DISPOSITION: NODE lpM:L3, lpM:L3#static, lpM:L3#dynamic
REASON: Q3 split (ruling root-b8): the full lemma and its static and dynamic parts
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq13
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L133-L136
DISPOSITION: NODE lpM:L3#static, lpM:L3#dynamic
REASON: Q3 split: the inequality of (13) is static (LP0), the identity dynamic
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L3#planar-orientation
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L137-L137
DISPOSITION: NODE lpM:L3#planar-orientation
REASON: ANCHORS: LP1,LP1-H,LP3-1; SLICE: LP-m2a; planar orientation choice L>0; consumed by T15's reflection step (N8, OD-1)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L3#conservation
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
DISPOSITION: NODE lpM:L3#conservation
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; dL/dt=0: recoil term, central forces, pair torques; constancy by the fundamental theorem of calculus
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L3#amd-nonneg
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
DISPOSITION: NODE lpM:L3#amd-nonneg
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; |L|<=sum|L_i|<=sum I_i by (11)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L3#L-nonzero
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
DISPOSITION: NODE lpM:L3#L-nonzero
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; L=0 would give C>=min I_i
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L3#projections
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
DISPOSITION: NODE lpM:L3#projections
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; H_i>=I_i-C, hence H_i>=m
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L3#deficit
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
DISPOSITION: NODE lpM:L3#deficit
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; H_i<=I_i sqrt(1-e_i^2) gives the inequality in (13); the identity from constant |L| (DYN only)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L3#ext-ftc
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
DISPOSITION: NODE lpM:ext-ftc
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; fundamental theorem of calculus (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L141-L160
DISPOSITION: NODE lpM:L4
REASON: attained, positive, continuous thresholds and (14); Q4 split: the radial-contact, Laskar-Petit and sharpness clauses are separate EXCLUDED items (lpM:L4#stmt-contact-lp, lpM:L4#stmt-sharpness)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq14
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L144-L146
DISPOSITION: NODE lpM:L4
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; display (14): B_ij<I_j, B=min(B_cross,I_1)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#feasible-compact
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
DISPOSITION: NODE lpM:L4#feasible-compact
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; feasible set closed and nonempty, (0,1-alpha) feasible; minimum attained
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#contact-reduction
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
DISPOSITION: NODE lpM:L4#contact-reduction
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; scaling to contact does not increase the objective
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#contact-param
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L153
DISPOSITION: NODE lpM:L4#contact-param
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; contact parameterized over [0,1], display (15)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:eq15
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L150-L153
DISPOSITION: NODE lpM:L4#contact-param
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; display (15)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#continuity
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L154-L156
DISPOSITION: NODE lpM:L4#continuity
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; joint continuity and uniform continuity on compact neighborhoods give continuity of B_ij and B
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#positivity
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L156-L156
DISPOSITION: NODE lpM:L4#positivity
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; a zero minimum cannot give contact
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#competitor
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L156-L156
DISPOSITION: NODE lpM:L4#competitor
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; competitor (0,1-alpha): B_ij<=I_j D(1-alpha)<I_j, proving (14)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#sharpness
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L158-L158
DISPOSITION: EXCLUDED
REASON: Q4 split and amendment N9: the interior-minimizer and geometric-realization paragraph is not used downstream; it supports only the excluded statement clauses
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#lp-identification
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L160-L160
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m2a; identification with the Laskar-Petit relative critical AMD; comparison only, no proof consumes it
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#cite-laskar-petit
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L160-L160
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m2a; provenance (arXiv:1703.07125v2 §3-3.2); MAIN: no optimizer formula from that source is needed
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#ext-extreme-value
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
DISPOSITION: NODE lpM:ext-compact-min
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; continuous function on a nonempty compact set attains its minimum (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#ext-unif-cont
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L154-L154
DISPOSITION: NODE lpM:ext-heine-cantor
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; uniform continuity on compact sets (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#stmt-contact-lp
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
DISPOSITION: EXCLUDED
REASON: Q4 split (ruling root-b8): the statement clauses 'The pair minimum occurs at radial contact. It agrees, after division by I_j, with the Laskar-Petit relative critical AMD' have no consumer (N9); the proof's contact reduction itself is the step lpM:L4#contact-reduction
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L4#stmt-sharpness
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L147-L147
DISPOSITION: EXCLUDED
REASON: Q4 split: the exact-least-AMD (sharpness) sentence has no consumer (N9); it is not in lpM:L4's source fields
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -

ITEM: lpM:L3#deficit-zero-L
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L133-L135
DISPOSITION: NODE lpM:L3#deficit-zero-L
REASON: the case L = 0 of the frozen deficit characterization, not argued in MAIN (SOURCE_GAP step)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
