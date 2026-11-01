# Track LP coverage inventory (draft): MAIN.md (sha256 68e9167f...48c1b, 679 lines)

CORPUS: docs/graph/LP/CORPUS.sha256 (MAIN.md, AMENDMENTS.md); LP3-PLAN.md candidate (SPEC Q1)

Pre-anchor coverage inventory (skill build-proof-dependency-graph, Phase 2), written before the LP anchors are frozen. Every disposition is PROPOSED; node IDs are planned IDs (SPEC.md, node scheme). The ANCHORS list in REASON names the anchors whose proof the item supports. Regenerate only before extraction starts; afterwards the slice packets are the source of truth.


ITEM: lpM:h:title
KIND: heading
SOURCE: docs/tracks/LP/source/MAIN.md#title@L1-L3
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m1; title and date
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:intro#result
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#intro@L5-L5
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m1; summary of T15/T19 and of what is not claimed; the content is restated by §1 and the theorems
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:intro#method
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#intro@L7-L7
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m1; method overview; the mathematics is in L9-L13; the L13 reuse remark is L13's own statement
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:h:s1
KIND: heading
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L9-L9
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m1; section heading
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s1:data
KIND: definition
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L11-L15
DISPOSITION: NODE lpM:s1:data
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; fixed data n>=2, nu>0 with max nu=1, compact ordered A, delta, gamma>0, tau>n-1, d in {2,3}, the two norms; LP0 uses only n, nu; LP3 drops gamma, tau; a result's SOURCE_HYPOTHESES name this package
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s1:model
KIND: definition
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L24
DISPOSITION: NODE lpM:s1:model
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; units G=1, star mass 1, masses mu*nu_i, iota_X Omega=-dH, exact Hamiltonian (1), physical domain, physical time
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq1
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L18-L23
DISPOSITION: NODE lpM:s1:model
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; display (1) maps to its enclosing definition
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s1:elements
KIND: definition
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L26-L37
DISPOSITION: NODE lpM:s1:elements
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; v_i, E_i, eccentricity vector, a_i, I_i=Lambda_i, e_i, L_i, L, C; planar cross product; frozen element definitions (planar reused, spatial new) bind here after freeze; CHAR: sourceKepler_axis_pos, spatialSourceKeplerAxis_pos, spatialSourceKeplerAction_pos, spatialSourceKeplerAction_sq
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq2
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L32-L36
DISPOSITION: NODE lpM:s1:elements
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; C = sum I - |L| (orientation-free; amendment N8, ruling OD-1/D59)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s1:elements#elliptic-remark
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L37-L37
DISPOSITION: NODE lpM:L5#perihelion
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; 'our hypotheses imply e_i<1' is a forward remark; it is a consequence of L5 (16), not a premise
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s1:model#normalization
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L39-L39
DISPOSITION: NODE lpM:s1:model
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; physical L and AMD are mu*L, mu*C; delta is normalized; splitting (1) uses central Kepler parameter one
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s1:chamber
KIND: definition
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L41-L44
DISPOSITION: NODE lpM:s1:chamber
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; action chamber Q; carrier of the thresholds (OrderedActions, OD-2/OD-11)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s1:thresholds
KIND: definition
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L45-L55
DISPOSITION: NODE lpM:s1:thresholds
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; a_i(I), D(u), B_ij, B_cross, B_star, B; attained minima by L4; on the chamber carrier; CHAR: orderedPairThreshold_isLeast, orderedPairThreshold_existsUnique_value, orderedCrossThreshold_isLeast, orderedStrongThreshold_isLeast
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq3
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L46-L54
DISPOSITION: NODE lpM:s1:thresholds
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; display (3) maps to its enclosing definition
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s1:fast
KIND: definition
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L57-L61
DISPOSITION: NODE lpM:s1:fast
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; fast Hamiltonian h and radian frequencies omega (4); LP3 uses h for the Kepler data of the partial-convex input
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq4
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L58-L61
DISPOSITION: NODE lpM:s1:fast
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; display (4)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s1:dioph
KIND: definition
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L62-L67
DISPOSITION: NODE lpM:s1:dioph
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H; SLICE: LP-m1; Diophantine condition (5) at omega(I^0), angles of period 2pi (L13 converts to period one); LP3 has no arithmetic premise
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq5
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L63-L66
DISPOSITION: NODE lpM:s1:dioph
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H; SLICE: LP-m1; display (5)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s1:conclusion
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L69-L91
DISPOSITION: NODE lpM:T15,lpM:T19
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; the common conclusion is the statement content of T15 (d=2) and T19 (d=3), i.e. of LP1/LP2; LP3-1/LP3-2 restate it with the changes of LP3-PLAN §1.2; includes 'initial pair collisions excluded' (L78) and the osculating sentence (L91, via L16, N10)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq6
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L71-L73
DISPOSITION: NODE lpM:T15,lpM:T19
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; premises (6); LP3 drops (5)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq7
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L75-L77
DISPOSITION: NODE lpM:T15,lpM:T19
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H; SLICE: LP-m1; horizon (7), a = 1/(2(tau+1)); LP3 replaces the exponent
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq8
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L79-L86
DISPOSITION: NODE lpM:T15,lpM:T19
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; drift and margin conclusions (8)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq9
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L87-L90
DISPOSITION: NODE lpM:T15,lpM:T19
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; canonical annulus separation (9)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s1:no-crossing
KIND: definition
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
DISPOSITION: NODE lpM:T15,lpM:T19
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m1; meaning of 'no orbit crossing' (strict ordering of the radial annuli; OD-5/OD-9); interpretive part of the conclusion
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s1:half-integer
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
DISPOSITION: NODE lpM:s1:half-integer
REASON: ANCHORS: LP1-H,LP2-H; SLICE: LP-m1; tau = n - 1/2 is admissible and gives exponent 1/(2n+1); the arithmetic step of the corollary anchors
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:h:s2
KIND: heading
SOURCE: docs/tracks/LP/source/MAIN.md#s2@L95-L95
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m2a; section heading
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L1
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L1@L97-L108
DISPOSITION: NODE lpM:L1
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; normalization and Newtonian reconstruction (frozen IsNewtonSolutionOn/barycentric maps); LP0 reaches it only through lpM:L3#conservation if L3 stays one node (SPEC Q3)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L1#reduction
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L1@L101-L102
DISPOSITION: NODE lpM:L1#reduction
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; translation reduction and division by mu give (1)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L1#reconstruction
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L1@L104-L108
DISPOSITION: NODE lpM:L1#reconstruction
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; explicit inverse, velocities (10), Newton's equations
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq10
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L1@L105-L107
DISPOSITION: NODE lpM:L1#reconstruction
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; (10) is consumed by L3 (recoil) and L16 (V_i); extractor may refine it to a display node lpM:L1#eq10
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L2
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L2@L110-L128
DISPOSITION: NODE lpM:L2
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; orbital identities (11)-(12), including e=1; CHAR: sourceKepler_ecc_le_one, sourceKeplerPeri_le_planeLength, planeLength_le_sourceKeplerApo and the spatial ecc/angular-momentum/peri/apo characterizations
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq11
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L2@L113-L116
DISPOSITION: NODE lpM:L2
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; display (11)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq12
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L2@L118-L121
DISPOSITION: NODE lpM:L2
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; display (12)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L2#ecc-identity
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
DISPOSITION: NODE lpM:L2#ecc-identity
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; expansion of |e|^2 and substitution 2E=-1/a give (11)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L2#radial-bounds
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L128
DISPOSITION: NODE lpM:L2#radial-bounds
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; radial/tangential decomposition, completing the square: (12)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L3
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L130-L139
DISPOSITION: NODE lpM:L3
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; L constant, C>=0, L!=0 and positive projections below B_star, identity and inequality (13), H_i>=m; CHAR: sourceStrongAMD_nonneg, sum_action_mul_eccDeficit_le_sourceStrongAMD and spatial twins
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq13
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L133-L136
DISPOSITION: NODE lpM:L3
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; (13): identity part is dynamic (DYN), inequality part is static (LP0); see SPEC Q3
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L3#planar-orientation
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L137-L137
DISPOSITION: NODE lpM:L3#planar-orientation
REASON: ANCHORS: LP1,LP1-H,LP3-1; SLICE: LP-m2a; planar orientation choice L>0; consumed by T15's reflection step (N8, OD-1)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L3#conservation
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
DISPOSITION: NODE lpM:L3#conservation
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; dL/dt=0: recoil term, central forces, pair torques; constancy by the fundamental theorem of calculus
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L3#amd-nonneg
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
DISPOSITION: NODE lpM:L3#amd-nonneg
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; |L|<=sum|L_i|<=sum I_i by (11)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L3#L-nonzero
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
DISPOSITION: NODE lpM:L3#L-nonzero
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; L=0 would give C>=min I_i
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L3#projections
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
DISPOSITION: NODE lpM:L3#projections
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; H_i>=I_i-C, hence H_i>=m
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L3#deficit
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
DISPOSITION: NODE lpM:L3#deficit
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; H_i<=I_i sqrt(1-e_i^2) gives the inequality in (13); the identity from constant |L| (DYN only)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L3#ext-ftc
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
DISPOSITION: NODE lpM:ext-ftc
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; fundamental theorem of calculus (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L4
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L141-L160
DISPOSITION: NODE lpM:L4
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; attained, positive, continuous thresholds, (14); the radial-contact/Laskar-Petit/sharpness clauses of the statement (L143, L147) have no consumer (SPEC Q4); CHAR: the four threshold characterizations
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq14
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L144-L146
DISPOSITION: NODE lpM:L4
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; display (14): B_ij<I_j, B=min(B_cross,I_1)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L4#feasible-compact
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
DISPOSITION: NODE lpM:L4#feasible-compact
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; feasible set closed and nonempty, (0,1-alpha) feasible; minimum attained
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L4#contact-reduction
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
DISPOSITION: NODE lpM:L4#contact-reduction
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; scaling to contact does not increase the objective
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L4#contact-param
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L153
DISPOSITION: NODE lpM:L4#contact-param
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; contact parameterized over [0,1], display (15)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq15
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L150-L153
DISPOSITION: NODE lpM:L4#contact-param
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; display (15)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L4#continuity
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L154-L156
DISPOSITION: NODE lpM:L4#continuity
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; joint continuity and uniform continuity on compact neighborhoods give continuity of B_ij and B
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L4#positivity
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L156-L156
DISPOSITION: NODE lpM:L4#positivity
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; a zero minimum cannot give contact
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L4#competitor
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L156-L156
DISPOSITION: NODE lpM:L4#competitor
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; competitor (0,1-alpha): B_ij<=I_j D(1-alpha)<I_j, proving (14)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L4#sharpness
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L158-L158
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m2a; amendment N9: interior minimizers and geometric realization are not used downstream; outside every root closure (to be confirmed by the slice reviewer and the global reviewer)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L4#lp-identification
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L160-L160
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m2a; identification with the Laskar-Petit relative critical AMD; comparison only, no proof consumes it
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L4#cite-laskar-petit
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L160-L160
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m2a; provenance (arXiv:1703.07125v2 §3-3.2); MAIN: no optimizer formula from that source is needed
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L4#ext-extreme-value
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
DISPOSITION: NODE lpM:ext-compact-min
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; continuous function on a nonempty compact set attains its minimum (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L4#ext-unif-cont
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L4@L154-L154
DISPOSITION: NODE lpM:ext-heine-cantor
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2a; uniform continuity on compact sets (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L5
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L162-L175
DISPOSITION: NODE lpM:L5
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; the uniform strong barrier; LP0 = full L5 (FREEZE-PROPOSAL draft 7 §3.1); proposed anchor node of LP0
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L5#gap-positive
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L166-L166
DISPOSITION: NODE lpM:L5#gap-positive
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; a nonpositive gap would be feasible, then L3 (13) gives C>=B_{i,i+1}>=B
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L5#Km-compact
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L166-L170
DISPOSITION: NODE lpM:L5#Km-compact
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; K_m compact by L4 continuity; d_pair = minimum of the gaps; display at L167-L169
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L5#empty-case
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L170-L170
DISPOSITION: NODE lpM:L5#empty-case
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; K_m empty: assertions vacuous
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L5#perihelion
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L170-L175
DISPOSITION: NODE lpM:L5#perihelion
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; (16): sqrt(1-e^2)>=m/I_max and a(1-e)>=d_star; amendment N11 (define d_star first)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq16
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L171-L174
DISPOSITION: NODE lpM:L5#perihelion
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; display (16)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L5#bounds
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L175-L175
DISPOSITION: NODE lpM:L5#bounds
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; |q_i|<=2a_max, |p_i|<=nu_i sqrt(2/d_star) by (12)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L5#pair-distances
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L175-L175
DISPOSITION: NODE lpM:L5#pair-distances
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; ordered radial intervals give |q_j-q_i|>=d_pair for all i<j
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L5#compact-physical
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L175-L175
DISPOSITION: NODE lpM:L5#compact-physical
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; energy <= -1/(2a_max); compact nonsingular physical set
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L5#projection
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L175-L175
DISPOSITION: NODE lpM:L5#projection
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; H_i>=m by L3
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L5#ext-compact-min
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L5@L170-L170
DISPOSITION: NODE lpM:ext-compact-min
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; minimum of finitely many positive continuous gaps over a compact set (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L6
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L177-L189
DISPOSITION: NODE lpM:L6
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; moving threshold (17) and continuation, both time directions
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq17
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L184-L186
DISPOSITION: NODE lpM:L6#moving-threshold
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; display (17)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L6#shared-U
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:L6#shared-U
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; compact neighborhood U and modulus Omega_B -> 0; amendment N2 makes U the one set shared with L8 and L14
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L6#moving-threshold
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:L6#moving-threshold
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; (17) from (13) and the modulus
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L6#local-existence
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:L6#local-existence
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; bounded field and derivative on a neighborhood of the L5 set; Picard contraction; uniqueness
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L6#continuation
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:L6#continuation
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; limit at a finite endpoint in the compact set, local solution there, gluing; ellipticity cannot be lost
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L6#backward
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:L6#backward
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; negated field gives the backward assertion
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L6#ext-picard
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:ext-picard
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; Picard iteration / contraction mapping (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L6#ext-gronwall
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
DISPOSITION: NODE lpM:ext-gronwall
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m2b; uniqueness by iterating the integral inequality (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:h:s3
KIND: heading
SOURCE: docs/tracks/LP/source/MAIN.md#s3@L191-L191
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m3; section heading
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L7
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L7@L193-L242
DISPOSITION: NODE lpM:L7
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; regular planar canonical chart; reused by L17 and L18
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq18
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L7@L208-L210
DISPOSITION: NODE lpM:L7#kepler-equation
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; display (18)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq19
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L7@L214-L220
DISPOSITION: NODE lpM:L7#chart-formula
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; display (19); reused by L17 (46)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq20
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L7@L222-L225
DISPOSITION: NODE lpM:L7#rotated-form
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; display (20)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L7#kepler-equation
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L7@L202-L211
DISPOSITION: NODE lpM:L7#kepler-equation
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; data a, s, b_e, k, l; unique analytic solution F of (18)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L7#chart-formula
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L7@L213-L220
DISPOSITION: NODE lpM:L7#chart-formula
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; the chart (19)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L7#rotated-form
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L7@L221-L226
DISPOSITION: NODE lpM:L7#rotated-form
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; (20); energy, angular momentum, eccentricity vector; extension to e=0
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L7#symplectic
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L7@L228-L238
DISPOSITION: NODE lpM:L7#symplectic
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; p.dq computation, exact differential; amendment N1 (fixed in place at L238)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L7#inverse
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L7@L240-L242
DISPOSITION: NODE lpM:L7#inverse
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; analytic inverse on the region
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L7#ext-holomorphic-limit
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L7@L211-L211
DISPOSITION: NODE lpM:ext-holomorphic-limit
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; uniform limits of holomorphic iterates are holomorphic (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L7#ext-identity
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L7@L238-L238
DISPOSITION: NODE lpM:ext-identity-theorem
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; analytic identity extends from e>0 across e=0 (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L244-L271
DISPOSITION: NODE lpM:L8
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; whole-sublevel planar analytic neighborhood; LP2 through L18#extension; LP3 through F1/F2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq21
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L247-L249
DISPOSITION: NODE lpM:L8
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; display (21)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq22
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L251-L254
DISPOSITION: NODE lpM:L8
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; display (22)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8#empty-case
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L257
DISPOSITION: NODE lpM:L8#empty-case
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; L_delta empty: no initial state
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8#shared-tube
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L257
DISPOSITION: NODE lpM:L8#shared-tube
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; U and r_g with Omega_B(4r_g)<=delta/16; amendment N2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8#real-margin
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L258-L261
DISPOSITION: NODE lpM:L8#real-margin
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; sum Gamma_i <= B(I)-3delta/16; all phases safe by L5; e<=e_*<1
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8#compact-real-set
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L261-L261
DISPOSITION: NODE lpM:L8#compact-real-set
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; compact set of (I^0,I,z,lambda); amendment N3 (projection K')
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8#newton-extension
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L263-L263
DISPOSITION: NODE lpM:L8#newton-extension
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; uniform complex extension of the Kepler-equation solution; bilinear complexification
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8#gluing
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L265-L265
DISPOSITION: NODE lpM:L8#gluing
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; gluing on complex balls, identity theorem, finite subcover, periodicity
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8#denominators
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L267-L271
DISPOSITION: NODE lpM:L8#denominators
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; Re(w.w)>=d^2/2 for every star and pair denominator
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8#widths
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L271-L271
DISPOSITION: NODE lpM:L8#widths
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; Cauchy bounds and the choice of r_*, s, b; amendment N3 (r_*<=4r_g)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8#exact-split
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L271-L271
DISPOSITION: NODE lpM:L8#exact-split
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; the product chart gives (4): exact split h + mu f
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8#ext-identity
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L265-L265
DISPOSITION: NODE lpM:ext-identity-theorem
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; identity theorem (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8#ext-compact-cover
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L265-L265
DISPOSITION: NODE lpM:ext-compact-cover
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; finite subcover (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L8#ext-cauchy
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L8@L271-L271
DISPOSITION: NODE lpM:ext-cauchy-estimates
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m3; Cauchy's one-variable estimates; holomorphic square root with positive real part (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:h:s4
KIND: heading
SOURCE: docs/tracks/LP/source/MAIN.md#s4@L273-L273
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m4a; section heading
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s4:intro
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#s4@L275-L275
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m4a; overview; 'any fixed number of slow pairs' is part of the L9-L11 statements
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L9
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L277-L304
DISPOSITION: NODE lpM:L9
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; Fourier, Cauchy and commutator estimates
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L9#domains
KIND: definition
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L279-L284
DISPOSITION: NODE lpM:L9#domains
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; domains D_rho (23)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq23
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L280-L284
DISPOSITION: NODE lpM:L9#domains
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; display (23)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L9#norm
KIND: definition
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L285-L291
DISPOSITION: NODE lpM:L9#norm
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; scaled components and the weighted norm (24)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq24
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L287-L291
DISPOSITION: NODE lpM:L9#norm
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; display (24)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq25
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L293-L295
DISPOSITION: NODE lpM:L9#commutator
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; display (25)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L9#sup-to-fourier
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L298-L299
DISPOSITION: NODE lpM:L9#sup-to-fourier
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; contour shift; sup bound to Fourier norm
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L9#banach-algebra
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L300-L300
DISPOSITION: NODE lpM:L9#banach-algebra
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; convolution estimate
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L9#cauchy-derivative
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L302-L303
DISPOSITION: NODE lpM:L9#cauchy-derivative
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; Cauchy 1/sigma; angle factor 1/(e sigma)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L9#commutator
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L304-L304
DISPOSITION: NODE lpM:L9#commutator
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; (25)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L9#projections-tail
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L304-L304
DISPOSITION: NODE lpM:L9#projections-tail
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; projections and Fourier tail
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L9#ext-fourier-contour
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L298-L298
DISPOSITION: NODE lpM:ext-fourier-contour
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; Fourier coefficients of periodic holomorphic functions and contour shift (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L9#ext-cauchy
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L9@L302-L302
DISPOSITION: NODE lpM:ext-cauchy-estimates
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; Cauchy's formula (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L10
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L10@L306-L349
DISPOSITION: NODE lpM:L10
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; cohomology and a controlled Lie step
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq26
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L10@L309-L314
DISPOSITION: NODE lpM:L10#homological
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; display (26)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq27
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L10@L316-L320
DISPOSITION: NODE lpM:L10#remainder
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; display (27)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq28
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L10@L331-L335
DISPOSITION: NODE lpM:L10#lie-series-bound
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; display (28)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq29
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L10@L343-L346
DISPOSITION: NODE lpM:L10#remainder
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; display (29)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L10#homological
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L10@L323-L328
DISPOSITION: NODE lpM:L10#homological
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; chi_k = f_k/(i k.omega); (26); reality
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L10#lie-series-bound
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L10@L330-L336
DISPOSITION: NODE lpM:L10#lie-series-bound
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; (28) and j! >= (j/e)^j
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L10#lie-flow-identification
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L10@L336-L338
DISPOSITION: NODE lpM:L10#lie-flow-identification
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; Lie series equals pullback by the flow; scalar series; amendment N5 (sketched): candidate SOURCE_GAP
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L10#flow-existence
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L10@L340-L340
DISPOSITION: NODE lpM:L10#flow-existence
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; flow existence, holomorphy, inverse, symplecticity; amendment N5 (sketched): candidate SOURCE_GAP
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L10#remainder
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L10@L342-L349
DISPOSITION: NODE lpM:L10#remainder
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; (29), B_D = 16eD; c_D implicit (amendment N5)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L10#ext-picard
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L10@L340-L340
DISPOSITION: NODE lpM:ext-picard
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; contraction on continuous paths (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L11
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L11@L351-L379
DISPOSITION: NODE lpM:L11
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; exponential normal form on the full slow set
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq30
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L11@L355-L357
DISPOSITION: NODE lpM:L11
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; display (30)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq31
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L11@L359-L362
DISPOSITION: NODE lpM:L11
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; display (31)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L11#step-estimate
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L11@L365-L370
DISPOSITION: NODE lpM:L11#step-estimate
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; one step with loss 1/N
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L11#qD-choice
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L11@L371-L374
DISPOSITION: NODE lpM:L11#qD-choice
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; q_D = min(c_D, 1/(6B_D), 1/64)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L11#induction
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L11@L375-L375
DISPOSITION: NODE lpM:L11#induction
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; E_{j+1}<=E_j/2, |X_g|<=2 eps
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L11#composition
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L11@L375-L379
DISPOSITION: NODE lpM:L11#composition
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; composition, displacement <= 1/32, domains
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L11#inverse
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L11@L379-L379
DISPOSITION: NODE lpM:L11#inverse
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; inverse by negative-time flows on D_{3/2}
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L11#derivative-bounds
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L11@L379-L379
DISPOSITION: NODE lpM:L11#derivative-bounds
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4a; Cauchy bounds on D Phi
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L12
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L381-L427
DISPOSITION: NODE lpM:L12
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; scaling r = sqrt(mu), N, eps; drift (34); (35) unused (amendment N4); conditional on the L8/L18 domain statement
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq32
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L384-L389
DISPOSITION: NODE lpM:L12
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; display (32)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq33
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L391-L395
DISPOSITION: NODE lpM:L12
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; display (33)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq34
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L397-L399
DISPOSITION: NODE lpM:L12#drift
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; display (34)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq35
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L401-L403
DISPOSITION: NODE lpM:L12#finite-divisors
REASON: ANCHORS: none; SLICE: LP-m4b; display (35): amendment N4, a remark with no consumer (SPEC Q5)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L12#perturbation-size
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L405-L405
DISPOSITION: NODE lpM:L12#perturbation-size
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; |X_{H-h_0}|_3 <= M_1 sqrt(mu)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L12#kappa-choice
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L407-L412
DISPOSITION: NODE lpM:L12#kappa-choice
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; (36) implies (30)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq36
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L408-L411
DISPOSITION: NODE lpM:L12#kappa-choice
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; display (36)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L12#time-choice
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L414-L414
DISPOSITION: NODE lpM:L12#time-choice
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; c = kappa log2 / 4, T_mu <= 2^{N/2}
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L12#drift
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L414-L420
DISPOSITION: NODE lpM:L12#drift
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m4b; transformed solutions; (34) both time signs
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L12#finite-divisors
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L420-L425
DISPOSITION: NODE lpM:L12#finite-divisors
REASON: ANCHORS: none; SLICE: LP-m4b; (35); amendment N4: not a formal dependency; extractor decides node-without-consumer vs exclusion (SPEC Q5)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L12#remark
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#L12@L427-L427
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m4b; commentary on what is inverted; no new obligation
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L13
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L429-L464
DISPOSITION: NODE lpM:L13
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; checked specialization of the Track N finite-cutoff theorem; Lean route of LP1/LP2 (N7)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L13#interface
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L433-L433
DISPOSITION: NODE lpM:L13#interface
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; interface check against named repository declarations; consumed through IMPORTED graph-N nodes, never by reading implementation Lean
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L13#cite-repository
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L433-L433
DISPOSITION: NODE N:bpN:p11:nonresonant
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; KAM.Nekhoroshev.nonresonant / ExtNFHyp / nf / preimage at f5625f19: candidate IMPORT N:bpN:p11:nonresonant (plus N:bpN:p11:s-nf#data if the NF hypothesis package is consumed separately); confirm in LP-imports
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L13#period-one
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L435-L440
DISPOSITION: NODE lpM:L13#period-one
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; theta = lambda/(2pi), rescaled slow variables, weighted bracket c_s, sign conventions
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L13#numeric-hypotheses
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L442-L457
DISPOSITION: NODE lpM:L13#numeric-hypotheses
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; (37) and the choices of kappa_1, D_0; amendment N6 (widths)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq37
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L448-L452
DISPOSITION: NODE lpM:L13#numeric-hypotheses
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; display (37)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L13#structural-hypotheses
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L458-L458
DISPOSITION: NODE lpM:L13#structural-hypotheses
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; holomorphy, reality, periodicity, module {0}, slow tube width, from L8
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L13#conclusion
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L460-L464
DISPOSITION: NODE lpM:L13#conclusion
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; (38): drift <= r/2 through exp(c_1 mu^{-a}) under stopped membership; slow displacement (nnf_disp_radius)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq38
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L13@L461-L463
DISPOSITION: NODE lpM:L13#conclusion
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m4b; display (38)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:h:s5
KIND: heading
SOURCE: docs/tracks/LP/source/MAIN.md#s5@L466-L466
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m5; section heading
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L14
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L468-L500
DISPOSITION: NODE lpM:L14
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; first exit on the whole ball; conditional on chart premises discharged by T15/T19; LP3 reuses it with the partial-convex drift supplier; routes route-L12/route-L13 (N7)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L14#centers
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L472-L472
DISPOSITION: NODE lpM:L14#centers
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; admissible centres lie in L_delta
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L14#choices
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L472-L476
DISPOSITION: NODE lpM:L14#choices
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; U, mu_0 and (39); amendment N2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq39
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L473-L475
DISPOSITION: NODE lpM:L14#choices
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; display (39)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L14#stopped-membership
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L478-L487
DISPOSITION: NODE lpM:L14#stopped-membership
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; stopped interval (40), whole-ball membership in D_1
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq40
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L479-L481
DISPOSITION: NODE lpM:L14#stopped-membership
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; display (40)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L14#improvement
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L487-L487
DISPOSITION: NODE lpM:L14#improvement
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; action bound improved (r/4 via L12, r/2 via L13), AMD margin to 3delta/4 by (13), (17), (39)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L14#route-L12
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L487-L487
DISPOSITION: NODE lpM:L14#route-L12
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-m5; route node: drift supplier L12 (N7)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L14#route-L13
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L500-L500
DISPOSITION: NODE lpM:L14#route-L13
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-m5; route node: drift supplier L13 with r = D_0 sqrt(mu) and improvement r/2 (N6, N7)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L14#no-exit
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L489-L489
DISPOSITION: NODE lpM:L14#no-exit
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; finite forward end contradicts L5/L6 continuation and the persisting improved bounds
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L14#backward
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L489-L489
DISPOSITION: NODE lpM:L14#backward
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; backward time by the same argument
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L14#separation
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L491-L495
DISPOSITION: NODE lpM:L14#separation
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; L5 with m = delta/2; d_star (41)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq41
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L492-L494
DISPOSITION: NODE lpM:L14#separation
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; display (41)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L14#axis-drift
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L14@L495-L500
DISPOSITION: NODE lpM:L14#axis-drift
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; action-to-axis estimate; A_I, A_a, T_0
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:T15
KIND: theorem
SOURCE: docs/tracks/LP/source/MAIN.md#T15@L502-L506
DISPOSITION: NODE lpM:T15
REASON: ANCHORS: LP1,LP1-H,LP3-1; SLICE: LP-m5; planar theorem; proposed anchor node of LP1; LP1-H is its tau = n-1/2 corollary; LP3-1 reuses its reduction steps
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:T15#orientation
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
DISPOSITION: NODE lpM:T15#orientation
REASON: ANCHORS: LP1,LP1-H,LP3-1; SLICE: LP-m5; L3 sign, reflection of the plane, invariance of H and constants (N8, OD-1)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:T15#chart-cover
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
DISPOSITION: NODE lpM:T15#chart-cover
REASON: ANCHORS: LP1,LP1-H,LP3-1; SLICE: LP-m5; product of L7 charts covers; C = |z|^2/2 in the prograde region; reference orientation fixed by L3
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:T15#apply-L14
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
DISPOSITION: NODE lpM:T15#apply-L14
REASON: ANCHORS: LP1,LP1-H; SLICE: LP-m5; discharges L14's chart premises with L7/L8 (m = n) and the drift supplier (routes, N7)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:T15#reconstruction
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
DISPOSITION: NODE lpM:T15#reconstruction
REASON: ANCHORS: LP1,LP1-H,LP3-1; SLICE: LP-m5; L1 reconstructs the Newtonian motion
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:T15#osculating
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#T15@L506-L506
DISPOSITION: NODE lpM:T15#osculating
REASON: ANCHORS: LP1,LP1-H,LP3-1; SLICE: LP-m5; L16 osculating conclusion
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L16
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L16@L508-L529
DISPOSITION: NODE lpM:L16
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; actual-velocity osculating ellipses (43); CHAR: osculating axis/peri/apo/ecc/energy characterizations
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L16:defs
KIND: definition
SOURCE: docs/tracks/LP/source/MAIN.md#L16@L510-L519
DISPOSITION: NODE lpM:L16:defs
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; V_i, k_i, E^osc, a^osc, e^osc vector, e^osc (42); frozen osculating definitions bind here after freeze
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq42
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L16@L511-L519
DISPOSITION: NODE lpM:L16:defs
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; display (42)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq43
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L16@L521-L524
DISPOSITION: NODE lpM:L16
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; display (43)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L16#element-error
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
DISPOSITION: NODE lpM:L16#element-error
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; |V-v|<=nP mu, |k-1|<=mu, energy and eccentricity-vector errors A_0 mu
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L16#elliptic
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
DISPOSITION: NODE lpM:L16#elliptic
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; E^osc <= -1/(4a_max), axis estimate, e^osc < 1
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L16#endpoint-estimate
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
DISPOSITION: NODE lpM:L16#endpoint-estimate
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; second estimate of (43)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L16#tangent-ellipse
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L16@L527-L527
DISPOSITION: NODE lpM:L16#tangent-ellipse
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; two-body ellipse through q_i tangent to V_i; L2 with parameter k_i
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L16#mu0-choice
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L16@L528-L528
DISPOSITION: NODE lpM:L16#mu0-choice
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; A_osc mu_0 <= d_star/2, 2A_osc mu_0 <= d_pair/2 (N10, OD-9)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L16#half-gaps
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L16@L529-L529
DISPOSITION: NODE lpM:L16#half-gaps
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-m5; osculating half gaps
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L16#convention-remark
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#L16@L529-L529
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m5; gravitational-parameter-one convention is a separately named variant; not used
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:h:s6
KIND: heading
SOURCE: docs/tracks/LP/source/MAIN.md#s6@L531-L531
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m6; section heading
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L17
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L17@L533-L578
DISPOSITION: NODE lpM:L17
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; regular spatial Poincare chart; fixed-plane deficit identity
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq44
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L17@L536-L540
DISPOSITION: NODE lpM:L17
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; display (44)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq45
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L17@L542-L544
DISPOSITION: NODE lpM:L17
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; display (45)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L17#deficit-identity
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#L17@L545-L546
DISPOSITION: NODE lpM:L17#deficit-identity
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; C_{e3} = |z|^2/2; proved by summing (45) at L578
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L17#rotation
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L17@L548-L558
DISPOSITION: NODE lpM:L17#rotation
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; rotation R (46), orthogonality, q x p = G R e_3
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq46
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L17@L549-L553
DISPOSITION: NODE lpM:L17#rotation
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; display (46)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L17#symplectic
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L17@L560-L571
DISPOSITION: NODE lpM:L17#symplectic
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; rotation terms G dg + H dh_n; density extension
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L17#inverse
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L17@L573-L578
DISPOSITION: NODE lpM:L17#inverse
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; inverse, onto the prograde region
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L17#ext-identity
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#L17@L571-L571
DISPOSITION: NODE lpM:ext-identity-theorem
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; dense set plus analyticity (candidate external)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L18
KIND: lemma
SOURCE: docs/tracks/LP/source/MAIN.md#L18@L580-L597
DISPOSITION: NODE lpM:L18
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; spatial whole-sublevel domain
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:eq47
KIND: display
SOURCE: docs/tracks/LP/source/MAIN.md#L18@L583-L585
DISPOSITION: NODE lpM:L18
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; display (47)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L18#margins
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L18@L588-L593
DISPOSITION: NODE lpM:L18#margins
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; G_i, H_i >= 3delta/16, c_i^2 > 1/2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L18#whole-ball-safe
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L18@L593-L593
DISPOSITION: NODE lpM:L18#whole-ball-safe
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; fixed-plane deficit bounds eccentricity AMD; L5 on the whole ball
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L18#extension
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L18@L595-L595
DISPOSITION: NODE lpM:L18#extension
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; L8's extension argument verbatim in 6n coordinates
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L18#rotation-invariance
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L18@L595-L595
DISPOSITION: NODE lpM:L18#rotation-invariance
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; rotation invariance of the bounds
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:L18#alignment
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#L18@L597-L597
DISPOSITION: NODE lpM:L18#alignment
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; one fixed rotation per solution, C_{e3} = C, L17 covers
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:T19
KIND: theorem
SOURCE: docs/tracks/LP/source/MAIN.md#T19@L599-L603
DISPOSITION: NODE lpM:T19
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; spatial theorem; proposed anchor node of LP2; LP2-H is its tau = n-1/2 corollary; LP3-2 reuses its reduction steps
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:T19#align
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
DISPOSITION: NODE lpM:T19#align
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; L18 alignment; ball (47); L17 symplectic
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:T19#apply-L14
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
DISPOSITION: NODE lpM:T19#apply-L14
REASON: ANCHORS: LP2,LP2-H; SLICE: LP-m6; m = 2n slow pairs; L9-L12 dimension constants; discharges L14 (routes, N7)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:T19#osculating
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
DISPOSITION: NODE lpM:T19#osculating
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; L16 in dimension three
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:T19#reconstruction
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
DISPOSITION: NODE lpM:T19#reconstruction
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; L1
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:T19#unrotate
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
DISPOSITION: NODE lpM:T19#unrotate
REASON: ANCHORS: LP2,LP2-H,LP3-2; SLICE: LP-m6; inverse fixed rotation leaves the inequalities unchanged
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:h:s7
KIND: heading
SOURCE: docs/tracks/LP/source/MAIN.md#s7@L605-L605
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m78; section heading
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s7#intro
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#s7@L607-L607
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m78; literature-check statement; no obligation
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s7#cite-lp-aa
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#s7@L611-L611
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m78; Laskar-Petit A&A 2017: interpretation; geometry proved in L2-L5
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s7#cite-lp-arxiv
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#s7@L612-L612
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m78; Laskar-Petit arXiv v2 page pins: provenance
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s7#cite-bmm
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#s7@L613-L613
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m78; Barbieri-Marco-Massetti Lemma B.1: not used as a supplier
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s7#cite-pinzari-liu
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#s7@L614-L614
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m78; Pinzari-Liu Prop. 3.2: comparison only
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s7#repository-baseline
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#s7@L616-L616
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m78; comparison with planetaryExponentialSafety and partialConvex_nekhoroshev; LP3's use of the latter is sourced in LP3-PLAN, not here
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s7#research-notes
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#s7@L618-L618
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m78; provenance of research notes; 'not used as an analytic axiom'
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s7#self-refutation
KIND: proof-region
SOURCE: docs/tracks/LP/source/MAIN.md#s7@L620-L644
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m78; self-review table; every resolution points to a lemma; reviewers confirm that no row adds an obligation absent from L1-T19
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:h:s8
KIND: heading
SOURCE: docs/tracks/LP/source/MAIN.md#s8@L646-L646
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m78; section heading
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s8#status
KIND: claim
SOURCE: docs/tracks/LP/source/MAIN.md#s8@L648-L661
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m78; status table
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpM:s8#input-hashes
KIND: citation
SOURCE: docs/tracks/LP/source/MAIN.md#s8@L663-L678
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-m78; input hashes and process record
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -
