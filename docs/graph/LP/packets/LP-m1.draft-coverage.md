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
