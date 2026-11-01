# Track LP coverage inventory (draft): AMENDMENTS.md (sha256 c887d1e2...51881, 26 lines)

CORPUS: docs/graph/LP/CORPUS.sha256 (MAIN.md, AMENDMENTS.md); LP3-PLAN.md candidate (SPEC Q1)

Pre-anchor coverage inventory (skill build-proof-dependency-graph, Phase 2), written before the LP anchors are frozen. Every disposition is PROPOSED; node IDs are planned IDs (SPEC.md, node scheme). The ANCHORS list in REASON names the anchors whose proof the item supports. Regenerate only before extraction starts; afterwards the slice packets are the source of truth.


ITEM: lpA:precedence
KIND: heading
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#header@L1-L6
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-amend; the precedence rule (N1 in place; N2-N12 override the cited MAIN lines); recorded in SPEC §Corpus and applied to every node
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:N1
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N1@L10-L10
DISPOSITION: NODE lpM:L7#symplectic
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-amend; typo fixed in place at MAIN L238; no locator change
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:N2
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N2@L11-L11
DISPOSITION: NODE lpM:L6#shared-U,lpM:L8#shared-tube,lpM:L14#choices
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-amend; one shared compact U with the 4r_g tube, its modulus in (17), L8 and (39); r <= r_g
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:N3
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N3@L12-L12
DISPOSITION: NODE lpM:L8#widths
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-amend; r_* <= 4r_g stated; sup-distance tube about K'
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:N4
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N4@L13-L13
DISPOSITION: NODE lpM:L12#finite-divisors
REASON: ANCHORS: none; SLICE: LP-amend; (35) is a remark, not a formal dependency
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:N5
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N5@L14-L14
DISPOSITION: NODE lpM:L10#lie-flow-identification,lpM:L10#flow-existence,lpM:L10#remainder
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L12 only); SLICE: LP-amend; sketched flow existence, Lie-series identification and c_D: candidate SOURCE_GAP steps on route-L12
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:N6
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N6@L15-L15
DISPOSITION: NODE lpM:L13#numeric-hypotheses,lpM:L14#route-L13
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route); SLICE: LP-amend; widths of the L13 specialization; radius D_0 sqrt(mu), improvement r/2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:N7
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N7@L16-L16
DISPOSITION: NODE lpM:L14#route-L12,lpM:L14#route-L13
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H; SLICE: LP-amend; L12 and L13 are alternative suppliers of the stopped drift: route nodes, never a conjunction
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:N8
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N8@L17-L17
DISPOSITION: NODE lpM:s1:elements,lpM:T15#orientation
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-amend; AMD convention; ruled OD-1 (D59): C = sum Lambda - |L|, no prograde premise
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:N9
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N9@L18-L18
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-amend; confirms the exclusion of lpM:L4#sharpness (MAIN L158)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:N10
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N10@L19-L19
DISPOSITION: NODE lpM:L16#mu0-choice
REASON: ANCHORS: LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-amend; final mu_0 constraints recorded in the constant list (OD-9)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:N11
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N11@L20-L20
DISPOSITION: NODE lpM:L5#perihelion
REASON: ANCHORS: LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2; SLICE: LP-amend; define d_star before bounding |p_i|
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:N12
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#N12@L21-L21
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-amend; engineering note on the roadmap's Lean typing; no MAIN line, no obligation
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lpA:order
KIND: claim
SOURCE: docs/tracks/LP/source/AMENDMENTS.md#order@L23-L26
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP-amend; recommended formalization order; administrative
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -
