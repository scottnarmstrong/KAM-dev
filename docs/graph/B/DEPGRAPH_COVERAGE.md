# Proof-source coverage manifest — track B

CORPUS: docs/explorations/program-b-plan.md (§2.1–2.3 L66–L206, Brief 2 L833–L870) and docs/tracks/B/FREEZE-PROPOSAL.md (§2 exact frozen text L17–L99, §6 deviations L161–L166), pinned by SHA-256 in docs/graph/B/CORPUS.sha256 (main 6ecfdbddc, 2026-11-03)

## Inventory

ITEM: b:2.1#conventions
KIND: heading
SOURCE: docs/explorations/program-b-plan.md#b:2.1@L66-L99
DISPOSITION: NODE b:defs#hamiltonianVectorField, b:defs#symplecticForm, b:defs#bracket, b:brief2#uniqueness, b:2.2#B1-T, b:2.3#B1-E
REASON: field, form and bracket conventions are definition nodes; the solution-quantifier conventions L90-L99 are realized in the two roots and the uniqueness step
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:2.2#statement
KIND: theorem
SOURCE: docs/explorations/program-b-plan.md#b:2.2@L100-L136
DISPOSITION: NODE b:2.2#B1-T
REASON: the B1-T statement
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:2.2#isotropic
KIND: corollary
SOURCE: docs/explorations/program-b-plan.md#b:2.2@L138-L141
DISPOSITION: EXCLUDED
REASON: isotropic specialization and all-time remark; not used by either root
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:2.2#transfer
KIND: corollary
SOURCE: docs/explorations/program-b-plan.md#b:2.2@L143-L155
DISPOSITION: EXCLUDED
REASON: B1-transfer is an internal corollary downstream of B1-T, outside the root closure
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:2.2#source-and-proof
KIND: proof-region
SOURCE: docs/explorations/program-b-plan.md#b:2.2-source-and-proof@L157-L163
DISPOSITION: NODE b:2.2#action-derivative, b:2.2#first-exit, b:2.2#periodic-reduction, b:brief2#stopped-drift
REASON: proof sketch of B1-T: stopped drift, first exit, periodic continuation
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:2.2#gls17
KIND: citation
SOURCE: docs/explorations/program-b-plan.md#b:2.2-source-and-proof@L157-L163
DISPOSITION: NODE b:2.2#B1-T
REASON: GLS17 §4.3 is provenance of the derivation reproduced in the plan
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:2.3#oscillatorAction
KIND: definition
SOURCE: docs/explorations/program-b-plan.md#b:2.3@L167-L173
DISPOSITION: NODE b:defs#oscillatorAction
REASON: frozen oscillator action reused
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:2.3#statement
KIND: theorem
SOURCE: docs/explorations/program-b-plan.md#b:2.3@L175-L193
DISPOSITION: NODE b:2.3#B1-E
REASON: the B1-E statement
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:2.3#continuation
KIND: proof-region
SOURCE: docs/explorations/program-b-plan.md#b:2.3-continuation@L195-L199
DISPOSITION: NODE b:2.3#first-exit, b:2.3#normal-form-commutes, b:2.3#compact-continuation
REASON: no exit through I_j=0, compact continuation set, algebraic lemma
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:2.3#transfer
KIND: corollary
SOURCE: docs/explorations/program-b-plan.md#b:2.3@L201-L201
DISPOSITION: EXCLUDED
REASON: oscillator observable transfer: internal corollary outside the root closure
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:2.3#cl20
KIND: citation
SOURCE: docs/explorations/program-b-plan.md#b:2.3-continuation@L202-L205
DISPOSITION: NODE b:2.3#B1-E
REASON: CL20 §4.1 provenance of the action-bracket estimate
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:2.4#approval
KIND: heading
SOURCE: docs/explorations/program-b-plan.md#b:2.4@L207-L226
DISPOSITION: EXCLUDED
REASON: approval-surface policy, no mathematics
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:brief2#proof-sequence
KIND: proof-region
SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L847-L855
DISPOSITION: NODE b:brief2#chart-transport, b:brief2#stopped-drift, b:brief2#uniqueness, b:2.2#action-derivative, b:2.2#first-exit, b:2.2#periodic-reduction, b:2.3#action-bracket, b:2.3#normal-form-commutes, b:2.3#first-exit, b:2.3#compact-continuation, ext:ode#local
REASON: proof sequence for both roots; edge cases (T=0, eta=0, zero actions) recorded in the first-exit/continuation NOTEs; the observable estimate (L853-L854) is the excluded transfer corollary
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: ext:continuation
KIND: external
SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L851-L851
DISPOSITION: NODE ext:ode#compact-continuation
REASON: "the existing continuation theorem"
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: ext:picard
KIND: external
SOURCE: docs/explorations/program-b-plan.md#b:brief2-proof-sequence@L854-L854
DISPOSITION: NODE ext:ode#local
REASON: "Handle T=0 by local existence" and local uniqueness
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:brief2#objective-scope
KIND: proof-region
SOURCE: docs/explorations/program-b-plan.md#b:brief2@L833-L846
DISPOSITION: EXCLUDED
REASON: task scope and policy; its mathematical constraint (no Diophantine or nondegeneracy premise) is reflected in the roots hypotheses
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: b:brief2#outputs-checks
KIND: proof-region
SOURCE: docs/explorations/program-b-plan.md#b:brief2@L857-L870
DISPOSITION: EXCLUDED
REASON: process and handoff rules; the reviewer rule L863-L864 (first exit must not assume the existence interval) is enforced in the first-exit nodes quantifiers
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: freeze#B1-T
KIND: theorem
SOURCE: docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L24-L54
DISPOSITION: NODE b:2.2#B1-T
REASON: exact frozen text of torus_confinement (statement source of the root)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: freeze#B1-E
KIND: theorem
SOURCE: docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L57-L95
DISPOSITION: NODE b:2.3#B1-E
REASON: exact frozen text of oscillator_confinement (statement source of the root)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: freeze#deviations
KIND: heading
SOURCE: docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-6@L161-L166
DISPOSITION: NODE b:2.2#B1-T, b:2.3#B1-E
REASON: owner-approved deviations from the plan statement, recorded in the roots NOTE
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: freeze#scaffold-open
KIND: heading
SOURCE: docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L17-L23
DISPOSITION: EXCLUDED
REASON: section heading, code fence, open Set and namespace line; no mathematics
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes

ITEM: freeze#scaffold-close
KIND: heading
SOURCE: docs/tracks/B/FREEZE-PROPOSAL.md#b:freeze-2@L96-L99
DISPOSITION: EXCLUDED
REASON: proof placeholder, end namespace and code fence; no mathematics
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-nodes
