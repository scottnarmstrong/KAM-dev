# Proof-source coverage manifest — track B

CORPUS: docs/explorations/program-b-plan.md (§2.1–2.3 L66–L206, §3.1 L300–L340, §3.2–3.3 L341–L424, §4 first instance L529–L566, Brief 2 L833–L870), docs/tracks/B/FREEZE-PROPOSAL.md (§2 L17–L99, §6 L161–L166) and docs/tracks/B/FREEZE-PROPOSAL-HH.md (L1–L41), pinned by SHA-256 in docs/graph/B/CORPUS.sha256 (main 95387f9b0, 2026-11-03)

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
DISPOSITION: NODE b:2.3#transfer, b:4#inverse-chart
REASON: B1-T observable transfer (proof source of b:2.3#transfer) and the inverse-chart requirement L153-L155
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

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
DISPOSITION: NODE b:2.3#transfer
REASON: oscillator observable transfer, used by the HH physical bounds
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

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

ITEM: b:3.1#certificate-table
KIND: proof-region
SOURCE: docs/explorations/program-b-plan.md#b:3.1@L300-L323
DISPOSITION: NODE b:3.1#checker-soundness, b:4#model-identification, b:3.2#chart-composition, b:3.2#oscillator-drift
REASON: certificate contents and checked meanings (L304-L310 model, L317-L318 domains and flows, L319-L322 bounds)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:3.1#soundness
KIND: claim
SOURCE: docs/explorations/program-b-plan.md#b:3.1@L324-L340
DISPOSITION: NODE b:3.1#checker-soundness, b:4#certificate-accepted
REASON: soundness shape, no-extra-premise rule, kernel replay of producer data (L338-L340)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:4#model
KIND: display
SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L529-L537
DISPOSITION: NODE b:4#model-identification, b:4#HH
REASON: the HH model (Appendix B of CL20)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:4#target
KIND: theorem
SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L539-L543
DISPOSITION: NODE b:4#HH
REASON: the proposed application theorem, frozen as D73
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:4#certificate
KIND: display
SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L545-L553
DISPOSITION: NODE b:4#certificate-accepted, b:4#inverse-chart
REASON: literals of the sufficient certificate, forward and inverse displacement
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:4#inequalities
KIND: proof-region
SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L554-L557
DISPOSITION: NODE b:4#initial-inclusion, b:4#physical-bounds
REASON: the three transparent inequalities and the outer bound
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:4#commentary
KIND: heading
SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L558-L559
DISPOSITION: EXCLUDED
REASON: remark on volume and indefinite energy; no proof obligation
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: freeze-hh#header
KIND: heading
SOURCE: docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L1-L14
DISPOSITION: EXCLUDED
REASON: approval record and placement; provenance of the root
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: freeze-hh#docstring
KIND: heading
SOURCE: docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L15-L19
DISPOSITION: EXCLUDED
REASON: freeze-time docstring (commentary)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: freeze-hh#statement
KIND: theorem
SOURCE: docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L20-L36
DISPOSITION: NODE b:4#HH
REASON: exact frozen text of henonHeiles_confinement
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: freeze-hh#provenance
KIND: heading
SOURCE: docs/tracks/B/FREEZE-PROPOSAL-HH.md#b:freeze-hh@L37-L41
DISPOSITION: EXCLUDED
REASON: code fence and literal provenance (E1, OD-B18)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:3.2#lie
KIND: display
SOURCE: docs/explorations/program-b-plan.md#b:3.2@L341-L356
DISPOSITION: NODE b:3.2#lie-identity, b:3.2#chart-composition
REASON: Lie identity, remainder bound, canonical composition
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:3.2#fourier
KIND: display
SOURCE: docs/explorations/program-b-plan.md#b:3.2@L358-L371
DISPOSITION: EXCLUDED
REASON: torus Fourier-Taylor norms; no oscillator root uses them
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:3.2#oscillator
KIND: proof-region
SOURCE: docs/explorations/program-b-plan.md#b:3.2@L373-L385
DISPOSITION: NODE b:3.2#oscillator-drift
REASON: oscillator bracket bounds and Cartesian Cauchy tails
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:3.2#tail
KIND: proof-region
SOURCE: docs/explorations/program-b-plan.md#b:3.2@L387-L397
DISPOSITION: EXCLUDED
REASON: CL-style infinite-majorant (Tail) formula, not used by the finite-order HH route
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:3.2#propagation
KIND: proof-region
SOURCE: docs/explorations/program-b-plan.md#b:3.2@L398-L402
DISPOSITION: NODE b:3.2#oscillator-drift, b:3.2#chart-composition
REASON: eta decomposition and propagation through charts
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: ext:cauchy
KIND: external
SOURCE: docs/explorations/program-b-plan.md#b:3.2@L382-L384
DISPOSITION: NODE ext:analysis#cauchy
REASON: Cauchy estimate behind the Cartesian tail contribution
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:3.2#provenance
KIND: citation
SOURCE: docs/explorations/program-b-plan.md#b:3.2@L404-L406
DISPOSITION: NODE b:3.2#oscillator-drift
REASON: CL20 provenance of the majorant strategy
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:3.3#divisors
KIND: heading
SOURCE: docs/explorations/program-b-plan.md#b:3.3@L408-L416
DISPOSITION: EXCLUDED
REASON: divisor witnesses are producer-side: an arbitrary generator is allowed (L317) and a bad one fails the checked inequality (L337); OD-B12
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:3.3#units
KIND: heading
SOURCE: docs/explorations/program-b-plan.md#b:3.3@L418-L424
DISPOSITION: EXCLUDED
REASON: unit and time rescalings; HH uses no rescaling (b:4#certificate-accepted)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes

ITEM: b:4#cl20-computation
KIND: citation
SOURCE: docs/explorations/program-b-plan.md#b:4-first-instance@L560-L566
DISPOSITION: EXCLUDED
REASON: CL20 reported computation: motivation of the literals, explicitly not a certificate (L564-L565)
COVERAGE_STATUS: REVIEWED
EXTRACTOR: kam-b1
REVIEWER: sonnet-review-B-hh-nodes
