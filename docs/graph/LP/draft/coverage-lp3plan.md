# Track LP coverage inventory (draft): LP3-PLAN.md (sha256 1b58b704...6ba, 506 lines; CANDIDATE corpus, pending SPEC Q1 and the draft-8 freeze)

CORPUS: docs/graph/LP/CORPUS.sha256 (MAIN.md, AMENDMENTS.md); LP3-PLAN.md candidate (SPEC Q1)

Pre-anchor coverage inventory (skill build-proof-dependency-graph, Phase 2), written before the LP anchors are frozen. Every disposition is PROPOSED; node IDs are planned IDs (SPEC.md, node scheme). The ANCHORS list in REASON names the anchors whose proof the item supports. Regenerate only before extraction starts; afterwards the slice packets are the source of truth.


ITEM: lp3:h:status
KIND: heading
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#status@L1-L16
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP3-a; status, source and label legend; administrative
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:review-note
KIND: claim
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#review-note@L20-L25
DISPOSITION: NODE lp3:s3#assembly
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; review-1 notes; C5 fixes the headline mu_0 as a minimum with the LP1/LP2 osculating and separation limits
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s0
KIND: claim
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s0@L27-L59
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP3-a; summary of §2-§5
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s1.1#exponents
KIND: definition
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s1.1@L63-L83
DISPOSITION: NODE lp3:s1.1#exponents
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; a_n, b_n: already-frozen track-P/N exponent definitions; bind after the draft-8 freeze
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:LP3-1
KIND: theorem
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s1.2@L85-L126
DISPOSITION: NODE lp3:LP3-1
REASON: ANCHORS: LP3-1; SLICE: LP3-a; planar target; proposed anchor node of LP3-1 (draft 8)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:LP3-2
KIND: theorem
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s1.3@L128-L134
DISPOSITION: NODE lp3:LP3-2
REASON: ANCHORS: LP3-2; SLICE: LP3-a; spatial target; proposed anchor node of LP3-2 (draft 8)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s1.4
KIND: claim
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s1.4@L136-L150
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP3-a; comparison table; no obligation
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.1
KIND: citation
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.1@L154-L175
DISPOSITION: NODE N:bpN:p0:partial
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; the sealed partialConvex_nekhoroshev read exactly: candidate IMPORT N:bpN:p0:partial (and the N definition anchors it uses, if a step consumes them separately)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.2#F1
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#F1@L181-L183
DISPOSITION: NODE lp3:s2.2#F1
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; shared tube r_g, U, Omega_B(4r_g) <= delta/16 (MAIN L8, N2)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.2#F2
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#F2@L184-L187
DISPOSITION: NODE lp3:s2.2#F2
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; uniform holomorphic extension fc, bound M, B_0 (MAIN L8)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.2#F3
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#F3@L188-L189
DISPOSITION: NODE lp3:s2.2#F3
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; widths rs, s, b, eta, rho
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.2#F4
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#F4@L190-L193
DISPOSITION: NODE lp3:s2.2#F4
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; finite cover of L_delta by centres in L_delta; empty case
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.2#F5
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#F5@L194-L197
DISPOSITION: NODE lp3:s2.2#F5
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; cells G_j, G'_j, A_j, D_j
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.2#F6
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#F6@L198-L199
DISPOSITION: NODE lp3:s2.2#F6
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; Kepler constants a_min, I_max, g, m, Mc
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.2#F7
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#F7@L200-L201
DISPOSITION: NODE lp3:s2.2#F7
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; slow erosion gap eps_D > 0
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.3#collar
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L207-L207
DISPOSITION: NODE lp3:s2.3#collar
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; collar premise
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.3#kepler-data
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L208-L214
DISPOSITION: NODE lp3:s2.3#kepler-data
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; holomorphy, C^2, reality, Hessian bound on the cell; adapted from track P (candidate IMPORT P:bpP:p14:h-data)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.3#definiteness
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L215-L218
DISPOSITION: NODE lp3:s2.3#definiteness
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; HasDefiniteFastPart with sigma = -1; negation for -h
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.3#perturbation
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L219-L235
DISPOSITION: NODE lp3:s2.3#perturbation
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; P = fc/B_0, cell containment, the four perturbation clauses (candidate IMPORT P:bpP:p14:perturbation)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.3#hamiltonian-identity
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L236-L246
DISPOSITION: NODE lp3:s2.3#hamiltonian-identity
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; N-Hamiltonian equals the chart Hamiltonian on the open set V_j; equal fields
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.3#thresholds
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L248-L255
DISPOSITION: NODE lp3:s2.3#thresholds
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; nu_0, mu_0, r(mu), T(mu), c, T_0 over the finite cover
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.3#time-check
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L257-L257
DISPOSITION: NODE lp3:s2.3#time-check
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-a; T(mu) <= the frozen horizon
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.4
KIND: lemma
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L259-L265
DISPOSITION: NODE lp3:s2.4
REASON: ANCHORS: LP3-1; SLICE: LP3-b; the drift supplier in the exact stopped (hstop) shape, planar
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.4#lift
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L269-L274
DISPOSITION: NODE lp3:s2.4#lift
REASON: ANCHORS: LP3-1; SLICE: LP3-b; chart lift of the stopped orbit (MAIN L7/L14 dictionary)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.4#cell
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L275-L275
DISPOSITION: NODE lp3:s2.4#cell
REASON: ANCHORS: LP3-1; SLICE: LP3-b; choice of the cell of I^0
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.4#fast-premises
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L276-L277
DISPOSITION: NODE lp3:s2.4#fast-premises
REASON: ANCHORS: LP3-1; SLICE: LP3-b; innerCore and G_j membership
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.4#sharp-slow-bound
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L278-L287
DISPOSITION: NODE lp3:s2.4#sharp-slow-bound
REASON: ANCHORS: LP3-1; SLICE: LP3-b; C < B(c_j) - 3delta/8 (the curvature step; uses the L6 modulus twice)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.4#slow-premise
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L288-L289
DISPOSITION: NODE lp3:s2.4#slow-premise
REASON: ANCHORS: LP3-1; SLICE: LP3-b; slow erosion
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.4#solution-premise
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L290-L293
DISPOSITION: NODE lp3:s2.4#solution-premise
REASON: ANCHORS: LP3-1; SLICE: LP3-b; the lift solves the N-field on [0,t]
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.4#forward
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L294-L295
DISPOSITION: NODE lp3:s2.4#forward
REASON: ANCHORS: LP3-1; SLICE: LP3-b; apply the imported theorem: drift <= r/2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.4#backward
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L296-L300
DISPOSITION: NODE lp3:s2.4#backward
REASON: ANCHORS: LP3-1; SLICE: LP3-b; reversed curve with (-h, -P)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.4#uniformity
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.4@L302-L303
DISPOSITION: NODE lp3:s2.4#uniformity
REASON: ANCHORS: LP3-1; SLICE: LP3-b; constants depend only on (n, nu, A, delta)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s2.5
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.5@L305-L328
DISPOSITION: NODE lp3:s2.5
REASON: ANCHORS: LP3-2; SLICE: LP3-b; spatial version (k = 2n): slow ball, extension, chart Hamiltonian, lift, erosion constant; MAIN L17/L18
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s3#sublevel
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s3@L333-L351
DISPOSITION: NODE lp3:s3#sublevel
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-b; no AMDBox; why D may be the sharp ball; ordered levels with fixed gaps (MAIN L5, L8)
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s3#first-exit
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s3@L352-L362
DISPOSITION: NODE lp3:s3#first-exit
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-b; application of MAIN L14 with r = (B_0 mu)^{b_n} and hstop from §2.4
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s3#assembly
KIND: proof-region
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s3@L363-L370
DISPOSITION: NODE lp3:s3#assembly
REASON: ANCHORS: LP3-1,LP3-2; SLICE: LP3-b; assembly as in T15/T19 with the drift supplier swapped; A_Lambda = B_0^{b_n}/2
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s4
KIND: claim
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s4@L373-L422
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP3-b; provider chain and import policy (D58, OD-13); governance
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s5
KIND: claim
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s5@L424-L462
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP3-b; Lean package list; planning
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s6
KIND: claim
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s6@L464-L489
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP3-b; risk register; its mathematical content is in §2-§3
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -

ITEM: lp3:s7
KIND: claim
SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s7@L491-L506
DISPOSITION: EXCLUDED
REASON: ANCHORS: none; SLICE: LP3-b; sketch remarks and errata candidates (A4); errata ledger, not graph
COVERAGE_STATUS: PROPOSED
EXTRACTOR: lp-preanchor-inventory
REVIEWER: -
