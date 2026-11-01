Audited HEAD: 5ba2f8b2a66c9207991e38b939b89b7c1ce7b0e2
Branch: inp-lp-graph
Reviewer: sol-review-LP-LP-m2a
Slice verdict: FAIL

Topology review only. All 24 nodes, 77 original edges and 36 inventory items were checked against MAIN L94–L160, MAIN §1 L11–L55, and AMENDMENTS L1–L26. Cross-slice consumers were checked at MAIN L164–L189 and L502–L525, with LP-m1, LP-m2b, LP-ext, the relevant LP-adef-pl definition records and the two LP-athm L3 characterization records. Manifest identity fields and anchor-binding.tsv identify the referenced anchors; no Lean declarations or proof bodies were read. No deferred items exist in this slice.

The ten failed node records are replaced in full below. The coverage dispositions remain correct even when their target node requires repair; passing a coverage item does not pass that node.

## Required hard rules (verbatim)

1. Never use set_option maxHeartbeats (or any heartbeat-budget override). A default-heartbeat elaboration failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules, preserving public import paths as cheap facades.

## Node verdicts

| Node | Verdict | Source spans re-read or failure |
| --- | --- | --- |
| lpM:L1 | PASS | MAIN L1@L99-L99; L1@L101-L108; §1 L11–L55 |
| lpM:L1#reduction | PASS | MAIN L1@L101-L102; L1@L101-L102; §1 L11–L55 |
| lpM:L1#velocity | PASS | MAIN L1@L105-L107; L1@L104-L107; §1 L11–L55 |
| lpM:L1#reconstruction | PASS | MAIN L1@L104-L108; L1@L104-L108; §1 L11–L55 |
| lpM:L2 | PASS | MAIN L2@L112-L122; L2@L124-L128; §1 L11–L55 |
| lpM:L2#ecc-identity | PASS | MAIN L2@L113-L115; L2@L124-L124; §1 L11–L55 |
| lpM:L2#radial-bounds | PASS | MAIN L2@L118-L121; L2@L124-L128; §1 L11–L55 |
| lpM:L3 | FAIL | Missing direct eccDeficit symbol edge for D in (13) (SPEC §5). |
| lpM:L3#static | PASS | MAIN L3@L132-L137; L3@L139-L139; §1 L11–L55 |
| lpM:L3#dynamic | PASS | MAIN L3@L132-L135; L3@L139-L139; §1 L11–L55 |
| lpM:L3#conservation | PASS | MAIN L3@L132-L132; L3@L139-L139; §1 L11–L55 |
| lpM:L3#amd-nonneg | PASS | MAIN L3@L132-L132; L3@L139-L139; §1 L11–L55 |
| lpM:L3#L-nonzero | PASS | MAIN L3@L132-L132; L3@L139-L139; §1 L11–L55 |
| lpM:L3#projections | FAIL | The L-nonzero dependency requires C < B_⋆, absent from this general L ≠ 0 step; remove that unnecessary conditional edge. |
| lpM:L3#deficit | PASS | MAIN L3@L133-L135; L3@L139-L139; §1 L11–L55 |
| lpM:L3#deficit-zero-L | PASS | MAIN L3@L133-L135; L3@L139-L139; §1 L11–L55 |
| lpM:L3#planar-orientation | FAIL | Missing direct supplier of L ≠ 0 for the projection step and the orientation choice; add L-nonzero. |
| lpM:L4 | FAIL | Missing inherited n ≥ 2 premise/data edge. |
| lpM:L4#feasible-compact | FAIL | Missing inherited n ≥ 2 premise/data edge. |
| lpM:L4#contact-reduction | FAIL | Missing inherited n ≥ 2 premise/data edge; missing direct chamber/actionAxis edges. |
| lpM:L4#contact-param | FAIL | Missing inherited n ≥ 2 premise/data edge; missing direct chamber/actionAxis, orderedPairThreshold edges. |
| lpM:L4#continuity | FAIL | Missing inherited n ≥ 2 premise/data edge; missing direct pairObjective edges. |
| lpM:L4#positivity | FAIL | Missing inherited n ≥ 2 premise/data edge; missing direct chamber/actionAxis, orderedPairThreshold, orderedCrossThreshold/pairObjective edges. |
| lpM:L4#competitor | FAIL | Missing inherited n ≥ 2 premise/data edge; missing direct chamber/actionAxis edges. |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |
| lpM:h:s2 | PASS | MAIN s2@L95-L95; Q3/Q4 and N9 where applicable |
| lpM:L1 | PASS | MAIN L1@L97-L108; Q3/Q4 and N9 where applicable |
| lpM:L1#reduction | PASS | MAIN L1@L101-L102; Q3/Q4 and N9 where applicable |
| lpM:L1#reconstruction | PASS | MAIN L1@L104-L108; Q3/Q4 and N9 where applicable |
| lpM:eq10 | PASS | MAIN L1@L105-L107; Q3/Q4 and N9 where applicable |
| lpM:L2 | PASS | MAIN L2@L110-L128; Q3/Q4 and N9 where applicable |
| lpM:eq11 | PASS | MAIN L2@L113-L116; Q3/Q4 and N9 where applicable |
| lpM:eq12 | PASS | MAIN L2@L118-L121; Q3/Q4 and N9 where applicable |
| lpM:L2#ecc-identity | PASS | MAIN L2@L124-L124; Q3/Q4 and N9 where applicable |
| lpM:L2#radial-bounds | PASS | MAIN L2@L124-L128; Q3/Q4 and N9 where applicable |
| lpM:L3 | PASS | MAIN L3@L130-L139; Q3/Q4 and N9 where applicable |
| lpM:eq13 | PASS | MAIN L3@L133-L136; Q3/Q4 and N9 where applicable |
| lpM:L3#planar-orientation | PASS | MAIN L3@L137-L137; Q3/Q4 and N9 where applicable |
| lpM:L3#conservation | PASS | MAIN L3@L139-L139; Q3/Q4 and N9 where applicable |
| lpM:L3#amd-nonneg | PASS | MAIN L3@L139-L139; Q3/Q4 and N9 where applicable |
| lpM:L3#L-nonzero | PASS | MAIN L3@L139-L139; Q3/Q4 and N9 where applicable |
| lpM:L3#projections | PASS | MAIN L3@L139-L139; Q3/Q4 and N9 where applicable |
| lpM:L3#deficit | PASS | MAIN L3@L139-L139; Q3/Q4 and N9 where applicable |
| lpM:L3#ext-ftc | PASS | MAIN L3@L139-L139; Q3/Q4 and N9 where applicable |
| lpM:L4 | PASS | MAIN L4@L141-L160; Q3/Q4 and N9 where applicable |
| lpM:eq14 | PASS | MAIN L4@L144-L146; Q3/Q4 and N9 where applicable |
| lpM:L4#feasible-compact | PASS | MAIN L4@L149-L149; Q3/Q4 and N9 where applicable |
| lpM:L4#contact-reduction | PASS | MAIN L4@L149-L149; Q3/Q4 and N9 where applicable |
| lpM:L4#contact-param | PASS | MAIN L4@L149-L153; Q3/Q4 and N9 where applicable |
| lpM:eq15 | PASS | MAIN L4@L150-L153; Q3/Q4 and N9 where applicable |
| lpM:L4#continuity | PASS | MAIN L4@L154-L156; Q3/Q4 and N9 where applicable |
| lpM:L4#positivity | PASS | MAIN L4@L156-L156; Q3/Q4 and N9 where applicable |
| lpM:L4#competitor | PASS | MAIN L4@L156-L156; Q3/Q4 and N9 where applicable |
| lpM:L4#sharpness | PASS | MAIN L4@L158-L158; Q3/Q4 and N9 where applicable |
| lpM:L4#lp-identification | PASS | MAIN L4@L160-L160; Q3/Q4 and N9 where applicable |
| lpM:L4#cite-laskar-petit | PASS | MAIN L4@L160-L160; Q3/Q4 and N9 where applicable |
| lpM:L4#ext-extreme-value | PASS | MAIN L4@L149-L149; Q3/Q4 and N9 where applicable |
| lpM:L4#ext-unif-cont | PASS | MAIN L4@L154-L154; Q3/Q4 and N9 where applicable |
| lpM:L4#stmt-contact-lp | PASS | MAIN L4@L143-L143; Q3/Q4 and N9 where applicable |
| lpM:L4#stmt-sharpness | PASS | MAIN L4@L147-L147; Q3/Q4 and N9 where applicable |
| lpM:L3#deficit-zero-L | PASS | MAIN L3@L133-L135; Q3/Q4 and N9 where applicable |

## Findings and scope

1. Q3: static, dynamic and planar-orientation records together preserve Lemma 3. Lemma 5 uses only the static supplier; its strict-threshold premise is supplied by C ≤ B − m < B ≤ B_⋆ (MAIN L166). Conservation explicitly consumes (10), the model forces and FTC at L139. The general nonzero-L projection argument does not use the strict-threshold implication to obtain a fact already stipulated by its local case. Its two positivity consequences remain conditional. The orientation consumer must therefore cite L-nonzero directly to supply the projection step’s L ≠ 0 premise.
2. The deficit-zero-L SOURCE_GAP is correctly exposed. MAIN L139 argues through L̂ and H_i after obtaining L ≠ 0; it never treats L = 0 for the unrestricted deficit characterization. Keep the gap and its coverage item. The LP-athm characterization cites both nonzero and zero cases; this audit does not certify its Lean statement or prove the missing case.
3. Q4: the contact/Laskar–Petit clauses at L143 and sharpness at L147 have no downstream consumer in the prescribed closure; the exclusions of L158 (N9) and L160 are justified. The contact reduction and parameterization remain necessary proof steps for continuity. No edge to the excluded geometric-realization paragraph or the external Laskar–Petit paper is warranted.
4. Lemma 4 has the inherited n ≥ 2 scope of MAIN §1 L11. Positivity of B_cross and B and the finite adjacent minima are not statements for n = 0 or 1. This premise is absent from all seven L4 records and must be explicit, with its data edge. Missing direct dimension-free symbol edges cannot be discharged merely by transitive reachability through another record. Added edges below point to the corresponding consumer proof region.
5. The independent (10) node correctly separates actual velocity q̇_i from canonical p_i/ν_i. The reconstruction uses it at L105–L108; the recoil cancellation uses it at L139; the osculating definition at L510 uses the same formula. Dimension-specific frozen phase, cross-product and orbital-element anchors are not demanded on these d-generic nodes.
6. The compact-minimum and Heine–Cantor hypotheses are supplied by the closed nonempty feasible subset of [0,1]² and compact neighborhoods times [0,1], respectively. FTC is applied after the torque computation. No additional external is needed for these elementary algebraic and finite-minimum steps. Constants in this slice have no extra parameter dependence.

## Complete replacement fragments

```text
NODE: lpM:L3
KIND: lemma
TITLE: Lemma 3: exact angular momentum and the AMD identity (static and dynamic parts)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L137
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model (1) with its data (n, ν, d, μ > 0); m > 0 in the last clause
SOURCE_QUANTIFIERS: for every solution of (1) on a connected interval of existence, every negative-energy state, and m > 0
SOURCE_CONCLUSION: L is constant on every connected interval of existence of (1); C ≥ 0 in the negative-energy region; if C < B_⋆(I) then L ≠ 0 and all H_i = L_i·L̂ are positive, and on such an orbit C(t) - C(0) = Σ_i(I_i(t) - I_i(0)) and C = Σ_i(I_i - H_i) ≥ Σ_i I_i D(e_i) (13); if C ≤ B_⋆(I) - m then H_i ≥ m for every i; in the planar case, orienting the plane so that L > 0 makes all individual scalar angular momenta positive
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#static, lpM:L3#dynamic, lpM:L3#planar-orientation, lpM:s1:thresholds#eccDeficit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#static | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the static clauses: C ≥ 0, L ≠ 0, H_i > 0, H_i ≥ m and the inequality of (13)
EDGE: lpM:L3#dynamic | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the dynamic clauses: conservation of L and the identity of (13)
EDGE: lpM:L3#planar-orientation | docs/tracks/LP/source/MAIN.md#L3@L137-L137 | the planar orientation clause
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L3@L135-L135 | D occurs directly in the full statement of (13), independently of the conjunction edges
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Q3 split (ruling root-b8): the conjunction of lpM:L3#static (consumed by Lemma 5, hence LP0, which thus does not reach Lemma 1) and lpM:L3#dynamic (consumed by Lemma 6 and the dynamic anchors)
```

```text
NODE: lpM:L3#projections
KIND: step
TITLE: 0 <= I_i - H_i, sum = C, so H_i >= I_i - C (> 0, >= m)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L137
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#projections
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: negative-energy state: ν_i > 0, q_i ≠ 0 and E_i < 0 for every i, d ∈ {2,3}; local nonzero-L case: L ≠ 0; local definitions L̂ = L/¦L¦ and H_i = L_i·L̂; m > 0 for the margin implication
SOURCE_QUANTIFIERS: for every such negative-energy state with L ≠ 0 and every m > 0
SOURCE_CONCLUSION: H_i ≤ ¦L_i¦ ≤ I_i, so every I_i - H_i ≥ 0, and Σ_i (I_i - H_i) = C; hence H_i ≥ I_i - C ≥ B_⋆(I) - C, so H_i > 0 when C < B_⋆(I) and H_i ≥ m when C ≤ B_⋆(I) - m
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | ¦L_i¦ ≤ I_i by (11)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | Σ_i H_i = ¦L¦ and C = Σ I_i - ¦L¦
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The local L ≠ 0 case is explicit, as needed by the nonzero-L deficit argument. The C < B_⋆ and C ≤ B_⋆ - m clauses are conditional conclusions. Do not apply lpM:L3#L-nonzero here: its premise C < B_⋆ is absent in the general nonzero-L case; lpM:L3#static obtains L ≠ 0 separately before using this step.
```

```text
NODE: lpM:L4
KIND: lemma
TITLE: Lemma 4: attained, positive, continuous thresholds and (14)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L146
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L156
CONTRACT_ID: lpM:L4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); ν_i > 0 for every i ('all positive masses'); I ∈ Q
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0 and I ∈ Q (each pair i < j)
SOURCE_CONCLUSION: every minimum in (3) is attained and positive; each B_ij and B is continuous on Q; B_ij(I) < I_j and B(I) = min(B_cross(I), I_1) (14)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#feasible-compact, lpM:L4#continuity, lpM:L4#positivity, lpM:L4#competitor, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#feasible-compact | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the pair minima are attained
EDGE: lpM:L4#continuity | docs/tracks/LP/source/MAIN.md#L4@L154-L156 | continuity of B_ij and B
EDGE: lpM:L4#positivity | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | positivity of the minima
EDGE: lpM:L4#competitor | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | the competitor proves (14)
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L143-L143 | I ∈ Q
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L4@L143-L143 | B_ij occurs
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#L4@L145-L145 | B_cross occurs in (14)
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L4@L143-L143 | B occurs
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L143-L143 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Q4 split (ruling root-b8): the statement clauses on radial contact and the Laskar-Petit identification (L143) and on geometric sharpness (L147) are not part of this record; no proof consumes them (N9). Their items lpM:L4#stmt-contact-lp and lpM:L4#stmt-sharpness and the supporting prose L158 and L160 are EXCLUDED
```

```text
NODE: lpM:L4#feasible-compact
KIND: step
TITLE: the feasible set is closed and nonempty and the objective continuous: minimum attained
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
CONTRACT_ID: lpM:L4#feasible-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4)
SOURCE_CONCLUSION: the feasible subset of [0,1]^2 is closed and nonempty, since (0, 1 - α) is feasible, and the objective I_i D(u) + I_j D(v) is continuous, so the pair minimum is attained
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#actionAxis, lpM:s1:chamber#chamber, lpM:ext-compact-min, lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the feasible set
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the objective
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | continuity of D on [0,1]
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | α = a_i(I)/a_j(I)
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | I ∈ Q gives α < 1
EDGE: lpM:ext-compact-min | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | a continuous function on a nonempty compact set attains its minimum
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: lpM:L4#contact-reduction
KIND: step
TITLE: scaling a feasible point to contact does not increase the objective
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
CONTRACT_ID: lpM:L4#contact-reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4); for every feasible (u,v)
SOURCE_CONCLUSION: replacing (u,v) by t(u,v) with t = (1 - α)/(αu + v) ≤ 1 gives contact a_i(1 + tu) = a_j(1 - tv) and does not increase the objective
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#eccDeficit, lpM:s1:data, lpM:s1:chamber#chamber, lpM:s1:thresholds#actionAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | feasibility and contact
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the objective
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | D is nondecreasing on [0,1]
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | I ∈ Q is a direct carrier premise
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the local ratio α = a_i(I)/a_j(I) directly uses the action-axis formula
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: lpM:L4#contact-param
KIND: step
TITLE: (15): contact parameterized over t in [0,1]
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L150-L153
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L153
CONTRACT_ID: lpM:L4#contact-param
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4); t ∈ [0,1]
SOURCE_CONCLUSION: with m(α) = min(1, (1 - α)/α), u = m(α)t, v = 1 - α - αm(α)t (15) parameterizes the contact set over the fixed interval [0,1], so B_ij(I) = min_{t ∈ [0,1]} F(I,t) with F the objective along (15)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#contact-reduction, lpM:s1:thresholds#pairObjective, lpM:s1:data, lpM:s1:chamber#chamber, lpM:s1:thresholds#actionAxis, lpM:s1:thresholds#orderedPairThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#contact-reduction | docs/tracks/LP/source/MAIN.md#L4@L149-L149 | the minimum is attained on the contact set
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L151-L151 | F is the objective along (15)
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | I ∈ Q is a direct carrier premise
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the local ratio α = a_i(I)/a_j(I) directly uses the action-axis formula
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the conclusion directly identifies or bounds B_ij(I)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: lpM:L4#continuity
KIND: step
TITLE: continuity of B_ij and B on Q via uniform continuity on compact neighborhoods
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L154-L156
CONTRACT_ID: lpM:L4#continuity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0 and every I, J ∈ Q
SOURCE_CONCLUSION: the objective in (15) is jointly continuous in (I,t), hence uniformly continuous on K × [0,1] for every compact neighborhood K ⊂ Q; ¦min_t F(I,t) - min_t F(J,t)¦ ≤ sup_t ¦F(I,t) - F(J,t)¦ proves continuity of B_ij on Q; finite minima preserve continuity, so B_cross and B are continuous
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#contact-param, lpM:ext-heine-cantor, lpM:ext-compact-min, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:data, lpM:s1:thresholds#pairObjective
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#contact-param | docs/tracks/LP/source/MAIN.md#L4@L154-L154 | B_ij is the minimum over t of the objective in (15)
EDGE: lpM:ext-heine-cantor | docs/tracks/LP/source/MAIN.md#L4@L154-L154 | uniform continuity on compact sets
EDGE: lpM:ext-compact-min | docs/tracks/LP/source/MAIN.md#L4@L155-L155 | the minima over t ∈ [0,1] are attained
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L154-L154 | compact neighborhoods inside the open chamber Q
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L4@L155-L155 | continuity of B_ij
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | finite minimum B_cross
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | finite minimum B
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L154-L156 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L154-L154 | joint continuity is asserted directly for the objective composed with (15)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: lpM:L4#positivity
KIND: step
TITLE: a zero minimum cannot give contact; finite minima stay positive
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L143-L143
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L156-L156
CONTRACT_ID: lpM:L4#positivity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4)
SOURCE_CONCLUSION: a zero minimum would require u = v = 0, which is not feasible because α < 1; so B_ij(I) > 0, and the finite minima B_cross(I), B(I) are positive (I_i > 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#feasible-compact, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:data, lpM:s1:chamber#chamber, lpM:s1:thresholds#actionAxis, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#pairObjective
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#feasible-compact | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | the minimum is attained at a feasible point
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | D(u) = 0 only at u = 0
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | (0,0) is not feasible when α < 1
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B is a finite minimum of positive numbers
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | I ∈ Q is a direct carrier premise
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the local ratio α = a_i(I)/a_j(I) directly uses the action-axis formula
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the conclusion directly identifies or bounds B_ij(I)
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B_cross(I) is directly asserted positive as a finite minimum
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | a zero value of I_i D(u) + I_j D(v) forces u = v = 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: lpM:L4#competitor
KIND: step
TITLE: competitor (0, 1 - alpha): B_ij <= I_j D(1 - alpha) < I_j, proving (14)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L144-L146
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L156-L156
CONTRACT_ID: lpM:L4#competitor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (MAIN §1 L11); context of the proof of lpM:L4: ν_i > 0 for every i; I ∈ Q; i < j; local data: α = a_i(I)/a_j(I) ∈ (0,1)
SOURCE_QUANTIFIERS: for every n ≥ 2; for every ν > 0, I ∈ Q and pair i < j (inherited from lpM:L4)
SOURCE_CONCLUSION: the feasible competitor (0, 1 - α) gives B_ij(I) ≤ I_j D(1 - α) < I_j; since B_{i,i+1}(I) < I_{i+1}, B(I) = min(B_cross(I), I_1) (14)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4#feasible-compact, lpM:s1:thresholds#pairObjective, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedCrossThreshold, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:data, lpM:s1:chamber#chamber, lpM:s1:thresholds#actionAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4#feasible-compact | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | (0, 1 - α) is feasible
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | the objective at the competitor is I_j D(1 - α)
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | D(1 - α) < 1 for 0 < α
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B_ij
EDGE: lpM:s1:thresholds#orderedCrossThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B_cross in (14)
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L4@L156-L156 | B in (14)
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the inherited n ≥ 2 and positive-mass data; only this part of the data package is assumed
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | I ∈ Q is a direct carrier premise
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L4@L149-L156 | the local ratio α = a_i(I)/a_j(I) directly uses the action-axis formula
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: lpM:L3#planar-orientation
KIND: claim
TITLE: planar case: orient so that L > 0; all scalar L_i are then positive
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L137-L137
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L137-L137
CONTRACT_ID: lpM:L3#planar-orientation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d = 2; a negative-energy state with C < B_⋆(I)
SOURCE_QUANTIFIERS: for every such planar state
SOURCE_CONCLUSION: choosing the plane's orientation so that L > 0, every individual scalar angular momentum L_i is positive
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#projections, lpM:L3#L-nonzero
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#projections | docs/tracks/LP/source/MAIN.md#L3@L137-L137 | in the plane H_i = L_i·sign(L) > 0
EDGE: lpM:L3#L-nonzero | docs/tracks/LP/source/MAIN.md#L3@L137-L137 | C < B_⋆ supplies L ≠ 0 before applying the projection step and choosing an orientation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: consumed by Theorem 15's orientation step (wave 2; N8, OD-1)
```

## Suspected defects of the source

- MAIN L135/L139: “relative to the unit vector” and “Finally H_i … proves the inequality in (13)”. This proves the deficit inequality through a nonzero-L construction. The unrestricted characterization also covers L = 0; MAIN gives no argument for that case. This is the already exposed source gap, not a claimed false inequality. Keep lpM:L3#deficit-zero-L as SOURCE_GAP; no mathematics is supplied here.
- MAIN L143–L156: “For all positive masses and I ∈ Q” relies on the n ≥ 2 scope fixed at MAIN L11. No new source erratum is alleged: the omission is in the graph records. The N9 exclusion is respected. No other suspected source defect or introduced mathematical deviation was found.

## Checks and limits

- Audited starting HEAD: inp-lp-graph; 5ba2f8b2a66c9207991e38b939b89b7c1ce7b0e2. A concurrent commit moved HEAD to 3ee7b4480fb27797643d618460bbc206225c40b5 (`LP: LP-GRAPH-W2 brief`). Read-only `git diff --name-only` between these commits over AGENTS.md, PLAN, DECISIONS, LP SPEC, REVIEW-BRIEF, packets, MAIN, AMENDMENTS and the manifest returned no paths. Thus the audited inputs are unchanged; the first-line audit revision remains the starting HEAD.
- `python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/LP/packets LP-m2a --root .`: `LP-m2a: 24 nodes, 77 edges, 36 coverage items, 0 problems` (exit 0). This checks the original packet structure, not the proposed replacements or mathematical fidelity.
- `sha256sum -c docs/graph/LP/CORPUS.sha256`: MAIN.md OK; AMENDMENTS.md OK (exit 0).
- In-memory review validation: 24 node verdicts (14 PASS, 10 FAIL), 36 coverage PASS, 10 complete replacement blocks; original field sets preserved; DEPS/EDGE agreement; locator bounds valid; no unknown dependency or cycle in the proposed closure. No packets were changed.
- Only this review file was written. No Lean, Lake, build, source lint, axiom inspection or state-changing git command was run. Source lint/build/axiom outputs are inapplicable to this report-only assignment and expressly excluded by the brief.
