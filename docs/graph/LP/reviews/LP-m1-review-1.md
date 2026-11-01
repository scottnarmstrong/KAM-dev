Audited HEAD: 5ba2f8b2a66c9207991e38b939b89b7c1ce7b0e2
Branch: inp-lp-graph
Reviewer: sol-review-LP-LP-m1
Slice: LP-m1

# Verdict: FAIL

One locator defect: `lpM:s1:model` includes the physical angular-momentum/AMD normalization, normalized margin and central-parameter convention of MAIN L39, but its STATEMENT_SOURCE ends at L24. REVIEW-BRIEF checklist 5 requires that the statement locator cover the source text represented by the node. The complete replacement below extends the range through L39, preserving the statement, dependencies and identity fields. The intervening element definitions remain owned by `lpM:s1:elements`; widening the source span does not transfer their ownership.

The six nodes and eight edges otherwise pass source/topology review. All 19 coverage dispositions pass, and all six deferrals are justified. A coverage PASS accepts the item's source span and disposition; it does not overturn the target node's locator FAIL. This is source-topology evidence, without Lean proof or implementation certification.

# Node table

| Node | Verdict | Source spans re-read or reason |
| --- | --- | --- |
| lpM:s1:data | PASS | MAIN L11–L15: definition of the fixed hypothesis package, including empty A and both norms; no standing assumption. |
| lpM:s1:model | FAIL | STATEMENT_SOURCE L17–L24 omits MAIN L39, whose normalization assertions occur in SOURCE_CONCLUSION; extend through L39. |
| lpM:s1:elements | PASS | MAIN L26–L37 and AMENDMENTS L17 (N8): d-generic canonical elements; negative-energy guard, scalar planar cross product, orientation-free C. |
| lpM:s1:fast | PASS | MAIN L45, L57–L61: positive-action formula (4); direct actionAxis edge at L60. |
| lpM:s1:dioph | PASS | MAIN L62–L67, with frequencies L57–L61 and data L11–L15: nonzero integer k, gamma/tau, radian convention. |
| lpM:s1:half-integer | PASS | MAIN L75–L77 and L93, with L15: tau = n - 1/2 is admissible and gives the stated arithmetic exponent. |

# Coverage table

| Item | Verdict | Source spans re-read or reason |
| --- | --- | --- |
| lpM:h:title | PASS | MAIN L1–L3: title/date; administrative exclusion. |
| lpM:intro#result | PASS | MAIN L5 and L69–L93; T15 L504–L506 and T19 L601–L603: overview repeated by the conclusions; no separate obligation. |
| lpM:intro#method | PASS | MAIN L7: method overview and future engine choice, without an independent estimate or construction. |
| lpM:h:s1 | PASS | MAIN L9: section heading. |
| lpM:s1:data | PASS | MAIN L11–L15: correct package node; LP0 uses its n/nu portion. |
| lpM:s1:model | PASS | MAIN L17–L24: correct definition target; target node's separate locator repair is required above. |
| lpM:eq1 | PASS | MAIN L18–L23: full Hamiltonian and perturbation belong to model. |
| lpM:s1:elements | PASS | MAIN L26–L37: correct d-generic definition target, with dimension-specific realization at the anchors. |
| lpM:eq2 | PASS | MAIN L32–L36 and AMENDMENTS L17: generic elements plus the planar strongAMD anchor faithfully cover the display. |
| lpM:s1:elements#elliptic-remark | PASS | MAIN L37 and L164–L175: e_i < 1 is a consequence of L5's positive perihelion estimate (16), not an added premise. |
| lpM:s1:model#normalization | PASS | MAIN L39: correct assignment to model; the item's own source locator is correct. |
| lpM:s1:chamber | PASS | MAIN L41–L44 and L55: chamber and OrderedActions anchors represent the set and carrier. |
| lpM:s1:thresholds | PASS | MAIN L45–L55 and L143–L156: threshold anchors cover formulas and carriers; attainment/continuity are L4 results, and L55 is a forward pointer. |
| lpM:eq3 | PASS | MAIN L46–L54: feasible set, objective, pair and adjacent minima, and inline B_star are covered by the listed anchors. |
| lpM:s1:fast | PASS | MAIN L57–L61: fast Hamiltonian and frequencies belong to fast. |
| lpM:eq4 | PASS | MAIN L58–L61: display (4) belongs to fast. |
| lpM:s1:dioph | PASS | MAIN L62–L67: condition (5) and period convention belong to dioph. |
| lpM:eq5 | PASS | MAIN L63–L66: quantified condition belongs to dioph. |
| lpM:s1:half-integer | PASS | MAIN L93 with L76: arithmetic specialization belongs to half-integer. |

# Deferred coverage table

| Item | Verdict | Source spans re-read and justification |
| --- | --- | --- |
| lpM:s1:conclusion | DEFER-OK | MAIN L69–L91, T15 L504–L506, T19 L601–L603, L16 L510–L529 and N10: combined existence, uniqueness, drift, safety, physical and osculating conclusions belong to the later headline results. |
| lpM:eq6 | DEFER-OK | MAIN L71–L73: hypotheses of T15/T19, including the initial AMD margin and arithmetic condition; no wave-1 node states these headline implications. |
| lpM:eq7 | DEFER-OK | MAIN L75–L77: exponential existence horizon belongs to T15/T19; half-integer supplies only its arithmetic specialization. |
| lpM:eq8 | DEFER-OK | MAIN L79–L86: time-dependent drift and moving-margin bounds belong to T15/T19, beyond the static barrier and local continuation of wave 1. |
| lpM:eq9 | DEFER-OK | MAIN L87–L90 with L69–L78: bounds throughout the exponential interval belong to T15/T19; L5 alone supplies static separation under its own premises. |
| lpM:s1:no-crossing | DEFER-OK | MAIN L93 and L91, with L16 L510–L529/N10: interpretation of the complete canonical and actual-velocity conclusions, including all phases and allowed secular states, belongs to T15/T19. |

The literal deferred DISPOSITION values are the ordinary MAIN nodes `lpM:T15,lpM:T19`, not their `#...` anchor IDs as the boilerplate REASON says. SPEC §1.1 explicitly retains those ordinary theorem nodes for waves 2/3. Thus the actual destinations are valid later-wave owners under §9 and do not require substitution by a wave-1 node. The writer should align that explanatory wording when activating the items. No deferral is permission to omit the osculating half-gaps, initial-collision consequence, ellipticity, chamber membership, maximal-solution interval, or constant quantifier order in the later theorem records.

# Refutation checks

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, REVIEW-BRIEF.md in full, SPEC.md in full, MAIN L1–L93 and all 26 AMENDMENTS lines. Re-read the cross-slice threshold records in LP-adef-pl, the strongAMD record, the L5 perihelion record in LP-m2b and their cited MAIN text. T15/T19 and L16 source statements/proofs were read only as raw MAIN text to check the deferrals. No Lean files or proof bodies were read.

The eight direct edges are accounted for: model uses data at L17; elements uses model variables and dimension/Euclidean lengths at L28; fast uses masses at L59 and the dimension-free actionAxis at L60; dioph uses frequencies and fixed gamma/tau at L64; half-integer uses the admissibility constraint at L93. These are consumer locators. There is no forward edge from L55 to L4, no alternative-route conjunction, and no new external input.

The package is a definition with SOURCE_HYPOTHESES `none`, not a global axiom. Model and fast name the portions they consume. Elements retains the d-generic meaning in dimensions two and three and adds no planar frozen-carrier edges. Canonical velocity is p_i/nu_i; no actual-velocity osculating element is substituted. The orientation-free C convention follows N8/OD-1. The source E_i is the specific energy, not the reused frozen keplerEnergy = nu_i E_i.

The chamber, carrier and ten threshold/helper dispositions were checked against the rendered LP-adef-pl records and binding identities. B_star is inline in orderedStrongThreshold. Internal helpers have source meaning on their indicated carriers; minima are not promoted to mathematical characterization merely from a definition's codomain. MAIN L55 attainment/continuity is already supplied by L4; its forward reference does not create a definition cycle. No missing independent obligation was found in L1–L93 beyond those represented or deferred.

Manifest access was restricted to identity fields (id, path, export, contract, abi_sha256, source.range). Fifteen relevant binding rows were compared with those fields: the two chamber anchors, ten threshold/helper anchors, strongAMD, and the LP1/LP2 headline anchors. All matched; headline waves are 2 and 3. Frozen declaration audits belong to LP-adef-pl/LP-athm and were not performed here.

# Complete replacement fragment

Only the statement locator changes. This replacement remains PROPOSED for an independent delta review.

```text
NODE: lpM:s1:model
KIND: definition
TITLE: the exact model: units, masses, symplectic form, Hamiltonian (1), domain, time
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L17-L39
PROOF_SOURCE: -
CONTRACT_ID: lpM:s1:model
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of lpM:s1:data (n, ν, d); μ > 0
SOURCE_QUANTIFIERS: for every μ > 0
SOURCE_CONCLUSION: G = 1 and stellar mass 1; planet masses m_i = μν_i; heliocentric positions q_i and scaled canonical momenta p_i with symplectic form Σ_i dp_i ∧ dq_i and ι_{X_H}Ω = -dH; the exact Hamiltonian (1) H_μ = Σ_i(¦p_i¦^2/(2ν_i) - ν_i/¦q_i¦) + μ f, f = ¦Σ_i p_i¦^2/2 - Σ_{i<j} ν_iν_j/¦q_i - q_j¦, on the open domain q_i ≠ 0, q_i ≠ q_j; solutions use physical time; physical angular momentum and AMD are μL and μC, so δ is a normalized margin; the splitting (1) uses central Kepler parameter one (L39)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L17-L17 | the data ν, n, d and the Euclidean length ¦·¦ enter (1)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

# Checks and scope

- `git rev-parse HEAD`: `5ba2f8b2a66c9207991e38b939b89b7c1ce7b0e2`.
- `git branch --show-current`: `inp-lp-graph`.
- `sha256sum -c docs/graph/LP/CORPUS.sha256`: MAIN.md OK; AMENDMENTS.md OK; exit 0.
- `python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/LP/packets LP-m1 --root .`: `LP-m1: 6 nodes, 8 edges, 19 coverage items, 0 problems`; exit 0. This checks the original packet structurally and does not detect the semantic locator omission.
- Identity-only comparison: 15 relevant binding identities matched; no manifest state queried.
- Report validation: all 6 node, 19 coverage and 6 deferred rows occur exactly once in their respective tables; the complete replacement differs from the original only in STATEMENT_SOURCE.
- Final read-only HEAD check returned `3ee7b4480fb27797643d618460bbc206225c40b5`, reflecting concurrent work. `git diff --name-only 5ba2f8b2a66c9207991e38b939b89b7c1ce7b0e2 3ee7b4480fb27797643d618460bbc206225c40b5` listed only `docs/tracks/LP/packages/LP-GRAPH-W2.md`; the scoped diff of all reviewed inputs was empty. The audited HEAD on the first line remains the initial snapshot; reviewed inputs are identical at the final checked HEAD.

Only this review file was written. No packet, manifest, frozen file or source was edited; no Lean, Lake, build, state-changing git, or source-lint run was performed, as required by the review-specific instructions. Axiom inspection is outside this source-only assignment. The proposed locator repair has not been applied to the packet.

# Suspected defects of the source

None newly identified in MAIN L1–L93 as amended. N8 and N10 are the existing normative convention/constant amendments; they are not fresh errata raised by this review. The defect above is in the graph transcription's source locator, not in the pinned mathematical source. No source or contract deviation is proposed.

# Lean hard rules (verbatim)

1. Never use set_option maxHeartbeats (or any heartbeat-budget override). A default-heartbeat elaboration failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules, preserving public import paths as cheap facades.
