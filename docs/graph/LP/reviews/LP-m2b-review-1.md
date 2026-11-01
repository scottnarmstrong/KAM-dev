Audited HEAD: 5ba2f8b2a66c9207991e38b939b89b7c1ce7b0e2
Branch: inp-lp-graph
Reviewer: sol-review-LP-LP-m2b
Slice: LP-m2b
Verdict: FAIL

Reviewed the rendered 15 nodes, all 64 edges and all 20 coverage items against MAIN L161-L189 and the full normative AMENDMENTS, with cross-slice suppliers read at their uses. No deferred file exists for this slice. Coverage PASS below accepts the inventory disposition, independently of whether its target node needs correction. No node or coverage item is deleted or added.

The material failures concern source contracts and direct symbol edges. N2's requirements cannot live only in NOTE while SOURCE_QUANTIFIERS still says “every r > 0”. In particular, shared-U must choose U before it quantifies over a trajectory lying in U. The replacement keeps Lemma 6 generic in 𝓛 and records its later specialization 𝓛 = 𝓛_δ; it does not make Lemma 6 depend backwards on Lemma 8 or 14. N2 supplies the shared choice, with the δ/16 requirement explicitly read at MAIN L257. Continuation in either time direction retains the conditional smallness test.

Lemma 5's constants remain before all states/lists and depend only on (n, ν, U, m). The independent list quantifier needs its own I ∈ U, and its axes are the dimension-free actionAxis. The nonpositive-gap contradiction directly uses both the eccentricity deficit and the pair objective, even though a transitive path already reaches their definitions.

Conditional-premise checks: L5 gap-positive uses only L3#static, with C ≤ B(I) - m < B(I) ≤ B_⋆(I). Km-compact uses that same implication to place states in K_m. Projection uses C ≤ B_⋆ - m. L6 local-existence explicitly obtains C ≤ B(I) - δ/2 from (17) and nr + Ω_B(r) ≤ δ/2, then applies L5 with m = δ/2 and the same U. L4's continuity supplies K_m closedness and the common modulus. No dynamic L3 edge is needed in L5; L6 moving-threshold uses L3#dynamic. N11 is respected: perihelion defines d_⋆ before bounds uses it in the momentum estimate, and compact-physical depends on those bounds. Physical distances are Euclidean; action tubes use the max norm; no planar carrier is imposed on a d-generic node.

Node verdicts:

| Node | Verdict | Source spans re-read / reason |
| --- | --- | --- |
| lpM:L5 | FAIL | Missing direct actionAxis edge for the independent list clause; spell out I ∈ U and constants before both independent universals. |
| lpM:L5#gap-positive | FAIL | Missing direct eccDeficit and pairObjective edges in the feasible-pair cost comparison (SPEC §5). |
| lpM:L5#Km-compact | PASS | MAIN L164-L170; L3 L132-L139; L4 L143-L154 |
| lpM:L5#empty-case | PASS | MAIN L164-L170 |
| lpM:L5#perihelion | PASS | MAIN L164-L175; AMENDMENTS N11 L20 |
| lpM:L5#bounds | PASS | MAIN L112-L128, L164-L175; AMENDMENTS N11 L20 |
| lpM:L5#pair-distances | PASS | MAIN L112-L128, L164-L175; §1 L91 |
| lpM:L5#compact-physical | PASS | MAIN L17-L37, L164-L175; AMENDMENTS N11 L20 |
| lpM:L5#projection | PASS | MAIN L132-L139, L164-L175; §1 L52-L53 |
| lpM:L6 | FAIL | N2 remains only in NOTE: source fields still allow arbitrary r > 0 and do not specify the common 4r_g tube and modulus. |
| lpM:L6#shared-U | FAIL | U occurs in solution hypotheses before its construction; witnesses are after r/solution, and the N2 shared tube/modulus requirements are absent from source fields. |
| lpM:L6#moving-threshold | FAIL | Inherited source scope omits N2 restriction r ≤ r_g and the prior shared U/r_g/modulus choice. |
| lpM:L6#local-existence | FAIL | Inherited N2 scope is absent; the direct B(I) application also lacks its dimension-free threshold edge. |
| lpM:L6#continuation | FAIL | Inherited N2 scope is absent; annotate the direct conditional L5 application with U, m = δ/2 and its supplied margin. |
| lpM:L6#backward | FAIL | Unqualified backward assertions drop nr + Ω_B(r) ≤ δ/2 required by the continuation supplier; N2 scope is also absent. |

Coverage verdicts:

| Item | Verdict | Source spans re-read |
| --- | --- | --- |
| lpM:L5 | PASS | docs/tracks/LP/source/MAIN.md#L5@L162-L175; AMENDMENTS N11 L20 |
| lpM:L5#gap-positive | PASS | docs/tracks/LP/source/MAIN.md#L5@L166-L166; AMENDMENTS N11 L20 |
| lpM:L5#Km-compact | PASS | docs/tracks/LP/source/MAIN.md#L5@L166-L170; AMENDMENTS N11 L20 |
| lpM:L5#empty-case | PASS | docs/tracks/LP/source/MAIN.md#L5@L170-L170; AMENDMENTS N11 L20 |
| lpM:L5#perihelion | PASS | docs/tracks/LP/source/MAIN.md#L5@L170-L175; AMENDMENTS N11 L20 |
| lpM:eq16 | PASS | docs/tracks/LP/source/MAIN.md#L5@L171-L174; AMENDMENTS N11 L20 |
| lpM:L5#bounds | PASS | docs/tracks/LP/source/MAIN.md#L5@L175-L175; AMENDMENTS N11 L20 |
| lpM:L5#pair-distances | PASS | docs/tracks/LP/source/MAIN.md#L5@L175-L175; AMENDMENTS N11 L20 |
| lpM:L5#compact-physical | PASS | docs/tracks/LP/source/MAIN.md#L5@L175-L175; AMENDMENTS N11 L20 |
| lpM:L5#projection | PASS | docs/tracks/LP/source/MAIN.md#L5@L175-L175; AMENDMENTS N11 L20 |
| lpM:L5#ext-compact-min | PASS | docs/tracks/LP/source/MAIN.md#L5@L170-L170; AMENDMENTS N11 L20 |
| lpM:L6 | PASS | docs/tracks/LP/source/MAIN.md#L6@L177-L189; AMENDMENTS N2 L11 |
| lpM:eq17 | PASS | docs/tracks/LP/source/MAIN.md#L6@L184-L186; AMENDMENTS N2 L11 |
| lpM:L6#shared-U | PASS | docs/tracks/LP/source/MAIN.md#L6@L189-L189; AMENDMENTS N2 L11 |
| lpM:L6#moving-threshold | PASS | docs/tracks/LP/source/MAIN.md#L6@L189-L189; AMENDMENTS N2 L11 |
| lpM:L6#local-existence | PASS | docs/tracks/LP/source/MAIN.md#L6@L189-L189; AMENDMENTS N2 L11 |
| lpM:L6#continuation | PASS | docs/tracks/LP/source/MAIN.md#L6@L189-L189; AMENDMENTS N2 L11 |
| lpM:L6#backward | PASS | docs/tracks/LP/source/MAIN.md#L6@L189-L189; AMENDMENTS N2 L11 |
| lpM:L6#ext-picard | PASS | docs/tracks/LP/source/MAIN.md#L6@L189-L189; AMENDMENTS N2 L11 |
| lpM:L6#ext-gronwall | PASS | docs/tracks/LP/source/MAIN.md#L6@L189-L189; AMENDMENTS N2 L11 |

Complete replacement fragments (proposals only; original packets remain unchanged):

```text
NODE: lpM:L5
KIND: lemma
TITLE: Lemma 5: the uniform strong barrier (any dimension d)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L164-L164
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L166-L175
CONTRACT_ID: lpM:L5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 and ν_i > 0 (lpM:s1:data); U ⊂ Q compact; m > 0
SOURCE_QUANTIFIERS: for every n ≥ 2, positive ν, d ∈ {2,3}, compact U ⊂ Q and m > 0: there exist d_⋆ > 0 and d_pair > 0 before all states and lists; for every negative-energy state with I ∈ U and C ≤ B(I) - m the state clauses hold; independently, for every I ∈ U and e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m the same perihelion and gap bounds hold with a_i = a_i(I)
SOURCE_CONCLUSION: perihelia a_i(1 - e_i) ≥ d_⋆ and adjacent-annulus gaps a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) ≥ d_pair, for these states and for these lists; all these states belong to a compact subset of the nonsingular physical region and satisfy H_i ≥ m in their invariable frame
CONSTANT_SCOPE: d_⋆ and d_pair are uniform: they depend only on (n, ν, U, m)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5#gap-positive, lpM:L5#Km-compact, lpM:L5#empty-case, lpM:L5#perihelion, lpM:L5#compact-physical, lpM:L5#projection, lpM:s1:data, lpM:s1:elements, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#actionAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5#gap-positive | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | every adjacent gap is positive
EDGE: lpM:L5#Km-compact | docs/tracks/LP/source/MAIN.md#L5@L166-L170 | the compact set K_m and d_pair
EDGE: lpM:L5#empty-case | docs/tracks/LP/source/MAIN.md#L5@L170-L170 | the empty case
EDGE: lpM:L5#perihelion | docs/tracks/LP/source/MAIN.md#L5@L170-L175 | the perihelion bound d_⋆ (16)
EDGE: lpM:L5#compact-physical | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | the compact nonsingular physical set
EDGE: lpM:L5#projection | docs/tracks/LP/source/MAIN.md#L5@L175-L175 | H_i ≥ m
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | n ≥ 2 and the masses ν are fixed data
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | C, the elements a_i, e_i and H_i of (2)
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | U ⊂ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | B(I) occurs
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | Σ I_i D(e_i) occurs
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L5@L164-L164 | the independent list clause uses a_i(I) = (I_i/ν_i)^2, rather than an axis extracted from a physical state
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: d-generic source lemma (d ∈ {2,3}); its planar instance is the anchor LP0 (lpM:L5#planar_strongAMD_barrier); the spatial consumers (Lemma 6, Lemma 16, wave 3) use this node. AMENDED: N11 (AMENDMENTS.md L20).
```

```text
NODE: lpM:L5#gap-positive
KIND: step
TITLE: a nonpositive adjacent gap would be feasible, so C >= B_{i,i+1} >= B: contradiction
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L164-L164
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L5@L166-L166
CONTRACT_ID: lpM:L5#gap-positive
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L5: n ≥ 2, ν_i > 0; U ⊂ Q compact; m > 0; negative-energy states with I ∈ U and C ≤ B(I) - m, or lists e ∈ [0,1]^n with Σ_i I_i D(e_i) ≤ B(I) - m
SOURCE_QUANTIFIERS: for every compact U ⊂ Q and m > 0, and every state or list as in lpM:L5 (inherited)
SOURCE_CONCLUSION: every adjacent gap a_{i+1}(1 - e_{i+1}) - a_i(1 + e_i) is positive: otherwise (e_i, e_{i+1}) is feasible for B_{i,i+1}(I), and Σ_k I_k D(e_k) ≥ B_{i,i+1}(I) ≥ B(I) (for states via C ≥ Σ_k I_k D(e_k)) contradicts ≤ B(I) - m
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#static, lpM:s1:thresholds#pairFeasible, lpM:s1:thresholds#orderedPairThreshold, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:thresholds#actionAxis, lpM:s1:elements, lpM:s1:thresholds#eccDeficit, lpM:s1:thresholds#pairObjective
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#static | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the inequality of (13), C ≥ Σ I_k D(e_k); its premise C < B_⋆ holds because C ≤ B(I) - m < B(I) ≤ B_⋆(I)
EDGE: lpM:s1:thresholds#pairFeasible | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | a nonpositive gap makes the pair feasible
EDGE: lpM:s1:thresholds#orderedPairThreshold | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the feasible pair costs at least B_{i,i+1}(I)
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | B_{i,i+1}(I) ≥ B(I)
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the constraint uses a_i(I) = (I_i/ν_i)^2
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the Kepler axis of a state equals a_i(I) since I_i = ν_i √a_i
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the deficit sum uses D and its nonnegativity on [0,1]
EDGE: lpM:s1:thresholds#pairObjective | docs/tracks/LP/source/MAIN.md#L5@L166-L166 | the feasible pair objective I_i D(e_i) + I_{i+1} D(e_{i+1}) is bounded by the total deficit and below by the pair minimum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: lpM:L6
KIND: lemma
TITLE: Lemma 6: the moving threshold (17) and continuation
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L179-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model (1) with its data (n ≥ 2, ν_i > 0, d ∈ {2,3}, μ > 0); compact 𝓛 ⊂ Q; δ > 0
SOURCE_QUANTIFIERS: for every fixed data, compact 𝓛 ⊂ Q and δ > 0: there exist one compact neighborhood U ⊂ Q of 𝓛, r_g > 0 and its modulus Ω_B, before r and the solution; then for every 0 < r ≤ r_g and every solution starting at I^0 ∈ 𝓛 with C_0 ≤ B(I^0) - δ, while its negative-energy actions stay within r of I^0 with that tube in U, and every time t
SOURCE_CONCLUSION: the closed 4r_g sup-norm tube about 𝓛 is contained in U; Ω_B(s) = sup{¦B(I) - B(J)¦ : I,J ∈ U, ‖I-J‖_∞ ≤ s} tends to zero as s ↓ 0 and Ω_B(4r_g) ≤ δ/16; the same U and Ω_B are used in Lemmas 8 and 14 when 𝓛 = 𝓛_δ; C(t) ≤ B(I(t)) - δ + nr + Ω_B(r) (17); if nr + Ω_B(r) ≤ δ/2, there is no finite-time termination while the action and ellipticity conditions hold, in either time direction
CONSTANT_SCOPE: U, r_g and Ω_B depend only on (n, ν, 𝓛, δ), before r and the solution; they are shared across the later applications with 𝓛 = 𝓛_δ
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L6#shared-U, lpM:L6#moving-threshold, lpM:L6#continuation, lpM:L6#backward, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L6#shared-U | docs/tracks/LP/source/AMENDMENTS.md#N2@L11-L11 | one shared U contains the closed 4r_g tube, supplies the common modulus, and r ≤ r_g (MAIN L179-L189 supplies the construction and modulus claim)
EDGE: lpM:L6#moving-threshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | (17)
EDGE: lpM:L6#continuation | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | no finite-time termination
EDGE: lpM:L6#backward | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the backward assertion
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L6@L179-L179 | 𝓛, U ⊂ Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L6@L181-L181 | B and Ω_B
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N2 (AMENDMENTS.md L11): one shared compact U and one modulus for (17), Lemma 8 and (39); when 𝓛 = 𝓛_δ, U contains the closed 4r_g sup-norm tube about 𝓛_δ, Ω_B(4r_g) ≤ δ/16, and r ≤ r_g. No planar-carrier dependency is introduced.
```

```text
NODE: lpM:L6#shared-U
KIND: step
TITLE: compact neighborhood U of the compact set inside the chamber; modulus Omega_B -> 0
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L179-L182
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#shared-U
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the model (1) with its data (n ≥ 2, ν_i > 0, d ∈ {2,3}, μ > 0); compact 𝓛 ⊂ Q; δ > 0
SOURCE_QUANTIFIERS: for every fixed data, compact 𝓛 ⊂ Q and δ > 0, there exist a compact neighborhood U ⊂ Q, r_g > 0 and Ω_B, chosen before any radius r or solution; Ω_B is defined for all s ≥ 0
SOURCE_CONCLUSION: choose one compact neighborhood U of 𝓛 inside Q; uniform continuity of B on U gives Ω_B(s) = sup{¦B(I)-B(J)¦ : I,J ∈ U, ‖I-J‖_∞ ≤ s} → 0 as s ↓ 0; choose r_g > 0 small enough that the closed 4r_g sup-norm tube about 𝓛 is in U and Ω_B(4r_g) ≤ δ/16; when 𝓛 = 𝓛_δ this U and its modulus are the same in (17), Lemma 8 and (39), with subsequent r ≤ r_g
CONSTANT_SCOPE: U, r_g and Ω_B depend only on (n, ν, 𝓛, δ), before r and the solution
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L4, lpM:ext-heine-cantor, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L4 | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | B is continuous on Q
EDGE: lpM:ext-heine-cantor | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | uniform continuity on the compact U
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | U lies in the open chamber Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the modulus of B
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N2 (AMENDMENTS.md L11): one shared compact U and one modulus for (17), Lemma 8 and (39); when 𝓛 = 𝓛_δ, U contains the closed 4r_g sup-norm tube about 𝓛_δ, Ω_B(4r_g) ≤ δ/16, and r ≤ r_g. No planar-carrier dependency is introduced.
```

```text
NODE: lpM:L6#moving-threshold
KIND: step
TITLE: (17) from the identity of (13) and B(I^0) <= B(I(t)) + Omega_B(r)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L183-L186
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#moving-threshold
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n ≥ 2, ν_i > 0, d ∈ {2,3}, μ > 0); compact 𝓛 ⊂ Q; δ > 0; local notation: U, r_g, Ω_B are the witnesses constructed by lpM:L6#shared-U before r and the solution; 0 < r ≤ r_g; a solution in the negative-energy region on the connected interval under consideration, with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ and ‖I(t) - I^0‖_∞ ≤ r, with that tube in U
SOURCE_QUANTIFIERS: for every fixed data, compact 𝓛 ⊂ Q and δ > 0, first choose the shared U, r_g > 0 and Ω_B; then for every 0 < r ≤ r_g and every solution as specified, and all times in the interval
SOURCE_CONCLUSION: C(t) = C_0 + Σ_i(I_i(t) - I_i^0) ≤ C_0 + nr and B(I^0) ≤ B(I(t)) + Ω_B(r), hence C(t) ≤ B(I(t)) - δ + nr + Ω_B(r) (17)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#dynamic, lpM:L6#shared-U, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#dynamic | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the action identity of (13)
EDGE: lpM:L6#shared-U | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | I^0 and I(t) lie in U within r, so the modulus applies
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | B occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N2 (AMENDMENTS.md L11): one shared compact U and one modulus for (17), Lemma 8 and (39); when 𝓛 = 𝓛_δ, U contains the closed 4r_g sup-norm tube about 𝓛_δ, Ω_B(4r_g) ≤ δ/16, and r ≤ r_g. No planar-carrier dependency is introduced.
```

```text
NODE: lpM:L6#local-existence
KIND: step
TITLE: Lemma 5 compact set, bounded field and derivative, Picard contraction, uniqueness
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L187-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#local-existence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n ≥ 2, ν_i > 0, d ∈ {2,3}, μ > 0); compact 𝓛 ⊂ Q; δ > 0; local notation: U, r_g, Ω_B are the witnesses constructed by lpM:L6#shared-U before r and the solution; 0 < r ≤ r_g; a solution in the negative-energy region on the connected interval under consideration, with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ and ‖I(t) - I^0‖_∞ ≤ r, with that tube in U; nr + Ω_B(r) ≤ δ/2 for the continuation assertion
SOURCE_QUANTIFIERS: for every fixed data, compact 𝓛 ⊂ Q and δ > 0, first choose the shared U, r_g > 0 and Ω_B; then for every 0 < r ≤ r_g and every solution as specified, and all times in the interval
SOURCE_CONCLUSION: by (17), C ≤ B(I) - δ/2 along the solution, so Lemma 5 (with U and m = δ/2) supplies a compact nonsingular physical set with bounded momenta and energies separated from zero; the vector field of (1) and its derivative are bounded on a neighborhood of it; at every point of that set a local solution exists and is unique: on a small closed ball, z(t) = z_* + ∫_0^t X_H(z(u)) du is a contraction for times below the ball radius divided by the field bound and the inverse derivative bound (Picard iteration), and the same Lipschitz bound gives uniqueness by iterating the integral inequality
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5, lpM:L6#moving-threshold, lpM:s1:model, lpM:ext-picard, lpM:ext-gronwall, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | Lemma 5 supplies the compact nonsingular physical set (its premise C ≤ B(I) - δ/2 comes from (17))
EDGE: lpM:L6#moving-threshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | (17) gives C ≤ B(I) - δ/2 along the solution
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the vector field X_H of (1)
EDGE: lpM:ext-picard | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | contraction mapping and Picard iteration
EDGE: lpM:ext-gronwall | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | uniqueness by iterating the integral inequality
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the direct application of Lemma 5 uses the moving bound C ≤ B(I) - δ/2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N2 (AMENDMENTS.md L11): one shared compact U and one modulus for (17), Lemma 8 and (39); when 𝓛 = 𝓛_δ, U contains the closed 4r_g sup-norm tube about 𝓛_δ, Ω_B(4r_g) ≤ δ/16, and r ≤ r_g. No planar-carrier dependency is introduced.
```

```text
NODE: lpM:L6#continuation
KIND: step
TITLE: limit at a finite endpoint, local solution there and gluing; ellipticity is not lost
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L187-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#continuation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n ≥ 2, ν_i > 0, d ∈ {2,3}, μ > 0); compact 𝓛 ⊂ Q; δ > 0; local notation: U, r_g, Ω_B are the witnesses constructed by lpM:L6#shared-U before r and the solution; 0 < r ≤ r_g; a solution in the negative-energy region on the connected interval under consideration, with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ and ‖I(t) - I^0‖_∞ ≤ r, with that tube in U; nr + Ω_B(r) ≤ δ/2 for the continuation assertion
SOURCE_QUANTIFIERS: for every fixed data, compact 𝓛 ⊂ Q and δ > 0, first choose the shared U, r_g > 0 and Ω_B; then for every 0 < r ≤ r_g and every solution as specified, and all times in the interval
SOURCE_CONCLUSION: the field bound makes the trajectory Lipschitz in time, so at a finite endpoint it has a limit in the compact set; the local solution there glues to extend the solution; bounded actions keep the energies a fixed distance below zero, so ellipticity cannot be lost unnoticed; hence the solution cannot terminate at a finite time while the action and ellipticity conditions hold
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L6#local-existence, lpM:L5
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L6#local-existence | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | local existence and uniqueness at the limit point
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | use U and m = δ/2: (17) and nr + Ω_B(r) ≤ δ/2 supply C ≤ B(I) - m, as delivered by local-existence; the endpoint limit stays in that compact set
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N2 (AMENDMENTS.md L11): one shared compact U and one modulus for (17), Lemma 8 and (39); when 𝓛 = 𝓛_δ, U contains the closed 4r_g sup-norm tube about 𝓛_δ, Ω_B(4r_g) ≤ δ/16, and r ≤ r_g. No planar-carrier dependency is introduced.
```

```text
NODE: lpM:L6#backward
KIND: step
TITLE: replacing the vector field by its negative gives the backward assertion
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L187-L187
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
CONTRACT_ID: lpM:L6#backward
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L6: the model (1) with its data (n ≥ 2, ν_i > 0, d ∈ {2,3}, μ > 0); compact 𝓛 ⊂ Q; δ > 0; local notation: U, r_g, Ω_B are the witnesses constructed by lpM:L6#shared-U before r and the solution; 0 < r ≤ r_g; a solution in the negative-energy region on the connected interval under consideration, with I^0 ∈ 𝓛, C_0 ≤ B(I^0) - δ and ‖I(t) - I^0‖_∞ ≤ r, with that tube in U
SOURCE_QUANTIFIERS: for every fixed data, compact 𝓛 ⊂ Q and δ > 0, first choose the shared U, r_g > 0 and Ω_B; then for every 0 < r ≤ r_g and every solution as specified, and all times in the interval; t ≤ 0 for the reversed-time assertion
SOURCE_CONCLUSION: the moving-threshold estimate (17) holds backwards in time; if nr + Ω_B(r) ≤ δ/2, the solution also cannot terminate at a finite backward endpoint while the action and ellipticity conditions hold, by applying the continuation argument to the negated field
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L6#continuation, lpM:L6#moving-threshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L6#continuation | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | the forward argument applied to the negated field
EDGE: lpM:L6#moving-threshold | docs/tracks/LP/source/MAIN.md#L6@L189-L189 | (17) holds for negative times as well
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N2 (AMENDMENTS.md L11): one shared compact U and one modulus for (17), Lemma 8 and (39); when 𝓛 = 𝓛_δ, U contains the closed 4r_g sup-norm tube about 𝓛_δ, Ω_B(4r_g) ≤ δ/16, and r ≤ r_g. No planar-carrier dependency is introduced.
```

Suspected defects of the source:

No additional defect found in MAIN L161-L189 as amended. The original ordering at MAIN L175 (“|p_i| ≤ ν_i √(2/d_⋆)”) is the already recorded N11 issue, resolved by defining d_⋆ from (16) first. The separate U choices at MAIN L179, L257 and L472 are the already recorded N2 issue, resolved by one shared U. These are not new errata. The failures above are packet transcription/scope issues; no source repair or new external input is proposed.

Checks and scope:

- Read-only `git rev-parse HEAD` returned the audited HEAD above; `git branch --show-current` returned `inp-lp-graph`.
- `sha256sum -c docs/graph/LP/CORPUS.sha256`: MAIN.md OK; AMENDMENTS.md OK.
- `python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/LP/packets LP-m2b --root .`: `LP-m2b: 15 nodes, 64 edges, 20 coverage items, 0 problems` (exit 0). This checks the unchanged packet, not acceptance of its mathematics or the proposed replacements.
- Cross-slice checks: MAIN §1 L11-L53, L2 L112-L128, L3 L132-L139, L4 L143-L154, L8 L257 and L14 L470-L478; rendered LP-m1, LP-m2a, LP-ext and the directly used dimension-free anchor records. Manifest reads were restricted to identity fields; binding checked against anchor-binding.tsv. No frozen declaration read is needed for this non-anchor slice.
- Review integrity check: 15/15 node verdicts, 20/20 coverage verdicts and 8/8 complete replacement blocks; every replacement preserves all fields and protected identity values, and its DEPS/EDGE sets agree. No trailing whitespace. Read-only `git diff --check -- docs/graph/LP/reviews/LP-m2b-review-1.md` exited 0 (the review is untracked, so the independent whitespace check is the relevant check).
- Concurrent branch advance: final `git rev-parse HEAD` returned `3ee7b4480fb27797643d618460bbc206225c40b5`. Read-only `git diff --name-only 5ba2f8b2a66c9207991e38b939b89b7c1ce7b0e2 3ee7b4480fb27797643d618460bbc206225c40b5` lists only `docs/tracks/LP/packages/LP-GRAPH-W2.md`; no audited input changed. The audited HEAD on the first line remains the initial snapshot.
- Only this review file was written. No Lean, Lake, build, source lint, proof-body read, axiom query or state-changing git was run. No Lean result is certified by this review. No implementation deviation was introduced.

Lean hard rules (verbatim):

1. Never use set_option maxHeartbeats (or any heartbeat-budget override). A default-heartbeat elaboration failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a proof will not elaborate at default heartbeats, report it as a design signal.
2. No Lean file may exceed 1500 lines of code. When a file approaches the cap, split it into focused modules, preserving public import paths as cheap facades.
