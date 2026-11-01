NODE: lpM:L1
KIND: lemma
TITLE: Lemma 1: normalization and Newtonian reconstruction
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L99-L99
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L101-L108
CONTRACT_ID: lpM:L1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d ∈ {2,3}; ν_i > 0; μ > 0
SOURCE_QUANTIFIERS: for every d ∈ {2,3}, ν > 0 and μ > 0
SOURCE_CONCLUSION: the Hamiltonian (1) is the zero-total-momentum translation reduction of the Newtonian (1+n)-body Hamiltonian, divided by μ, in unchanged time; its solutions reconstruct Newtonian solutions with masses (1, μν_1, ..., μν_n)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L1#reduction, lpM:L1#reconstruction, lpM:s1:model
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1#reduction | docs/tracks/LP/source/MAIN.md#L1@L101-L102 | the reduction and the division by μ give (1)
EDGE: lpM:L1#reconstruction | docs/tracks/LP/source/MAIN.md#L1@L104-L108 | the explicit inverse reconstructs Newtonian solutions
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L1@L99-L99 | the statement concerns Hamiltonian (1) and the masses μν_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L1#reduction
KIND: step
TITLE: translation reduction with P_i = mu p_i, cancelling mu gives (1)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L101-L102
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L101-L102
CONTRACT_ID: lpM:L1#reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L1: d ∈ {2,3}; ν_i > 0; μ > 0
SOURCE_QUANTIFIERS: for every d, ν, μ (inherited from lpM:L1)
SOURCE_CONCLUSION: in barycentric coordinates with P_i = μ p_i and P_0 = -Σ_i P_i, the translation reduction has relative positions q_i = x_i - x_0 and momenta P_i (Σ_{i=0}^n P_i·dx_i = Σ_{i≥1} P_i·dq_i), kinetic energy Σ_i ¦P_i¦^2/(2μν_i) + ¦Σ_i P_i¦^2/2 and potential -Σ_i μν_i/¦q_i¦ - Σ_{i<j} μ^2 ν_iν_j/¦q_i - q_j¦; the symplectic form and the Hamiltonian both acquire the factor μ, and cancelling it gives (1) with the same time
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:model
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L1@L102-L102 | the result is compared with the Hamiltonian (1) and its symplectic form
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L1#velocity
KIND: display
TITLE: (10): Hamilton's equation for q_i, the actual velocity
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L105-L107
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L104-L107
CONTRACT_ID: lpM:L1#velocity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L1: d ∈ {2,3}; ν_i > 0; μ > 0; a solution of (1)
SOURCE_QUANTIFIERS: along every solution of (1) and for every i
SOURCE_CONCLUSION: q̇_i = p_i/ν_i + μ Σ_j p_j, (10)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:model
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L1@L106-L106 | Hamilton's equation q̇_i = ∂H_μ/∂p_i for the Hamiltonian (1)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: display (10), refined into its own node because Lemma 3 (recoil term) and Lemma 16 (V_i) consume it independently of the reconstruction (SPEC §5, displays)

NODE: lpM:L1#reconstruction
KIND: step
TITLE: explicit inverse: barycentric positions and velocities, Newton's equations
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L104-L108
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L1@L104-L108
CONTRACT_ID: lpM:L1#reconstruction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L1: d ∈ {2,3}; ν_i > 0; μ > 0; a solution of (1)
SOURCE_QUANTIFIERS: for every solution of (1) (inherited from lpM:L1)
SOURCE_CONCLUSION: with M = 1 + μΣ_i ν_i, x_0 = -μ Σ_i ν_i q_i/M, x_i = x_0 + q_i, ẋ_0 = -μ Σ_i p_i and ẋ_i = p_i/ν_i, the displayed velocities differentiate the displayed positions, and the equations for ṗ_i are Newton's equations after multiplying the planet momenta by μ; pair differences are q_i - q_j and star differences q_i
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L1#velocity, lpM:L1#reduction, lpM:s1:model
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1#velocity | docs/tracks/LP/source/MAIN.md#L1@L105-L108 | Hamilton's equation (10) shows that the displayed velocities differentiate the displayed positions
EDGE: lpM:L1#reduction | docs/tracks/LP/source/MAIN.md#L1@L108-L108 | the planet momenta are multiplied by μ (P_i = μ p_i) as in the reduction
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L1@L108-L108 | the equations for ṗ_i come from differentiating the potentials in (1)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L2
KIND: lemma
TITLE: Lemma 2: elementary orbital identities (11)-(12)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L112-L122
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L128
CONTRACT_ID: lpM:L2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν > 0; q ≠ 0; v = p/ν; E = ¦v¦^2/2 - 1/¦q¦ < 0 (one planet, any dimension)
SOURCE_QUANTIFIERS: for every ν > 0, q ≠ 0 and p with E < 0
SOURCE_CONCLUSION: e^2 = 1 + 2E¦q × v¦^2 = 1 - ¦q × v¦^2/a ≤ 1 and ¦q × p¦ = I √(1 - e^2) (11); a(1 - e) ≤ ¦q¦ ≤ a(1 + e) and ¦p¦^2 = ν^2(2/¦q¦ - 1/a) (12); including the radial case e = 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2#ecc-identity, lpM:L2#radial-bounds, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2#ecc-identity | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | the first identity of (11) and its substitutions
EDGE: lpM:L2#radial-bounds | docs/tracks/LP/source/MAIN.md#L2@L124-L128 | the bounds and the momentum identity (12)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L2@L112-L112 | definitions (2) of a, e, I
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L2#ecc-identity
KIND: step
TITLE: (11): e^2 = 1 + 2E¦q x v¦^2 = 1 - ¦q x v¦^2/a and ¦q x p¦ = I sqrt(1 - e^2)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L113-L115
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L124
CONTRACT_ID: lpM:L2#ecc-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L2: ν > 0, q ≠ 0, v = p/ν, E = ¦v¦^2/2 - 1/¦q¦ < 0
SOURCE_QUANTIFIERS: for every such q, p (inherited from lpM:L2)
SOURCE_CONCLUSION: expanding the square of (¦v¦^2 - 1/¦q¦) q - (q·v) v with ¦q × v¦^2 = ¦q¦^2¦v¦^2 - (q·v)^2 gives e^2 = 1 + 2E¦q × v¦^2; substituting 2E = -1/a gives e^2 = 1 - ¦q × v¦^2/a ≤ 1 and ¦q × p¦ = I √(1 - e^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | the eccentricity vector, E, a and I of (2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L2#radial-bounds
KIND: step
TITLE: (12): a(1-e) <= ¦q¦ <= a(1+e) and ¦p¦^2 = nu^2(2/¦q¦ - 1/a)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L118-L121
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L2@L124-L128
CONTRACT_ID: lpM:L2#radial-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L2: ν > 0, q ≠ 0, v = p/ν, E = ¦v¦^2/2 - 1/¦q¦ < 0; local data: r = ¦q¦, ℓ = q × v
SOURCE_QUANTIFIERS: for every such q, p (inherited from lpM:L2)
SOURCE_CONCLUSION: the energy identity and the radial/tangential decomposition give (q·v)^2 = 2r - r^2/a - ¦ℓ¦^2 ≥ 0; with ¦ℓ¦^2 = a(1 - e^2), completing the square gives (r - a)^2 ≤ a^2 e^2, i.e. a(1 - e) ≤ r ≤ a(1 + e); ¦p¦^2 = ν^2(2/¦q¦ - 1/a) is the energy definition
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2#ecc-identity, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2#ecc-identity | docs/tracks/LP/source/MAIN.md#L2@L128-L128 | uses ¦ℓ¦^2 = a(1 - e^2) from (11)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L2@L124-L124 | the energy definition E = ¦v¦^2/2 - 1/¦q¦ = -1/(2a)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

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
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Q3 split (ruling root-b8): the conjunction of lpM:L3#static (consumed by Lemma 5, hence LP0, which thus does not reach Lemma 1) and lpM:L3#dynamic (consumed by Lemma 6 and the dynamic anchors)

NODE: lpM:L3#static
KIND: lemma
TITLE: Lemma 3, static part: C >= 0, L != 0, positive projections, H_i >= m, inequality of (13)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L137
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#static
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a negative-energy state of the model (E_i < 0, q_i ≠ 0 for every i; ν > 0); m > 0 in the last clause
SOURCE_QUANTIFIERS: for every negative-energy state and every m > 0
SOURCE_CONCLUSION: C ≥ 0; if C < B_⋆(I) = min_i I_i then L ≠ 0, every H_i = L_i·L̂ is positive, and C = Σ_i(I_i - H_i) ≥ Σ_i I_i D(e_i) (the inequality of (13)); if C ≤ B_⋆(I) - m then H_i ≥ m for every i
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#amd-nonneg, lpM:L3#L-nonzero, lpM:L3#projections, lpM:L3#deficit, lpM:s1:thresholds#eccDeficit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#amd-nonneg | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | C ≥ 0
EDGE: lpM:L3#L-nonzero | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | L ≠ 0 when C < B_⋆
EDGE: lpM:L3#projections | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | H_i ≥ I_i - C, hence H_i > 0 and H_i ≥ m
EDGE: lpM:L3#deficit | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the inequality of (13)
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L3@L135-L135 | D occurs in (13)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Q3 split: no dynamics is used; this is the part of Lemma 3 that Lemma 5 (and LP0) consumes

NODE: lpM:L3#dynamic
KIND: lemma
TITLE: Lemma 3, dynamic part: L is conserved and C(t) - C(0) = sum(I_i(t) - I_i(0))
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L135
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#dynamic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a solution of (1) on a connected interval of existence; for the identity, negative energies along it (MAIN: 'on such an orbit', C < B_⋆)
SOURCE_QUANTIFIERS: for every such solution and all times t in its interval
SOURCE_CONCLUSION: L(t) is constant; C(t) - C(0) = Σ_i(I_i(t) - I_i(0)), the identity of (13)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#conservation, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#conservation | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | L̇ = 0 and constancy
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | C = Σ I_i - ¦L¦ with constant ¦L¦ gives the identity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Q3 split: the dynamic clauses of Lemma 3 (consumed by Lemma 6 and the dynamic anchors)

NODE: lpM:L3#conservation
KIND: step
TITLE: dL/dt = 0: recoil term, central forces and pair torques vanish; constancy by FTC
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L132
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#conservation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L3: the model (1) with its data (n, ν, d, μ > 0); a negative-energy state (E_i < 0, q_i ≠ 0 for every i) or a solution of (1) on a connected interval of existence (a solution on a connected interval)
SOURCE_QUANTIFIERS: along every solution of (1) on a connected interval of existence
SOURCE_CONCLUSION: differentiating Σ_i q_i × p_i: the recoil contribution from q̇_i is μ(Σ_j p_j) × (Σ_i p_i) = 0, the other kinetic terms vanish individually, central forces have zero torque, and the two forces of each planet pair contribute a multiple of (q_i - q_j) × (q_i - q_j) = 0; thus L̇ = 0 and L is constant
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L1#velocity, lpM:s1:model, lpM:s1:elements, lpM:ext-ftc
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1#velocity | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the recoil term comes from q̇_i = p_i/ν_i + μΣ_j p_j of (10)
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the forces are those of the Hamiltonian (1)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | L = Σ_i q_i × p_i
EDGE: lpM:ext-ftc | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | the fundamental theorem of calculus gives constancy
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L3#amd-nonneg
KIND: step
TITLE: ¦L¦ <= sum ¦L_i¦ <= sum I_i, so C >= 0
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L132
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#amd-nonneg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L3: the model (1) with its data (n, ν, d, μ > 0); a negative-energy state (E_i < 0, q_i ≠ 0 for every i) or a solution of (1) on a connected interval of existence (a negative-energy state)
SOURCE_QUANTIFIERS: for every negative-energy state
SOURCE_CONCLUSION: ¦L¦ ≤ Σ_i ¦L_i¦ ≤ Σ_i I_i, hence C = Σ_i I_i - ¦L¦ ≥ 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | by (11), ¦L_i¦ = ¦q_i × p_i¦ = I_i √(1 - e_i^2) ≤ I_i
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | C = Σ I_i - ¦L¦
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L3#L-nonzero
KIND: step
TITLE: C < B_star forces L != 0
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L132-L132
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#L-nonzero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L3: the model (1) with its data (n, ν, d, μ > 0); a negative-energy state (E_i < 0, q_i ≠ 0 for every i) or a solution of (1) on a connected interval of existence (a negative-energy state with C < B_⋆(I))
SOURCE_QUANTIFIERS: for every such state
SOURCE_CONCLUSION: if L = 0 then C = Σ_i I_i ≥ min_i I_i = B_⋆(I), contradicting C < B_⋆(I); so L ≠ 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | C = Σ I_i - ¦L¦ and the actions I_i > 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

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
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The local L ≠ 0 case is explicit, as needed by the nonzero-L deficit argument. The C < B_⋆ and C ≤ B_⋆ - m clauses are conditional conclusions. Do not apply lpM:L3#L-nonzero here: its premise C < B_⋆ is absent in the general nonzero-L case; lpM:L3#static obtains L ≠ 0 separately before using this step.

NODE: lpM:L3#deficit
KIND: step
TITLE: H_i <= I_i sqrt(1 - e_i^2) gives C >= sum I_i D(e_i) (inequality of (13))
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L133-L135
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#deficit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L3: the model (1) with its data (n, ν, d, μ > 0); a negative-energy state (E_i < 0, q_i ≠ 0 for every i) or a solution of (1) on a connected interval of existence (a negative-energy state with L ≠ 0, as on an orbit with C < B_⋆); local data: L̂, H_i
SOURCE_QUANTIFIERS: for every such state
SOURCE_CONCLUSION: H_i ≤ ¦L_i¦ = I_i √(1 - e_i^2), hence C = Σ_i(I_i - H_i) ≥ Σ_i I_i(1 - √(1 - e_i^2)) = Σ_i I_i D(e_i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#projections, lpM:L2, lpM:s1:thresholds#eccDeficit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#projections | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | C = Σ_i (I_i - H_i)
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | ¦L_i¦ = I_i √(1 - e_i^2) by (11)
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | D(e) = 1 - √(1 - e^2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the argument uses only L ≠ 0 (to define L̂); MAIN applies it on orbits with C < B_⋆

NODE: lpM:L3#deficit-zero-L
KIND: step
TITLE: the deficit bound when L = 0: C = sum I_i >= sum I_i D(e_i)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L133-L135
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
CONTRACT_ID: lpM:L3#deficit-zero-L
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L3: the model (1) with its data (n, ν, d, μ > 0); a negative-energy state (E_i < 0, q_i ≠ 0 for every i) or a solution of (1) on a connected interval of existence (a negative-energy state with L = 0)
SOURCE_QUANTIFIERS: for every such state
SOURCE_CONCLUSION: C = Σ_i I_i ≥ Σ_i I_i D(e_i), since 0 ≤ e_i ≤ 1 and D(e) ≤ 1 on [0,1]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2, lpM:s1:thresholds#eccDeficit, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | e_i ≤ 1 by (11)
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | D(e) ≤ 1 for e ∈ [0,1]
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L3@L139-L139 | C = Σ I_i - ¦L¦ = Σ I_i when L = 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m2a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: MAIN states and proves the inequality of (13) only on orbits with C < B_⋆ (hence L ≠ 0, via H_i); the frozen characterization sum_action_mul_eccDeficit_le_sourceStrongAMD asserts it on every source canonical phase, and the case L = 0 is not argued in MAIN (it is immediate from D ≤ 1 on [0,1])

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
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: consumed by Theorem 15's orientation step (wave 2; N8, OD-1)

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
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Q4 split (ruling root-b8): the statement clauses on radial contact and the Laskar-Petit identification (L143) and on geometric sharpness (L147) are not part of this record; no proof consumes them (N9). Their items lpM:L4#stmt-contact-lp and lpM:L4#stmt-sharpness and the supporting prose L158 and L160 are EXCLUDED

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
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

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
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

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
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

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
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

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
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

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
EXTRACTOR: kam-lp+sol-review-LP-LP-m2a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
