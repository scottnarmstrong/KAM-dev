NODE: lpM:ext-ftc
KIND: external
TITLE: fundamental theorem of calculus (zero derivative on an interval)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L3@L139-L139
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-ftc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J a real interval; f : J → V continuous on J and differentiable on its interior, with derivative zero there; V is a finite-dimensional real normed vector space (including ℝ)
SOURCE_QUANTIFIERS: for every such J, V and f, and every s, t ∈ J
SOURCE_CONCLUSION: f(t) = f(s); thus f is constant on J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp+sol-review-LP-R1-small
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-compact-min
KIND: external
TITLE: extreme values of a continuous function on a nonempty compact set
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L149-L149
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-compact-min
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K a nonempty compact set; f : K → ℝ continuous
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: f attains its minimum and its maximum on K (for finitely many functions, the minimum of their minima)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-R1-small
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-heine-cantor
KIND: external
TITLE: Heine-Cantor: continuity on a compact set is uniform
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L4@L154-L154
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-heine-cantor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K a compact metric space; f continuous on K
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: f is uniformly continuous on K
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-R1-small
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-picard
KIND: external
TITLE: contraction mapping principle / Picard iteration for the integral equation
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-picard
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X bounded with bounded derivative (locally Lipschitz) on a closed ball B(z_*, ρ); a time T below ρ/sup¦X¦ and the inverse Lipschitz bound
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: the map z ↦ z_* + ∫_0^t X(z(u)) du is a contraction of C([0,T], B(z_*, ρ)) and its fixed point is a solution of ż = X(z), z(0) = z_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-R1-small
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-gronwall
KIND: external
TITLE: uniqueness of ODE solutions by iterating the integral inequality
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L6@L189-L189
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-gronwall
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X Lipschitz on a set containing two solutions with the same initial value
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: the two solutions coincide (iterating ¦z_1 - z_2¦(t) ≤ L ∫_0^t ¦z_1 - z_2¦ gives zero)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-R1-small
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level
