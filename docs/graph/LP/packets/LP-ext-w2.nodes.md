NODE: lpM:ext-holomorphic-limit
KIND: external
TITLE: uniform limits of holomorphic maps are holomorphic
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L211-L211
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-holomorphic-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a sequence of holomorphic maps on an open set of ℂ^k converging uniformly (on compact subsets)
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: the limit is holomorphic (in particular a uniformly convergent iteration of holomorphic maps has a holomorphic limit)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-identity-theorem
KIND: external
TITLE: identity theorem for analytic maps on a connected domain
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L238-L238
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-identity-theorem
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: two analytic (holomorphic, or real analytic) maps on a connected open set that agree on a nonempty open subset (or have the same power series at one point)
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: they agree on the whole connected set
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-compact-cover
KIND: external
TITLE: finite subcover of a compact set
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L265-L265
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-compact-cover
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K a compact subset of a metric space; an open cover of K (e.g. balls centered at points of K)
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: finitely many members of the cover already cover K (with half-sized balls: a Lebesgue-number neighborhood)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-cauchy-estimates
KIND: external
TITLE: Cauchy's integral formula and estimates; holomorphic square root on a half plane
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L271-L271
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-cauchy-estimates
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f holomorphic on a neighborhood of a closed polydisk of radius ρ, bounded by M there; w in the half plane Re w > 0
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: Cauchy's formula holds and ¦∂^α f¦ ≤ α! M ρ^{-¦α¦} at the center (one-variable form: ¦f'¦ ≤ M/ρ); the principal square root is holomorphic on Re w > 0 with positive real part
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level

NODE: lpM:ext-fourier-contour
KIND: external
TITLE: Fourier coefficients of periodic holomorphic maps and the contour shift
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L298-L298
PROOF_SOURCE: -
CONTRACT_ID: lpM:ext-fourier-contour
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f holomorphic and 2π-periodic in each angle on the strip ¦Im θ¦_∞ < σ, bounded by M on narrower strips
SOURCE_QUANTIFIERS: for every instance of the hypotheses
SOURCE_CONCLUSION: the Fourier coefficients are integrals over the real torus, independent of the contour within the strip, and ¦f_k¦ ≤ M e^{-σ'¦k¦_1} for every σ' < σ (shift each contour with sign opposite to the Fourier index)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external input of the closed list (SPEC §3); Mathlib-level
