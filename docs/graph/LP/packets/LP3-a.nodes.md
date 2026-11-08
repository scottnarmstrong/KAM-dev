NODE: lp3:s2.3
KIND: step
TITLE: fixed data F1-F7 and the cell-by-cell discharge of the premises of partialConvex_nekhoroshev
STATEMENT_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.2@L177-L201
PROOF_SOURCE: docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L203-L257
CONTRACT_ID: lp3:s2.3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data n ≥ 2, ν_i > 0 with max ν = 1, 𝒜 compact and ordered, δ > 0 (no γ, τ, no (5)); planar (the spatial version is §2.5)
SOURCE_QUANTIFIERS: fixed before μ and the initial state
SOURCE_CONCLUSION: the shared tube (U, r_g, Ω_B(4r_g) ≤ δ/16), the uniform holomorphic extension of the chart and perturbation, widths, a finite cover of 𝓛_δ by centres c_j with fast cells G_j ⊂ G'_j and slow sets D_j = {¦y¦²/2 < B(c_j) - 5δ/16}, the Kepler constants and the slow erosion gap are fixed; on every cell the premises of partialConvex_nekhoroshev hold (holomorphic, C², real, bounded Hessian, definite fast part of the Kepler h, partial perturbation P = fc/B_0, the Hamiltonian identity with the chart Hamiltonian); thresholds ν_0, μ_0, r(μ) = (B_0μ)^{b_n}, T(μ) ≤ the frozen horizon T_0 exp(cμ^{-a_n})
CONSTANT_SCOPE: all constants and the cover depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p0:partial, lpM:L8#shared-tube, lpM:L8, lpM:L5, lpM:s1:fast, lpM:ext-compact-cover, lpM:s1:thresholds#orderedStrongThreshold, lp3:s1.1#planetaryTimeExponent, lp3:s1.1#planetaryDriftExponent
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p0:partial | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L154-L154 | the premises of the imported theorem are read from its frozen interface (§2.1)
EDGE: lpM:L8#shared-tube | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L181-L181 | F1: the shared tube U, r_g and Ω_B(4r_g) ≤ δ/16 (N2)
EDGE: lpM:L8 | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L184-L184 | F2/F3: the uniform holomorphic extension, bounds and widths of Lemma 8
EDGE: lpM:L5 | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L198-L198 | F6: the Kepler constants of the safe compact set
EDGE: lpM:s1:fast | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L215-L215 | the Kepler fast part h and its definite Hessian (∂ω_i/∂I_i = -3ν_i³/I_i⁴)
EDGE: lpM:ext-compact-cover | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L190-L190 | F4: a finite cover of the compact 𝓛_δ by centres
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L194-L194 | F5: the slow levels B(c_j) - 5δ/16
EDGE: lp3:s1.1#planetaryTimeExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L248-L248 | the time exponent a_n = 2/(6n² - 3n + 14)
EDGE: lp3:s1.1#planetaryDriftExponent | docs/tracks/LP/lp3/LP3-PLAN.md#s2.3@L248-L248 | the drift exponent b_n = 3/(6n² - 3n + 14)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: LP3-PLAN §2.2-§2.3 (F1-F7 and the discharge cells) folded into one step (D65 minimal model)
