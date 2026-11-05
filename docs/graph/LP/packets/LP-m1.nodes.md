NODE: lpM:s1:data
KIND: definition
TITLE: fixed data of track LP (n, nu, A, delta, gamma, tau, d; the two norms)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L11-L15
PROOF_SOURCE: -
CONTRACT_ID: lpM:s1:data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: fixed once: n, ν, 𝒜, δ, γ, τ, d
SOURCE_CONCLUSION: an integer n ≥ 2; ν_i > 0 with max_i ν_i = 1; a compact set 𝒜 ⊂ {a ∈ ℝ^n : 0 < a_1 < ... < a_n} (possibly empty, giving a vacuous assertion); δ, γ > 0; τ > n - 1; space dimension d ∈ {2, 3}; physical Euclidean lengths ¦·¦ are distinguished from the max norm ‖·‖_∞ on action and complex coordinate vectors
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
REVIEWER: sol-review-LP-LP-m1
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: hypothesis package (SPEC §3): not a global standing assumption; a result that assumes part of it names that part in SOURCE_HYPOTHESES and depends on this node

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
EXTRACTOR: kam-lp+sol-review-LP-LP-m1
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:s1:elements
KIND: definition
TITLE: canonical Kepler elements and the strong AMD (2), in dimension d
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L26-L37
PROOF_SOURCE: -
CONTRACT_ID: lpM:s1:elements
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of lpM:s1:data; a state (q, p) of the model
SOURCE_QUANTIFIERS: for every state and every i
SOURCE_CONCLUSION: v_i = p_i/ν_i, E_i = ¦v_i¦^2/2 - 1/¦q_i¦, e_i = (¦v_i¦^2 - 1/¦q_i¦) q_i - (q_i·v_i) v_i; when E_i < 0: a_i = -1/(2E_i), I_i = Λ_i = ν_i √a_i, e_i = ¦e_i¦, L_i = q_i × p_i, L = Σ_i L_i, C = Σ_i I_i - ¦L¦ (2); in the plane × is the oriented scalar determinant and ¦L¦ its absolute value; a nondegenerate elliptic canonical state has E_i < 0 and e_i < 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:model, lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#s1@L28-L28 | q_i, p_i and ν_i are the variables of the model
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L28-L28 | the Euclidean length ¦·¦ and the dimension d
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m1
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: d-generic source definition (d ∈ {2,3}); the planar frozen realizations are the anchors lpM:s1:elements#* (LP-adef-pl), the spatial ones come in wave 3 (SPEC §5, dimension rule). AMENDED: N8 (AMENDMENTS.md L17): C = ΣI - ¦L¦ is the frozen convention (OD-1).

NODE: lpM:s1:fast
KIND: definition
TITLE: fast Hamiltonian h(I) and radian frequencies omega(I) (4)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L57-L61
PROOF_SOURCE: -
CONTRACT_ID: lpM:s1:fast
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of lpM:s1:data (n, ν)
SOURCE_QUANTIFIERS: for every action vector I with I_i > 0
SOURCE_CONCLUSION: h(I) = -Σ_i ν_i^3/(2 I_i^2) and ω_i(I) = ν_i^3/I_i^3 = a_i(I)^{-3/2}, (4)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:data, lpM:s1:thresholds#actionAxis
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L59-L59 | the masses ν_i enter h and ω
EDGE: lpM:s1:thresholds#actionAxis | docs/tracks/LP/source/MAIN.md#s1@L60-L60 | ω_i(I) = a_i(I)^{-3/2} uses the action axis
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m1
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:s1:dioph
KIND: definition
TITLE: the Diophantine condition (5) at omega(I^0); angles of period 2 pi
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L62-L67
PROOF_SOURCE: -
CONTRACT_ID: lpM:s1:dioph
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of lpM:s1:data (γ > 0, τ > n - 1); an initial action vector I^0
SOURCE_QUANTIFIERS: for every I^0 and every 0 ≠ k ∈ ℤ^n
SOURCE_CONCLUSION: ¦k·ω(I^0)¦ ≥ γ ¦k¦_1^{-τ} for every 0 ≠ k ∈ ℤ^n (5); all angles of the proof have period 2π (Lemma 13 records the conversion to period one)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:fast, lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#s1@L64-L64 | the frequencies ω(I^0) of (4)
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L64-L64 | γ and τ are fixed data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m1
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:s1:half-integer
KIND: claim
TITLE: tau = n - 1/2 is admissible and gives exponent 1/(2n+1)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#s1@L93-L93
CONTRACT_ID: lpM:s1:half-integer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 2 (lpM:s1:data)
SOURCE_QUANTIFIERS: for every n ≥ 2
SOURCE_CONCLUSION: τ = n - 1/2 satisfies τ > n - 1, and a = 1/(2(τ + 1)) = 1/(2n + 1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L93-L93 | admissibility is the condition τ > n - 1 of the data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: kam-lp
REVIEWER: sol-review-LP-LP-m1
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: arithmetic step of the half-integer corollary anchors LP1-H and LP2-H (waves 2 and 3); the exponent a = 1/(2(τ+1)) is defined in (7)
