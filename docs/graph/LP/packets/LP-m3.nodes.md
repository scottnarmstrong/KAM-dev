NODE: lpM:L7
KIND: lemma
TITLE: Lemma 7: a regular planar canonical chart
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L195-L200
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L202-L242
CONTRACT_ID: lpM:L7
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν > 0 (one planet, d = 2)
SOURCE_QUANTIFIERS: for every ν > 0
SOURCE_CONCLUSION: the map (19), with angle read modulo 2π, is a real analytic symplectic diffeomorphism from {I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I} onto the positive-angular-momentum negative-energy planar region; its form is dI ∧ dλ + dx ∧ dy, its energy is -ν^3/(2I^2), its angular momentum is G = I - Γ; it is regular at circular orbits
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7#kepler-equation, lpM:L7#chart-formula, lpM:L7#rotated-form, lpM:L7#symplectic, lpM:L7#inverse, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7#kepler-equation | docs/tracks/LP/source/MAIN.md#L7@L207-L211 | the eccentric longitude F of (18) and its analytic dependence
EDGE: lpM:L7#chart-formula | docs/tracks/LP/source/MAIN.md#L7@L213-L220 | the chart (19)
EDGE: lpM:L7#rotated-form | docs/tracks/LP/source/MAIN.md#L7@L221-L226 | the energy, angular momentum and eccentricity vector of the image
EDGE: lpM:L7#symplectic | docs/tracks/LP/source/MAIN.md#L7@L228-L238 | the chart is symplectic
EDGE: lpM:L7#inverse | docs/tracks/LP/source/MAIN.md#L7@L240-L242 | the analytic inverse onto the region: a diffeomorphism modulo the angle lattice
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L7@L200-L200 | energy, angular momentum and the negative-energy region are those of (2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L7#kepler-equation
KIND: step
TITLE: (18): unique eccentric longitude F, analytic in the data, F(lambda + 2 pi) = F(lambda) + 2 pi
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L202-L210
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L207-L211
CONTRACT_ID: lpM:L7#kepler-equation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L7: ν > 0; the region I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I; local data a = (I/ν)^2, s = 1 - Γ/I > 0, b_e = √((1 - Γ/(2I))/I), k = b_e x, l = -b_e y
SOURCE_QUANTIFIERS: for every ν > 0 and every point of the region (inherited from lpM:L7)
SOURCE_CONCLUSION: k^2 + l^2 = 1 - s^2 < 1; F - k sin F + l cos F = λ (18) has a unique solution F modulo 2π, since D_F = 1 - k cos F - l sin F ≥ 1 - √(k^2 + l^2) > 0 and the lift increases by 2π per period; the solution is analytic in (I, λ, x, y): the Newton-type fixed-point map is a contraction on small complex disks, its holomorphic iterates converge uniformly; uniqueness patches the branches and gives F(λ + 2π) = F(λ) + 2π
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:ext-holomorphic-limit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:ext-holomorphic-limit | docs/tracks/LP/source/MAIN.md#L7@L211-L211 | uniform limits of the holomorphic iterates are holomorphic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the convergence of the iterates of a contraction is elementary (geometric series); only the holomorphy of the limit is an external input

NODE: lpM:L7#chart-formula
KIND: display
TITLE: (19): the chart q = a(A c(F) - (k,l)), p = nu A c'(F)/(sqrt(a) D_F)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L213-L220
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L213-L220
CONTRACT_ID: lpM:L7#chart-formula
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L7: ν > 0; the region I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I; local data a = (I/ν)^2, s = 1 - Γ/I > 0, b_e = √((1 - Γ/(2I))/I), k = b_e x, l = -b_e y
SOURCE_QUANTIFIERS: for every ν > 0 and every point of the region (inherited from lpM:L7)
SOURCE_CONCLUSION: with A = [[1 - l^2/(1+s), kl/(1+s)], [kl/(1+s), 1 - k^2/(1+s)]], c(F) = (cos F, sin F), c'(F) = (-sin F, cos F): q = a(A c(F) - (k,l)), p = (ν/√a) A c'(F)/D_F (19); no perihelion angle is used at zero eccentricity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7#kepler-equation
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7#kepler-equation | docs/tracks/LP/source/MAIN.md#L7@L219-L219 | F solves (18) and D_F > 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L7#rotated-form
KIND: step
TITLE: (20) for e > 0; energy -nu^3/(2I^2), angular momentum G = I - Gamma, eccentricity vector (k,l); e = 0 by continuity
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L221-L226
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L221-L226
CONTRACT_ID: lpM:L7#rotated-form
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L7: ν > 0; the region I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I; local data a = (I/ν)^2, s = 1 - Γ/I > 0, b_e = √((1 - Γ/(2I))/I), k = b_e x, l = -b_e y
SOURCE_QUANTIFIERS: for every ν > 0 and every point of the region (inherited from lpM:L7)
SOURCE_CONCLUSION: for e = √(k^2 + l^2) > 0, (k, l) = e(cos ϖ, sin ϖ), F = E + ϖ, (19) is the rotation of (20) q = a(cos E - e, s sin E), p = ν(-sin E, s cos E)/(√a(1 - e cos E)); multiplication gives energy -ν^3/(2I^2), angular momentum G = I - Γ and eccentricity vector (k, l); the identities extend to e = 0 by continuity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7#chart-formula, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7#chart-formula | docs/tracks/LP/source/MAIN.md#L7@L221-L224 | (20) is (19) in rotated coordinates
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L7@L226-L226 | energy, angular momentum and eccentricity vector are those of (2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L7#symplectic
KIND: step
TITLE: p.dq = I dlambda + Gamma d(-varpi) + d(2Ie sin E): the chart is symplectic
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L228-L238
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L228-L238
CONTRACT_ID: lpM:L7#symplectic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L7: ν > 0; the region I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I; local data a = (I/ν)^2, s = 1 - Γ/I > 0, b_e = √((1 - Γ/(2I))/I), k = b_e x, l = -b_e y
SOURCE_QUANTIFIERS: for every ν > 0 and every point of the region (inherited from lpM:L7)
SOURCE_CONCLUSION: in the coordinates (20), p·dq = 2e sin E dI + I(1 + e cos E) dE + I sin E de; a varying perihelion rotation adds G dϖ; with ℓ = E - e sin E, p·dq = I dλ + Γ d(-ϖ) + d(2Ie sin E), and (x, y) = √(2Γ)(cos ϖ, -sin ϖ) gives Γ d(-ϖ) = (x dy - y dx)/2; exterior differentiation proves symplecticity on e > 0, and analyticity extends it across e = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7#rotated-form, lpM:L7#kepler-equation, lpM:ext-identity-theorem
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7#rotated-form | docs/tracks/LP/source/MAIN.md#L7@L229-L232 | the computation is done in the rotated coordinates (20)
EDGE: lpM:L7#kepler-equation | docs/tracks/LP/source/MAIN.md#L7@L232-L235 | λ = ℓ + ϖ through (18) with F = E + ϖ
EDGE: lpM:ext-identity-theorem | docs/tracks/LP/source/MAIN.md#L7@L238-L238 | the analytic identity of the two forms extends from e > 0 across e = 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N1 (AMENDMENTS.md L10), fixed in place at MAIN L238: Γ d(-ϖ) = (x dy - y dx)/2

NODE: lpM:L7#inverse
KIND: step
TITLE: analytic inverse: a, I, G from energy and momentum, (k,l) from the eccentricity vector, lambda from (18)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L240-L242
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L7@L240-L242
CONTRACT_ID: lpM:L7#inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L7: ν > 0; the region I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I; local data a = (I/ν)^2, s = 1 - Γ/I > 0, b_e = √((1 - Γ/(2I))/I), k = b_e x, l = -b_e y
SOURCE_QUANTIFIERS: for every ν > 0 and every point of the region (inherited from lpM:L7)
SOURCE_CONCLUSION: on the positive-angular-momentum negative-energy region: a, I, G from energy and angular momentum; (k, l) as the eccentricity vector, x = k/b_e, y = -l/b_e; A has eigenvalues 1, s > 0 and A^{-1}(q/a + (k,l)) = c(F) (length one by e·q = a(1 - e^2) - ¦q¦); λ from (18) modulo 2π via e^{iλ} = e^{iF} exp[-i(k sin F - l cos F)]; the momentum is recovered uniquely from the positive angular momentum and e = v × (q × v) - q/¦q¦; all inverse formulas are analytic, so the chart is a diffeomorphism onto the region modulo the angle lattice
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L2, lpM:L7#rotated-form, lpM:L7#kepler-equation, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L7@L240-L240 | (11): ¦q × p¦ = I √(1 - e^2), so s = G/I = √(1 - e^2) and k^2 + l^2 = 1 - s^2 recover the eccentricity data
EDGE: lpM:L7#rotated-form | docs/tracks/LP/source/MAIN.md#L7@L240-L240 | the image has energy -ν^3/(2I^2), angular momentum I - Γ and eccentricity vector (k, l), which the inverse inverts
EDGE: lpM:L7#kepler-equation | docs/tracks/LP/source/MAIN.md#L7@L240-L241 | λ is recovered from F through (18)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L7@L242-L242 | the eccentricity vector of (2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L8
KIND: lemma
TITLE: Lemma 8: a whole-sublevel planar analytic neighborhood (21)-(22)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L246-L255
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L271
CONTRACT_ID: lpM:L8
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data (n, ν, 𝒜, δ) of lpM:s1:data, planar (d = 2); 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}
SOURCE_QUANTIFIERS: there exist r_*, s, b, M > 0 (fixed first); then for every I^0 ∈ 𝓛_δ, with Z_0 = {z = (x_i, y_i)_i : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21)
SOURCE_CONCLUSION: the product chart of Lemma 7 and the exact pulled-back perturbation f are holomorphic on ‖I - I^0‖_∞ < r_*, ¦Im λ¦_∞ < 4s, dist_∞(z, Z_0) < 4b (22); on a slightly smaller domain the chart, momenta, f and all their first derivatives are bounded by M; every Newtonian denominator there has a single holomorphic branch with modulus bounded away from zero; in physical coordinates the chart Hamiltonian equals h(I) + μ f(I, λ, z) without truncation; the ball (21) contains every secular state allowed by the initial margin, with a fixed collar
CONSTANT_SCOPE: r_*, s, b, M depend only on (n, ν, 𝒜, δ) and are chosen before I^0 (and before μ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#empty-case, lpM:L8#shared-tube, lpM:L8#real-margin, lpM:L8#compact-real-set, lpM:L8#newton-extension, lpM:L8#gluing, lpM:L8#denominators, lpM:L8#widths, lpM:L8#exact-split, lpM:L7, lpM:s1:model, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#empty-case | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | the empty case
EDGE: lpM:L8#shared-tube | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | U and r_g
EDGE: lpM:L8#real-margin | docs/tracks/LP/source/MAIN.md#L8@L258-L261 | the real margin, safety and e_*
EDGE: lpM:L8#compact-real-set | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | the compact real set and analyticity of the chart near it
EDGE: lpM:L8#newton-extension | docs/tracks/LP/source/MAIN.md#L8@L263-L263 | the uniform complex extension of the Kepler-equation solution
EDGE: lpM:L8#gluing | docs/tracks/LP/source/MAIN.md#L8@L265-L265 | single-valued uniform complex neighborhood
EDGE: lpM:L8#denominators | docs/tracks/LP/source/MAIN.md#L8@L267-L271 | the Newtonian denominators
EDGE: lpM:L8#widths | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | the widths r_*, s, b and the bound M
EDGE: lpM:L8#exact-split | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | the exact split h + μ f
EDGE: lpM:L7 | docs/tracks/LP/source/MAIN.md#L8@L255-L255 | the product chart of Lemma 7 gives ΣΓ_i = Σ(I_i - G_i) = C on prograde states, so the ball (21) contains every secular state with C ≤ B(I^0) - δ, with collar 3δ/4
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L8@L250-L250 | the perturbation f of (1)
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L8@L246-L246 | 𝓛_δ lies in the chamber Q (𝒜 is ordered)
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L8@L246-L246 | B occurs in 𝓛_δ and in (21)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: planar (d = 2) lemma; the spatial analogue is Lemma 18 (wave 3). Lemmas 12-14 take its conclusion (with m = n slow pairs here) as a premise; Theorem 15 discharges it (lpM:T15#apply-L14). AMENDED: N2, N3 (AMENDMENTS.md L11, L12).

NODE: lpM:L8#empty-case
KIND: step
TITLE: L_delta empty: no initial state satisfies (6); otherwise L_delta is compact
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L246-L246
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L257
CONTRACT_ID: lpM:L8#empty-case
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21)
SOURCE_QUANTIFIERS: for the fixed data
SOURCE_CONCLUSION: if 𝓛_δ is empty there is no initial state satisfying (6) (C(0) ≥ 0 and C(0) ≤ B(I^0) - δ force B(I^0) ≥ δ); otherwise 𝓛_δ is compact (a closed subset of the compact 𝓛, B being continuous)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3#static, lpM:L4, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3#static | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | C ≥ 0, so an initial state with (6) has B(I^0) ≥ δ
EDGE: lpM:L4 | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | B is continuous, so 𝓛_δ is closed in the compact 𝓛
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | B occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L8#shared-tube
KIND: step
TITLE: compact chamber neighborhood U and width r_g: 4r_g tube in U, Omega_B(4 r_g) <= delta/16
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L257
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L257
CONTRACT_ID: lpM:L8#shared-tube
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅
SOURCE_QUANTIFIERS: for the fixed data
SOURCE_CONCLUSION: there are a compact chamber neighborhood U of 𝓛_δ and a fixed real action width r_g > 0 such that every 4r_g-tube about 𝓛_δ (sup norm) lies in U and Ω_B(4r_g) ≤ δ/16
CONSTANT_SCOPE: U and r_g depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L6#shared-U, lpM:L8#empty-case, lpM:s1:chamber#chamber, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L6#shared-U | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | the compact neighborhood U of the compact 𝓛_δ and the modulus Ω_B(r) → 0
EDGE: lpM:L8#empty-case | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | 𝓛_δ is compact
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | U lies in the chamber Q
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L8@L257-L257 | B occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N2 (AMENDMENTS.md L11): this U is the one compact set shared with Lemmas 6 and 14; it contains the closed 4r_g-tube about 𝓛_δ

NODE: lpM:L8#real-margin
KIND: step
TITLE: real tube: sum Gamma_i <= B(I) - 3 delta/16, Gamma_i < I_i, phases safe by Lemma 5, e <= e_* < 1
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L261
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L257-L261
CONTRACT_ID: lpM:L8#real-margin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅; real I with ‖I - I^0‖_∞ ≤ 4r_g and z ∈ Z_0
SOURCE_QUANTIFIERS: for every I^0 ∈ 𝓛_δ (inherited from lpM:L8; the widths are fixed before I^0); for every such real (I, z) and λ
SOURCE_CONCLUSION: Σ_i Γ_i ≤ B(I^0) - δ/4 ≤ B(I) - 3δ/16; consequently Γ_i < I_i with a fixed margin, the corresponding planar phases are safe (a compact nonsingular set of Lemma 5) and the eccentricities are bounded by one fixed e_* < 1
CONSTANT_SCOPE: the margin and e_* depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#shared-tube, lpM:L7, lpM:L5, lpM:L5#perihelion, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#shared-tube | docs/tracks/LP/source/MAIN.md#L8@L258-L259 | Ω_B(4r_g) ≤ δ/16 gives B(I^0) - δ/4 ≤ B(I) - 3δ/16
EDGE: lpM:L7 | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | G_i = I_i - Γ_i, so these points are prograde states with C = ΣΓ_i
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | Lemma 5 with U and m = 3δ/16: the phases form a compact nonsingular set (its premise C ≤ B(I) - 3δ/16 is the display)
EDGE: lpM:L5#perihelion | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | √(1 - e_i^2) ≥ m/I_max bounds the eccentricities by e_* < 1
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L8@L259-L259 | B occurs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L8#compact-real-set
KIND: step
TITLE: the set of (I^0, I, z, lambda) with one closed angle cell is compact; the chart is analytic near it
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L261-L261
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L261-L261
CONTRACT_ID: lpM:L8#compact-real-set
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅
SOURCE_QUANTIFIERS: for the fixed data
SOURCE_CONCLUSION: the set of (I^0, I, z, λ) with I^0 ∈ 𝓛_δ, real ‖I - I^0‖_∞ ≤ 4r_g, z ∈ Z_0 and λ in one closed period cell is compact, and the chart of Lemma 7 is analytic on an open neighborhood of it; every point of (22) lies within sup distance max(r_*, 4s, 4b) of the compact projection K' of this set
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#real-margin, lpM:L8#shared-tube, lpM:L7
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#real-margin | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | the points lie in the chart's region with a fixed margin
EDGE: lpM:L8#shared-tube | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | the tube is closed and bounded inside U
EDGE: lpM:L7 | docs/tracks/LP/source/MAIN.md#L8@L261-L261 | the chart is real analytic on its region
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N3 (AMENDMENTS.md L12): the projection K' over I^0 ∈ 𝓛_δ of this closed set, with r_* ≤ 4r_g

NODE: lpM:L8#newton-extension
KIND: step
TITLE: uniform complex extension of the solution of (18): radii rho, eta, contraction by 1/2
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L263-L263
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L263-L263
CONTRACT_ID: lpM:L8#newton-extension
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅
SOURCE_QUANTIFIERS: at every point of the compact real set
SOURCE_CONCLUSION: at each real point the derivative of (18) is at least 1 - e_*; fixed radii ρ, η > 0 make the Newton fixed-point map preserve the ρ-disk and contract by 1/2, so its holomorphic iterates converge uniformly to a bounded holomorphic local branch; the positive radicands and 1 + s in (19) stay a fixed distance from zero; complexified real squares are bilinear (w·w), never Hermitian
CONSTANT_SCOPE: ρ and η are fixed (depend only on (n, ν, 𝒜, δ))
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#real-margin, lpM:L7#kepler-equation, lpM:L8#compact-real-set, lpM:ext-holomorphic-limit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#real-margin | docs/tracks/LP/source/MAIN.md#L8@L263-L263 | the derivative bound 1 - e_*
EDGE: lpM:L7#kepler-equation | docs/tracks/LP/source/MAIN.md#L8@L263-L263 | the fixed-point map of (18)
EDGE: lpM:L8#compact-real-set | docs/tracks/LP/source/MAIN.md#L8@L263-L263 | uniformity over the compact real set
EDGE: lpM:ext-holomorphic-limit | docs/tracks/LP/source/MAIN.md#L8@L263-L263 | the uniform limit of the holomorphic iterates is holomorphic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L8#gluing
KIND: step
TITLE: glue local extensions on complex balls (identity theorem, finite subcover): single-valued on the angle torus
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L265-L265
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L265-L265
CONTRACT_ID: lpM:L8#gluing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅
SOURCE_QUANTIFIERS: for the fixed data
SOURCE_CONCLUSION: local extensions on complex balls centered at real points agree on intersections (convex, with a nonempty real part where both equal the real analytic map; power series and the identity theorem); translates of the angle cell patch the same way; a finite subcover of the compact real set with half-sized balls leaves a uniform complex neighborhood; the periodic chart and disturbing function are single-valued on the angle torus, independently of I^0 and μ
CONSTANT_SCOPE: the complex neighborhood is fixed (independent of I^0 and μ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#newton-extension, lpM:L8#compact-real-set, lpM:ext-identity-theorem, lpM:ext-compact-cover
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#newton-extension | docs/tracks/LP/source/MAIN.md#L8@L265-L265 | the local holomorphic extensions
EDGE: lpM:L8#compact-real-set | docs/tracks/LP/source/MAIN.md#L8@L265-L265 | the compact real set covered by finitely many balls
EDGE: lpM:ext-identity-theorem | docs/tracks/LP/source/MAIN.md#L8@L265-L265 | equality on the connected intersection
EDGE: lpM:ext-compact-cover | docs/tracks/LP/source/MAIN.md#L8@L265-L265 | a finite subcover of the compact real set
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L8#denominators
KIND: step
TITLE: Re(w.w) >= d^2/2 for every star and pair denominator; holomorphic square root, reciprocal <= sqrt 2/d
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L255-L255
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L267-L271
CONTRACT_ID: lpM:L8#denominators
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅; local data: d a common real lower bound of ¦q_i¦ and ¦q_i - q_j¦, Q a real upper bound
SOURCE_QUANTIFIERS: for every complex w within η_q of a real w_0
SOURCE_CONCLUSION: ¦w·w - ¦w_0¦^2¦ ≤ 2Qη_q + η_q^2 ≤ d^2/2 after reducing the neighborhood, so Re(w·w) ≥ d^2/2; the square root with positive real part and its reciprocal are holomorphic, the reciprocal bounded by √2/d; this applies to every star and pair denominator
CONSTANT_SCOPE: d, Q and η_q depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L5#pair-distances, lpM:L8#real-margin, lpM:L8#gluing, lpM:ext-cauchy-estimates
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L5#pair-distances | docs/tracks/LP/source/MAIN.md#L8@L267-L267 | the safe real phases have ¦q_i¦ ≥ d_⋆ and ¦q_i - q_j¦ ≥ d_pair: a common real lower bound d
EDGE: lpM:L8#real-margin | docs/tracks/LP/source/MAIN.md#L8@L267-L267 | the real phases are those of Lemma 5's compact set (bounded lengths Q)
EDGE: lpM:L8#gluing | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | the neighborhood being reduced
EDGE: lpM:ext-cauchy-estimates | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | the holomorphic square root with positive real part
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L8#widths
KIND: step
TITLE: Cauchy bounds on a smaller compact complex neighborhood; choice of r_*, s, b (r_* <= 4 r_g) and M
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L246-L255
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L271-L271
CONTRACT_ID: lpM:L8#widths
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21); 𝓛_δ ≠ ∅
SOURCE_QUANTIFIERS: for the fixed data
SOURCE_CONCLUSION: the chart and its derivatives are bounded on a smaller compact complex neighborhood (displayed formulas and Cauchy's one-variable estimates); f and its first derivatives have a uniform bound M; r_*, s, b are chosen so that (22) and a small enlargement lie inside this neighborhood
CONSTANT_SCOPE: r_*, s, b, M depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#gluing, lpM:L8#denominators, lpM:ext-cauchy-estimates, lpM:L8#shared-tube
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#gluing | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | the uniform complex neighborhood
EDGE: lpM:L8#denominators | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | f's denominators are holomorphic and bounded away from zero
EDGE: lpM:ext-cauchy-estimates | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | Cauchy's one-variable estimates for the derivatives
EDGE: lpM:L8#shared-tube | docs/tracks/LP/source/AMENDMENTS.md#N3@L12-L12 | N3: r_* ≤ 4r_g, so (22) lies within the 4r_g-tube data
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N3 (AMENDMENTS.md L12): r_* ≤ 4r_g is stated explicitly

NODE: lpM:L8#exact-split
KIND: step
TITLE: the product chart gives (4): chart Hamiltonian h(I) + mu f, no truncation
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L255-L255
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L8@L271-L271
CONTRACT_ID: lpM:L8#exact-split
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21)
SOURCE_QUANTIFIERS: for every μ > 0 and every point of (22)
SOURCE_CONCLUSION: the product of the Lemma 7 charts turns the Kepler part of (1) into h(I) = -Σ_i ν_i^3/(2I_i^2) of (4), so the chart Hamiltonian is exactly h(I) + μ f(I, λ, z)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7, lpM:s1:fast, lpM:s1:model
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7 | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | each planet's Kepler term has energy -ν_i^3/(2I_i^2) in the chart
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | h of (4)
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L8@L271-L271 | the splitting (1) H_μ = Σ Kepler terms + μ f
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
