NODE: lpM:L12
KIND: lemma
TITLE: Lemma 12: planetary scaling, exponential time and the drift (34)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L383-L399
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L405-L427
CONTRACT_ID: lpM:L12
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the uniform chart-domain statement of Lemma 8 holds with m canonical slow pairs; I^0 satisfies (5)
SOURCE_QUANTIFIERS: there are M_1, κ, μ_1, c > 0 (uniform in I^0); then for every 0 < μ ≤ μ_1, with r = √μ, a = 1/(2(τ+1)), N = ⌊κμ^{-a}⌋ ≥ 1, ε = M_1√μ, h_0 = h(I^0) + ω(I^0)·(I - I^0) (32), and every portion of an original solution
SOURCE_CONCLUSION: the normal form of Lemma 11 exists on the entire corresponding slow tube and H_μ∘Φ = h(J) + 𝒵(J, z) + R(J, θ, z), ∂_θ𝒵 = 0, ¦J̇¦_∞ ≤ rε2^{-N} along every transformed solution in D_2 (33); with T_μ = exp(cμ^{-a}), any portion of an original solution in D_1 of duration at most T_μ starting at action I^0 has ‖I(t) - I^0‖_∞ ≤ r/4 (34)
CONSTANT_SCOPE: M_1, κ, μ_1, c are uniform in I^0 and depend only on the fixed chart data and (γ, τ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L12#perturbation-size, lpM:L12#kappa-choice, lpM:L12#time-choice, lpM:L12#normal-form, lpM:L12#drift, lpM:s1:dioph, lpM:s1:fast
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L12#perturbation-size | docs/tracks/LP/source/MAIN.md#L12@L405-L405 | ‖X_{H_μ - h_0}‖_3 ≤ M_1√μ
EDGE: lpM:L12#kappa-choice | docs/tracks/LP/source/MAIN.md#L12@L407-L412 | κ, (36) implies (30), N and ε
EDGE: lpM:L12#time-choice | docs/tracks/LP/source/MAIN.md#L12@L414-L414 | c and T_μ ≤ 2^{N/2}
EDGE: lpM:L12#normal-form | docs/tracks/LP/source/MAIN.md#L12@L414-L414 | (33)
EDGE: lpM:L12#drift | docs/tracks/LP/source/MAIN.md#L12@L414-L420 | (34)
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#L12@L383-L383 | I^0 satisfies (5)
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#L12@L388-L388 | h and ω of (4) in h_0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Q5 (ruling root-b8) and AMENDED: N4 (AMENDMENTS.md L13): (35) (L400-L403, proof L420-L425) is a remark, not a formal dependency, and is omitted from these source fields; Lemma 8's conclusion is a premise (discharged at the application); alternative supplier of the stopped drift (N7): route lpM:L14#route-L12

NODE: lpM:L12#perturbation-size
KIND: step
TITLE: ¦¦X_{H_mu - h_0}¦¦_3 <= M_1 sqrt(mu): h - h_0 of size r, mu f of size mu/r + mu/s + mu/b
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L383-L389
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L405-L405
CONTRACT_ID: lpM:L12#perturbation-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L12: the uniform chart-domain statement of Lemma 8 with m slow pairs (widths r_*, s, b, bound M); I^0 satisfying (5); 0 < μ ≤ μ_1 and the choices (32)
SOURCE_QUANTIFIERS: for every I^0 and 0 < μ ≤ μ_1 (constants fixed first; inherited from lpM:L12)
SOURCE_CONCLUSION: after decreasing the widths of Lemma 8 (D_4 closures with uniform first-derivative bounds) and restricting μ_1 so that 4r < r_* and r ≤ 1, the scaled field of h - h_0 has only angle components (ω(I) - ω(I^0))/s = O(r), the scaled components of X_{μf} are O(μ/r + μ/s + μ/b), both O(√μ); the supremum-to-Fourier estimate of Lemma 9 (losing the fixed strip between D_4 and D_3) gives ‖X_{H_μ - h_0}‖_3 ≤ M_1√μ
CONSTANT_SCOPE: M_1 depends only on the fixed chart data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9, lpM:s1:fast, lpM:s1:model
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9 | docs/tracks/LP/source/MAIN.md#L12@L405-L405 | the supremum-to-Fourier estimate of Lemma 9, from D_4 to D_3
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#L12@L405-L405 | ω(I) - ω(I^0) is O(r) on the action tube
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L12@L405-L405 | H_μ = h + μ f in the chart (the perturbation f)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L12#kappa-choice
KIND: step
TITLE: (36): A M_1 kappa^{tau+1} <= q_D/2 implies (30); N >= kappa mu^{-a}/2, eps <= 1/8
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L407-L412
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L407-L412
CONTRACT_ID: lpM:L12#kappa-choice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L12: the uniform chart-domain statement of Lemma 8 with m slow pairs (widths r_*, s, b, bound M); I^0 satisfying (5); 0 < μ ≤ μ_1 and the choices (32)
SOURCE_QUANTIFIERS: for every I^0 and 0 < μ ≤ μ_1 (constants fixed first; inherited from lpM:L12)
SOURCE_CONCLUSION: choose κ > 0 with A M_1 κ^{τ+1} ≤ q_D/2 and 4L_ω κ^{τ+1} ≤ γ/2 (36), L_ω a complex Lipschitz bound of ω on the action neighborhood (∂_{I_i}ω_i = -3ν_i^3/I_i^4); since a(τ+1) = 1/2, (36) implies (30); decreasing μ_1 gives κμ^{-a} ≥ 2, N ≥ κμ^{-a}/2 and ε ≤ 1/8
CONSTANT_SCOPE: κ depends only on M_1, A, q_D, L_ω and γ (hence on the chart data and (γ, τ))
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L12#perturbation-size, lpM:L11, lpM:L10, lpM:s1:fast
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L12#perturbation-size | docs/tracks/LP/source/MAIN.md#L12@L408-L408 | M_1
EDGE: lpM:L11 | docs/tracks/LP/source/MAIN.md#L12@L412-L412 | (30) and q_D
EDGE: lpM:L10 | docs/tracks/LP/source/MAIN.md#L12@L408-L408 | A of (26)
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#L12@L412-L412 | ω and its Lipschitz bound L_ω
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the second restriction of (36) serves only (35), which Q5/N4 omit

NODE: lpM:L12#time-choice
KIND: step
TITLE: c = (log 2) kappa/4, so T_mu = exp(c mu^{-a}) <= 2^{N/2}
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L396-L396
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L414-L414
CONTRACT_ID: lpM:L12#time-choice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L12: the uniform chart-domain statement of Lemma 8 with m slow pairs (widths r_*, s, b, bound M); I^0 satisfying (5); 0 < μ ≤ μ_1 and the choices (32)
SOURCE_QUANTIFIERS: for every I^0 and 0 < μ ≤ μ_1 (constants fixed first; inherited from lpM:L12)
SOURCE_CONCLUSION: with c = (log 2)κ/4 and N ≥ κμ^{-a}/2, T_μ = exp(cμ^{-a}) ≤ 2^{N/2}
CONSTANT_SCOPE: c depends only on κ
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L12#kappa-choice
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L12#kappa-choice | docs/tracks/LP/source/MAIN.md#L12@L414-L414 | N ≥ κμ^{-a}/2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L12#normal-form
KIND: step
TITLE: Lemma 11 with eps = M_1 sqrt(mu), N; Z := h_0 - h + Z gives (33) and ¦dJ/dt¦ <= r eps 2^{-N}
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L390-L395
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L414-L414
CONTRACT_ID: lpM:L12#normal-form
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L12: the uniform chart-domain statement of Lemma 8 with m slow pairs (widths r_*, s, b, bound M); I^0 satisfying (5); 0 < μ ≤ μ_1 and the choices (32)
SOURCE_QUANTIFIERS: for every I^0 and 0 < μ ≤ μ_1 (constants fixed first; inherited from lpM:L12)
SOURCE_CONCLUSION: Lemma 11 applies on the entire slow tube with ε, N of (32); 𝒵 := h_0 - h + Z is independent of θ, so (31) becomes (33), and ‖X_R‖_2 ≤ ε2^{-N} gives ¦J̇¦_∞ ≤ rε2^{-N} along every transformed solution in D_2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L11, lpM:L12#kappa-choice, lpM:L12#perturbation-size
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L11 | docs/tracks/LP/source/MAIN.md#L12@L414-L414 | the normal form Φ and (31)
EDGE: lpM:L12#kappa-choice | docs/tracks/LP/source/MAIN.md#L12@L412-L412 | (30) holds
EDGE: lpM:L12#perturbation-size | docs/tracks/LP/source/MAIN.md#L12@L405-L405 | ‖X_F‖_3 ≤ ε with F = H_μ - h_0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L12#drift
KIND: step
TITLE: (34): transformed solution in D_2, integrate (33), errors r/16 + r/16: ¦¦I(t) - I^0¦¦ <= r/4
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L396-L399
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L12@L414-L420
CONTRACT_ID: lpM:L12#drift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L12: the uniform chart-domain statement of Lemma 8 with m slow pairs (widths r_*, s, b, bound M); I^0 satisfying (5); 0 < μ ≤ μ_1 and the choices (32); a portion of an original solution in D_1 of duration ≤ T_μ starting at I^0
SOURCE_QUANTIFIERS: for every I^0 and 0 < μ ≤ μ_1 (constants fixed first; inherited from lpM:L12); both signs of t
SOURCE_CONCLUSION: the inverse of Lemma 11 maps the original solution to a transformed solution inside D_2, which solves the transformed Hamilton equations by symplecticity; integrating (33) with the forward error at t and the inverse error at 0 gives ‖I(t) - I^0‖_∞ ≤ r/16 + rε¦t¦2^{-N} + r/16 ≤ r/8 + rε2^{-N/2} ≤ r/4, for both signs of t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L12#normal-form, lpM:L11, lpM:L12#time-choice
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L12#normal-form | docs/tracks/LP/source/MAIN.md#L12@L414-L414 | (33) along transformed solutions
EDGE: lpM:L11 | docs/tracks/LP/source/MAIN.md#L12@L414-L414 | the inverse on D_{3/2} and the action errors ≤ r/16
EDGE: lpM:L12#time-choice | docs/tracks/LP/source/MAIN.md#L12@L418-L418 | ¦t¦ ≤ T_μ ≤ 2^{N/2}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L13
KIND: lemma
TITLE: Lemma 13: checked reuse of the repository's finite-cutoff engine (nonresonant)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L431-L431
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L433-L464
CONTRACT_ID: lpM:L13
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfies (5)
SOURCE_QUANTIFIERS: for every fixed D_0 > 0 there are κ_1, c_1 > 0 and a smallness threshold for μ (uniform in I^0); then for every small μ > 0, with r = D_0√μ, K = ⌊κ_1μ^{-a}⌋, and every physical orbit starting at action I^0
SOURCE_CONCLUSION: the data can be fed to KAM.Nekhoroshev.nonresonant with the full center-dependent slow ball S = (21), radius r = D_0√μ, cutoff K ≍ μ^{-a} and a fixed slow collar; its stopped action estimate gives ‖I(t) - I^0‖_∞ ≤ r/2 for ¦t¦ ≤ exp(c_1μ^{-a}) provided the physical slow coordinates belong to S through the queried time (the same exponent a as Lemma 12)
CONSTANT_SCOPE: κ_1, c_1 and the μ threshold depend only on the fixed chart data, (γ, τ) and D_0
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L13#interface, lpM:L13#period-one, lpM:L13#numeric-hypotheses, lpM:L13#structural-hypotheses, lpM:L13#conclusion, lpM:s1:dioph
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L13#interface | docs/tracks/LP/source/MAIN.md#L13@L433-L433 | the slow set S of nonresonant is arbitrary: take the ball (21)
EDGE: lpM:L13#period-one | docs/tracks/LP/source/MAIN.md#L13@L435-L440 | the period-one conversion
EDGE: lpM:L13#numeric-hypotheses | docs/tracks/LP/source/MAIN.md#L13@L442-L457 | the numeric hypotheses (37)
EDGE: lpM:L13#structural-hypotheses | docs/tracks/LP/source/MAIN.md#L13@L458-L458 | the structural hypotheses
EDGE: lpM:L13#conclusion | docs/tracks/LP/source/MAIN.md#L13@L460-L464 | the drift ≤ r/2 through (38)
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#L13@L431-L431 | I^0 satisfies (5) (the nonresonance at I^0)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Lemma 8's conclusion is a premise (discharged at the application); alternative supplier of the stopped drift (N7): route lpM:L14#route-L13, the Lean route. The repository citation (L433) is consumed only through the IMPORTED node N:bpN:p11:nonresonant. AMENDED: N6 (AMENDMENTS.md L15): widths 2πs_1 < 4s with a convergence margin, w < 4b, D_0√μ < r_*, J the stopped interval of Lemma 14; stopped radius r = D_0√μ and improvement to r/2

NODE: lpM:L13#interface
KIND: step
TITLE: nonresonant's real slow set S is arbitrary: take S = the closed ball (21)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L431-L431
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L433-L433
CONTRACT_ID: lpM:L13#interface
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L13: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfying (5); a fixed D_0 > 0; r = D_0√μ, K = ⌊κ_1 μ^{-a}⌋
SOURCE_QUANTIFIERS: for every I^0 and small μ > 0 (constants fixed first; inherited from lpM:L13)
SOURCE_CONCLUSION: the normal-form input of nonresonant leaves the real slow set S arbitrary; S is taken to be the closed ball (21), not a neighborhood of the starting secular point
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p11:nonresonant
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p11:nonresonant | docs/tracks/LP/source/MAIN.md#L13@L433-L433 | the interface of the imported theorem (arbitrary slow set S)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L13#period-one
KIND: step
TITLE: theta = lambda/(2 pi), slow rescaling ell = w/r, H-hat = H/(2 pi); bracket 2 pi/ell^2; same equations and time
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L435-L440
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L435-L440
CONTRACT_ID: lpM:L13#period-one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L13: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfying (5); a fixed D_0 > 0; r = D_0√μ, K = ⌊κ_1 μ^{-a}⌋; local data θ = λ/(2π), ℓ = w/r, z̃ = z/ℓ
SOURCE_QUANTIFIERS: for every I^0 and small μ > 0 (constants fixed first; inherited from lpM:L13)
SOURCE_CONCLUSION: Ĥ(θ, I, z̃) = H(2πθ, I, ℓz̃)/(2π) with the weighted slow bracket coefficient c_s = 2π/ℓ^2 gives θ̇ = H_I/(2π), İ = -H_λ, dz̃/dt = J H_z/ℓ: exactly the original equations, in unchanged time; the unperturbed frequencies are ω/(2π); (ξ, η) = (x, -y) planar and (u, -v) for the spatial node pair give the repository's slow bracket
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:model, lpM:s1:fast
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L13@L440-L440 | the symplectic form Σ dp ∧ dq and ι_{X_H}Ω = -dH of (1)
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#L13@L440-L440 | the frequencies ω of (4)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L13#numeric-hypotheses
KIND: step
TITLE: (37): K L r <= alpha/2, eps <= alpha r/(256 K), 64 pi m s_1 r <= w^2, 2 pi K s_1 >= 6
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L442-L452
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L442-L457
CONTRACT_ID: lpM:L13#numeric-hypotheses
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L13: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfying (5); a fixed D_0 > 0; r = D_0√μ, K = ⌊κ_1 μ^{-a}⌋; fixed period-one strip s_1 > 0 and slow width w > 0; p = q = 2
SOURCE_QUANTIFIERS: for every I^0 and small μ > 0 (constants fixed first; inherited from lpM:L13)
SOURCE_CONCLUSION: the scalar Fourier bound ε = M_2μ holds uniformly (the contour estimate of Lemma 9 applied to f/(2π)); with α = γK^{-τ}/(2π), K = ⌊κ_1μ^{-a}⌋, r = D_0√μ, the non-geometric numeric hypotheses of ExtNFHyp and nonresonant are KLr ≤ α/2, ε ≤ αr/(256K), 64πm s_1 r ≤ w^2, 2πKs_1 ≥ 6 (37); the first two follow from LD_0κ_1^{τ+1} ≤ γ/(4π) and M_2κ_1^{τ+1} ≤ γD_0/(512π), the last two by decreasing μ_0
CONSTANT_SCOPE: κ_1 depends only on L, M_2, γ, τ and D_0
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9, lpM:L13#period-one, lpM:s1:dioph, lpM:s1:fast
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9 | docs/tracks/LP/source/MAIN.md#L13@L442-L442 | the contour estimate of Lemma 9 applied to f/(2π) gives ε = M_2μ
EDGE: lpM:L13#period-one | docs/tracks/LP/source/MAIN.md#L13@L442-L442 | the period-one Hamiltonian f/(2π) and frequencies ω/(2π)
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#L13@L444-L444 | (5) gives ¦k·ω(I^0)/(2π)¦ ≥ α for 0 < ¦k¦_1 ≤ K
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#L13@L442-L442 | L bounds the complex frequency derivative of h/(2π)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N6 (AMENDMENTS.md L15): widths 2πs_1 < 4s with a convergence margin, w < 4b, D_0√μ < r_*, J the stopped interval of Lemma 14; stopped radius r = D_0√μ and improvement to r/2

NODE: lpM:L13#structural-hypotheses
KIND: step
TITLE: holomorphy, reality, periodicity, Fourier norm, widths, module {0}, tube inside (22), orbit-field equality
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L458-L458
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L458-L458
CONTRACT_ID: lpM:L13#structural-hypotheses
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L13: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfying (5); a fixed D_0 > 0; r = D_0√μ, K = ⌊κ_1 μ^{-a}⌋
SOURCE_QUANTIFIERS: for every I^0 and small μ > 0 (constants fixed first; inherited from lpM:L13)
SOURCE_CONCLUSION: holomorphy, reality, periodicity, the weighted Fourier norm, positivity of widths and perturbation bound, and the dimension hypotheses follow from Lemma 8's data and n ≥ 2, m ≥ 1; the nonresonance module is {0} (symmetric); the rescaled slow tube has physical width w (ℓr = w), not shrinking with μ; the finite action tube lies in (22) for small μ; the computed equations give the literal orbit-field equality; the initial fast action is the center
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L13#period-one, lpM:s1:data
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L13#period-one | docs/tracks/LP/source/MAIN.md#L13@L458-L458 | the computed equations in the new coordinates
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#L13@L458-L458 | n ≥ 2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L13#conclusion
KIND: step
TITLE: (38): drift <= r/2 through (s_1 r/(5 eps)) exp(2 pi K s_1/6) >= exp(c_1 mu^{-a}) under stopped slow membership
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L460-L463
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L13@L460-L464
CONTRACT_ID: lpM:L13#conclusion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L13: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfying (5); a fixed D_0 > 0; r = D_0√μ, K = ⌊κ_1 μ^{-a}⌋
SOURCE_QUANTIFIERS: for every I^0 and small μ > 0 (constants fixed first; inherited from lpM:L13); every queried time t_1
SOURCE_CONCLUSION: nonresonant gives ‖I(t) - I^0‖_∞ ≤ r/2 through (s_1r/(5ε)) exp(2πKs_1/6) (38), provided the physical slow coordinates belong to S up to the queried time; since K ≥ κ_1μ^{-a}/2 for small μ, (38) exceeds exp(c_1μ^{-a}) for a fixed c_1 > 0; the stopped membership is discharged by Lemma 14
CONSTANT_SCOPE: c_1 depends only on κ_1, s_1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p11:nonresonant, lpM:L13#numeric-hypotheses, lpM:L13#structural-hypotheses, lpM:L13#interface
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p11:nonresonant | docs/tracks/LP/source/MAIN.md#L13@L460-L460 | the conclusion of nonresonant: drift ≤ r/2 through T_nr = (s_1r/(5ε))e^{κ/6}
EDGE: lpM:L13#numeric-hypotheses | docs/tracks/LP/source/MAIN.md#L13@L460-L460 | (37) supplies its numeric hypotheses
EDGE: lpM:L13#structural-hypotheses | docs/tracks/LP/source/MAIN.md#L13@L460-L460 | its structural hypotheses
EDGE: lpM:L13#interface | docs/tracks/LP/source/MAIN.md#L13@L460-L460 | S is the ball (21)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: the closing sentences on nnf_disp_radius (slow displacement ≤ w/2^{10}) and on the independent paper proof are a check, not a premise of the drift conclusion; no edge
