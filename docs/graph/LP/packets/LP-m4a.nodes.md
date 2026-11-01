NODE: lpM:L9
KIND: lemma
TITLE: Lemma 9: Fourier, Cauchy and commutator estimates in the norm (24)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L279-L296
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L298-L304
CONTRACT_ID: lpM:L9
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; the domains D_ρ (23) and the norm (24) with D = 2n + 2m
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4, every loss 0 < σ < ρ - 1, all periodic holomorphic vector fields V, W and every K
SOURCE_CONCLUSION: norms are monotone under restriction; the mean and complementary Fourier projections have norm at most one; ‖[V,W]‖_{ρ-σ} ≤ (2D/σ)‖V‖_ρ‖W‖_ρ (25); the Fourier tail with ¦k¦_1 > K on a strip narrowed by σs has norm at most e^{-σsK}‖V‖_ρ; a uniform supremum bound for V̂ on D_4 gives a finite bound on ‖V‖_3 depending only on that bound, n and s
CONSTANT_SCOPE: the bound on ‖V‖_3 depends only on the supremum bound, n and s
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9#domains, lpM:L9#norm, lpM:L9#sup-to-fourier, lpM:L9#commutator, lpM:L9#projections-tail
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9#domains | docs/tracks/LP/source/MAIN.md#L9@L279-L284 | the domains (23)
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L9@L285-L291 | the norm (24)
EDGE: lpM:L9#sup-to-fourier | docs/tracks/LP/source/MAIN.md#L9@L298-L299 | the supremum-to-Fourier bound
EDGE: lpM:L9#commutator | docs/tracks/LP/source/MAIN.md#L9@L302-L304 | (25)
EDGE: lpM:L9#projections-tail | docs/tracks/LP/source/MAIN.md#L9@L304-L304 | monotonicity, projections and the tail
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L9#domains
KIND: definition
TITLE: the complex domains D_rho (23): action, angle-strip and slow max-norm tube
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L279-L285
PROOF_SOURCE: -
CONTRACT_ID: lpM:L9#domains
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; I^0
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4
SOURCE_CONCLUSION: D_ρ = {‖I - I^0‖_∞ < ρr, ¦Im θ¦_∞ < ρs, dist_∞(z, Z) < ρb} (23); the slow tube uses the maximum norm and Z need not be a polydisk; Hamiltonian fields use the standard constant symplectic form in (I, θ, z), with blocks rs and b^2 after scaling
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L9#norm
KIND: definition
TITLE: scaled components and the weighted Fourier norm (24)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L285-L291
PROOF_SOURCE: -
CONTRACT_ID: lpM:L9#norm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the domains D_ρ (lpM:L9#domains); D = 2n + 2m
SOURCE_QUANTIFIERS: for every periodic holomorphic vector field V and 1 ≤ ρ ≤ 4
SOURCE_CONCLUSION: V̂ = (V_I/r, V_θ/s, V_z/b) and ‖V‖_ρ = Σ_{k ∈ ℤ^n} sup_{‖I - I^0‖ < ρr, dist(z,Z) < ρb} ¦V̂_k(I,z)¦_∞ e^{ρs¦k¦_1} (24)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9#domains
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9#domains | docs/tracks/LP/source/MAIN.md#L9@L289-L289 | the supremum runs over the action and slow parts of D_ρ
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L9#sup-to-fourier
KIND: step
TITLE: contour shift: a sup bound M on width 4s gives ¦V_k¦ <= M e^{-4s¦k¦_1}, hence ¦¦V¦¦_3 <= M((1+e^{-s})/(1-e^{-s}))^n
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L296-L296
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L298-L299
CONTRACT_ID: lpM:L9#sup-to-fourier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L9: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; D = 2n + 2m; the domains D_ρ (23) and the norm (24)
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4, 0 < σ < ρ - 1 and periodic holomorphic vector fields V, W (inherited from lpM:L9)
SOURCE_CONCLUSION: a supremum bound M for V̂ on D_4 gives coefficient bound M e^{-4s¦k¦_1} on the parameter domain of D_3 (limits from narrower contours), and summing at width 3s gives ‖V‖_3 ≤ M Σ_k e^{-s¦k¦_1} = M((1 + e^{-s})/(1 - e^{-s}))^n
CONSTANT_SCOPE: the bound depends only on M, n and s
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:ext-fourier-contour, lpM:L9#norm, lpM:L9#domains
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:ext-fourier-contour | docs/tracks/LP/source/MAIN.md#L9@L298-L298 | Fourier coefficients as torus integrals and the contour shift
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L9@L299-L299 | summing the coefficients in the norm (24)
EDGE: lpM:L9#domains | docs/tracks/LP/source/MAIN.md#L9@L298-L298 | the strip of width 4s of D_4
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L9#banach-algebra
KIND: step
TITLE: products have convolution coefficients: the Banach-algebra estimate
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L300-L300
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L300-L300
CONTRACT_ID: lpM:L9#banach-algebra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L9: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; D = 2n + 2m; the domains D_ρ (23) and the norm (24)
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4, 0 < σ < ρ - 1 and periodic holomorphic vector fields V, W (inherited from lpM:L9)
SOURCE_CONCLUSION: products of Fourier series have convolution coefficients and ¦k + l¦_1 ≤ ¦k¦_1 + ¦l¦_1, so the weighted norm is submultiplicative; absolute convergence on smaller domains justifies multiplication and differentiation
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9#norm
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L9@L300-L300 | the weights e^{ρs¦k¦_1} of (24)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L9#cauchy-derivative
KIND: step
TITLE: Cauchy: derivative bound 1/sigma in scaled action and slow coordinates; angle factor 1/(e sigma)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L302-L303
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L302-L303
CONTRACT_ID: lpM:L9#cauchy-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L9: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; D = 2n + 2m; the domains D_ρ (23) and the norm (24)
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4, 0 < σ < ρ - 1 and periodic holomorphic vector fields V, W (inherited from lpM:L9)
SOURCE_CONCLUSION: a complex disk of radius σr or σb about a point of D_{ρ-σ} lies in D_ρ (triangle inequality for dist to Z), so Cauchy's formula gives derivative bound 1/σ in scaled coordinates; for angles s¦k_j¦e^{-σs¦k¦_1} ≤ 1/(eσ)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:ext-cauchy-estimates, lpM:L9#domains, lpM:L9#norm
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:ext-cauchy-estimates | docs/tracks/LP/source/MAIN.md#L9@L302-L302 | Cauchy's formula on the disks
EDGE: lpM:L9#domains | docs/tracks/LP/source/MAIN.md#L9@L302-L302 | the disks lie in the larger tube
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L9@L303-L303 | the angle derivative acts on the weights of (24)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L9#commutator
KIND: display
TITLE: (25): ¦¦[V,W]¦¦_{rho-sigma} <= (2D/sigma) ¦¦V¦¦_rho ¦¦W¦¦_rho
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L292-L295
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L302-L304
CONTRACT_ID: lpM:L9#commutator
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L9: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; D = 2n + 2m; the domains D_ρ (23) and the norm (24)
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4, 0 < σ < ρ - 1 and periodic holomorphic vector fields V, W (inherited from lpM:L9)
SOURCE_CONCLUSION: each of the D terms in a component of DV W - DW V is bounded by the product of the norms divided by σ, giving ‖[V,W]‖_{ρ-σ} ≤ (2D/σ)‖V‖_ρ‖W‖_ρ (25)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9#cauchy-derivative, lpM:L9#banach-algebra
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9#cauchy-derivative | docs/tracks/LP/source/MAIN.md#L9@L304-L304 | the derivative bounds 1/σ and 1/(eσ)
EDGE: lpM:L9#banach-algebra | docs/tracks/LP/source/MAIN.md#L9@L304-L304 | products of the derivative and the field
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L9#projections-tail
KIND: step
TITLE: monotonicity; mean and complementary projections have norm <= 1; tail bound e^{-sigma s K}
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L292-L296
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L9@L304-L304
CONTRACT_ID: lpM:L9#projections-tail
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L9: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; D = 2n + 2m; the domains D_ρ (23) and the norm (24)
SOURCE_QUANTIFIERS: for every 1 ≤ ρ ≤ 4, 0 < σ < ρ - 1 and periodic holomorphic vector fields V, W (inherited from lpM:L9)
SOURCE_CONCLUSION: norms are monotone under restriction; removing the zero coefficient proves that the mean and complementary Fourier projections have norm at most one; extracting e^{-σsK} bounds the tail with ¦k¦_1 > K on the strip narrowed by σs by e^{-σsK}‖V‖_ρ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9#norm
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L9@L304-L304 | the norm (24) is a weighted sum over k
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L10
KIND: lemma
TITLE: Lemma 10: cohomological equation (26) and a controlled Lie step (27)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L308-L321
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L323-L349
CONTRACT_ID: lpM:L10
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of lpM:L9 (n, m, Z, r, b, s); ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ
SOURCE_QUANTIFIERS: for every such H and every loss 0 < σ < ρ - 1; constants c_D, B_D > 0 depending only on D are fixed first
SOURCE_CONCLUSION: there is a Hamiltonian generator χ, real on real points, with ω·∂_θχ = f - ⟨f⟩ and ‖X_χ‖_{ρ-σ/2} ≤ Aσ^{-τ}E =: u, A = γ^{-1} max{1, (2τ/(es))^τ} (26); if u/σ ≤ c_D its time-one map φ is holomorphic, real, symplectic and periodic-equivariant on D_{ρ-σ}, with H∘φ = h_0 + g + ⟨f⟩ + f_+ and ‖X_{f_+}‖_{ρ-σ} ≤ B_D (u/σ)(G + E) (27); the map and the negative-time map move points by at most u in scaled coordinates where the collar is available, their derivatives differ from the identity by at most a dimension constant times u/σ on a further half-collar, and they are mutual inverses on their common inner domain
CONSTANT_SCOPE: c_D, B_D depend only on D; the constants do not depend on r, b, Z, I^0 or the coefficients of the scaled symplectic form
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L10#homological, lpM:L10#flow-existence, lpM:L10#remainder, lpM:L9#norm, lpM:s1:dioph
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L10#homological | docs/tracks/LP/source/MAIN.md#L10@L323-L328 | the generator χ and (26)
EDGE: lpM:L10#flow-existence | docs/tracks/LP/source/MAIN.md#L10@L340-L340 | the time-one map, its displacement, inverse and symplecticity
EDGE: lpM:L10#remainder | docs/tracks/LP/source/MAIN.md#L10@L342-L349 | the exact remainder (29) and (27)
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L10@L308-L308 | the norms ‖X_f‖_ρ of (24)
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#L10@L308-L308 | ω satisfies the Diophantine condition (5)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L10#homological
KIND: step
TITLE: chi_k = f_k/(i k.omega): (26), the scalar series and reality
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L309-L314
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L323-L328
CONTRACT_ID: lpM:L10#homological
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L10: the setting of lpM:L9; ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ; a loss 0 < σ < ρ - 1
SOURCE_QUANTIFIERS: for every such H and loss σ (inherited from lpM:L10)
SOURCE_CONCLUSION: χ_0 = 0 and χ_k = f_k/(ik·ω) for k ≠ 0; the Fourier coefficients of X_χ are those of X_f divided by ik·ω; with ¦k¦_1^τ e^{-σs¦k¦_1/2} ≤ (2τ/(eσs))^τ this gives (26); the scalar series exists (a fast action component of X_f equals -ik_j f_k); f_{-k} = conj(f_k) gives the same relation for χ (reality)
CONSTANT_SCOPE: A = γ^{-1} max{1, (2τ/(es))^τ}
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:dioph, lpM:L9#norm
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#L10@L323-L323 | (5): ¦ik·ω¦ ≥ γ¦k¦_1^{-τ} for k ≠ 0
EDGE: lpM:L9#norm | docs/tracks/LP/source/MAIN.md#L10@L325-L325 | the coefficients are weighted as in (24) on the narrowed strip
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L10#lie-series-bound
KIND: display
TITLE: (28): (1/j!)¦¦ad_Y^j V¦¦_{rho-eta} <= (2eDu/eta)^j ¦¦V¦¦_rho
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L330-L336
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L330-L336
CONTRACT_ID: lpM:L10#lie-series-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L10: the setting of lpM:L9; ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ; a loss 0 < σ < ρ - 1; a holomorphic field Y of norm u on a larger domain; a collar η
SOURCE_QUANTIFIERS: for every such H and loss σ (inherited from lpM:L10); for every j ≥ 1
SOURCE_CONCLUSION: repeated application of (25), dividing the collar η into j equal parts, gives (1/j!)‖ad_Y^j V‖_{ρ-η} ≤ (j^j/j!)(2Du/η)^j‖V‖_ρ ≤ (2eDu/η)^j‖V‖_ρ (28), using j! ≥ (j/e)^j; the Lie series converges when 2eDu/η < 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L9#commutator
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L9#commutator | docs/tracks/LP/source/MAIN.md#L10@L331-L331 | (25) applied j times with loss η/j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L10#lie-flow-identification
KIND: step
TITLE: the Lie series represents the pullback by the flow; exact scalar identity
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L315-L321
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L336-L338
CONTRACT_ID: lpM:L10#lie-flow-identification
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L10: the setting of lpM:L9; ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ; a loss 0 < σ < ρ - 1; 4eDu/σ ≤ 1/4
SOURCE_QUANTIFIERS: for every such H and loss σ (inherited from lpM:L10)
SOURCE_CONCLUSION: the Lie series of the pullback converges and equals the pullback by the actual flow (the flow solves the integral equation, its derivative the variational equation, and differentiating the pullback gives the commutator equation); the scalar series converges after its first bracket (a scalar bracket is bounded by D max(rs, b^2)‖X_F‖‖X_χ‖); trajectories from D_{ρ-σ} stay in D_{ρ-3σ/4}, and the Taylor remainders have geometric ratio ≤ 8eDu/σ ≤ 1/2, proving the exact scalar identity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L10#lie-series-bound, lpM:L10#flow-existence
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L10#lie-series-bound | docs/tracks/LP/source/MAIN.md#L10@L336-L338 | (28) bounds the iterated brackets and the remainders
EDGE: lpM:L10#flow-existence | docs/tracks/LP/source/MAIN.md#L10@L336-L338 | the actual flow exists and moves points by at most u
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: AMENDED N5 (AMENDMENTS.md L14): MAIN only sketches the flow existence, the Lie-series identification and the choice of c_D; they matter only for the optional packages 9-11 (route lpM:L14#route-L12), not for the Lean route through Lemma 13

NODE: lpM:L10#flow-existence
KIND: step
TITLE: the flow exists for ¦t¦ <= 1: contraction on paths, holomorphy, inverse, reality, displacement, symplecticity
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L315-L321
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L340-L340
CONTRACT_ID: lpM:L10#flow-existence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L10: the setting of lpM:L9; ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ; a loss 0 < σ < ρ - 1; u a sufficiently small multiple of the collar
SOURCE_QUANTIFIERS: for every such H and loss σ (inherited from lpM:L10); both signs of time up to one
SOURCE_CONCLUSION: in a scaled ball about any starting point of the inner domain, Cauchy bounds DY by a dimension constant times u/η; the integral map on continuous paths stays in the ball and contracts, its iterates converge uniformly (holomorphic dependence, also for complex initial values); uniqueness gives the inverse, reality and lattice equivariance; displacement ≤ u and ‖Dφ - 1‖ ≤ e^{C_D u/η} - 1 ≤ 2C_D u/η; (DY)^T Ω + Ω DY = 0 gives symplecticity, for any constant nondegenerate Ω; c_D is decreased so that these estimates hold
CONSTANT_SCOPE: C_D and c_D depend only on D
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L10#homological, lpM:ext-cauchy-estimates, lpM:ext-picard, lpM:ext-holomorphic-limit, lpM:ext-gronwall
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L10#homological | docs/tracks/LP/source/MAIN.md#L10@L340-L340 | the generator χ with ‖X_χ‖ ≤ u
EDGE: lpM:ext-cauchy-estimates | docs/tracks/LP/source/MAIN.md#L10@L340-L340 | Cauchy's estimate for DY
EDGE: lpM:ext-picard | docs/tracks/LP/source/MAIN.md#L10@L340-L340 | the integral map on continuous paths is a contraction (Picard iteration)
EDGE: lpM:ext-holomorphic-limit | docs/tracks/LP/source/MAIN.md#L10@L340-L340 | uniform limits of the holomorphic iterates are holomorphic
EDGE: lpM:ext-gronwall | docs/tracks/LP/source/MAIN.md#L10@L340-L340 | uniqueness of the flow gives the inverse, reality and equivariance
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: AMENDED N5 (AMENDMENTS.md L14): MAIN only sketches the flow existence, the Lie-series identification and the choice of c_D; they matter only for the optional packages 9-11 (route lpM:L14#route-L12), not for the Lean route through Lemma 13

NODE: lpM:L10#remainder
KIND: step
TITLE: L_chi h_0 = -f^osc and the exact remainder (29); (27) with B_D = 16eD
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L316-L320
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L10@L342-L349
CONTRACT_ID: lpM:L10#remainder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L10: the setting of lpM:L9; ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ; a loss 0 < σ < ρ - 1; v = 4eDu/σ ≤ 1/4
SOURCE_QUANTIFIERS: for every such H and loss σ (inherited from lpM:L10)
SOURCE_CONCLUSION: with L_χF = {F, χ}, L_χ h_0 = -(f - ⟨f⟩); the exact remainder is f_+ = Σ_{j≥1} L_χ^j(g + f)/j! - Σ_{j≥1} L_χ^j f^osc/(j+1)! (29); each bracket is a vector-field commutator, so (28) with η = σ/2 bounds the two sums by v(1 - v)^{-1}(G + 2E) ≤ 4v(G + E), proving (27) with B_D = 16eD; the field X_{h_0} disappears through the homological identity
CONSTANT_SCOPE: B_D = 16eD
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L10#homological, lpM:L10#lie-series-bound, lpM:L10#lie-flow-identification
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L10#homological | docs/tracks/LP/source/MAIN.md#L10@L342-L342 | ω·∂_θχ = f - ⟨f⟩ gives L_χ h_0 = -f^osc
EDGE: lpM:L10#lie-series-bound | docs/tracks/LP/source/MAIN.md#L10@L347-L347 | (28) with η = σ/2
EDGE: lpM:L10#lie-flow-identification | docs/tracks/LP/source/MAIN.md#L10@L349-L349 | H∘φ equals the Lie series (exact scalar identity)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: AMENDED: N5 (AMENDMENTS.md L14): c_D is only implicit ('decreased to satisfy the flow estimates')

NODE: lpM:L11
KIND: lemma
TITLE: Lemma 11: exponential normal form on the full slow set (30)-(31)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L353-L363
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L365-L379
CONTRACT_ID: lpM:L11
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1
SOURCE_QUANTIFIERS: a number q_D > 0 depending only on D is fixed first; then for every such H, ε, N with A ε N^{τ+1} ≤ q_D (30)
SOURCE_CONCLUSION: there is a real holomorphic symplectic map Φ : D_2 → D_3 with H∘Φ = h_0 + Z + R, ∂_θZ = 0, ‖X_R‖_2 ≤ ε2^{-N}, ‖X_Z‖_2 ≤ 2ε (31); its scaled displacement is at most 1/16; its inverse exists on D_{3/2}, takes values in D_2 and has the same displacement bound, so the two action-coordinate errors are at most r/16; this holds on the entire tube around Z, with no restriction on the slow dynamics
CONSTANT_SCOPE: q_D depends only on D
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L11#qD-choice, lpM:L11#induction, lpM:L11#composition, lpM:L11#inverse
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L11#qD-choice | docs/tracks/LP/source/MAIN.md#L11@L371-L375 | q_D and the validity of each step under (30)
EDGE: lpM:L11#induction | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | the estimates E_j ≤ ε2^{-j}, ‖X_{g_j}‖ ≤ 2ε
EDGE: lpM:L11#composition | docs/tracks/LP/source/MAIN.md#L11@L375-L379 | Φ, (31) and the displacement 1/32 < 1/16
EDGE: lpM:L11#inverse | docs/tracks/LP/source/MAIN.md#L11@L379-L379 | the inverse on D_{3/2}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L11#step-estimate
KIND: step
TITLE: one Lie step with loss 1/N: u_j <= A N^tau eps 2^{-j}, E_{j+1} <= 3 B_D A eps N^{tau+1} E_j
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L365-L370
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L365-L370
CONTRACT_ID: lpM:L11#step-estimate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L11: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1 with A ε N^{τ+1} ≤ q_D (30); local data ρ_j = 3 - j/N, g_0 = 0, f_0 = F; E_j ≤ ε2^{-j}, G_j ≤ 2ε at step j
SOURCE_QUANTIFIERS: for every such H, ε and N (inherited from lpM:L11); every j < N
SOURCE_CONCLUSION: Lemma 10 with σ = 1/N on ρ_j gives u_j ≤ A N^τ ε 2^{-j} and E_{j+1} ≤ 3B_D A ε N^{τ+1} E_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L10
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L10 | docs/tracks/LP/source/MAIN.md#L11@L365-L370 | Lemma 10 with loss σ = 1/N on D_{ρ_j}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L11#qD-choice
KIND: step
TITLE: q_D = min(c_D, 1/(6 B_D), 1/64): (30) validates every step and halves E_j
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L371-L374
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L371-L375
CONTRACT_ID: lpM:L11#qD-choice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L11: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1 with A ε N^{τ+1} ≤ q_D (30); local data ρ_j = 3 - j/N, g_0 = 0, f_0 = F
SOURCE_QUANTIFIERS: for every such H, ε and N (inherited from lpM:L11)
SOURCE_CONCLUSION: with q_D = min(c_D, 1/(6B_D), 1/64), condition (30) gives u_j/σ ≤ c_D (the step is valid) and E_{j+1} ≤ E_j/2
CONSTANT_SCOPE: q_D depends only on D
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L11#step-estimate, lpM:L10
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L11#step-estimate | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | the step estimates
EDGE: lpM:L10 | docs/tracks/LP/source/MAIN.md#L11@L373-L373 | the constants c_D and B_D of Lemma 10
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L11#induction
KIND: step
TITLE: g_{j+1} = g_j + <f_j>: ¦X_g¦ <= 2 eps, angle independent; induction on j
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L375-L375
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L375-L375
CONTRACT_ID: lpM:L11#induction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L11: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1 with A ε N^{τ+1} ≤ q_D (30); local data ρ_j = 3 - j/N, g_0 = 0, f_0 = F
SOURCE_QUANTIFIERS: for every such H, ε and N (inherited from lpM:L11); every j ≤ N
SOURCE_CONCLUSION: g_{j+1} = g_j + ⟨f_j⟩ has norm at most Σ_{l<j+1} E_l ≤ 2ε and stays angle independent; induction proves E_j ≤ ε2^{-j}, G_j ≤ 2ε for all j ≤ N
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L11#qD-choice, lpM:L9#projections-tail, lpM:L11#step-estimate
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L11#qD-choice | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | E_{j+1} ≤ E_j/2 under (30)
EDGE: lpM:L9#projections-tail | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | the mean projection has norm at most one: ‖⟨f_l⟩‖ ≤ E_l
EDGE: lpM:L11#step-estimate | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | the estimates at each step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L11#composition
KIND: step
TITLE: Phi = phi_0 o ... o phi_{N-1}: (31) with Z = g_N, R = f_N; displacement <= 2 q_D/N <= 1/32
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L358-L363
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L375-L379
CONTRACT_ID: lpM:L11#composition
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L11: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1 with A ε N^{τ+1} ≤ q_D (30); local data ρ_j = 3 - j/N, g_0 = 0, f_0 = F
SOURCE_QUANTIFIERS: for every such H, ε and N (inherited from lpM:L11)
SOURCE_CONCLUSION: composing the actual flow maps gives Φ = φ_0∘...∘φ_{N-1} and the exact identity (31) with Z = g_N, R = f_N; the telescoped displacement is Σ_{j<N} u_j ≤ 2AεN^τ ≤ 2q_D/N ≤ 1/32 < 1/16; each factor maps its smaller domain into its larger one, so Φ : D_2 → D_3 is defined, injective and symplectic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L11#induction, lpM:L10
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L11#induction | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | the estimates of every step
EDGE: lpM:L10 | docs/tracks/LP/source/MAIN.md#L11@L375-L375 | each φ_j is a holomorphic real symplectic time-one map with displacement u_j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: lpM:L11#inverse
KIND: step
TITLE: the inverse on D_{3/2} by negative-time flows in reverse order, values in D_2
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L363-L363
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L11@L379-L379
CONTRACT_ID: lpM:L11#inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L11: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1 with A ε N^{τ+1} ≤ q_D (30); local data ρ_j = 3 - j/N, g_0 = 0, f_0 = F
SOURCE_QUANTIFIERS: for every such H, ε and N (inherited from lpM:L11)
SOURCE_CONCLUSION: for an initial point in D_{3/2}, the negative-time flows in reverse composition order keep every intermediate point within scaled distance 1/32 of D_{3/2}, hence in D_2, inside every factor's domain; this constructs the inverse with the same telescoped bound, and the compositions are identities by uniqueness of each flow
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L11#composition, lpM:L10
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L11#composition | docs/tracks/LP/source/MAIN.md#L11@L379-L379 | the telescoped displacement 1/32
EDGE: lpM:L10 | docs/tracks/LP/source/MAIN.md#L11@L379-L379 | the negative-time maps are inverses of the time-one maps
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
