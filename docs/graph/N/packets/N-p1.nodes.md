NODE: bpN:p1:ext-linalg
KIND: external
TITLE: Finite-dimensional linear algebra
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:ext-linalg@L18-L21
PROOF_SOURCE: -
CONTRACT_ID: bpN:p1:ext-linalg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: L : V → W linear, V and W finite-dimensional real vector spaces with dim V = dim W; L injective
SOURCE_QUANTIFIERS: V, W; L
SOURCE_CONCLUSION: L is bijective (rank-nullity; finranks dim(ℝⁿ×ℝ) = dim(ℝ×ℝⁿ) = n+1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external fact E1 (finite-dimensional linear algebra); consumed by stepN:p2:qk-bij

NODE: bpN:p1:ext-norms
KIND: external
TITLE: Norm comparison and Cauchy--Schwarz
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:ext-norms@L22-L23
PROOF_SOURCE: -
CONTRACT_ID: bpN:p1:ext-norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: x, y ∈ ℝⁿ or ℂⁿ
SOURCE_QUANTIFIERS: n; x, y
SOURCE_CONCLUSION: ¦x¦_∞ ≤ ¦x¦₂ ≤ √n ¦x¦_∞; ¦x¦₁ ≤ √n ¦x¦₂; ¦x¦₂ ≤ ¦x¦₁; ¦x·y¦ ≤ ¦x¦₂¦y¦₂ (also for the bilinear, not Hermitian, product)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external fact E2 (norm comparison and Cauchy-Schwarz)

NODE: bpN:p1:ext-restrict
KIND: external
TITLE: Restriction of scalars and chain rule
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:ext-restrict@L24-L26
PROOF_SOURCE: -
CONTRACT_ID: bpN:p1:ext-restrict
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a ℂ-differentiable (resp. C^k) map; ι : ℝᴺ → ℂᴺ the ℝ-linear inclusion; Re
SOURCE_QUANTIFIERS: N; the map
SOURCE_CONCLUSION: a ℂ-differentiable (C^k) map is ℝ-differentiable (C^k) with the same derivative; chain rule for ι and for Re
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external fact E3 (restriction of scalars and chain rule)

NODE: bpN:p1:ext-prod
KIND: external
TITLE: Product rule
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:ext-prod@L27-L28
PROOF_SOURCE: -
CONTRACT_ID: bpN:p1:ext-prod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (x,λ) ↦ λ v(x) with v differentiable; vector functions
SOURCE_QUANTIFIERS: v differentiable
SOURCE_CONCLUSION: product rule for (x,λ) ↦ λ v(x); differentiability of a vector function coordinatewise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external fact E4 (product rule); consumed by stepN:p2:qd-prod

NODE: bpN:p1:norm-compare
KIND: lemma
TITLE: Norm and lattice comparisons
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-compare@L35-L39
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-compare@L40-L44
CONTRACT_ID: bpN:p1:norm-compare
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 0 (all norms 0 for n = 0); (a) x ∈ ℝⁿ or ℂⁿ; (b) k ∈ ℤⁿ, K; (c) matrix Q with ¦Q_ij¦ ≤ M₀, x, y ∈ ℂⁿ
SOURCE_QUANTIFIERS: n ≥ 0; x, y; k; K; Q; M₀
SOURCE_CONCLUSION: (a) ¦x¦_∞ ≤ ¦x¦₂ ≤ √n ¦x¦_∞ (so ¦x¦₂² ≤ n¦x¦_∞², and ¦x¦_∞² ≥ ¦x¦₂²/n for n > 0); (b) ¦k¦₂ ≤ ¦k¦₁ ≤ √n ¦k¦₂, hence {¦k¦₁ ≤ K} ⊂ {¦k¦₂ ≤ K} ⊂ {¦k¦₁ ≤ √n K}; (c) ¦xᵀQy¦ ≤ n M₀ ¦x¦₂¦y¦₂
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:nc-vec, stepN:p1:nc-mat
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:nc-vec | blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-compare@L41-L41 | proof step of this result
EDGE: stepN:p1:nc-mat | blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-compare@L43-L43 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.euclid, norm_le_euclid, modeSize_euclid_compare, lattice_ball_inclusions, bilinear_euclid_bound (KAM/Nekhoroshev/Interfaces/Norms.lean)
LEAN_NOTE: audit P1-1 PASS WITH NOTES; clauses (a),(b),(c) all covered
NOTE: forward pointers to Part 8 (bpN:p8:direction, bpN:p8:cutoffs) in the statement (L37) are not uses and are dropped; ext-norms is cited in \source and used at stepN:p1:nc-vec

NODE: stepN:p1:nc-vec
KIND: step
TITLE: Vectors
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-vec@L41-L41
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-vec@L41-L41
CONTRACT_ID: stepN:p1:nc-vec
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: x ∈ ℝⁿ or ℂⁿ; k ∈ ℤⁿ
SOURCE_QUANTIFIERS: as norm-compare
SOURCE_CONCLUSION: (a), (b): ¦x¦₂² = Σ¦x_i¦² ≤ n max¦x_i¦²; ¦x¦₁ ≤ √n¦x¦₂ by Cauchy-Schwarz with (1,…,1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:ext-norms
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:ext-norms | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-vec@L41-L41 | norm comparison and Cauchy-Schwarz
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:nc-mat
KIND: step
TITLE: Matrices
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-mat@L43-L43
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-mat@L43-L43
CONTRACT_ID: stepN:p1:nc-mat
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ¦Q_ij¦ ≤ M₀; x, y ∈ ℂⁿ
SOURCE_QUANTIFIERS: as norm-compare
SOURCE_CONCLUSION: ¦xᵀQy¦ ≤ M₀¦x¦₁¦y¦₁ ≤ n M₀ ¦x¦₂¦y¦₂
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:nc-vec
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:nc-vec | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-mat@L43-L43 | part (b): ¦x¦₁ ≤ √n¦x¦₂
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p1:realdomain
KIND: lemma
TITLE: Domains
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:realdomain@L46-L57
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:realdomain@L58-L64
CONTRACT_ID: bpN:p1:realdomain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: R, s > 0; n ≥ 0; (c) P = {J ∈ ℝⁿ : ¦J¦ ≤ R/2}, 0 < r₀ ≤ min(s/2, R/8); I ∈ ℂⁿ, J ∈ P with ¦I−J¦_∞ < r₀
SOURCE_QUANTIFIERS: n ≥ 0; R, s > 0; r₀; I; J
SOURCE_CONCLUSION: (a) 𝓑_s(R) = B(0,R+s), open, B(0,R) ⊂ 𝓑_s(R); W_s := ℝⁿ × 𝓑_s(R) open and D_s(R) ∩ (ℝⁿ×ℝⁿ) = W_s; (b) B(0,R)_s ∩ ℝⁿ = 𝓑_s(R); D_s(R) and B(0,R)_s open; (c) I ∈ B(0,R)_s and ¦I−J¦ < s; if I ∈ ℝⁿ then ¦I¦ < 5R/8 ≤ 3R/4 (also for the Euclidean tube); (d) T_ρ ⊂ T_s for ρ ≤ s; T_s = ℂ⁰ for n = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:rd-real, stepN:p1:rd-open, stepN:p1:rd-euclid, bpN:p0:rdomain#realActionDomain, bpN:p0:cdomain#complexDomain, bpN:p0:actionnbhd#actionNbhd, bpN:p0:ball#actionBall, bpN:p0:strip#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:rd-real | blueprint-N/parts/p1-interfaces.tex#bpN:p1:realdomain@L59-L59 | proof step of this result
EDGE: stepN:p1:rd-open | blueprint-N/parts/p1-interfaces.tex#bpN:p1:realdomain@L61-L61 | proof step of this result
EDGE: stepN:p1:rd-euclid | blueprint-N/parts/p1-interfaces.tex#bpN:p1:realdomain@L63-L63 | proof step of this result
EDGE: bpN:p0:rdomain#realActionDomain | blueprint-N/parts/p1-interfaces.tex#bpN:p1:realdomain@L49-L49 | 𝓑_s(R)
EDGE: bpN:p0:cdomain#complexDomain | blueprint-N/parts/p1-interfaces.tex#bpN:p1:realdomain@L50-L50 | D_s(R) and its real points
EDGE: bpN:p0:actionnbhd#actionNbhd | blueprint-N/parts/p1-interfaces.tex#bpN:p1:realdomain@L51-L51 | B(0,R)_s
EDGE: bpN:p0:ball#actionBall | blueprint-N/parts/p1-interfaces.tex#bpN:p1:realdomain@L49-L49 | B(0,R)
EDGE: bpN:p0:strip#complexStrip | blueprint-N/parts/p1-interfaces.tex#bpN:p1:realdomain@L54-L54 | T_ρ, T_s
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.realActionDomain_eq, isOpen_realActionDomain, ball_subset_realActionDomain, isOpen_Wdom, realInclusion₂_preimage_complexDomain, isOpen_actionNbhd_ball, isOpen_complexDomain, realInclusion_preimage_actionNbhd, tube_subset, tube_real, complexStrip_mono, complexStrip_zero (KAM/Nekhoroshev/Interfaces/Domains.lean)
LEAN_NOTE: audit P1-1 PASS WITH NOTES; (a)-(d) all covered
NOTE: remark rdomain-eq (cited L49, L56) states the same identity as step rd-real, which proves it independently: no edge (rdomain-eq is a claim consumed by bpN:p3:s-N and stepN:p2:zd-diff); the "as in Definition bpN:p4:domains" of (c) (L52) restates the tube explicitly and is not a use: no edge

NODE: stepN:p1:rd-real
KIND: step
TITLE: Real tube
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-real@L59-L59
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-real@L59-L59
CONTRACT_ID: stepN:p1:rd-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: R, s > 0; I ∈ ℝⁿ
SOURCE_QUANTIFIERS: as realdomain
SOURCE_CONCLUSION: 𝓑_s(R) = B(0,R+s): (⊂) ¦I¦ ≤ ¦J¦ + ¦I−J¦ < R+s; (⊃) J = R I/(R+s) has ¦J¦ < R, ¦I−J¦ < s
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:rdomain#realActionDomain, bpN:p0:actionnbhd#actionNbhd, bpN:p0:ball#actionBall
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:rdomain#realActionDomain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-real@L59-L59 | the set 𝓑_s(R)
EDGE: bpN:p0:actionnbhd#actionNbhd | blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-real@L59-L59 | B(0,R)_s via ¦I−J¦ < s
EDGE: bpN:p0:ball#actionBall | blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-real@L59-L59 | J ∈ B(0,R)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:rd-open
KIND: step
TITLE: Openness and real points
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-open@L61-L61
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-open@L61-L61
CONTRACT_ID: stepN:p1:rd-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: R, s > 0
SOURCE_QUANTIFIERS: as realdomain
SOURCE_CONCLUSION: B(0,R)_s is a union of open balls, T_s is open, products of open sets are open; hence D_s(R), B(0,R)_s, W_s open and 𝓑_s(R) = B(0,R)_s ∩ ℝⁿ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:actionnbhd#actionNbhd, bpN:p0:ball#actionBall, bpN:p0:strip#complexStrip, bpN:p0:cdomain#complexDomain, stepN:p1:rd-real
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:actionnbhd#actionNbhd | blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-open@L61-L61 | B(0,R)_s as a union of balls
EDGE: bpN:p0:ball#actionBall | blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-open@L61-L61 | J ∈ B(0,R)
EDGE: bpN:p0:strip#complexStrip | blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-open@L61-L61 | T_s open
EDGE: bpN:p0:cdomain#complexDomain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-open@L61-L61 | D_s(R) = T_s × B(0,R)_s
EDGE: stepN:p1:rd-real | blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-open@L61-L61 | 𝓑_s(R) = B(0,R)_s ∩ ℝⁿ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:rd-euclid
KIND: step
TITLE: Max-norm tubes
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-euclid@L63-L63
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-euclid@L63-L63
CONTRACT_ID: stepN:p1:rd-euclid
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J ∈ P, ¦I−J¦_∞ < r₀ ≤ min(s/2,R/8)
SOURCE_QUANTIFIERS: as realdomain
SOURCE_CONCLUSION: I ∈ B(0,R)_s, ¦I−J¦ < s; for real I: ¦I¦ < R/2 + R/8; the Euclidean tube is contained in the max-norm tube
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:ext-norms, bpN:p0:actionnbhd#actionNbhd, bpN:p0:ball#actionBall
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:ext-norms | blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-euclid@L63-L63 | ¦x¦_∞ ≤ ¦x¦₂
EDGE: bpN:p0:actionnbhd#actionNbhd | blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-euclid@L63-L63 | I ∈ B(0,R)_s
EDGE: bpN:p0:ball#actionBall | blueprint-N/parts/p1-interfaces.tex#stepN:p1:rd-euclid@L63-L63 | ¦J¦ < R
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p1:s-holo#data
KIND: definition
TITLE: Standing data of the section on holomorphy and real smoothness
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:s-holo@L68-L70
PROOF_SOURCE: -
CONTRACT_ID: bpN:p1:s-holo#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: R, s > 0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f (ε ≥ 0)
SOURCE_QUANTIFIERS: R, s; h; f; ε
SOURCE_CONCLUSION: defines the standing data of §s-holo: G(θ,I) = h(I) + f(θ,I) on D_s(R); H = H_{h,f}; ι : ℝⁿ × ℝⁿ → ℂⁿ × ℂⁿ the componentwise inclusion; complex partials ∂_{θ_i}G(w) = DG(w)[(e_i,0)], ∂_{I_i}G(w) = DG(w)[(0,e_i)]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:integrable#IsAnalyticIntegrable, bpN:p0:pert#IsAnalyticPerturbation, bpN:p0:cdomain#complexDomain, bpN:p0:realH#realHamiltonian
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:integrable#IsAnalyticIntegrable | blueprint-N/parts/p1-interfaces.tex#bpN:p1:s-holo@L68-L68 | h satisfies IsAnalyticIntegrable
EDGE: bpN:p0:pert#IsAnalyticPerturbation | blueprint-N/parts/p1-interfaces.tex#bpN:p1:s-holo@L68-L68 | f satisfies IsAnalyticPerturbation
EDGE: bpN:p0:cdomain#complexDomain | blueprint-N/parts/p1-interfaces.tex#bpN:p1:s-holo@L69-L69 | G defined on D_s(R)
EDGE: bpN:p0:realH#realHamiltonian | blueprint-N/parts/p1-interfaces.tex#bpN:p1:s-holo@L69-L69 | H = H_{h,f}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.Data, Wdom (KAM/Nekhoroshev/Interfaces/Setting.lean)
LEAN_NOTE: Definition formalized, nothing to prove; audit P1-1 PASS WITH NOTES
NOTE: section data node for coverage item p1:prose-L68-L70 (unlabelled prose); consumers: bpN:p1:holo-real and its steps

NODE: bpN:p1:holo-real
KIND: lemma
TITLE: Real smoothness and real Hamiltonian field
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L72-L85
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L86-L98
CONTRACT_ID: bpN:p1:holo-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data of §s-holo (bpN:p1:s-holo#data): R, s > 0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f (ε ≥ 0); G, H, ι
SOURCE_QUANTIFIERS: R, s; h; f; ε ≥ 0
SOURCE_CONCLUSION: (a) G holomorphic and C^∞ on D_s(R), h on B(0,R)_s; (b) H is C^∞ on W_s = ℝⁿ × B(0,R+s), real, H = G∘ι with D^kH(z)[ζ] = D^kG(ιz)[ιζ] ∈ ℝ, likewise h_ℝ = h∘ι is C^∞ on 𝓑_s(R); (c) H differentiable at z ∈ W_s and X_H(z) = X_{h+f}(ιz); ω_h(I)_i = ∂_i h(I) and D²h_ℝ(I)[e_i,e_j] = ∂_i∂_j h(I) symmetric, real, for I ∈ 𝓑_s(R); (d) H(θ+k,I) = H(θ,I) on W_s for k ∈ ℤⁿ, DH, D^kH, X_H 1-periodic in θ; (e) if ε = 0 then f = 0 on D_s(R) and H = h_ℝ on W_s
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:hr-holo, stepN:p1:hr-real, stepN:p1:hr-deriv, stepN:p1:hr-field, stepN:p1:hr-per, stepN:p1:hr-zero, bpN:p1:s-holo#data, bpN:p1:realdomain, bpN:p0:vf#hamiltonianVectorField, bpN:p0:freq#frequencyMap, bpN:p0:realpart#realPart, bpN:p0:realH#realHamiltonian
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:hr-holo | blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L87-L87 | proof step of this result
EDGE: stepN:p1:hr-real | blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L89-L89 | proof step of this result
EDGE: stepN:p1:hr-deriv | blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L91-L91 | proof step of this result
EDGE: stepN:p1:hr-field | blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L93-L93 | proof step of this result
EDGE: stepN:p1:hr-per | blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L95-L95 | proof step of this result
EDGE: stepN:p1:hr-zero | blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L97-L97 | proof step of this result
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L68-L68 | standing data
EDGE: bpN:p1:realdomain | blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L75-L75 | W_s and its openness
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L79-L79 | X_H
EDGE: bpN:p0:freq#frequencyMap | blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L80-L80 | ω_h
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L76-L76 | h_ℝ
EDGE: bpN:p0:realH#realHamiltonian | blueprint-N/parts/p1-interfaces.tex#bpN:p1:holo-real@L75-L75 | H = H_{h,f}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.holo_real_a, holo_real_b, complexHessian, holo_real_c, holo_real_d, holo_real_e (KAM/Nekhoroshev/Interfaces/HoloReal.lean)
LEAN_NOTE: audit P1-2 PASS WITH NOTES; clauses (a)-(e) all covered
NOTE: forward pointer (Part 3 uses this as bpN:p3:holo-input, L84) is not an edge; K:holomorphic-regularity and K:hamiltonian-real are cited in \source and used at steps hr-holo, hr-field

NODE: stepN:p1:hr-holo
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-holo@L87-L87
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-holo@L87-L87
CONTRACT_ID: stepN:p1:hr-holo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; R,s > 0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f; G(θ,I) = h(I)+f(θ,I); H = H_{h,f}; ι and complex partials as in §s-holo data
SOURCE_QUANTIFIERS: as holo-real
SOURCE_CONCLUSION: G is holomorphic and C∞ on D_s(R), and h is holomorphic and C∞ on B(0,R)_s, with holomorphic derivatives of every order; restriction of scalars gives real C∞.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:s-holo#data, bpN:p0:integrable#IsAnalyticIntegrable, bpN:p0:pert#IsAnalyticPerturbation, bpN:p1:realdomain, bpN:p0:cdomain#complexDomain, bpN:p1:ext-restrict, K:bp:p1:holomorphic-regularity
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-holo@L87-L87 | h, f, G of the standing data
EDGE: bpN:p0:integrable#IsAnalyticIntegrable | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-holo@L87-L87 | clause (i)
EDGE: bpN:p0:pert#IsAnalyticPerturbation | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-holo@L87-L87 | clause (i)
EDGE: bpN:p1:realdomain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-holo@L87-L87 | openness, Lemma realdomain (b)
EDGE: bpN:p0:cdomain#complexDomain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-holo@L87-L87 | G on D_s(R), B(0,R)_s second factor
EDGE: bpN:p1:ext-restrict | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-holo@L87-L87 | C^∞ in the real sense
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-holo@L87-L87 | holomorphic implies C^∞ with holomorphic derivatives
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:hr-real
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-real@L89-L89
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-real@L89-L89
CONTRACT_ID: stepN:p1:hr-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; R,s > 0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f; G(θ,I) = h(I)+f(θ,I); H = H_{h,f}; ι and complex partials as in §s-holo data
SOURCE_QUANTIFIERS: as holo-real
SOURCE_CONCLUSION: G(ιz) ∈ ℝ and H(z) = Re G(ιz) = G(ιz) on W_s; h_ℝ = h∘ι on 𝓑_s(R)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:realdomain, bpN:p0:integrable#IsAnalyticIntegrable, bpN:p0:pert#IsAnalyticPerturbation, bpN:p0:realH#realHamiltonian, bpN:p0:realpart#realPart, bpN:p1:s-holo#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:realdomain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-real@L89-L89 | ι(W_s) ⊂ D_s(R); W_s open
EDGE: bpN:p0:integrable#IsAnalyticIntegrable | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-real@L89-L89 | clause (iv)
EDGE: bpN:p0:pert#IsAnalyticPerturbation | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-real@L89-L89 | clause (iii)
EDGE: bpN:p0:realH#realHamiltonian | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-real@L89-L89 | H(z) = Re G(ιz)
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-real@L89-L89 | h_ℝ = h∘ι
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-real@L89-L89 | G, ι
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:hr-deriv
KIND: step
TITLE: Derivatives of all orders
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-deriv@L91-L91
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-deriv@L91-L91
CONTRACT_ID: stepN:p1:hr-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; R,s > 0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f; G(θ,I) = h(I)+f(θ,I); H = H_{h,f}; ι and complex partials as in §s-holo data
SOURCE_QUANTIFIERS: as holo-real
SOURCE_CONCLUSION: H ∈ C^∞(W_s), D^kH(z)[ζ] = D^kG(ιz)[ιζ] real; same for h_ℝ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:hr-holo, stepN:p1:hr-real, bpN:p1:ext-restrict, bpN:p0:realpart#realPart, bpN:p1:s-holo#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:hr-holo | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-deriv@L91-L91 | G is real-C^∞
EDGE: stepN:p1:hr-real | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-deriv@L91-L91 | H = G∘ι, real values
EDGE: bpN:p1:ext-restrict | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-deriv@L91-L91 | chain rule
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-deriv@L91-L91 | h_ℝ
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-deriv@L91-L91 | standing h,f,G,H,ι and local data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:hr-field
KIND: step
TITLE: The field
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-field@L93-L93
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-field@L93-L93
CONTRACT_ID: stepN:p1:hr-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; R,s > 0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f; G(θ,I) = h(I)+f(θ,I); H = H_{h,f}; ι and complex partials as in §s-holo data
SOURCE_QUANTIFIERS: as holo-real
SOURCE_CONCLUSION: X_H(z) = ((∂_{I_i}G(ιz))_i, (−∂_{θ_i}G(ιz))_i) = X_{h+f}(ιz); ω_h(I)_i = ∂_i h(I); D²h_ℝ(I)[e_i,e_j] = ∂_i∂_j h(I), symmetric
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:vf#hamiltonianVectorField, stepN:p1:hr-deriv, K:bp:p1:hamiltonian-real, K:bp:p1:holomorphic-regularity, K:bp:p1:ext-schwarz, bpN:p0:freq#frequencyMap, bpN:p0:realpart#realPart, bpN:p1:s-holo#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-field@L93-L93 | Definition vf
EDGE: stepN:p1:hr-deriv | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-field@L93-L93 | DH(z) = DG(ιz)∘ι
EDGE: K:bp:p1:hamiltonian-real | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-field@L93-L93 | Hamiltonian field at real points
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-field@L93-L93 | symmetry of complex second derivatives
EDGE: K:bp:p1:ext-schwarz | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-field@L93-L93 | symmetric mixed partials
EDGE: bpN:p0:freq#frequencyMap | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-field@L93-L93 | ω_h(I)_i = Dh_ℝ(I)[e_i]
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-field@L93-L93 | h_ℝ
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-field@L93-L93 | standing h,f,G,H,ι and local data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:hr-per
KIND: step
TITLE: Periodicity
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-per@L95-L95
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-per@L95-L95
CONTRACT_ID: stepN:p1:hr-per
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; R,s > 0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f; G(θ,I) = h(I)+f(θ,I); H = H_{h,f}; ι and complex partials as in §s-holo data; z ∈ W_s, k ∈ ℤⁿ
SOURCE_QUANTIFIERS: as holo-real
SOURCE_CONCLUSION: H∘τ_k = H on W_s, hence D^jH(τ_k z) = D^jH(z) and X_H(τ_k z) = X_H(z)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:pert#IsAnalyticPerturbation, bpN:p1:realdomain, bpN:p0:realH#realHamiltonian, stepN:p1:hr-deriv, bpN:p1:ext-restrict, bpN:p1:s-holo#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:pert#IsAnalyticPerturbation | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-per@L95-L95 | clause (ii) periodicity
EDGE: bpN:p1:realdomain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-per@L95-L95 | W_s ⊂ D_s(R), W_s invariant
EDGE: bpN:p0:realH#realHamiltonian | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-per@L95-L95 | H = Re(h(I) + f(θ,I))
EDGE: stepN:p1:hr-deriv | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-per@L95-L95 | differentiating H (smoothness on W_s)
EDGE: bpN:p1:ext-restrict | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-per@L95-L95 | chain rule
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-per@L95-L95 | standing h,f,G,H,ι and local data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:hr-zero
KIND: step
TITLE: Zero perturbation
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-zero@L97-L97
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-zero@L97-L97
CONTRACT_ID: stepN:p1:hr-zero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ε = 0; IsAnalyticPerturbation R s 0 f
SOURCE_QUANTIFIERS: as holo-real
SOURCE_CONCLUSION: f = 0 on D_s(R) and H = Re h(I) = h_ℝ(I) on W_s
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:pert#IsAnalyticPerturbation, bpN:p1:realdomain, bpN:p0:realH#realHamiltonian, bpN:p0:realpart#realPart, bpN:p1:s-holo#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:pert#IsAnalyticPerturbation | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-zero@L97-L97 | clause (iv) with ε = 0
EDGE: bpN:p1:realdomain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-zero@L97-L97 | W_s ⊂ D_s(R)
EDGE: bpN:p0:realH#realHamiltonian | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-zero@L97-L97 | H = Re(h(I) + f)
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-zero@L97-L97 | h_ℝ
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hr-zero@L97-L97 | standing h,f,G,H,ι and local data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p1:partials
KIND: lemma
TITLE: Ordered partials and first-order bounds
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:partials@L100-L105
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:partials@L106-L110
CONTRACT_ID: bpN:p1:partials
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; R,s>0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f; G,H,ι and partials fixed by §s-holo data; additionally U ⊂ ℝⁿ open with HasDerivativeBounds U h M; I ∈ U; a, b ∈ ℝⁿ
SOURCE_QUANTIFIERS: n; U; h; M; I ∈ U; a, b
SOURCE_CONCLUSION: ¦ω_h(I)_i¦ ≤ M, ¦ω_h(I)¦_∞ ≤ M, ¦ω_h(I)¦₂ ≤ √n M, ¦D²h_ℝ(I)[e_i,e_j]¦ ≤ M; ordered partials D^kh_ℝ(I)[e_{i_1},…,e_{i_k}] (k ≤ 3) are invariant under permutations of the indices
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:pa-first, stepN:p1:pa-sym, bpN:p0:bm#HasDerivativeBounds, bpN:p0:freq#frequencyMap, bpN:p0:realpart#realPart, bpN:p1:s-holo#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:pa-first | blueprint-N/parts/p1-interfaces.tex#bpN:p1:partials@L107-L107 | proof step of this result
EDGE: stepN:p1:pa-sym | blueprint-N/parts/p1-interfaces.tex#bpN:p1:partials@L109-L109 | proof step of this result
EDGE: bpN:p0:bm#HasDerivativeBounds | blueprint-N/parts/p1-interfaces.tex#bpN:p1:partials@L101-L101 | hypothesis HasDerivativeBounds U h M
EDGE: bpN:p0:freq#frequencyMap | blueprint-N/parts/p1-interfaces.tex#bpN:p1:partials@L102-L102 | ω_h
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p1-interfaces.tex#bpN:p1:partials@L102-L102 | D²h_ℝ
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#bpN:p1:partials@L100-L105 | standing subsection data, including analytic-integrable h and reality on real points
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: PROVED
LEAN_REF: partials (KAM/Nekhoroshev/Interfaces/Hessian.lean)
LEAN_NOTE: audit P1-3b PASS WITH NOTES
NOTE: K:ext-schwarz is cited in \source and used at step pa-sym

NODE: stepN:p1:pa-first
KIND: step
TITLE: First order
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:pa-first@L107-L107
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:pa-first@L107-L107
CONTRACT_ID: stepN:p1:pa-first
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; R,s>0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f; G,H,ι and partials fixed by §s-holo data; additionally k = 1 in HasDerivativeBounds
SOURCE_QUANTIFIERS: as partials
SOURCE_CONCLUSION: ¦Dh_ℝ(I)[e_i]¦ = ¦ω_h(I)_i¦ ≤ M; ¦ω¦₂ ≤ √n ¦ω¦_∞
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:bm#HasDerivativeBounds, bpN:p0:freq#frequencyMap, bpN:p1:norm-compare, bpN:p0:realpart#realPart, bpN:p1:s-holo#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:bm#HasDerivativeBounds | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pa-first@L107-L107 | k = 1 clause
EDGE: bpN:p0:freq#frequencyMap | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pa-first@L107-L107 | Definition freq
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pa-first@L107-L107 | ¦ω¦₂ ≤ √n¦ω¦_∞
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pa-first@L107-L107 | h_ℝ
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pa-first@L107-L107 | standing subsection data, including analytic-integrable h and reality on real points
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:pa-sym
KIND: step
TITLE: Symmetry
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:pa-sym@L109-L109
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:pa-sym@L109-L109
CONTRACT_ID: stepN:p1:pa-sym
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; R,s>0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f; G,H,ι and partials fixed by §s-holo data; additionally h_ℝ ∈ C³ on the open U
SOURCE_QUANTIFIERS: as partials
SOURCE_CONCLUSION: D²h_ℝ(I) and D³h_ℝ(I) are symmetric: permutation invariance; the entry bound is k = 2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:bm#HasDerivativeBounds, K:bp:p1:ext-schwarz, bpN:p1:s-holo#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:bm#HasDerivativeBounds | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pa-sym@L109-L109 | h_ℝ ∈ C³(U), k = 2 bound
EDGE: K:bp:p1:ext-schwarz | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pa-sym@L109-L109 | Schwarz for h_ℝ, Dh_ℝ, D²h_ℝ
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pa-sym@L109-L109 | standing subsection data, including analytic-integrable h and reality on real points
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p1:hessian-convert
KIND: lemma
TITLE: Complex Hessian bound in Euclidean form
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:hessian-convert@L112-L118
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:hessian-convert@L119-L123
CONTRACT_ID: bpN:p1:hessian-convert
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; R,s>0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f; G,H,ι and partials fixed by §s-holo data; additionally HasComplexHessianBound R s h M_ℂ; I ∈ B(0,R)_s; Q(I) = (∂_i∂_j h(I))_{ij}; x, y ∈ ℂⁿ (real x, y for the real statement, I real in 𝓑_s(R))
SOURCE_QUANTIFIERS: n; R, s; h; M_ℂ; I; x, y
SOURCE_CONCLUSION: ¦Q(I)_ij¦ ≤ M_ℂ; ¦xᵀQ(I)y¦ ≤ n M_ℂ ¦x¦₂¦y¦₂; operator norm of Q(I) on (ℂⁿ,¦·¦₂) ≤ n M_ℂ; for real I ∈ 𝓑_s(R), Q(I) is the real Hessian D²h_ℝ(I)[e_i,e_j] and ¦D²h_ℝ(I)[x,y]¦ ≤ n M_ℂ ¦x¦₂¦y¦₂
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:hc-entries, stepN:p1:hc-eucl, bpN:p0:hess#HasComplexHessianBound, bpN:p1:holo-real, bpN:p0:actionnbhd#actionNbhd, bpN:p0:rdomain#realActionDomain, bpN:p0:realpart#realPart, bpN:p1:s-holo#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:hc-entries | blueprint-N/parts/p1-interfaces.tex#bpN:p1:hessian-convert@L120-L120 | proof step of this result
EDGE: stepN:p1:hc-eucl | blueprint-N/parts/p1-interfaces.tex#bpN:p1:hessian-convert@L122-L122 | proof step of this result
EDGE: bpN:p0:hess#HasComplexHessianBound | blueprint-N/parts/p1-interfaces.tex#bpN:p1:hessian-convert@L113-L113 | hypothesis
EDGE: bpN:p1:holo-real | blueprint-N/parts/p1-interfaces.tex#bpN:p1:hessian-convert@L115-L115 | real Hessian is the complex one, Lemma holo-real (c)
EDGE: bpN:p0:actionnbhd#actionNbhd | blueprint-N/parts/p1-interfaces.tex#bpN:p1:hessian-convert@L113-L113 | B(0,R)_s
EDGE: bpN:p0:rdomain#realActionDomain | blueprint-N/parts/p1-interfaces.tex#bpN:p1:hessian-convert@L115-L115 | 𝓑_s(R)
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p1-interfaces.tex#bpN:p1:hessian-convert@L115-L115 | D²h_ℝ
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#bpN:p1:hessian-convert@L112-L118 | standing subsection data, including analytic-integrable h and reality on real points
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: PROVED
LEAN_REF: hessian_convert (KAM/Nekhoroshev/Interfaces/Hessian.lean)
LEAN_NOTE: audit P1-3b PASS WITH NOTES
NOTE: The lemma lies in §s-holo, whose standing IsAnalyticIntegrable premise supplies the reality required by holo-real(c). Keep the stated Hessian bound and all complex/real estimates; there is no missing reality premise in the raw subsection. Link its data directly.

NODE: stepN:p1:hc-entries
KIND: step
TITLE: Entries
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hc-entries@L120-L120
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hc-entries@L120-L120
CONTRACT_ID: stepN:p1:hc-entries
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; R,s>0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f; G,H,ι and partials fixed by §s-holo data; additionally HasComplexHessianBound R s h M_ℂ; ¦e_i¦ = 1 (max norm)
SOURCE_QUANTIFIERS: as hessian-convert
SOURCE_CONCLUSION: ¦∂_i∂_j h(I)¦ = ¦D²h(I)[e_i,e_j]¦ ≤ M_ℂ (order of arguments immaterial by symmetry)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:hess#HasComplexHessianBound, K:bp:p1:holomorphic-regularity, bpN:p1:s-holo#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:hess#HasComplexHessianBound | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hc-entries@L120-L120 | norm bound of D(Dh)(I)
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hc-entries@L120-L120 | symmetry of the complex Hessian
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hc-entries@L120-L120 | standing subsection data, including analytic-integrable h and reality on real points
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:hc-eucl
KIND: step
TITLE: Euclidean bound
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hc-eucl@L122-L122
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:hc-eucl@L122-L122
CONTRACT_ID: stepN:p1:hc-eucl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; R,s>0; IsAnalyticIntegrable R s h; IsAnalyticPerturbation R s ε f; G,H,ι and partials fixed by §s-holo data; additionally HasComplexHessianBound R s h M_ℂ; I ∈ B(0,R)_s; x,y ∈ ℂⁿ; Q(I) = (∂_i∂_j h(I))_ij
SOURCE_QUANTIFIERS: as hessian-convert
SOURCE_CONCLUSION: ¦xᵀQy¦ ≤ nM_ℂ¦x¦₂¦y¦₂; ¦Qx¦₂ ≤ nM_ℂ¦x¦₂ (same estimate applied to ȳ)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:norm-compare, stepN:p1:hc-entries, bpN:p1:s-holo#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hc-eucl@L122-L122 | part (c)
EDGE: stepN:p1:hc-entries | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hc-eucl@L122-L122 | entry bound
EDGE: bpN:p1:s-holo#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:hc-eucl@L122-L122 | standing subsection data, including analytic-integrable h and reality on real points
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p1:conic-coercive
KIND: lemma
TITLE: Transverse coercivity gives conic coercivity (linear algebra core)
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:conic-coercive@L127-L133
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:conic-coercive@L134-L145
CONTRACT_ID: bpN:p1:conic-coercive
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1; B, q > 0; Q : ℝⁿ × ℝⁿ → ℝ bilinear (not necessarily symmetric) with ¦Q[x,y]¦ ≤ B¦x¦₂¦y¦₂; ω ∈ ℝⁿ∖{0}; ω·v = 0 ⟹ Q[v,v] ≥ q¦v¦₂² (v ∈ ℝⁿ); ℓ' ≥ 0, ℓ' ≤ ¦ω¦₂ q/(8(B+q))
SOURCE_QUANTIFIERS: n; B, q; Q; ω; ℓ'; ξ ∈ ℝⁿ
SOURCE_CONCLUSION: ¦ω·ξ¦ ≤ ℓ'¦ξ¦₂ ⟹ Q[ξ,ξ] ≥ (5/8) q ¦ξ¦₂² (≥ (q/2)¦ξ¦₂²)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:cc-unit, stepN:p1:cc-decomp, stepN:p1:cc-expand, stepN:p1:cc-num
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:cc-unit | blueprint-N/parts/p1-interfaces.tex#bpN:p1:conic-coercive@L135-L135 | proof step of this result
EDGE: stepN:p1:cc-decomp | blueprint-N/parts/p1-interfaces.tex#bpN:p1:conic-coercive@L137-L137 | proof step of this result
EDGE: stepN:p1:cc-expand | blueprint-N/parts/p1-interfaces.tex#bpN:p1:conic-coercive@L140-L140 | proof step of this result
EDGE: stepN:p1:cc-num | blueprint-N/parts/p1-interfaces.tex#bpN:p1:conic-coercive@L144-L144 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.conic_coercive (KAM/Nekhoroshev/Interfaces/ConicCoercive.lean)
LEAN_NOTE: audit P1-3a PASS WITH NOTES; full 5/8 q conclusion on cone
NOTE: pure linear algebra core (ours); no references

NODE: stepN:p1:cc-unit
KIND: step
TITLE: Reduction to unit vectors
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:cc-unit@L135-L135
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:cc-unit@L135-L135
CONTRACT_ID: stepN:p1:cc-unit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1; B, q > 0; Q : ℝⁿ × ℝⁿ → ℝ bilinear (not necessarily symmetric) with ¦Q[x,y]¦ ≤ B¦x¦₂¦y¦₂; ω ∈ ℝⁿ∖{0}; ω·v = 0 ⟹ Q[v,v] ≥ q¦v¦₂² (v ∈ ℝⁿ); ℓ' ≥ 0, ℓ' ≤ ¦ω¦₂ q/(8(B+q)); ξ ∈ ℝⁿ satisfies ¦ω·ξ¦ ≤ ℓ′¦ξ¦₂
SOURCE_QUANTIFIERS: as conic-coercive
SOURCE_CONCLUSION: the case ξ = 0 is trivial; assume ¦ξ¦₂ = 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:cc-decomp
KIND: step
TITLE: Decomposition
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:cc-decomp@L137-L138
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:cc-decomp@L137-L138
CONTRACT_ID: stepN:p1:cc-decomp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ¦ξ¦₂ = 1; e = ω/¦ω¦₂
SOURCE_QUANTIFIERS: as conic-coercive
SOURCE_CONCLUSION: t = ξ·e, u = ξ − te: u·ω = 0, ¦u¦₂² = 1−t², ¦t¦ ≤ 1, ¦t¦ = ¦ω·ξ¦/¦ω¦₂ ≤ ℓ'/¦ω¦₂ ≤ κ := q/(8(B+q)) < 1/8
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:cc-unit
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:cc-unit | blueprint-N/parts/p1-interfaces.tex#stepN:p1:cc-decomp@L137-L137 | reduction to unit vectors
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.conic_coercive (KAM/Nekhoroshev/Interfaces/ConicCoercive.lean)
LEAN_NOTE: audit P1-3a PASS WITH NOTES; decomposition/orthogonality inside conic_coercive proof (lines 87-143)
NOTE: -

NODE: stepN:p1:cc-expand
KIND: step
TITLE: Expansion
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:cc-expand@L140-L142
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:cc-expand@L140-L142
CONTRACT_ID: stepN:p1:cc-expand
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1; B, q > 0; Q : ℝⁿ × ℝⁿ → ℝ bilinear (not necessarily symmetric) with ¦Q[x,y]¦ ≤ B¦x¦₂¦y¦₂; ω ∈ ℝⁿ∖{0}; ω·v = 0 ⟹ Q[v,v] ≥ q¦v¦₂² (v ∈ ℝⁿ); ℓ' ≥ 0, ℓ' ≤ ¦ω¦₂ q/(8(B+q)); ξ ∈ ℝⁿ satisfies ¦ω·ξ¦ ≤ ℓ′¦ξ¦₂; in the normalized branch ¦ξ¦₂ = 1, with e,t,u,κ as defined at L137–138
SOURCE_QUANTIFIERS: as conic-coercive
SOURCE_CONCLUSION: Q[ξ,ξ] = Q[u,u] + tQ[u,e] + tQ[e,u] + t²Q[e,e] ≥ q − (q+B)t² − 2B¦t¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:cc-decomp
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:cc-decomp | blueprint-N/parts/p1-interfaces.tex#stepN:p1:cc-expand@L140-L140 | t, u, e and ω·u = 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.conic_coercive (KAM/Nekhoroshev/Interfaces/ConicCoercive.lean)
LEAN_NOTE: audit P1-3a PASS WITH NOTES; both mixed terms, no symmetry assumed (lines 145-159)
NOTE: -

NODE: stepN:p1:cc-num
KIND: step
TITLE: Numerics
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:cc-num@L144-L144
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:cc-num@L144-L144
CONTRACT_ID: stepN:p1:cc-num
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1; B, q > 0; Q : ℝⁿ × ℝⁿ → ℝ bilinear (not necessarily symmetric) with ¦Q[x,y]¦ ≤ B¦x¦₂¦y¦₂; ω ∈ ℝⁿ∖{0}; ω·v = 0 ⟹ Q[v,v] ≥ q¦v¦₂² (v ∈ ℝⁿ); ℓ' ≥ 0, ℓ' ≤ ¦ω¦₂ q/(8(B+q)); ξ ∈ ℝⁿ satisfies ¦ω·ξ¦ ≤ ℓ′¦ξ¦₂; in the normalized branch ¦ξ¦₂ = 1, with e,t,u,κ as defined at L137–138
SOURCE_QUANTIFIERS: as conic-coercive
SOURCE_CONCLUSION: (q+B)t² ≤ q/8 and 2B¦t¦ ≤ q/4, hence Q[ξ,ξ] ≥ (5/8)q
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:cc-expand, stepN:p1:cc-decomp
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:cc-expand | blueprint-N/parts/p1-interfaces.tex#stepN:p1:cc-num@L144-L144 | the lower bound
EDGE: stepN:p1:cc-decomp | blueprint-N/parts/p1-interfaces.tex#stepN:p1:cc-num@L144-L144 | ¦t¦ ≤ κ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.conic_coercive (KAM/Nekhoroshev/Interfaces/ConicCoercive.lean)
LEAN_NOTE: audit P1-3a PASS WITH NOTES; numerics (conic_numerics private helper, lines 149-175)
NOTE: -

NODE: bpN:p1:qc-convert
KIND: lemma
TITLE: Quasi-convexity in P\"oschel's quantified form
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L147-L161
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L162-L172
CONTRACT_ID: bpN:p1:qc-convert
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1; R, s, m, M_ℂ, ω_min > 0; q = m/n, B_c = nM_ℂ + q, μ = q/2, ℓ = ω_min q/(8(B_c+q)); IsAnalyticIntegrable R s h; HasComplexHessianBound R s h M_ℂ; IsStrictlyQuasiConvex 𝓑_s(R) h m; ω_min ≤ ¦ω_h(I)¦_∞ for all I ∈ B(0,R); I ∈ B(0,R), ω = ω_h(I), Q = D²h_ℝ(I)
SOURCE_QUANTIFIERS: n ≥ 1; R, s, m, M_ℂ, ω_min; q, B_c, μ, ℓ defined from them; h; I ∈ B(0,R); then ξ ∈ ℝⁿ
SOURCE_CONCLUSION: (a) ¦Q[x,y]¦ ≤ B_c¦x¦₂¦y¦₂ and ω·v = 0 ⟹ Q[v,v] ≥ q¦v¦₂²; (b) ¦ω·ξ¦ ≤ ℓ¦ξ¦₂ ⟹ Q[ξ,ξ] ≥ μ¦ξ¦₂² (Pöschel alternative, conditional only); (c) ¦ω¦₂ ≥ ¦ω¦_∞ ≥ ω_min and ¦ω¦₂ ≤ √n ¦ω¦_∞; in Pöschel normalisation (h̃ = 2πh) the same with (ℓ̃, μ̃, B̃_c, ω̃, Q̃) = 2π(ℓ, μ, B_c, ω, Q)
CONSTANT_SCOPE: q, B_c, μ, ℓ depend only on (n, m, M_ℂ, ω_min)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:qc-reg, stepN:p1:qc-trans, stepN:p1:qc-freq, stepN:p1:qc-conic, stepN:p1:qc-scale, bpN:p1:period-convert, bpN:p0:integrable#IsAnalyticIntegrable, bpN:p0:hess#HasComplexHessianBound, bpN:p0:qc#IsStrictlyQuasiConvex, bpN:p0:ball#actionBall, bpN:p0:rdomain#realActionDomain, bpN:p0:freq#frequencyMap, bpN:p0:realpart#realPart
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:qc-reg | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L163-L163 | proof step of this result
EDGE: stepN:p1:qc-trans | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L165-L165 | proof step of this result
EDGE: stepN:p1:qc-freq | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L167-L167 | proof step of this result
EDGE: stepN:p1:qc-conic | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L169-L169 | proof step of this result
EDGE: stepN:p1:qc-scale | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L171-L171 | proof step of this result
EDGE: bpN:p1:period-convert | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L158-L158 | Pöschel normalisation h̃ = 2πh, Lemma period-convert
EDGE: bpN:p0:integrable#IsAnalyticIntegrable | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L150-L150 | hypothesis
EDGE: bpN:p0:hess#HasComplexHessianBound | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L150-L150 | hypothesis
EDGE: bpN:p0:qc#IsStrictlyQuasiConvex | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L150-L150 | hypothesis
EDGE: bpN:p0:ball#actionBall | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L150-L150 | B(0,R)
EDGE: bpN:p0:rdomain#realActionDomain | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L150-L150 | 𝓑_s(R)
EDGE: bpN:p0:freq#frequencyMap | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L150-L150 | ω_h(I)
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p1-interfaces.tex#bpN:p1:qc-convert@L151-L151 | D²h_ℝ(I)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: PROVED
LEAN_REF: qc_convert (KAM/Nekhoroshev/Interfaces/QuasiConvex.lean); qc_convert_tilde (KAM/Nekhoroshev/Interfaces/Period.lean)
LEAN_NOTE: audit P1-3b PASS WITH NOTES
NOTE: the warning that full positive definiteness is false (L159) and the \source (L160) are not uses

NODE: stepN:p1:qc-reg
KIND: step
TITLE: Regularity and Hessian
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-reg@L163-L163
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-reg@L163-L163
CONTRACT_ID: stepN:p1:qc-reg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1; R, s, m, M_ℂ, ω_min > 0; q = m/n, B_c = nM_ℂ + q, μ = q/2, ℓ = ω_min q/(8(B_c+q)); IsAnalyticIntegrable R s h; HasComplexHessianBound R s h M_ℂ; IsStrictlyQuasiConvex 𝓑_s(R) h m; ω_min ≤ ¦ω_h(I)¦_∞ for all I ∈ B(0,R); I ∈ B(0,R), ω = ω_h(I), Q = D²h_ℝ(I)
SOURCE_QUANTIFIERS: as qc-convert
SOURCE_CONCLUSION: I ∈ 𝓑_s(R) and ¦Q[x,y]¦ ≤ nM_ℂ¦x¦₂¦y¦₂ ≤ B_c¦x¦₂¦y¦₂ (first half of (a))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:hessian-convert, bpN:p1:realdomain, bpN:p0:hess#HasComplexHessianBound
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:hessian-convert | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-reg@L163-L163 | real Hessian and its Euclidean bound
EDGE: bpN:p1:realdomain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-reg@L163-L163 | B(0,R) ⊂ 𝓑_s(R), Lemma realdomain (a)
EDGE: bpN:p0:hess#HasComplexHessianBound | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-reg@L163-L163 | hypothesis with constant M_ℂ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-delta-N-a
REVIEWER: sol-delta2-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: The current hessian-convert contract includes the standing §s-holo data IsAnalyticPerturbation R s ε f (L68–70 and its SOURCE_HYPOTHESES). This application supplies hypotheses on h only and no such f,ε datum. The quoted Hessian estimate is h-only in its proof, but that premise-free projection has not been recorded as a distinct source result. Keep the present source premises unchanged and expose the conditional-application mismatch.

NODE: stepN:p1:qc-trans
KIND: step
TITLE: Transverse coercivity in the Euclidean norm
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-trans@L165-L165
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-trans@L165-L165
CONTRACT_ID: stepN:p1:qc-trans
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: IsStrictlyQuasiConvex 𝓑_s(R) h m at I ∈ 𝓑_s(R)
SOURCE_QUANTIFIERS: as qc-convert
SOURCE_CONCLUSION: ω·v = 0 ⟹ Q[v,v] ≥ m¦v¦_∞² ≥ (m/n)¦v¦₂² = q¦v¦₂²; ω ≠ 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:qc#IsStrictlyQuasiConvex, bpN:p1:norm-compare, stepN:p1:qc-reg
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:qc#IsStrictlyQuasiConvex | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-trans@L165-L165 | Definition qc at I
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-trans@L165-L165 | part (a): ¦v¦_∞² ≥ ¦v¦₂²/n
EDGE: stepN:p1:qc-reg | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-trans@L165-L165 | I ∈ 𝓑_s(R)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:qc-freq
KIND: step
TITLE: Frequency size
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-freq@L167-L167
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-freq@L167-L167
CONTRACT_ID: stepN:p1:qc-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ω_min ≤ ¦ω¦_∞ on B(0,R)
SOURCE_QUANTIFIERS: as qc-convert
SOURCE_CONCLUSION: (c): ¦ω¦₂ ≥ ¦ω¦_∞ ≥ ω_min; ¦ω¦₂ ≤ √n¦ω¦_∞
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:norm-compare
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:norm-compare | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-freq@L167-L167 | part (a)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:qc-conic
KIND: step
TITLE: Conic coercivity
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-conic@L169-L169
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-conic@L169-L169
CONTRACT_ID: stepN:p1:qc-conic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1; R, s, m, M_ℂ, ω_min > 0; q = m/n, B_c = nM_ℂ + q, μ = q/2, ℓ = ω_min q/(8(B_c+q)); IsAnalyticIntegrable R s h; HasComplexHessianBound R s h M_ℂ; IsStrictlyQuasiConvex 𝓑_s(R) h m; ω_min ≤ ¦ω_h(I)¦_∞ for all I ∈ B(0,R); I ∈ B(0,R), ω = ω_h(I), Q = D²h_ℝ(I)
SOURCE_QUANTIFIERS: as qc-convert
SOURCE_CONCLUSION: (b): Q[ξ,ξ] ≥ (5/8)q¦ξ¦₂² ≥ μ¦ξ¦₂² when ¦ω·ξ¦ ≤ ℓ¦ξ¦₂
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:conic-coercive, stepN:p1:qc-reg, stepN:p1:qc-trans, stepN:p1:qc-freq
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:conic-coercive | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-conic@L169-L169 | with B = B_c, q, ℓ' = ℓ
EDGE: stepN:p1:qc-reg | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-conic@L169-L169 | bilinear bound
EDGE: stepN:p1:qc-trans | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-conic@L169-L169 | transverse coercivity
EDGE: stepN:p1:qc-freq | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-conic@L169-L169 | ℓ ≤ ¦ω¦₂ q/(8(B_c+q))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:qc-scale
KIND: step
TITLE: Scaling
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-scale@L171-L171
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-scale@L171-L171
CONTRACT_ID: stepN:p1:qc-scale
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 1; R, s, m, M_ℂ, ω_min > 0; q = m/n, B_c = nM_ℂ + q, μ = q/2, ℓ = ω_min q/(8(B_c+q)); IsAnalyticIntegrable R s h; HasComplexHessianBound R s h M_ℂ; IsStrictlyQuasiConvex 𝓑_s(R) h m; ω_min ≤ ¦ω_h(I)¦_∞ for all I ∈ B(0,R); I ∈ B(0,R), ω = ω_h(I), Q = D²h_ℝ(I)
SOURCE_QUANTIFIERS: as qc-convert
SOURCE_CONCLUSION: the same statements for h̃ = 2πh with 2π(ℓ, μ, B_c, ω, Q), since the implications are homogeneous
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:period-convert, stepN:p1:qc-conic, stepN:p1:qc-reg, stepN:p1:qc-trans
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:period-convert | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-scale@L171-L171 | clause (b): scaling of ω, D²h_ℝ by 2π
EDGE: stepN:p1:qc-conic | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-scale@L171-L171 | implication (b)
EDGE: stepN:p1:qc-reg | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-scale@L171-L171 | (a)
EDGE: stepN:p1:qc-trans | blueprint-N/parts/p1-interfaces.tex#stepN:p1:qc-scale@L171-L171 | (a)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p1:period-convert
KIND: lemma
TITLE: Period conversion
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L176-L189
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L190-L196
CONTRACT_ID: bpN:p1:period-convert
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Λ(θ,I) = (2πθ,I); H : ℝⁿ×ℝⁿ → ℝ; h, f arbitrary; H̃(φ,I) = 2πH(φ/2π,I), h̃ = 2πh, f̃(φ,I) = 2πf(φ/2π,I) (so H̃ = H_{h̃,f̃} when H = H_{h,f}); (a),(b) unconditional; (c)-(e) with IsAnalyticPerturbation R s ε f, R, s > 0; (d) needs f(θ+k,I) = f(θ,I) on D_s(R)
SOURCE_QUANTIFIERS: n; H,h,f arbitrary; define Λ,H̃,h̃,f̃; for (a) all U,J,z and I₀; for (b) all parameters of the corresponding predicate/bound implications, without positivity restrictions on R,s beyond those predicates; for (c)–(e) R,s>0, ε and f satisfying IsAnalyticPerturbation R s ε f; then the points, k and Fourier indices in the respective clauses
SOURCE_CONCLUSION: (a) IsSolutionOn H U J z ⟺ IsSolutionOn H̃ U J (Λ∘z) (same time, same actions); (b) ω_{h̃} = 2πω_h, D²h̃_ℝ = 2πD²h_ℝ; QC(m) ⟹ QC(2πm) on the same U; B(M) ⟹ partials of h̃_ℝ bounded by 2πM; M_ℂ → 2πM_ℂ, ω_min → 2πω_min, ¦ω̃¦₂ = 2π¦ω¦₂; (c) f̃ holomorphic on {¦Im φ¦ < 2πs} × B(0,R)_s with ¦f̃¦ ≤ 2πε, strip T_ρ ↔ width 2πρ; (d) f̃(φ+2πk,I) = f̃(φ,I) for k ∈ ℤⁿ; (e) f̃(φ,I) = Σ_k f̃^_k(I) e^{ik·φ}, f̃^_k = 2πf^_k, f^_k(I) = ∫_{[0,1]ⁿ} f(θ,I)e^{−2πik·θ}dθ, whenever the Fourier series of f(·,I) converges to f (coefficient radius s' = 2πρ)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:pc-chain, stepN:p1:pc-field, stepN:p1:pc-scalar, bpN:p0:sol#IsSolutionOn, bpN:p0:realH#realHamiltonian, bpN:p0:qc#IsStrictlyQuasiConvex, bpN:p0:bm#HasDerivativeBounds, bpN:p0:hess#HasComplexHessianBound, bpN:p0:pert#IsAnalyticPerturbation, bpN:p0:freq#frequencyMap, bpN:p0:realpart#realPart, bpN:p0:cdomain#complexDomain
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:pc-chain | blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L191-L191 | proof step of this result
EDGE: stepN:p1:pc-field | blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L193-L193 | proof step of this result
EDGE: stepN:p1:pc-scalar | blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L195-L195 | proof step of this result
EDGE: bpN:p0:sol#IsSolutionOn | blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L181-L181 | IsSolutionOn in (a)
EDGE: bpN:p0:realH#realHamiltonian | blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L179-L179 | H̃ = H_{h̃,f̃}
EDGE: bpN:p0:qc#IsStrictlyQuasiConvex | blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L182-L182 | QC in (b)
EDGE: bpN:p0:bm#HasDerivativeBounds | blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L183-L183 | B(M) in (b)
EDGE: bpN:p0:hess#HasComplexHessianBound | blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L183-L183 | complex Hessian bound in (b)
EDGE: bpN:p0:pert#IsAnalyticPerturbation | blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L179-L179 | IsAnalyticPerturbation in (c)-(e)
EDGE: bpN:p0:freq#frequencyMap | blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L182-L182 | ω_h̃
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L182-L182 | D²h̃_ℝ
EDGE: bpN:p0:cdomain#complexDomain | blueprint-N/parts/p1-interfaces.tex#bpN:p1:period-convert@L184-L184 | D_s(R) and B(0,R)_s
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.periodLift, tildeH, tildeh, tildef, realHamiltonian_tilde, isSolutionOn_tilde_iff, frequencyMap_tildeh, fderiv_fderiv_realPart_tildeh, tilde_hypotheses, tildef_domain, tildef_periodic, tildef_fourier (KAM/Nekhoroshev/Interfaces/Period.lean)
LEAN_NOTE: audit P1-4 PASS WITH NOTES; clauses (a)-(e) all covered (e) under convergence input
NOTE: the statement says the source is sources.md/Pos93 (provenance only); K:bp:p1:summation is cited in (e) and used at stepN:p1:pc-scalar. The \source in the statement is provenance

NODE: stepN:p1:pc-chain
KIND: step
TITLE: Chain rule
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-chain@L191-L191
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-chain@L191-L191
CONTRACT_ID: stepN:p1:pc-chain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H̃ = 2π H∘Λ^{-1}; Λ linear isomorphism
SOURCE_QUANTIFIERS: as period-convert
SOURCE_CONCLUSION: H̃ differentiable at Λz iff H at z, ∂_{I_i}H̃(Λz) = 2π∂_{I_i}H(z), ∂_{φ_i}H̃(Λz) = ∂_{θ_i}H(z)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1
REVIEWER: sol-review-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:pc-field
KIND: step
TITLE: Vector field
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-field@L193-L193
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-field@L193-L193
CONTRACT_ID: stepN:p1:pc-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; H arbitrary; Λ(θ,I)=(2πθ,I); H̃=2πH∘Λ⁻¹; U,J arbitrary; z arbitrary, with IsSolutionOn H U J z in the forward implication (the transformed solution in the reverse implication)
SOURCE_QUANTIFIERS: as period-convert
SOURCE_CONCLUSION: X_{H̃}(Λz) = (2π∂_IH(z), −∂_θH(z)) = d/dt Λz iff ż = X_H(z); the condition z(t)_2 ∈ U unchanged: this is (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:pc-chain, bpN:p0:vf#hamiltonianVectorField, bpN:p0:sol#IsSolutionOn
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:pc-chain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-field@L193-L193 | derivatives of H̃
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-field@L193-L193 | X_H, X_{H̃}
EDGE: bpN:p0:sol#IsSolutionOn | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-field@L193-L193 | clauses of IsSolutionOn
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:pc-scalar
KIND: step
TITLE: Scalars
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-scalar@L195-L195
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-scalar@L195-L195
CONTRACT_ID: stepN:p1:pc-scalar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ∈ ℕ; h,f arbitrary; h̃=2πh, f̃(φ,I)=2πf(φ/(2π),I); for (b), each indicated bound/predicate is assumed only for its corresponding implication; for (c)–(e), R,s>0 and IsAnalyticPerturbation R s ε f; for (e), Fourier convergence as stated
SOURCE_QUANTIFIERS: as period-convert
SOURCE_CONCLUSION: (b) by linearity of h ↦ ω_h, D^kh_ℝ and of the operator norm; (c)-(e) by φ = 2πθ, ¦Im φ¦ = 2π¦Im θ¦, e^{ik·φ} = e^{2πik·θ}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:freq#frequencyMap, bpN:p0:realpart#realPart, bpN:p0:qc#IsStrictlyQuasiConvex, bpN:p0:bm#HasDerivativeBounds, bpN:p0:hess#HasComplexHessianBound, bpN:p0:pert#IsAnalyticPerturbation, bpN:p0:strip#complexStrip, bpN:p0:cdomain#complexDomain
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:freq#frequencyMap | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-scalar@L195-L195 | ω_h linear in h
EDGE: bpN:p0:realpart#realPart | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-scalar@L195-L195 | D^kh_ℝ linear in h
EDGE: bpN:p0:qc#IsStrictlyQuasiConvex | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-scalar@L195-L195 | QC for h̃
EDGE: bpN:p0:bm#HasDerivativeBounds | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-scalar@L195-L195 | B(M) for h̃
EDGE: bpN:p0:hess#HasComplexHessianBound | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-scalar@L195-L195 | Hessian bound for h̃
EDGE: bpN:p0:pert#IsAnalyticPerturbation | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-scalar@L195-L195 | premises (c),(d) on f
EDGE: bpN:p0:strip#complexStrip | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-scalar@L195-L195 | strip of width 2πρ
EDGE: bpN:p0:cdomain#complexDomain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:pc-scalar@L195-L195 | domain substitution
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-delta-N-a
REVIEWER: sol-delta2-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Clause (e) assumes Fourier convergence explicitly at L186. The proof at L195 substitutes φ=2πθ into that given expansion; it does not apply the K summation theorem. The K citation at L186 is a pointer to a sufficient convergence result, not a prerequisite of this conditional substitution.

NODE: bpN:p1:norm-convert
KIND: lemma
TITLE: From sup norm on a strip to the weighted Fourier norm
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-convert@L198-L204
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-convert@L205-L209
CONTRACT_ID: bpN:p1:norm-convert
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u : T_ρ → ℂ holomorphic, bounded and 1-periodic; ¦u¦_ρ = sup_{T_ρ}¦u¦; 0 < δ < ρ; for I-dependent u(θ,I), fixed I
SOURCE_QUANTIFIERS: n; ρ, δ with 0 < δ < ρ; u
SOURCE_CONCLUSION: Σ_{k∈ℤⁿ} ¦û_k¦ e^{2π¦k¦₁(ρ−δ)} ≤ coth(πδ)ⁿ ¦u¦_ρ (Pöschel weight e^{¦k¦₁s'}, s' = 2π(ρ−δ)); conversely ¦u¦_ρ ≤ Σ_k ¦û_k¦ e^{2π¦k¦₁ρ}; for I-dependent u the same constant for each fixed I
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:strip#complexStrip, bpN:p1:norm-convert#converse
ROUTES: bpN:p1:norm-convert#decay-route, bpN:p1:norm-convert#summation-route
ROUTE_FOR: -
EDGE: bpN:p0:strip#complexStrip | blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-convert@L199-L199 | T_ρ
EDGE: bpN:p1:norm-convert#converse | blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-convert@L202-L202 | converse comparison included in the lemma
EDGE: bpN:p1:norm-convert#decay-route | blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-convert@L205-L209 | alternative derivation offered by the proof (route)
EDGE: bpN:p1:norm-convert#summation-route | blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-convert@L205-L209 | alternative derivation offered by the proof (route)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: PROVED
LEAN_REF: norm_convert, norm_convert_converse (KAM/Nekhoroshev/Interfaces/ConstantsAnalytic.lean)
LEAN_NOTE: audit P1-6 PASS WITH NOTES
NOTE: Conjunctive prerequisites are the strip definition and the converse. Either forward route suffices: decay plus geometric sum, or K summation directly. All use the frozen period-one weight e^{2π¦k¦₁ρ}.

NODE: stepN:p1:nc-decay
KIND: step
TITLE: Decay
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L206
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L206
CONTRACT_ID: stepN:p1:nc-decay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic bounded 1-periodic on T_ρ; ρ' ∈ (ρ−δ,ρ)
SOURCE_QUANTIFIERS: as norm-convert
SOURCE_CONCLUSION: ¦û_k¦ ≤ e^{−2π¦k¦₁ρ'}¦u¦_ρ, hence (ρ' ↑ ρ) ¦û_k¦e^{2π¦k¦₁(ρ−δ)} ≤ e^{−2πδ¦k¦₁}¦u¦_ρ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:decay, bpN:p0:strip#complexStrip, bpN:p4:n-zero
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:decay | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L206 | Fourier coefficient decay
EDGE: bpN:p0:strip#complexStrip | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L206 | strip T_ρ
EDGE: bpN:p4:n-zero | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L206 | case n=0: singleton branch (T_ρ a point, Z^0={0}, û_0=u, ¦u¦_ρ=¦u¦) replaces the K strip decay
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-delta-N-a+sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Explicit cases n=0 (Remark bpN:p4:n-zero, no K result) and n≥1 (K decay under the standing convention); the earlier SOURCE_GAP about the missing n=0 branch is supplied. First forward route only: use coefficient decay, then take the scalar limit ρ′↑ρ. The text offers K summation as an alternative for the aggregate weighted bound; see the parent's route nodes.

NODE: stepN:p1:nc-sum
KIND: step
TITLE: Sum
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-sum@L208-L208
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-sum@L208-L208
CONTRACT_ID: stepN:p1:nc-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u : T_ρ → ℂ holomorphic, bounded and 1-periodic; ¦u¦_ρ = sup_{T_ρ}¦u¦; 0 < δ < ρ; for I-dependent u(θ,I), fixed I
SOURCE_QUANTIFIERS: as norm-convert
SOURCE_CONCLUSION: Σ_k e^{−2πδ¦k¦₁} = coth(πδ)ⁿ, so the weighted sum is ≤ coth(πδ)ⁿ¦u¦_ρ (pointwise in I)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:exp-sums, stepN:p1:nc-decay, bpN:p4:n-zero
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:exp-sums | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-sum@L208-L208 | geometric sums (b) with x = 2πδ
EDGE: stepN:p1:nc-decay | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-sum@L208-L208 | per-k bound
EDGE: bpN:p4:n-zero | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-sum@L208-L208 | case n=0: Z^0={0}, single term k=0 equal to 1=coth(πδ)^0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-global-N+sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Explicit cases: n≥1 uses K exp-sums(b); n=0 the sum is the single term k=0 (Remark bpN:p4:n-zero); the earlier SOURCE_GAP about the missing n=0 branch is supplied.

NODE: bpN:p1:constants
KIND: lemma
TITLE: Constants dictionary for N-HEAD-C
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L213-L235
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L236-L252
CONTRACT_ID: bpN:p1:constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 3 (only n ≥ 2 used by Pöschel); R, s, M, m, M_ℂ, ω_min > 0; definitions in constants#data; (a)–(c) no h,f premises; (d) h satisfies (H1)–(H5); (e) f satisfies (H6) with ε, and only the second inequality assumes ε≤ε₀; (f),(g) state I₀∈B(0,R/2) but do not explicitly bind h or repeat its frequency/derivative premises; (h) ε>0, ε_P=Fε, and T₀,Ω₀ as in (g)
SOURCE_QUANTIFIERS: n≥3; R,s,M,m,M_ℂ,ω_min>0; then all dictionary definitions in order; (a)–(c) unconditional in h,f; (d) each h with H1–H5; (e) each f,ε with H6 and the additional threshold for its smallness conclusion; (f),(g) I₀∈B(0,R/2), with the source’s h-premise scope left unresolved; (h) ε>0
SOURCE_CONCLUSION: (a) all constants positive, finite, depending only on (n, R, s, M, m, M_ℂ, ω_min), C ε₀^a ≤ R/4, 0 < ε₀ ≤ ε_*/F; (b) r₀ ≤ ℓ_P/(2M_P) (= hypothesis s-r of Definition bpN:p9:setting), r₀ ≤ 4ℓ_P/m_P, A ≥ 22, R₀ = r₀/A ≤ r₀/22 ≤ R/176; (c) V_{r₀}P ⊂ B(0,R)_s and U_{r₀}P ⊂ B(0,5R/8) ⊂ B(0,R); (d) (H1)-(H5) imply h̃ is (ℓ_P,μ_P)-quasi-convex on U_{r₀}P, complex Hessian norm of h̃ ≤ M_P on V_{r₀}P, hypotheses of Pöschel Theorem 1 (m_P, M_P, r₀ ≤ 4ℓ_P/m_P) plus r₀ ≤ ℓ_P/(2M_P); (e) (H6) ⟹ Pöschel norm of f̃ ≤ Fε; additionally Fε ≤ ε_{0,P} if ε≤ε₀; (f) for I_0 ∈ B(0,R/2): ¦ω̃(I_0)¦₂ ≥ 2πω_min > π ω_min ≥ m_P r₀/8 (exceptional branch empty); (g) 0 < 2πω_min ≤ Ω₀ ≤ 2π√n M ≤ 2πnM, T_0 = A_P²s₀/Ω₀ ≥ 2T; (h) R₀(ε_P/ε_{0,P})^a = C ε^a, the actual radius of Theorem bpN:p9:thm1(a) is ½C ε^a ≤ C ε^a, and its time scale is T₀exp(cε^{−a}), and T exp(cε^{−a}) ≤ ½ T₀ exp(cε^{−a})
CONSTANT_SCOPE: C, T, c, ε₀ (and all of q, B_c, μ, ℓ, r₀, A, s₀, σ, F, ε_*) depend only on (n, R, s, M, m, M_ℂ, ω_min); not on h, f, ε, θ₀, I₀, nor on the bound A of IsAnalyticIntegrable(iii); order of choice q, B_c, μ, ℓ, r₀, A; then s₀, σ, F; ε_*; C, c; T; ε₀
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:co-pos, stepN:p1:co-size, stepN:p1:co-tubes, stepN:p1:co-qc, stepN:p1:co-pert, stepN:p1:co-exc, stepN:p1:co-time, stepN:p1:co-conc, bpN:p9:setting, bpN:p4:domains, bpN:p4:norm, bpN:p0:integrable#IsAnalyticIntegrable, bpN:p0:hess#HasComplexHessianBound, bpN:p0:qc#IsStrictlyQuasiConvex, bpN:p0:bm#HasDerivativeBounds, bpN:p0:pert#IsAnalyticPerturbation, bpN:p0:ball#actionBall, bpN:p0:rdomain#realActionDomain, bpN:p0:freq#frequencyMap, bpN:p1:qc-convert, bpN:p1:hessian-convert, bpN:p1:constants#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:co-pos | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L237-L237 | proof step of this result
EDGE: stepN:p1:co-size | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L239-L239 | proof step of this result
EDGE: stepN:p1:co-tubes | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L241-L241 | proof step of this result
EDGE: stepN:p1:co-qc | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L243-L243 | proof step of this result
EDGE: stepN:p1:co-pert | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L245-L245 | proof step of this result
EDGE: stepN:p1:co-exc | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L247-L247 | proof step of this result
EDGE: stepN:p1:co-time | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L249-L249 | proof step of this result
EDGE: stepN:p1:co-conc | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L251-L251 | proof step of this result
EDGE: bpN:p9:setting | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L230-L230 | defined Ω₀ and Theorem-1 parameters used in the comparison; no assumption that its hypotheses already hold
EDGE: bpN:p4:domains | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L226-L226 | tubes V_{r₀}P, U_{r₀}P
EDGE: bpN:p4:norm | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L228-L228 | Pöschel weighted norm of f̃
EDGE: bpN:p0:integrable#IsAnalyticIntegrable | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L227-L227 | (H1)
EDGE: bpN:p0:hess#HasComplexHessianBound | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L227-L227 | (H2)
EDGE: bpN:p0:qc#IsStrictlyQuasiConvex | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L227-L227 | (H4)
EDGE: bpN:p0:bm#HasDerivativeBounds | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L227-L227 | (H5)
EDGE: bpN:p0:pert#IsAnalyticPerturbation | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L228-L228 | (H6)
EDGE: bpN:p0:ball#actionBall | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L229-L229 | B(0,R/2), B(0,R)
EDGE: bpN:p0:rdomain#realActionDomain | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L227-L227 | 𝓑_s(R) in (H4),(H5)
EDGE: bpN:p0:freq#frequencyMap | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L229-L229 | ω_h in (f),(g)
EDGE: bpN:p1:qc-convert | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L227-L227 | (d): quasi-convexity form
EDGE: bpN:p1:hessian-convert | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L227-L227 | (d): Hessian bound
EDGE: bpN:p1:constants#data | blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L214-L221 | local constants used in all clauses
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: PROVED
LEAN_REF: const_pos, const_eps0, const_size, const_conclusion (KAM/Nekhoroshev/Interfaces/Constants.lean); const_tubes, const_hyp, const_perturbation, const_exceptional, const_time (KAM/Nekhoroshev/Interfaces/ConstantsAnalytic.lean)
LEAN_NOTE: composite of audits P1-5 PASS WITH NOTES + P1-6 PASS WITH NOTES; parts (a)-(h)
NOTE: SOURCE_GAP: clauses (f),(g) and their proof steps use h-frequency and derivative bounds, but the lemma binds h with H1–H5 only inside clause (d). Preserve the raw conditional scope and expose the missing attachment at co-exc/co-time. No frozen anchor is changed.

NODE: stepN:p1:co-pos
KIND: step
TITLE: Positivity and dependence
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pos@L237-L237
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pos@L237-L237
CONTRACT_ID: stepN:p1:co-pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 3 (only n ≥ 2 used by Pöschel); R, s, M, m, M_ℂ, ω_min > 0; local dictionary definitions of constants#data
SOURCE_QUANTIFIERS: as constants
SOURCE_CONCLUSION: all constants positive finite, ε₀ > 0, C ε₀^a ≤ R/4 since ((R/4C)^{2n})^{1/(2n)} = R/(4C); inputs only (n,R,s,M,m,M_ℂ,ω_min): (a)
CONSTANT_SCOPE: All dictionary constants depend only on (n,R,s,M,m,M_ℂ,ω_min); h,f,ε,I₀ are later conditional data.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:constants#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:constants#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pos@L237-L237 | local dictionary constants used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.const_pos, const_eps0 (KAM/Nekhoroshev/Interfaces/Constants.lean)
LEAN_NOTE: audit P1-5 PASS WITH NOTES; clause (a) positivity and C eps0^a <= R/4, eps0 <= eps*/F
NOTE: -

NODE: stepN:p1:co-size
KIND: step
TITLE: Size relations
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-size@L239-L239
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-size@L239-L239
CONTRACT_ID: stepN:p1:co-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 3 (only n ≥ 2 used by Pöschel); R, s, M, m, M_ℂ, ω_min > 0; local dictionary definitions of constants#data
SOURCE_QUANTIFIERS: as constants
SOURCE_CONCLUSION: A ≥ 22; r₀ ≤ ℓ_P/(2M_P); r₀ ≤ 4ℓ_P/m_P; R₀ ≤ r₀/22 ≤ R/176: (b)
CONSTANT_SCOPE: All dictionary constants depend only on (n,R,s,M,m,M_ℂ,ω_min); h,f,ε,I₀ are later conditional data.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:co-pos, bpN:p1:constants#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:co-pos | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-size@L239-L239 | positivity of the constants
EDGE: bpN:p1:constants#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-size@L239-L239 | local dictionary constants used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.const_size (KAM/Nekhoroshev/Interfaces/Constants.lean)
LEAN_NOTE: audit P1-5 PASS WITH NOTES; clause (b) all five inequalities
NOTE: -

NODE: stepN:p1:co-tubes
KIND: step
TITLE: Tubes
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-tubes@L241-L241
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-tubes@L241-L241
CONTRACT_ID: stepN:p1:co-tubes
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 3 (only n ≥ 2 used by Pöschel); R, s, M, m, M_ℂ, ω_min > 0; local dictionary definitions of constants#data
SOURCE_QUANTIFIERS: as constants
SOURCE_CONCLUSION: (c): V_{r₀}P ⊂ B(0,R)_s and U_{r₀}P ⊂ B(0,5R/8) ⊂ B(0,R)
CONSTANT_SCOPE: All dictionary constants depend only on (n,R,s,M,m,M_ℂ,ω_min); h,f,ε,I₀ are later conditional data.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:realdomain, bpN:p4:domains, bpN:p1:constants#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:realdomain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-tubes@L241-L241 | Lemma realdomain (c)
EDGE: bpN:p4:domains | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-tubes@L241-L241 | tubes V_{r₀}P, U_{r₀}P
EDGE: bpN:p1:constants#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-tubes@L241-L241 | local dictionary constants used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p1:co-qc
KIND: step
TITLE: Quasi-convexity and Hessian
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-qc@L243-L243
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-qc@L243-L243
CONTRACT_ID: stepN:p1:co-qc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 3 (only n ≥ 2 used by Pöschel); R, s, M, m, M_ℂ, ω_min > 0; local dictionary definitions of constants#data; h satisfies H1–H5 of N-HEAD-C
SOURCE_QUANTIFIERS: as constants
SOURCE_CONCLUSION: (d): (ℓ_P,μ_P)-quasi-convexity of h̃ on U_{r₀}P; Euclidean Hessian norm of Q̃ ≤ 2πnM_ℂ ≤ M_P on V_{r₀}P; Pöschel A = 11B_c/μ = A; r₀ ≤ ℓ/(2B_c)
CONSTANT_SCOPE: All dictionary constants depend only on (n,R,s,M,m,M_ℂ,ω_min); h,f,ε,I₀ are later conditional data.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:qc-convert, bpN:p1:period-convert, bpN:p1:hessian-convert, stepN:p1:co-tubes, stepN:p1:co-size, bpN:p1:constants#data, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:qc-convert | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-qc@L243-L243 | alternative (b) on U_{r₀}P
EDGE: bpN:p1:period-convert | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-qc@L243-L243 | clause (b): scaling by 2π
EDGE: bpN:p1:hessian-convert | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-qc@L243-L243 | Euclidean operator norm of Q̃
EDGE: stepN:p1:co-tubes | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-qc@L243-L243 | U_{r₀}P ⊂ B(0,R), V_{r₀}P ⊂ B(0,R)_s
EDGE: stepN:p1:co-size | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-qc@L243-L243 | r₀ ≤ ℓ/(2B_c) and A
EDGE: bpN:p1:constants#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-qc@L243-L243 | local dictionary constants used directly
EDGE: bpN:p4:domains | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-qc@L243-L243 | V_{r₀}P or its real slice is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-delta-N-a
REVIEWER: sol-delta2-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: The current hessian-convert contract includes the standing §s-holo data IsAnalyticPerturbation R s ε f (L68–70 and its SOURCE_HYPOTHESES). This application supplies hypotheses on h only and no such f,ε datum. The quoted Hessian estimate is h-only in its proof, but that premise-free projection has not been recorded as a distinct source result. Keep the present source premises unchanged and expose the conditional-application mismatch.

NODE: stepN:p1:co-pert
KIND: step
TITLE: Perturbation
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pert@L245-L245
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pert@L245-L245
CONTRACT_ID: stepN:p1:co-pert
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 3 (only n ≥ 2 used by Pöschel); R, s, M, m, M_ℂ, ω_min > 0; local dictionary definitions of constants#data; f satisfies H6 with ε; for Fε≤ε_{0,P}, ε≤ε₀
SOURCE_QUANTIFIERS: as constants
SOURCE_CONCLUSION: (e): Pöschel norm of f̃ ≤ coth(πs/4)ⁿ·2π ε = Fε ≤ ε_* = ε_{0,P} for ε ≤ ε₀
CONSTANT_SCOPE: All dictionary constants depend only on (n,R,s,M,m,M_ℂ,ω_min); h,f,ε,I₀ are later conditional data.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:pert#IsAnalyticPerturbation, stepN:p1:co-tubes, bpN:p1:norm-convert, bpN:p1:period-convert, bpN:p0:cdomain#complexDomain, bpN:p4:norm, bpN:p1:constants#data, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:pert#IsAnalyticPerturbation | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pert@L245-L245 | (H6): ¦f¦ ≤ ε on D_s(R)
EDGE: stepN:p1:co-tubes | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pert@L245-L245 | V_{r₀}P ⊂ B(0,R)_s
EDGE: bpN:p1:norm-convert | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pert@L245-L245 | sup norm to weighted norm with ρ = 3s/4, δ = s/4
EDGE: bpN:p1:period-convert | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pert@L245-L245 | clause (e): coefficient scaling by 2π
EDGE: bpN:p0:cdomain#complexDomain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pert@L245-L245 | D_s(R) ⊃ T_{3s/4} × V_{r₀}P
EDGE: bpN:p4:norm | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pert@L245-L245 | Pöschel weighted norm
EDGE: bpN:p1:constants#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pert@L245-L245 | local dictionary constants used directly
EDGE: bpN:p4:domains | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-pert@L245-L245 | V_{r₀}P or its real slice is used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: Only numerical conjunct proved (const_perturbation_arith, Constants.lean); Poschel-norm bound of f-tilde not proved; audit P1-5
NOTE: -

NODE: stepN:p1:co-exc
KIND: step
TITLE: Exceptional branch
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-exc@L247-L247
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-exc@L247-L247
CONTRACT_ID: stepN:p1:co-exc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 3 (only n ≥ 2 used by Pöschel); R, s, M, m, M_ℂ, ω_min > 0; local dictionary definitions of constants#data; I₀∈B(0,R/2); the source does not explicitly state the needed hypotheses on h here
SOURCE_QUANTIFIERS: as constants
SOURCE_CONCLUSION: (f): ¦ω̃(I_0)¦₂ = 2π¦ω(I_0)¦₂ ≥ 2πω_min > πω_min ≥ m_P r₀/8
CONSTANT_SCOPE: All dictionary constants depend only on (n,R,s,M,m,M_ℂ,ω_min); h,f,ε,I₀ are later conditional data.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:qc-convert, bpN:p1:period-convert, bpN:p1:constants#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:qc-convert | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-exc@L247-L247 | (c): ¦ω¦₂ ≥ ω_min
EDGE: bpN:p1:period-convert | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-exc@L247-L247 | ¦ω̃¦₂ = 2π¦ω¦₂
EDGE: bpN:p1:constants#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-exc@L247-L247 | local dictionary constants used directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: Only numerical threshold comparisons proved (const_exceptional_arith, Constants.lean); frequency lower bound not; audit P1-5
NOTE: SOURCE_GAP: the lemma explicitly assumes H1–H5 only in clause (d). This clause needs the corresponding hypotheses on h (H3 for the frequency lower bound; H5 also for the time upper bound). The cited conditional conversions do not supply those premises. No such premise is added to the source contract.

NODE: stepN:p1:co-time
KIND: step
TITLE: Time
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-time@L249-L249
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-time@L249-L249
CONTRACT_ID: stepN:p1:co-time
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 3 (only n ≥ 2 used by Pöschel); R, s, M, m, M_ℂ, ω_min > 0; local dictionary definitions of constants#data; I₀∈B(0,R/2); the source does not explicitly state the needed hypotheses on h here
SOURCE_QUANTIFIERS: as constants
SOURCE_CONCLUSION: (g): Ω₀ ≤ 2π√nM ≤ 2πnM, Ω₀ ≥ 2πω_min > 0, T_0 ≥ 2T
CONSTANT_SCOPE: All dictionary constants depend only on (n,R,s,M,m,M_ℂ,ω_min); h,f,ε,I₀ are later conditional data.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:partials, bpN:p1:qc-convert, bpN:p1:realdomain, bpN:p1:period-convert, bpN:p1:constants#data, bpN:p9:setting, stepN:p1:co-size
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:partials | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-time@L249-L249 | ¦ω(I)¦₂ ≤ √n M on 𝓑_s(R)
EDGE: bpN:p1:qc-convert | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-time@L249-L249 | (c): ¦ω(I_0)¦₂ ≥ ω_min
EDGE: bpN:p1:realdomain | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-time@L249-L249 | B(0,5R/8) ⊂ 𝓑_s(R)
EDGE: bpN:p1:period-convert | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-time@L249-L249 | ω̃ = 2πω
EDGE: bpN:p1:constants#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-time@L249-L249 | local dictionary constants used directly
EDGE: bpN:p9:setting | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-time@L249-L249 | Ω₀ is the maximum on the closed Euclidean R₀-ball
EDGE: stepN:p1:co-size | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-time@L249-L249 | uses R₀≤r₀ and R₀≤R/176 to place the closed frequency ball in B(0,5R/8)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-delta-N-a
REVIEWER: sol-delta2-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: Only numerical conjunct proved (const_time_arith, Constants.lean); Omega0 bounds not; audit P1-5
NOTE: SOURCE_GAP: In addition to the already recorded missing h-bound scope, the current partials contract inherits IsAnalyticPerturbation R s ε f from §s-holo. This application does not bind or supply that datum. No source hypothesis is added here. SOURCE_GAP: the lemma explicitly assumes H1–H5 only in clause (d). This clause needs the corresponding hypotheses on h (H3 for the frequency lower bound; H5 also for the time upper bound). The cited conditional conversions do not supply those premises. No such premise is added to the source contract.

NODE: stepN:p1:co-conc
KIND: step
TITLE: Exponent and constants
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-conc@L251-L251
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-conc@L251-L251
CONTRACT_ID: stepN:p1:co-conc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 3 (only n ≥ 2 used by Pöschel); R, s, M, m, M_ℂ, ω_min > 0; local dictionary definitions of constants#data; ε>0, ε_P=Fε; T₀,Ω₀ as in clause (g), whose h-premise scope is unresolved
SOURCE_QUANTIFIERS: as constants
SOURCE_CONCLUSION: (h): R₀(Fε/ε_*)^a = Cε^a and (s₀/(6√n))(ε_*/(Fε))^a = cε^{−a}; the radius of Theorem 1(a) is ½Cε^a ≤ Cε^a (max norm); T ≤ T_0/2
CONSTANT_SCOPE: All dictionary constants depend only on (n,R,s,M,m,M_ℂ,ω_min); h,f,ε,I₀ are later conditional data.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:co-time, bpN:p1:constants#data, bpN:p9:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p1:co-time | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-conc@L251-L251 | T_0 ≥ 2T
EDGE: bpN:p1:constants#data | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-conc@L251-L251 | local dictionary constants used directly
EDGE: bpN:p9:setting | blueprint-N/parts/p1-interfaces.tex#stepN:p1:co-conc@L251-L251 | defined parameters of the Theorem-1 formula; this is not an application of its theorem conclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p1+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Expression comparison only. Do not depend on Theorem 1 as a proved result; the time inequality uses co-time, which exposes the missing h-premise scope.

NODE: bpN:p1:norm-convert#decay-route
KIND: route
TITLE: Forward bound via coefficient decay and geometric sum
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L208
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L208
CONTRACT_ID: bpN:p1:norm-convert#decay-route
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u : T_ρ → ℂ holomorphic, bounded and 1-periodic; ¦u¦_ρ = sup_{T_ρ}¦u¦; 0 < δ < ρ; for I-dependent u(θ,I), fixed I
SOURCE_QUANTIFIERS: n; ρ,δ,u with 0<δ<ρ
SOURCE_CONCLUSION: Σ_k ¦û_k¦e^{2π¦k¦₁(ρ−δ)} ≤ coth(πδ)^n ¦u¦_ρ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p1:nc-decay, stepN:p1:nc-sum
ROUTES: -
ROUTE_FOR: bpN:p1:norm-convert
EDGE: stepN:p1:nc-decay | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L206 | coefficient bound after scalar limit
EDGE: stepN:p1:nc-sum | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-sum@L208-L208 | sum the coefficient bounds
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p1:norm-convert#summation-route
KIND: route
TITLE: Forward bound directly by the imported summation converse
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L206
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L206
CONTRACT_ID: bpN:p1:norm-convert#summation-route
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u : T_ρ → ℂ holomorphic, bounded and 1-periodic; ¦u¦_ρ = sup_{T_ρ}¦u¦; 0 < δ < ρ; for I-dependent u(θ,I), fixed I
SOURCE_QUANTIFIERS: n; ρ,δ,u with 0<δ<ρ
SOURCE_CONCLUSION: Σ_k ¦û_k¦e^{2π¦k¦₁(ρ−δ)} ≤ coth(πδ)^n ¦u¦_ρ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:summation, bpN:p4:n-zero
ROUTES: -
ROUTE_FOR: bpN:p1:norm-convert
EDGE: K:bp:p1:summation | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L206 | the explicitly offered direct alternative; all bounded holomorphic periodic premises and 0<δ<ρ are supplied
EDGE: bpN:p4:n-zero | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L206 | the explicit n=0 singleton branch precedes the positive-dimension K summation alternative
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-global-N
REVIEWER: sol-delta-N-global2
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: For n=0 use the explicit singleton case at p1 L206 and bpN:p4:n-zero; for n≥1 use the imported K summation converse. The source supplies both cases, so the earlier missing-dimension SOURCE_GAP is resolved.

NODE: bpN:p1:norm-convert#converse
KIND: step
TITLE: Converse comparison from Fourier reconstruction
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-convert@L202-L202
PROOF_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-convert@L202-L206
CONTRACT_ID: bpN:p1:norm-convert#converse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u : T_ρ → ℂ holomorphic, bounded and 1-periodic; ¦u¦_ρ = sup_{T_ρ}¦u¦; 0 < δ < ρ; for I-dependent u(θ,I), fixed I
SOURCE_QUANTIFIERS: n; ρ,δ,u with 0<δ<ρ
SOURCE_CONCLUSION: ¦u¦_ρ ≤ Σ_k ¦û_k¦ e^{2π¦k¦₁ρ}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:summation, bpN:p4:n-zero
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:summation | blueprint-N/parts/p1-interfaces.tex#bpN:p1:norm-convert@L202-L203 | Fourier reconstruction and the forward sup bound when the full weighted sum is finite; otherwise the extended upper bound is immediate
EDGE: bpN:p4:n-zero | blueprint-N/parts/p1-interfaces.tex#stepN:p1:nc-decay@L206-L206 | the n=0 branch explicitly proves the converse as the identity abs(u)<=abs(u)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-global-N
REVIEWER: sol-delta-N-global2
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: For n=0 the proof at p1 L206 explicitly reduces the converse to abs(u)<=abs(u), using the singleton Fourier coefficient. For n≥1 use K summation/Fourier reconstruction, with the infinite full weighted-sum case immediate. This is common to both forward routes; the earlier missing-dimension SOURCE_GAP is resolved.

NODE: bpN:p1:constants#data
KIND: definition
TITLE: Local constants and Pöschel parameter dictionary
STATEMENT_SOURCE: blueprint-N/parts/p1-interfaces.tex#bpN:p1:constants@L214-L221
PROOF_SOURCE: -
CONTRACT_ID: bpN:p1:constants#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n ≥ 3 (only n ≥ 2 used by Pöschel); R, s, M, m, M_ℂ, ω_min > 0
SOURCE_QUANTIFIERS: n≥3; R,s,M,m,M_ℂ,ω_min>0; then successive definitions in the displayed order
SOURCE_CONCLUSION: Defines a = 1/(2n); q = m/n, B_c = nM_ℂ+q, μ = q/2, ℓ = ω_min q/(8(B_c+q)), r₀ = min(s/2, R/8, ℓ/(2B_c), 4ω_min/μ), A = 11B_c/μ, s₀ = πs, σ = πs/4, F = 2π coth^n(πs/4), ε_* = 2πμ r₀²/(2^{10}A^{2n}), C = (r₀/A)(F/ε_*)^a, c = (s₀/(6√n))(ε_*/F)^a, T = A²s₀/(4πnM), ε₀ = min(ε_*/F, (R/(4C))^{2n}); Pöschel data m_P = 2πμ, ℓ_P = 2πℓ, M_P = 2πB_c, A_P = 11M_P/m_P = A, ε_{0,P} = m_P r₀²/(2^{10}A_P^{2n}) = ε_*, R₀ = r₀/A, P = {J ∈ ℝⁿ : ¦J¦ ≤ R/2}
CONSTANT_SCOPE: Every defined constant depends only on (n,R,s,M,m,M_ℂ,ω_min), before h,f,ε,θ₀,I₀. The dictionary A is distinct from the existential bound in IsAnalyticIntegrable.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-N-a
REVIEWER: sol-delta-N-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.HeadParams, HeadParams.Pos, HeadParams.expo, q, B, mu, ell, r0, A, s0, sigma, F, epsStar, C, c, T, eps0, centralSet (KAM/Nekhoroshev/Interfaces/Constants.lean)
LEAN_NOTE: Definition formalized, nothing to prove; audit P1-5 PASS WITH NOTES
NOTE: Local definition portion split from the lemma package so its proof steps can consume the data without a parent cycle. Downstream users still consume bpN:p1:constants as required by SPEC.
