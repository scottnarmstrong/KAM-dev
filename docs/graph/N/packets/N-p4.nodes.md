NODE: bpN:p4:ext-param
KIND: external
TITLE: Holomorphic dependence on a parameter
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:ext-param@L23-L25
PROOF_SOURCE: -
CONTRACT_ID: bpN:p4:ext-param
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q ⊂ ℝ^p compact box; U ⊂ ℂ^q open; G: Q×U → ℂ^d continuous, holomorphic in I ∈ U for each x ∈ Q, with D_I G continuous on Q×U
SOURCE_QUANTIFIERS: p, q, d; Q; U; G
SOURCE_CONCLUSION: g(I) = ∫_Q G(x,I) dx is holomorphic on U and Dg(I) = ∫_Q D_I G(x,I) dx
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: external item (E1) of Part 4's list (the Mathlib hint in the text is not a source premise)

NODE: bpN:p4:ext-weier
KIND: claim
TITLE: Uniform limits
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:ext-weier@L26-L27
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:ext-weier@L26-L180
CONTRACT_ID: bpN:p4:ext-weier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K_j holomorphic on an open U ⊂ ℂ^q (j ∈ ℕ); K_j → K uniformly on U
SOURCE_QUANTIFIERS: q; U; (K_j)_j; K; η > 0
SOURCE_CONCLUSION: K is holomorphic on U, and DK_j → DK uniformly on {z : P̄(z,η) ⊂ U} for each η > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:general-cauchy, K:bp:p1:uniform-limits
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:general-cauchy | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:ext-weier@L26-L27 | derivative part: Lemma general-cauchy applied to K_j−K_l (text: 'the derivatives by Lemma general-cauchy'; also L177)
EDGE: K:bp:p1:uniform-limits | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:ext-weier@L27-L27 | holomorphy of the uniform limit
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Weighted.uniform_limit_holomorphic (KAM/Weighted/Parametric.lean)
LEAN_NOTE: Holomorphy and uniform derivative convergence on closed-ball loci; audit W4-2 PASS WITH NOTES
NOTE: Modelled as a claim, not a pure external, per SPEC ruling: 'Exists in this form modulo that lemma' (L27) and L177 'This also gives ext-weier's derivative statement: apply it to K_j−K_l on the ball of radius η' (coverage item p4:prose-L177 is mapped here); PROOF_SOURCE spans the inline proof at L26–27 and the derivative argument at L177; the intervening results are not additional proof ingredients

NODE: bpN:p4:ext-series
KIND: external
TITLE: Series and integrals
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:ext-series@L28-L29
PROOF_SOURCE: -
CONTRACT_ID: bpN:p4:ext-series
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (i) nonnegative double series, resp. nonnegative integrands; (ii) two absolutely convergent series; (iii) a uniformly convergent series of functions on a box
SOURCE_QUANTIFIERS: series and integrals as quantified in each of the three standard facts
SOURCE_CONCLUSION: Tonelli for nonnegative double series and for integrals of nonnegative functions; the Cauchy product of two absolutely convergent series is absolutely convergent (sum of the products); termwise integration of a uniformly convergent series over a box
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: stays an external per SPEC; the \Kref to K:bp:p1:ext-integral is a pointer to the related termwise-integration statement, not a restatement

NODE: bpN:p4:domains
KIND: definition
TITLE: Domains
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:domains@L34-L39
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:domains@L40-L45
CONTRACT_ID: bpN:p4:domains
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m, n ≥ 0; D ⊂ ℂ^m any subset; r, s > 0
SOURCE_QUANTIFIERS: m, n; D; r, s; then z = (θ,I); a, b ≥ 0; r' ≤ r, s' ≤ s (resp. 0<r'<r, 0<s'<s)
SOURCE_CONCLUSION: defines V_rD = {I ∈ ℂ^m : ∃ I' ∈ D, ¦I−I'¦_∞ < r}, 𝒟_{r,s} = T_s × V_rD ⊂ ℂⁿ×ℂ^m, P̄(z;a,b) = {(θ',I') : ¦θ'−θ¦_∞ ≤ a, ¦I'−I¦_∞ ≤ b}; (a) V_rD and 𝒟_{r,s} are open and 𝒟_{r',s'} ⊂ 𝒟_{r,s} for r' ≤ r, s' ≤ s; (b) if 0<r'<r, 0<s'<s and z ∈ 𝒟_{r',s'} then P̄(z;s−s',r−r') ⊂ 𝒟_{r,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p4:dom-open, stepN:p4:dom-poly, bpN:p0:strip#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p4:dom-open | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:domains@L41-L41 | proof step of this result (a)
EDGE: stepN:p4:dom-poly | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:domains@L43-L43 | proof step of this result (b)
EDGE: bpN:p0:strip#complexStrip | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:domains@L36-L36 | T_s = {θ ∈ ℂⁿ : ¦Im θ¦_∞ < s} is the frozen strip (Kref bp:p0:domains; Part 4 Normalisation L13)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Weighted.polyNbhd, Dom, polydisc, isOpen_polyNbhd, isOpen_Dom, polyNbhd_mono, Dom_mono, polydisc_subset_Dom, actionNbhd_eq_polyNbhd (KAM/Weighted/Domains.lean)
LEAN_NOTE: Definitions plus clauses (a),(b); audit W4-1 PASS WITH NOTES
NOTE: Max norms throughout (Part 4 convention paragraph L10, Normalisation L12-L17: period 1, geometric strip width s); this definition is the package bpN:p4:domains (SPEC)

NODE: stepN:p4:dom-open
KIND: step
TITLE: Openness and monotonicity
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:dom-open@L41-L41
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:dom-open@L41-L41
CONTRACT_ID: stepN:p4:dom-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m,n ≥ 0; D ⊂ ℂ^m; r,s > 0; 0 < r′ ≤ r and 0 < s′ ≤ s; V_rD and 𝒟_{r,s} are the displayed definitions at L35–36 (expanded locally to avoid a definition/proof cycle)
SOURCE_QUANTIFIERS: m,n≥0; D; r,s>0; then positive r′≤r, s′≤s; for dom-poly, z∈𝒟_{r′,s′} and a point of its closed polydisc
SOURCE_CONCLUSION: V_rD and 𝒟_{r,s} are open; 𝒟_{r',s'} ⊂ 𝒟_{r,s} (monotonicity, 'clear')
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:strip#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:strip#complexStrip | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:dom-open@L41-L41 | T_s is the max-norm complex strip, used in the domain proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: isOpen_polyNbhd, isOpen_Dom, polyNbhd_mono, Dom_mono (KAM/Weighted/Domains.lean)
LEAN_NOTE: audit W4-1 PASS; rows domains(a)
NOTE: -

NODE: stepN:p4:dom-poly
KIND: step
TITLE: Polydisc
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:dom-poly@L43-L44
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:dom-poly@L43-L44
CONTRACT_ID: stepN:p4:dom-poly
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ¦θ'−θ¦_∞ ≤ s−s', ¦I'−I¦_∞ ≤ r−r'; z = (θ,I) ∈ 𝒟_{r',s'}
SOURCE_QUANTIFIERS: m,n≥0; D; r,s>0; then positive r′≤r, s′≤s; for dom-poly, z∈𝒟_{r′,s′} and a point of its closed polydisc
SOURCE_CONCLUSION: ¦Im θ'_j¦ ≤ ¦Im θ_j¦ + s − s' < s and ¦I'−I_0¦ < r, hence P̄(z;s−s',r−r') ⊂ 𝒟_{r,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:strip#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:strip#complexStrip | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:dom-poly@L43-L43 | T_s is the max-norm complex strip, used in the domain proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: polydisc_subset_Dom (KAM/Weighted/Domains.lean)
LEAN_NOTE: audit W4-1 PASS; row domains(b)
NOTE: -

NODE: bpN:p4:norm
KIND: definition
TITLE: The class $\Os rs$ and the weighted norm
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:norm@L47-L54
PROOF_SOURCE: -
CONTRACT_ID: bpN:p4:norm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m, n ≥ 0; D ⊂ ℂ^m; r, s > 0 (the domains of Definition bpN:p4:domains); u: 𝒟_{r,s} → ℂ
SOURCE_QUANTIFIERS: m, n; D; r, s; u; k ∈ ℤⁿ; I ∈ V_rD
SOURCE_CONCLUSION: defines 𝒪(r,s) = {u: 𝒟_{r,s} → ℂ holomorphic and 1-periodic in each θ_j}; û_k(I) = ∫_{[0,1]ⁿ} u(x,I) e^{−2πik·x} dx; ¦u¦_{I,s} = Σ_k ¦û_k(I)¦ e^{2π¦k¦₁ s}; ¦u¦_{r,s} = sup_{I∈V_rD} ¦u¦_{I,s} ∈ [0,∞]; for vector/matrix u the coefficients are componentwise with ¦û_k¦_∞ = max_a ¦û_{a,k}¦ in ¦u¦_{I,s}; 'finite norm' means ¦u¦_{r,s} < ∞
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:norm@L47-L50 | 𝒟_{r,s}, V_rD in the definition of 𝒪(r,s) and ¦·¦_{r,s}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Weighted.InClass, coeff, modeWeight, wsum, WSummable, WBound, HasFiniteWNorm, wnorm, wbound_iff (KAM/Weighted/Norm.lean)
LEAN_NOTE: Definition formalized; norm encoded on finite locus (WBound/HasFiniteWNorm, N1/N2 notes); audit W4-1 PASS WITH NOTES
NOTE: This definition is the package bpN:p4:norm (SPEC): 𝒪(r,s), û_k(I), ¦u¦_{I,s}, ¦u¦_{r,s}, finite norm; convention paragraph L12-L17 (max norms, geometric width s, weight e^{2π¦k¦₁s}) recorded here

NODE: bpN:p4:norm#monotone
KIND: claim
TITLE: Monotonicity of the weighted norm and vector norms
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:norm#monotone@L58-L58
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:norm#monotone@L58-L58
CONTRACT_ID: bpN:p4:norm#monotone
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u ∈ 𝒪(r,s); r' ≤ r, s' ≤ s (r',s' > 0); for vectors u = (u_a)_a with components in 𝒪(r,s)
SOURCE_QUANTIFIERS: D, m, n; u; r, s; r', s'
SOURCE_CONCLUSION: ¦u¦_{r',s'} ≤ ¦u¦_{r,s} (restriction to 𝒟_{r',s'}; the coefficients at I ∈ V_{r'}D are unchanged); for a vector, max_a ¦u_a¦_{r,s} ≤ ¦u¦_{r,s} ≤ Σ_a ¦u_a¦_{r,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:norm#monotone@L58-L58 | definition of ¦·¦_{r,s}, û_k(I)
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:norm#monotone@L58-L58 | restriction to 𝒟_{r',s'} ⊂ 𝒟_{r,s} (Definition domains(a))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Weighted.modeWeight_mono, WBound.mono, coeff_apply_pi, wbound_pi_apply, wbound_pi_of_components (KAM/Weighted/Norm.lean)
LEAN_NOTE: Stated in WBound (finite-bound) form; audit W4-1 PASS WITH NOTES
NOTE: section-data claim created from coverage item p4:prose-L55-L55 (SPEC); consumed by stepN:p4:b4-four, stepN:p4:b4-prod, stepN:p5:vf-deriv, bpN:p4:bracket (proof preamble L152) and later parts

NODE: bpN:p4:n-zero
KIND: claim
TITLE: The case n=0 (no angles)
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:n-zero@L55-L57
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:n-zero@L55-L57
CONTRACT_ID: bpN:p4:n-zero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n = 0, m ≥ 0; D ⊂ ℂ^m; r, s > 0; u ∈ 𝒪(r,s) (Definitions bpN:p4:domains, bpN:p4:norm); a_k: V_rD → ℂ (k ∈ ℤ⁰) for the series statement
SOURCE_QUANTIFIERS: m; D; r, s; u; I ∈ V_rD; σ > 0; (a_k)
SOURCE_CONCLUSION: T_s = ℂ⁰ is a point, ℤ⁰ = {0}, χ_0 ≡ 1, ¦0¦_1 = 0, [0,1]⁰ is a point of measure one; hence û_0(I) = u(I), ¦u¦_{I,s} = ¦u(I)¦, ¦u¦_{r,s} = sup_{V_rD}¦u¦ (independent of s), coth(πσ)⁰ = 1; a series Σ_{k∈ℤ⁰} a_kχ_k is the single term a_0 (no convergence question) and u = û_0χ_0 identically; replaces every use of K's n≥1 strip results (decay, summation, fourier-basic(c), exp-sums) when n = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:n-zero@L56-L57 | û_0, ¦u¦_{I,s}, ¦u¦_{r,s} evaluated for n=0
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:n-zero@L56-L56 | V_rD, T_s=ℂ⁰ and 𝒟_{r,s} for n=0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Remark bpN:p4:n-zero (G1): consumed by stepN:p4:co-series, co-repr, b1-a, b1-b and by stepN:p1:nc-decay, nc-sum as the n=0 singleton branch; the K strip results are stated for n≥1 only (K Part 1 standing convention)

NODE: bpN:p4:coefficients
KIND: lemma
TITLE: Coefficients, derivatives, series
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:coefficients@L60-L70
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:coefficients@L71-L84
CONTRACT_ID: bpN:p4:coefficients
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u ∈ 𝒪(r,s) on 𝒟_{r,s}, D ⊂ ℂ^m (Definitions domains, norm); (c) a_k: V_rD → ℂ (k ∈ ℤⁿ) holomorphic with S := sup_I Σ_k ¦a_k(I)¦ e^{2π¦k¦₁s} < ∞; (d) ¦u¦_{r,s} < ∞
SOURCE_QUANTIFIERS: D, m, n; r, s; u; (a_k)_k; S; s' < s
SOURCE_CONCLUSION: (a) each û_k is holomorphic on V_rD; (b) ∂_{θ_j}u, ∂_{I_i}u ∈ 𝒪(r,s), (∂_{θ_j}u)^_k = 2πik_j û_k, (∂_{I_i}u)^_k = ∂_{I_i}û_k; (c) v = Σ a_k χ_k converges absolutely and uniformly on 𝒟_{r,s'} for each s' < s, v ∈ 𝒪(r,s), v̂_k = a_k and ¦v¦_{r,s} = S; (d) u(θ,I) = Σ_k û_k(I) χ_k(θ) on 𝒟_{r,s} and ¦û_k(I)¦ e^{2π¦k¦₁s} ≤ ¦u¦_{r,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p4:co-holo, stepN:p4:co-deriv, stepN:p4:co-series, stepN:p4:co-repr, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p4:co-holo | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:coefficients@L72-L73 | proof step (a)
EDGE: stepN:p4:co-deriv | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:coefficients@L75-L76 | proof step (b)
EDGE: stepN:p4:co-series | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:coefficients@L78-L80 | proof step (c)
EDGE: stepN:p4:co-repr | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:coefficients@L82-L83 | proof step (d)
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:coefficients@L61-L61 | class 𝒪(r,s), û_k, ¦·¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:coefficients@L61-L61 | 𝒟_{r,s}, V_rD
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: coeff_differentiableOn, inClass_fderiv_apply, coefficients_deriv, coefficients_series, coefficients_repr (KAM/Weighted/Coefficients.lean)
LEAN_NOTE: audit W4-3 PASS WITH NOTES; parts (a)-(d)
NOTE: the one-variable ingredients cited in \source (K:fourier-basic, K:summation) are used by the steps and linked there

NODE: stepN:p4:co-holo
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-holo@L72-L73
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-holo@L72-L73
CONTRACT_ID: stepN:p4:co-holo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u ∈ 𝒪(r,s); I_0 ∈ V_rD, η > 0 with P̄(I_0,η) ⊂ V_rD; k ∈ ℤⁿ
SOURCE_QUANTIFIERS: u; k; I_0; η
SOURCE_CONCLUSION: û_k is holomorphic near I_0 (integrand u(x,I)e^{−2πik·x} continuous on [0,1]ⁿ×P(I_0,η), holomorphic in I, D_I continuous)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:ext-param, K:bp:p1:holomorphic-regularity, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:ext-param | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-holo@L73-L73 | holomorphy of the parameter integral û_k
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-holo@L73-L73 | Du holomorphic hence continuous
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-holo@L72-L72 | û_k(I) definition, 𝒪(r,s)
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-holo@L72-L72 | V_rD open (so P̄(I_0,η) ⊂ V_rD)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: coeff_differentiableOn (KAM/Weighted/Coefficients.lean)
LEAN_NOTE: audit W4-3 PASS WITH NOTES; row (a)
NOTE: -

NODE: stepN:p4:co-deriv
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-deriv@L75-L76
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-deriv@L75-L76
CONTRACT_ID: stepN:p4:co-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u ∈ 𝒪(r,s); u(θ+e_j,I) = u(θ,I)
SOURCE_QUANTIFIERS: D,m,n; positive widths; the function(s) with the SOURCE_HYPOTHESES; then local data in source order: u; i, j
SOURCE_CONCLUSION: ∂_{θ_j}u, ∂_{I_i}u ∈ 𝒪(r,s) (holomorphic, periodic); (∂_{θ_j}u)^_k = 2πik_j û_k; (∂_{I_i}u)^_k = ∂_{I_i}û_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:holomorphic-regularity, K:bp:p1:fourier-basic, bpN:p4:ext-param, stepN:p4:co-holo, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-deriv@L75-L75 | derivatives of holomorphic u are holomorphic
EDGE: K:bp:p1:fourier-basic | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-deriv@L75-L75 | derivative formula (a) at fixed I
EDGE: bpN:p4:ext-param | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-deriv@L76-L76 | derivative formula for I_i
EDGE: stepN:p4:co-holo | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-deriv@L76-L76 | 'as in Step co-holo': hypotheses of the parameter integral
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-deriv@L75-L75 | 𝒪(r,s), û_k
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-deriv@L75-L75 | Uses the action neighbourhood or the domain of the function class directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: inClass_fderiv_apply, coefficients_deriv (KAM/Weighted/Coefficients.lean)
LEAN_NOTE: audit W4-3 PASS WITH NOTES; row (b)
NOTE: -

NODE: stepN:p4:co-series
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-series@L78-L80
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-series@L78-L80
CONTRACT_ID: stepN:p4:co-series
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a_k holomorphic on V_rD with S < ∞; s' < s
SOURCE_QUANTIFIERS: a_k; S; s'
SOURCE_CONCLUSION: v = Σ a_kχ_k converges uniformly on 𝒟_{r,s'}, is holomorphic and periodic on 𝒟_{r,s}, v̂_k = a_k, and ¦v¦_{r,s} = S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:exp-sums, bpN:p4:ext-weier, bpN:p4:ext-series, K:bp:p1:summation, bpN:p4:norm, bpN:p4:domains, bpN:p4:n-zero
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:exp-sums | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-series@L79-L79 | summability of S e^{−2π¦k¦₁(s−s')}
EDGE: bpN:p4:ext-weier | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-series@L79-L79 | uniform limit of holomorphic partial sums is holomorphic
EDGE: bpN:p4:ext-series | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-series@L80-L80 | termwise integration against χ_{−k}
EDGE: K:bp:p1:summation | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-series@L80-L80 | 'as in the coefficient step of K summation'
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-series@L80-L80 | norm identity is the definition
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-series@L79-L79 | 𝒟_{r,s'} ⊂ 𝒟_{r,s}; holomorphy on 𝒟_{r,s} as s' arbitrary
EDGE: bpN:p4:n-zero | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-series@L79-L79 | n=0: index set Z^0={0}, the series is the single term a_0 (no K strip/series result needed)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-global-N+sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: PROVED
LEAN_REF: coefficients_series (KAM/Weighted/Coefficients.lean)
LEAN_NOTE: audit W4-3 PASS WITH NOTES; row (c)
NOTE: Explicit cases n=0 (Remark bpN:p4:n-zero, singleton branch, no K result) and n≥1 (K results under the standing convention); the earlier SOURCE_GAP about the missing n=0 branch is supplied.

NODE: stepN:p4:co-repr
KIND: step
TITLE: (d)
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-repr@L82-L83
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-repr@L82-L83
CONTRACT_ID: stepN:p4:co-repr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u ∈ 𝒪(r,s) with finite norm; I ∈ V_rD
SOURCE_QUANTIFIERS: D,m,n; positive widths; the function(s) with the SOURCE_HYPOTHESES; then local data in source order: u; I
SOURCE_CONCLUSION: ¦û_k(I)¦e^{2π¦k¦₁s} ≤ ¦u¦_{r,s}; u(·,I) = Σ_k û_k(I)χ_k on T_s
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:summation, K:bp:p1:fourier-basic, bpN:p4:norm, bpN:p4:domains, bpN:p4:n-zero
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:summation | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-repr@L82-L82 | Σ û_k(I)χ_k holomorphic periodic with these coefficients
EDGE: K:bp:p1:fourier-basic | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-repr@L83-L83 | (c): holomorphic periodic function with all coefficients zero vanishes
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-repr@L82-L82 | single term of ¦u¦_{I,s} ≤ ¦u¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-repr@L82-L82 | Uses the action neighbourhood or the domain of the function class directly
EDGE: bpN:p4:n-zero | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:co-repr@L82-L82 | case n=0: u(·,I)=û_0(I)χ_0 is the number u(I); representation trivial
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-global-N+sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: PROVED
LEAN_REF: coefficients_repr (KAM/Weighted/Coefficients.lean)
LEAN_NOTE: audit W4-3 PASS WITH NOTES; row (d)
NOTE: Explicit cases n=0 (Remark bpN:p4:n-zero, singleton branch, no K result) and n≥1 (K results under the standing convention); the earlier SOURCE_GAP about the missing n=0 branch is supplied.

NODE: bpN:p4:sup-weighted
KIND: lemma
TITLE: B.1
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:sup-weighted@L88-L96
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:sup-weighted@L97-L104
CONTRACT_ID: bpN:p4:sup-weighted
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u ∈ 𝒪(r,s) (scalar, vector or matrix valued; sup¦u¦ is the sup of the max norm of the values); (b) σ > 0 and ¦u¦ ≤ M on 𝒟_{r,s+σ}
SOURCE_QUANTIFIERS: D, m, n; r, s; u; σ; M
SOURCE_CONCLUSION: (a) sup_{𝒟_{r,s}} ¦u¦ ≤ ¦u¦_{r,s}; (b) ¦u¦_{r,s} ≤ coth(πσ)ⁿ M
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p4:b1-a, stepN:p4:b1-b, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p4:b1-a | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:sup-weighted@L98-L99 | proof step (a)
EDGE: stepN:p4:b1-b | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:sup-weighted@L101-L103 | proof step (b)
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:sup-weighted@L89-L89 | 𝒪(r,s), ¦·¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:sup-weighted@L89-L89 | 𝒟_{r,s}, 𝒟_{r,s+σ}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: sup_le_wbound, wbound_of_sup_bound (KAM/Weighted/SupWeighted.lean)
LEAN_NOTE: audit W4-4 PASS WITH NOTES; B.1(a),(b)
NOTE: candidate edges to bpN:p4:dictionary and bpN:p1:norm-convert dropped: 'In Pöschel's form … see Remark' and \source ('this is Lemma norm-convert with the I-dependence made explicit') are provenance/comparison

NODE: stepN:p4:b1-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-a@L98-L99
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-a@L98-L99
CONTRACT_ID: stepN:p4:b1-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u ∈ 𝒪(r,s), scalar/vector/matrix with the max coefficient norm; (θ,I) ∈ 𝒟_{r,s}; the finite-norm branch (the infinite branch is immediate)
SOURCE_QUANTIFIERS: D,m,n; positive widths; the function(s) with the SOURCE_HYPOTHESES; then local data in source order: u; (θ,I)
SOURCE_CONCLUSION: ¦u(θ,I)¦ ≤ Σ_k ¦û_k(I)¦ ¦χ_k(θ)¦ ≤ Σ_k ¦û_k(I)¦ e^{2π¦k¦₁s} ≤ ¦u¦_{r,s}, using ¦χ_k(θ)¦ ≤ e^{2π¦k¦₁¦Im θ¦_∞}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:coefficients, bpN:p0:strip#complexStrip, bpN:p4:norm, bpN:p4:domains, bpN:p4:n-zero
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:coefficients | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-a@L98-L98 | (d): Fourier representation of u
EDGE: bpN:p0:strip#complexStrip | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-a@L99-L99 | bound ¦χ_k(θ)¦ ≤ e^{2π¦k¦₁¦Im θ¦_∞} on T_s (Kref bp:p0:domains)
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-a@L98-L98 | ¦û_k(I)¦e^{2π¦k¦₁s} sum is ¦u¦_{I,s} ≤ ¦u¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-a@L98-L98 | (θ,I) ∈ 𝒟_{r,s}
EDGE: bpN:p4:n-zero | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-a@L98-L98 | n=0: ¦u¦_{I,s}=¦u(I)¦ and the display is the single term k=0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b+sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: PROVED
LEAN_REF: sup_le_wbound (KAM/Weighted/SupWeighted.lean)
LEAN_NOTE: audit W4-4 PASS WITH NOTES; row B.1(a)
NOTE: Explicit n=0 branch via Remark bpN:p4:n-zero; n≥1 as before.

NODE: stepN:p4:b1-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-b@L101-L103
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-b@L101-L103
CONTRACT_ID: stepN:p4:b1-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u(·,I) holomorphic, periodic, ¦u¦ ≤ M on T_{s+σ}; I ∈ V_rD
SOURCE_QUANTIFIERS: I; σ; M
SOURCE_CONCLUSION: ¦û_k(I)¦_∞ ≤ e^{−2π¦k¦₁(s+σ)}M and ¦u¦_{I,s} ≤ M Σ_k e^{−2π¦k¦₁σ} = coth(πσ)ⁿ M; take sup over I
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:decay, K:bp:p1:exp-sums, bpN:p4:norm, bpN:p4:domains, bpN:p4:n-zero
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:decay | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-b@L101-L101 | Cauchy-type decay of Fourier coefficients (limit ρ' ↑ s+σ)
EDGE: K:bp:p1:exp-sums | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-b@L102-L102 | (b) with x = 2πσ: Σ_k e^{−2π¦k¦₁σ} = coth(πσ)ⁿ
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-b@L101-L101 | û_k(I), ¦u¦_{I,s}, ¦u¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-b@L101-L101 | T_{s+σ}, V_rD
EDGE: bpN:p4:n-zero | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b1-b@L101-L101 | case n=0: ¦u¦_{I,s}=¦u(I)¦ ≤ M=coth(πσ)^0 M
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-global-N+sonnet-amend-N
REVIEWER: sol-delta-N-amend
LEAN_STATUS: PROVED
LEAN_REF: wbound_of_sup_bound (KAM/Weighted/SupWeighted.lean)
LEAN_NOTE: audit W4-4 PASS WITH NOTES; row B.1(b)
NOTE: Explicit cases n=0 (Remark bpN:p4:n-zero, singleton branch, no K result) and n≥1 (K results under the standing convention); the earlier SOURCE_GAP about the missing n=0 branch is supplied.

NODE: bpN:p4:algebra
KIND: lemma
TITLE: B.2
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:algebra@L108-L112
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:algebra@L113-L121
CONTRACT_ID: bpN:p4:algebra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u, v ∈ 𝒪(r,s) scalar with finite norms
SOURCE_QUANTIFIERS: D, m, n; r, s; u, v; I ∈ V_rD; j ≥ 1
SOURCE_CONCLUSION: uv ∈ 𝒪(r,s); (uv)^_k(I) = Σ_l û_{k−l}(I) v̂_l(I) (absolutely convergent); ¦uv¦_{I,s} ≤ ¦u¦_{I,s}¦v¦_{I,s} for every I ∈ V_rD; hence ¦uv¦_{r,s} ≤ ¦u¦_{r,s}¦v¦_{r,s} and ¦u^j¦_{r,s} ≤ ¦u¦_{r,s}^j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p4:b2-class, stepN:p4:b2-coeff, stepN:p4:b2-norm, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p4:b2-class | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:algebra@L114-L114 | proof step
EDGE: stepN:p4:b2-coeff | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:algebra@L116-L117 | proof step
EDGE: stepN:p4:b2-norm | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:algebra@L119-L120 | proof step
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:algebra@L109-L109 | 𝒪(r,s), ¦·¦_{I,s}, ¦·¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:algebra@L109-L109 | V_rD, 𝒟_{r,s}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: coeff_mul, wbound_mul, wbound_pow (KAM/Weighted/Algebra.lean)
LEAN_NOTE: audit W4-5 PASS WITH NOTES
NOTE: the \source remark about a Lean-proved coefficient-level inequality is provenance; the identification with the product of functions is steps b2-class/b2-coeff

NODE: stepN:p4:b2-class
KIND: step
TITLE: Product is in the class
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-class@L114-L114
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-class@L114-L114
CONTRACT_ID: stepN:p4:b2-class
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u, v holomorphic and 1-periodic on 𝒟_{r,s}
SOURCE_QUANTIFIERS: D,m,n; positive widths; the function(s) with the SOURCE_HYPOTHESES; then local data in source order: u, v
SOURCE_CONCLUSION: uv is holomorphic and 1-periodic on 𝒟_{r,s}, i.e. uv ∈ 𝒪(r,s)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-class@L114-L114 | membership in the class 𝒪(r,s)
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-class@L114-L114 | Uses the action neighbourhood or the domain of the function class directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p4:b2-coeff
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-coeff@L116-L117
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-coeff@L116-L117
CONTRACT_ID: stepN:p4:b2-coeff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u,v ∈ 𝒪(r,s) scalar with finite norms; I ∈ V_rD; x ∈ ℝⁿ
SOURCE_QUANTIFIERS: D,m,n; positive widths; the function(s) with the SOURCE_HYPOTHESES; then local data in source order: I; x ∈ ℝⁿ; k
SOURCE_CONCLUSION: u(x,I)v(x,I) = Σ_k c_kχ_k(x) with c_k = Σ_l û_{k−l}v̂_l, Σ_k ¦c_k¦ ≤ ¦u¦_{I,0}¦v¦_{I,0} < ∞, uniform in x, and (uv)^_k(I) = c_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:coefficients, bpN:p4:ext-series, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:coefficients | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-coeff@L116-L116 | (d): u(x,I) = Σ û_kχ_k(x), absolutely convergent
EDGE: bpN:p4:ext-series | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-coeff@L116-L117 | Cauchy product of absolutely convergent series; termwise integration
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-coeff@L117-L117 | ¦u¦_{I,0}, û_k(I)
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-coeff@L116-L116 | Uses the action neighbourhood or the domain of the function class directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p4:b2-norm
KIND: step
TITLE: Norm
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-norm@L119-L120
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-norm@L119-L120
CONTRACT_ID: stepN:p4:b2-norm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u,v ∈ 𝒪(r,s) scalar with finite norms; I ∈ V_rD; c_k denotes Σ_l û_{k−l}v̂_l (its identification as the product coefficient is proved by the dependency)
SOURCE_QUANTIFIERS: D,m,n; positive widths; the function(s) with the SOURCE_HYPOTHESES; then local data in source order: I; s
SOURCE_CONCLUSION: ¦uv¦_{I,s} ≤ ¦u¦_{I,s}¦v¦_{I,s} (Tonelli with (k,l) ↦ (k−l,l)); sup over I; induction gives ¦u^j¦_{r,s} ≤ ¦u¦_{r,s}^j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p4:b2-coeff, bpN:p4:ext-series, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p4:b2-coeff | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-norm@L119-L120 | the coefficient formula (uv)^_k = c_k
EDGE: bpN:p4:ext-series | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-norm@L120-L120 | Tonelli for nonnegative double series
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-norm@L119-L120 | ¦·¦_{I,s}, ¦·¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b2-norm@L120-L120 | Uses the action neighbourhood or the domain of the function class directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p4:cauchy
KIND: lemma
TITLE: B.3
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:cauchy@L125-L133
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:cauchy@L134-L143
CONTRACT_ID: bpN:p4:cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u ∈ 𝒪(r_0,s_0) with finite norm; 0 < r < r_0, 0 < s < s_0; (vector/matrix u componentwise)
SOURCE_QUANTIFIERS: D, m, n; r_0, s_0; u; r, s (then ρ, σ with r_0 = r+ρ, s_0 = s+σ)
SOURCE_CONCLUSION: (a) for every I ∈ V_{r_0}D: Σ_j ¦∂_{θ_j}u¦_{I,s} ≤ ¦u¦_{I,s_0}/(e(s_0−s)), hence sup_I Σ_j ¦∂_{θ_j}u¦_{I,s} ≤ ¦u¦_{r_0,s_0}/(e(s_0−s)) and for each single j ¦∂_{θ_j}u¦_{r_0,s} ≤ ¦u¦_{r_0,s_0}/(e(s_0−s)); (b) max_i ¦∂_{I_i}u¦_{r,s_0} ≤ ¦u¦_{r_0,s_0}/(r_0−r); in particular Σ-pointwise form with (e σ)^{−1}, ρ^{−1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p4:b3-a, stepN:p4:b3-b, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p4:b3-a | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:cauchy@L135-L136 | proof step (a)
EDGE: stepN:p4:b3-b | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:cauchy@L138-L142 | proof step (b)
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:cauchy@L126-L126 | 𝒪(r_0,s_0), ¦·¦_{I,s}, ¦·¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:cauchy@L126-L126 | V_{r_0}D
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: cauchy_theta, cauchy_action, cauchy_loss (KAM/Weighted/Cauchy.lean)
LEAN_NOTE: audit W4-6 PASS WITH NOTES; (a),(b) and loss form
NOTE: Cycle bpN:p4:cauchy <-> bpN:p4:sharp resolved: the candidate edge cauchy -> sharp is the parenthetical remark at L125 ('with the norm ♯ of Lemma sharp it is bounded'), a forward pointer/comparison, not a use; sharp uses cauchy (it is a variant statement). No edge cauchy -> sharp. The edge to bpN:p4:dictionary (Pöschel comparison in \source) is provenance and dropped

NODE: stepN:p4:b3-a
KIND: step
TITLE: (a): coefficients
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-a@L135-L136
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-a@L135-L136
CONTRACT_ID: stepN:p4:b3-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I ∈ V_{r_0}D; u ∈ 𝒪(r_0,s_0) finite norm
SOURCE_QUANTIFIERS: D,m,n; r₀,s₀; u; r,s with 0<r<r₀, 0<s<s₀; then I and coordinate indices
SOURCE_CONCLUSION: Σ_j ¦∂_{θ_j}u¦_{I,s} = Σ_k 2π¦k¦₁ e^{−2π¦k¦₁(s_0−s)} ¦û_k¦e^{2π¦k¦₁s_0} ≤ ¦u¦_{I,s_0}/(e(s_0−s)); global consequences by sup over I and ¦u¦_{I,s_0} ≤ ¦u¦_{r_0,s_0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:coefficients, K:bp:p1:exp-sums, bpN:p4:norm, bpN:p4:domains, bpN:p4:n-zero
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:coefficients | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-a@L135-L135 | (b): (∂_{θ_j}u)^_k = 2πik_jû_k
EDGE: K:bp:p1:exp-sums | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-a@L136-L136 | (a) with τ = 1, a = 2π(s_0−s): x e^{−ax} ≤ 1/(ea)
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-a@L135-L136 | ¦·¦_{I,s}, ¦·¦_{r_0,s_0}
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-a@L135-L135 | Uses the action neighbourhood or the domain of the function class directly
EDGE: bpN:p4:n-zero | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-a@L135-L136 | the no-angle branch has an empty angular sum, equal to zero; no n>=1 K estimate is used in this branch
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-global-N
REVIEWER: sol-delta-N-global2
LEAN_STATUS: PROVED
LEAN_REF: cauchy_theta (KAM/Weighted/Cauchy.lean)
LEAN_NOTE: audit W4-6 PASS WITH NOTES; row cauchy (a)
NOTE: For n=0 the no-angle convention and singleton branch of bpN:p4:n-zero give an empty angular sum, hence zero, and no K exp-sums application is needed. For n≥1 the coefficient computation uses K exp-sums(a) as cited. The native all-n contract is unchanged; the earlier missing-empty-sum SOURCE_GAP is resolved.

NODE: stepN:p4:b3-b
KIND: step
TITLE: (b): Cauchy integral
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-b@L138-L142
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-b@L138-L142
CONTRACT_ID: stepN:p4:b3-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u ∈ 𝒪(r₀,s₀) with finite norm; 0 < r < r₀; I ∈ V_rD; coordinate i; ρ′ := r₀−r; ¦ζ¦ ≤ ρ′
SOURCE_QUANTIFIERS: D,m,n; r₀,s₀; u; r,s with 0<r<r₀, 0<s<s₀; then I and coordinate indices
SOURCE_CONCLUSION: I+ζe_i ∈ V_{r_0}D; ¦∂_{I_i}u¦_{I,s_0} ≤ (1/2π)∮ρ'^{−2}¦u¦_{I+ζe_i,s_0}¦dζ¦ ≤ ρ'^{−1}¦u¦_{r_0,s_0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:coefficients, K:bp:p1:ext-cauchy, bpN:p4:ext-series, bpN:p4:domains, bpN:p4:norm
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:coefficients | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-b@L139-L139 | (a),(b): û_k holomorphic and ∂_{I_i}û_k the coefficient of ∂_{I_i}u
EDGE: K:bp:p1:ext-cauchy | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-b@L139-L139 | Cauchy integral formula for ∂_{I_i}û_k
EDGE: bpN:p4:ext-series | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-b@L140-L140 | Tonelli for the sum over k
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-b@L138-L138 | I+ζe_i ∈ V_{r_0}D
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b3-b@L140-L141 | ¦·¦_{I,s_0}, ¦·¦_{r_0,s_0}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: cauchy_action (KAM/Weighted/Cauchy.lean)
LEAN_NOTE: audit W4-6 PASS WITH NOTES; row cauchy (b)
NOTE: -

NODE: bpN:p4:s-b4#data
KIND: definition
TITLE: The Poisson bracket for m = n (Lemma B.4 data)
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:s-b4#data@L147-L147
PROOF_SOURCE: -
CONTRACT_ID: bpN:p4:s-b4#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data: m = n; u, v holomorphic on an open subset of ℂⁿ×ℂⁿ)
SOURCE_QUANTIFIERS: n; u, v
SOURCE_CONCLUSION: defines, for m = n, the Poisson bracket {u,v} = Σ_i (∂_{θ_i}u ∂_{I_i}v − ∂_{I_i}u ∂_{θ_i}v) = Du·X_v with the frozen field X_v = (∂_Iv, −∂_θv), as in Definition bpN:p5:setting
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:setting | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:s-b4#data@L147-L147 | the bracket and X_v are Definition p5:setting
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: section-data node created from coverage item p4:prose-L144-L144 (SPEC option); notation only, but Lemma bracket and its proof use the bracket by symbol

NODE: bpN:p4:bracket
KIND: lemma
TITLE: B.4
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:bracket@L149-L153
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:bracket@L154-L167
CONTRACT_ID: bpN:p4:bracket
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m = n; u ∈ 𝒪(r_0,s_0), v ∈ 𝒪(r,s) with finite norms; 0<ρ<r, 0<σ<s, r−ρ<r_0, s−σ<s_0; {u,v} the bracket of s-b4#data
SOURCE_QUANTIFIERS: D, n; r_0, s_0, r, s; u, v; ρ, σ
SOURCE_CONCLUSION: {u,v} ∈ 𝒪(r−ρ,s−σ) and ¦{u,v}¦_{r−ρ,s−σ} ≤ (1/e)(1/((r_0−r+ρ)σ) + 1/((s_0−s+σ)ρ)) ¦u¦_{r_0,s_0}¦v¦_{r,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p4:b4-four, stepN:p4:b4-prod, bpN:p4:s-b4#data, bpN:p4:norm, bpN:p4:domains, bpN:p4:norm#monotone, bpN:p4:coefficients, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p4:b4-four | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:bracket@L157-L160 | proof step: pointwise product estimate
EDGE: stepN:p4:b4-prod | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:bracket@L162-L166 | proof step: the four derivative bounds
EDGE: bpN:p4:s-b4#data | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:bracket@L149-L150 | the bracket {u,v} of the statement
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:bracket@L150-L151 | 𝒪, ¦·¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:bracket@L155-L155 | 𝒟_{r−ρ,s−σ} ⊂ 𝒟_{r_0,s_0} ∩ 𝒟_{r,s}
EDGE: bpN:p4:norm#monotone | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:bracket@L155-L155 | restriction of the terms to 𝒟_{r−ρ,s−σ} (monotonicity)
EDGE: bpN:p4:coefficients | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:bracket@L155-L155 | {u,v} ∈ 𝒪(r−ρ,s−σ): derivatives of 𝒪-functions are in the class (b) and products by algebra
EDGE: bpN:p5:setting | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:bracket@L150-L150 | Uses the Hamiltonian Poisson bracket fixed in Part 5; SPEC requires its package edge
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: wbound_bracket (KAM/Weighted/Bracket.lean)
LEAN_NOTE: audit W4-8 PASS
NOTE: -

NODE: stepN:p4:b4-four
KIND: step
TITLE: Pointwise product estimate
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-four@L157-L160
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-four@L157-L160
CONTRACT_ID: stepN:p4:b4-four
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m=n; u ∈ 𝒪(r₀,s₀), v ∈ 𝒪(r,s), both of finite norm; 0<ρ<r, 0<σ<s, r−ρ<r₀, s−σ<s₀; I ∈ V_{r−ρ}D; t := s−σ
SOURCE_QUANTIFIERS: D,n; r₀,s₀,r,s; u,v; ρ,σ subject to the bracket hypotheses; then I∈V_{r−ρ}D; t:=s−σ
SOURCE_CONCLUSION: ¦{u,v}¦_{I,t} ≤ (Σ_i ¦∂_{θ_i}u¦_{I,t}) max_i ¦∂_{I_i}v¦_{I,t} + max_i ¦∂_{I_i}u¦_{I,t} (Σ_i ¦∂_{θ_i}v¦_{I,t}), angular sums kept pointwise in I
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:algebra, bpN:p4:s-b4#data, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:algebra | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-four@L157-L157 | pointwise-in-I product estimate ¦uv¦_{I,t} ≤ ¦u¦_{I,t}¦v¦_{I,t}
EDGE: bpN:p4:s-b4#data | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-four@L157-L157 | The bracket in the pointwise product estimate is the two-sum bracket defined at L144
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-four@L157-L157 | ¦·¦_{I,t}
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-four@L157-L157 | Uses the action neighbourhood or the domain of the function class directly
EDGE: bpN:p5:setting | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-four@L157-L157 | Uses the Hamiltonian Poisson bracket fixed in Part 5; SPEC requires its package edge
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p4:b4-prod
KIND: step
TITLE: Four derivative bounds
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-prod@L162-L166
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-prod@L162-L166
CONTRACT_ID: stepN:p4:b4-prod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m=n; u ∈ 𝒪(r₀,s₀), v ∈ 𝒪(r,s), both of finite norm; 0<ρ<r, 0<σ<s, r−ρ<r₀, s−σ<s₀; I ∈ V_{r−ρ}D; t := s−σ
SOURCE_QUANTIFIERS: D,n; r₀,s₀,r,s; u,v; ρ,σ subject to the bracket hypotheses; then I∈V_{r−ρ}D; t:=s−σ
SOURCE_CONCLUSION: Σ_i¦∂_{θ_i}u¦_{I,t} ≤ ¦u¦_{r_0,s_0}/(e(s_0−s+σ)); max_i¦∂_{I_i}u¦_{I,t} ≤ ¦u¦_{r_0,s_0}/(r_0−r+ρ); Σ_i¦∂_{θ_i}v¦_{I,t} ≤ ¦v¦_{r,s}/(eσ); max_i¦∂_{I_i}v¦_{I,t} ≤ ¦v¦_{r,s}/ρ; inserting and taking sup over I last gives the claim
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:cauchy, bpN:p4:norm#monotone, stepN:p4:b4-four, bpN:p4:domains, bpN:p4:norm, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:cauchy | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-prod@L163-L165 | (a) pointwise and (b) global bounds of the four derivative factors
EDGE: bpN:p4:norm#monotone | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-prod@L162-L162 | monotonicity of the norm in both widths
EDGE: stepN:p4:b4-four | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-prod@L166-L166 | the display into which the four bounds are inserted
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-prod@L163-L163 | I ∈ V_{r_0}D since r−ρ < r_0
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-prod@L163-L165 | ¦·¦_{I,s}, ¦·¦_{r,s}
EDGE: bpN:p5:setting | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:b4-prod@L166-L166 | Uses the Hamiltonian Poisson bracket fixed in Part 5; SPEC requires its package edge
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-delta-N-b
REVIEWER: sol-delta2-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p4:general-cauchy
KIND: lemma
TITLE: C.1
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:general-cauchy@L171-L174
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:general-cauchy@L175-L179
CONTRACT_ID: bpN:p4:general-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A, B finite-dimensional complex normed spaces; v ∈ A; R > 0; G: P_A(v,R) = {a : ¦a−v¦_A < R} → B holomorphic with ¦G¦_B ≤ M on this ball
SOURCE_QUANTIFIERS: A, B; v; R; G; M
SOURCE_CONCLUSION: the operator norm satisfies ¦DG(v)¦_{B,A} ≤ M/R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p4:c1-line, stepN:p4:c1-cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p4:c1-line | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:general-cauchy@L176-L176 | proof step: reduction to one variable
EDGE: stepN:p4:c1-cauchy | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:general-cauchy@L178-L178 | proof step: one-variable Cauchy estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Weighted.general_cauchy (KAM/Weighted/Parametric.lean)
LEAN_NOTE: Operator-norm bound M/R on open ball; audit W4-2 PASS WITH NOTES
NOTE: -

NODE: stepN:p4:c1-line
KIND: step
TITLE: Reduction to one variable
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:c1-line@L176-L176
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:c1-line@L176-L176
CONTRACT_ID: stepN:p4:c1-line
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A,B finite-dimensional complex normed spaces; v ∈ A; R>0; G holomorphic on P_A(v,R), ¦G¦_B ≤ M there; u ∈ A, u ≠ 0
SOURCE_QUANTIFIERS: A,B; v; R>0; G; M; then u≠0; for c1-cauchy, 0<ϱ<R/¦u¦_A
SOURCE_CONCLUSION: f(ζ) = G(v+ζu) is holomorphic on ¦ζ¦ < R/¦u¦_A with ¦f¦ ≤ M and f'(0) = DG(v)u
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p4:c1-cauchy
KIND: step
TITLE: Cauchy
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:c1-cauchy@L178-L178
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:c1-cauchy@L178-L178
CONTRACT_ID: stepN:p4:c1-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A,B finite-dimensional complex normed spaces; v ∈ A; R>0; G holomorphic on P_A(v,R), ¦G¦_B ≤ M there; u ∈ A, u ≠ 0; f(ζ) := G(v+ζu); 0<ϱ<R/¦u¦_A
SOURCE_QUANTIFIERS: A,B; v; R>0; G; M; then u≠0; for c1-cauchy, 0<ϱ<R/¦u¦_A
SOURCE_CONCLUSION: ¦f'(0)¦ ≤ M/ϱ for every ϱ < R/¦u¦_A; letting ϱ ↑ R/¦u¦_A, ¦DG(v)u¦_B ≤ M¦u¦_A/R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:ext-cauchy, stepN:p4:c1-line
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:ext-cauchy | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:c1-cauchy@L178-L178 | one-variable Cauchy estimate ¦f'(0)¦ ≤ M/ϱ
EDGE: stepN:p4:c1-line | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:c1-cauchy@L178-L178 | the function f and f'(0) = DG(v)u
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p4:projections
KIND: lemma
TITLE: $P_S$, $T_K$, averages
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:projections@L184-L190
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:projections@L191-L195
CONTRACT_ID: bpN:p4:projections
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u ∈ 𝒪(r,s) with finite norm; S ⊂ ℤⁿ; K ≥ 0; 0 < σ < s; Λ ⊂ ℤⁿ any set (Λ-normal form u = P_Λu); vector-valued u componentwise
SOURCE_QUANTIFIERS: D, m, n; r, s; u; S; K; σ; Λ
SOURCE_CONCLUSION: P_Su = Σ_{k∈S}û_kχ_k ∈ 𝒪(r,s), (P_Su)^_k = û_k for k ∈ S and 0 otherwise, ¦P_Su¦_{r,s} ≤ ¦u¦_{r,s}; for T_Ku = P_{¦k¦₁≤K}u and ⟨u⟩(I) = û_0(I): ¦T_Ku¦_{r,s}, ¦⟨u⟩¦_{r,s} ≤ ¦u¦_{r,s}; u − T_Ku = P_{¦k¦₁>K}u and ¦u−T_Ku¦_{r,s−σ} ≤ e^{−2πKσ}¦u¦_{r,s}; P_Λu, u−P_Λu in the class with norms ≤ ¦u¦_{r,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p4:pr-class, stepN:p4:pr-tail, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p4:pr-class | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:projections@L192-L192 | proof step: class and coefficients
EDGE: stepN:p4:pr-tail | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:projections@L194-L194 | proof step: tail estimate
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:projections@L185-L187 | 𝒪(r,s), û_k, ¦·¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#bpN:p4:projections@L185-L185 | 𝒟_{r,s}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: projMode, truncate, modeAverage, projections, truncation_tail (KAM/Weighted/Projections.lean)
LEAN_NOTE: audit W4-7 PASS WITH NOTES
NOTE: -

NODE: stepN:p4:pr-class
KIND: step
TITLE: Class and coefficients
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:pr-class@L192-L192
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:pr-class@L192-L192
CONTRACT_ID: stepN:p4:pr-class
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u ∈ 𝒪(r,s) with finite norm; S ⊂ ℤⁿ; a_k := û_k 1_S(k) (holomorphy and the summability bound are established here, not assumed)
SOURCE_QUANTIFIERS: D,m,n; r,s>0; u; S⊂ℤⁿ; K≥0; 0<σ<s; then I and k
SOURCE_CONCLUSION: P_Su ∈ 𝒪(r,s) with coefficients û_k1_S(k) and ¦P_Su¦_{r,s} ≤ ¦u¦_{r,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:coefficients, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:coefficients | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:pr-class@L192-L192 | (a) holomorphy of a_k and (c) series lemma
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:pr-class@L192-L192 | ¦·¦_{r,s}, 𝒪(r,s)
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:pr-class@L192-L192 | Uses the action neighbourhood or the domain of the function class directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: P_Su := Σ_{k∈S} û_kχ_k; T_K := P_{¦k¦₁≤K}. These are local definitions from L182–184; no edge to the parent projections lemma (which depends on this step).

NODE: stepN:p4:pr-tail
KIND: step
TITLE: Tail
STATEMENT_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:pr-tail@L194-L194
PROOF_SOURCE: blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:pr-tail@L194-L194
CONTRACT_ID: stepN:p4:pr-tail
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u ∈ 𝒪(r,s) with finite norm; K≥0; 0<σ<s; for the coefficient estimate fix k with ¦k¦₁>K
SOURCE_QUANTIFIERS: D,m,n; r,s>0; u; S⊂ℤⁿ; K≥0; 0<σ<s; then I and k
SOURCE_CONCLUSION: e^{2π¦k¦₁(s−σ)} ≤ e^{−2πKσ}e^{2π¦k¦₁s} for ¦k¦₁ > K, so ¦u−T_Ku¦_{r,s−σ} ≤ e^{−2πKσ}¦u¦_{r,s}; and u − T_Ku = P_{¦k¦₁>K}u from u = Σû_kχ_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:coefficients, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:coefficients | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:pr-tail@L194-L194 | (d): u = Σ_k û_kχ_k
EDGE: bpN:p4:norm | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:pr-tail@L194-L194 | ¦·¦_{r,s−σ} as sup of the weighted sum
EDGE: bpN:p4:domains | blueprint-N/parts/p4-weighted-norms.tex#stepN:p4:pr-tail@L194-L194 | Uses the action neighbourhood or the domain of the function class directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p4+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: P_Su := Σ_{k∈S} û_kχ_k; T_K := P_{¦k¦₁≤K}. These are local definitions from L182–184; no edge to the parent projections lemma (which depends on this step).
