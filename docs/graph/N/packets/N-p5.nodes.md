NODE: bpN:p5:setting
KIND: definition
TITLE: Hamiltonian field, bracket, scaled norm
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:setting@L19-L26
PROOF_SOURCE: -
CONTRACT_ID: bpN:p5:setting
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data: n; z = (θ,I) ∈ ℂⁿ×ℂⁿ, angles first; u, v holomorphic on an open set; ρ, σ > 0)
SOURCE_QUANTIFIERS: n; u, v; ρ, σ; c > 0; φ; j ≥ 0
SOURCE_CONCLUSION: defines J = ((0,1),(−1,0)), ∇u = (∂_θu,∂_Iu)ᵀ, X_u = J∇u = (∂_Iu, −∂_θu), {u,v} = Σ_i(∂_{θ_i}u∂_{I_i}v − ∂_{I_i}u∂_{θ_i}v) = Du·X_v = ∇uᵀJ∇v = −{v,u}; ν_{ρ,σ}(a,b) = max(¦a¦_∞/σ, ¦b¦_∞/ρ) with closed ball of radius c about z equal to P̄(z;cσ,cρ); ad^0_φu = u, ad^j_φu = {ad^{j−1}_φu, φ}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:vf#hamiltonianVectorField, K:bp:p1:hamiltonian-real, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:setting@L24-L24 | X_u is the frozen Hamiltonian field (Definition p0:vf)
EDGE: K:bp:p1:hamiltonian-real | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:setting@L24-L24 | real-valued functions on real points
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:setting@L25-L26 | closed ν-ball of radius c about z is the polydisc P̄(z;cσ,cρ) of Definition domains
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Canonical.poissonBracket, adPow, scaledNorm, scaleCLE, norm_scaleCLE, symplFormC, poissonBracket_eq_fderiv_field, poissonBracket_antisymm, differentiableOn_poissonBracket, differentiableOn_adPow, poissonBracket_eq_zero_of_snd, RealOn (KAM/Canonical/Setting.lean)
LEAN_NOTE: Definition formalized plus bracket identities; audit C5-1 PASS WITH NOTES
NOTE: Package bpN:p5:setting (SPEC): X_u, {u,v} and its sign, ν_{ρ,σ}, ad^j. Candidate edge to bpN:p5:lie-derivative dropped: the normalisation 'd/dt u(X_φ^t)={u,φ}' is a forward pointer to the result that consumes this definition. The \sourcegap at L25 (printed sign of the bracket not located in Pos93) is a gap in the paper filled by this definition (coverage p5:sourcegap-L25)

NODE: bpN:p5:vf-bound
KIND: lemma
TITLE: Size of the field
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:vf-bound@L29-L34
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:vf-bound@L35-L40
CONTRACT_ID: bpN:p5:vf-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: φ ∈ 𝒪(r,s) with finite norm (D ⊂ ℂⁿ); 0 < ρ < r, 0 < σ < s
SOURCE_QUANTIFIERS: D, n; r, s; φ; ρ, σ; i; on 𝒟_{r−ρ,s−σ}
SOURCE_CONCLUSION: on 𝒟_{r−ρ,s−σ}: ¦∂_{I_i}φ¦ ≤ ¦φ¦_{r,s}/ρ, ¦∂_{θ_i}φ¦ ≤ ¦φ¦_{r,s}/(eσ) and ν_{ρ,σ}(X_φ) = max(max_i¦∂_{I_i}φ¦/σ, max_i¦∂_{θ_i}φ¦/ρ) ≤ ¦φ¦_{r,s}/(ρσ)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:vf-deriv, stepN:p5:vf-field, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:vf-deriv | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:vf-bound@L36-L37 | proof step: derivative bounds
EDGE: stepN:p5:vf-field | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:vf-bound@L39-L39 | proof step: the field
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:vf-bound@L30-L30 | 𝒪(r,s), ¦φ¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:vf-bound@L30-L31 | 𝒟_{r−ρ,s−σ}
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:vf-bound@L31-L33 | X_φ and ν_{ρ,σ}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: differentiableOn_hamField, vf_bound (KAM/Canonical/VectorField.lean)
LEAN_NOTE: audit C5-4 PASS
NOTE: -

NODE: stepN:p5:vf-deriv
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:vf-deriv@L36-L37
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:vf-deriv@L36-L37
CONTRACT_ID: stepN:p5:vf-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; φ ∈ 𝒪(r,s) with finite norm; 0<ρ<r and 0<σ<s; coordinates i,j
SOURCE_QUANTIFIERS: D,n; r,s>0; φ; 0<ρ<r, 0<σ<s; then the coordinate indices
SOURCE_CONCLUSION: ¦∂_{I_i}φ¦_{r−ρ,s} ≤ ¦φ¦_{r,s}/ρ and ¦∂_{θ_j}φ¦_{r,s−σ} ≤ ¦φ¦_{r,s}/(eσ) (single index); restricted to 𝒟_{r−ρ,s−σ} and bounded pointwise by sup ≤ weighted norm
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:cauchy, bpN:p4:sup-weighted, bpN:p4:norm#monotone, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:cauchy | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:vf-deriv@L36-L36 | (a) single-index global and (b) Cauchy estimates
EDGE: bpN:p4:sup-weighted | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:vf-deriv@L37-L37 | (a): sup ≤ weighted norm for each derivative
EDGE: bpN:p4:norm#monotone | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:vf-deriv@L37-L37 | restriction to 𝒟_{r−ρ,s−σ} (monotonicity)
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:vf-deriv@L36-L36 | ¦·¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:vf-deriv@L37-L37 | 𝒟_{r−ρ,s−σ}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:vf-field
KIND: step
TITLE: The field
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:vf-field@L39-L39
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:vf-field@L39-L39
CONTRACT_ID: stepN:p5:vf-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; φ ∈ 𝒪(r,s) with finite norm; 0<ρ<r and 0<σ<s
SOURCE_QUANTIFIERS: D,n; r,s>0; φ; 0<ρ<r, 0<σ<s; then the coordinate indices
SOURCE_CONCLUSION: ν_{ρ,σ}(X_φ) = max(max_i¦∂_{I_i}φ¦/σ, max_i¦∂_{θ_i}φ¦/ρ) ≤ ¦φ¦_{r,s}/(ρσ); the action block alone is bounded by ¦φ¦_{r,s}/(eρσ)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:setting, stepN:p5:vf-deriv, bpN:p4:norm
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:vf-field@L39-L39 | definition of ν_{ρ,σ} and X_φ
EDGE: stepN:p5:vf-deriv | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:vf-field@L39-L39 | the two derivative bounds inserted
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:vf-field@L39-L39 | Uses 𝒪 or its finite weighted norm, including the inherited source data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-delta-N-b
REVIEWER: sol-delta2-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p5:flow
KIND: lemma
TITLE: Flow of a small holomorphic field
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:flow@L44-L54
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:flow@L55-L74
CONTRACT_ID: bpN:p5:flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω ⊂ ℂ^N open; F: Ω → ℂ^N holomorphic with ν(F) ≤ ε on Ω, 0 ≤ ε ≤ ½; Ω^c = {z : B̄_ν(z,c) ⊂ Ω} for c > 0; (d) τ ∈ ℂ^N with Ω+τ = Ω and F(w+τ) = F(w); (e) N = 2n and F(x) ∈ ℝ^N for x ∈ Ω∩ℝ^N
SOURCE_QUANTIFIERS: N; ν; Ω; F; ε; c > 0; z; t; τ
SOURCE_CONCLUSION: (a) for z ∈ Ω^{1/2} there is γ_z: ℝ → ℂ^N with IsSolIn F Ω [−1,1] γ_z, γ_z(0) = z, any solution in Ω through z on J ∋ 0 equals γ_z on J∩[−1,1]; X^t(z) = γ_z(t) and ν(X^t(z)−z) ≤ ¦t¦ε; (b) (t,z) ↦ X^t(z) continuous on [−1,1]×Ω^{1/2}, X^t holomorphic Ω^{1/2} → Ω, D_zX^t continuous, Y = D_zX^t satisfies Y(t) = 1 + ∫_0^t DF(X^τz)Y(τ)dτ; (c) for z ∈ Ω^1: X^1(z) ∈ Ω^{1/2}, X^{−1}(X^1z) = z, ¦DX^t(z)−1¦_ν ≤ 2ε (¦t¦ ≤ 1), likewise X^1(X^{−1}z) = z; (d) Ω^{1/2}+τ = Ω^{1/2} and X^t(z+τ) = X^t(z)+τ; (e) X^t(x) ∈ ℝ^N for x ∈ Ω^{1/2}∩ℝ^N
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:fl-max, stepN:p5:fl-picard, stepN:p5:fl-limit, stepN:p5:fl-inverse, stepN:p5:fl-symmetry, bpN:p3:gen-sol, K:bp:p1:holomorphic-regularity, bpN:p1:ext-restrict
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:fl-max | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:flow@L58-L60 | proof step (a)
EDGE: stepN:p5:fl-picard | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:flow@L62-L64 | proof step (b) Picard iterates
EDGE: stepN:p5:fl-limit | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:flow@L66-L67 | proof step (b) convergence
EDGE: stepN:p5:fl-inverse | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:flow@L69-L70 | proof step (c)
EDGE: stepN:p5:fl-symmetry | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:flow@L72-L73 | proof steps (d),(e)
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:flow@L47-L47 | the predicate IsSolIn F Ω [−1,1] γ_z in the statement of (a)
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:flow@L56-L56 | F is C¹ on Ω (restriction of scalars)
EDGE: bpN:p1:ext-restrict | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:flow@L56-L56 | Restrict the holomorphic vector field to the real normed space for the Part 3 ODE results
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-delta-N-b
REVIEWER: sol-delta2-N-b
LEAN_STATUS: PROVED
LEAN_REF: gaugeInterior, flow, SmallField, flow_a, flow_d (KAM/Canonical/Flow.lean); flow_b (KAM/Canonical/FlowRegular.lean); flow_c, flow_e (KAM/Canonical/FlowInverse.lean)
LEAN_NOTE: composite of audits C5-2 PASS WITH NOTES (a),(d) + C5-3 PASS WITH NOTES (b) + C5-5 PASS WITH NOTES (c),(e)
NOTE: Part 11b re-uses this lemma verbatim for N = 2n+2k (not an edge here)

NODE: stepN:p5:fl-max
KIND: step
TITLE: (a) The maximal solution stays in a compact set
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-max@L58-L60
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-max@L58-L60
CONTRACT_ID: stepN:p5:fl-max
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; z∈Ω^{1/2}; (T₋,T₊,γ) denotes the maximal solution constructed using Part 3
SOURCE_QUANTIFIERS: N; ν; Ω; F; ε∈[0,1/2]; then local data in source order: z; T_±; γ
SOURCE_CONCLUSION: T₊>1, and the time-reversal argument is invoked for the left endpoint; uniqueness on J∋0 and ν(X^t(z)−z)≤¦t¦ε. The printed endpoint conclusion at L59 is T₋>−1; the required endpoint is T₋<−1 (source defect, see NOTE).
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-maximal, K:bp:p1:ext-mvt, bpN:p3:gen-sol, bpN:p3:gen-continuation-compact, bpN:p3:gen-symmetry, bpN:p3:gen-uniqueness, K:bp:p1:holomorphic-regularity, bpN:p1:ext-restrict
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-maximal | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-max@L58-L58 | maximal interval and solution
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-max@L58-L58 | ν(γ(t)−z) ≤ εt (mean value inequality in one variable)
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-max@L58-L58 | γ solves the ODE in the IsSolIn sense
EDGE: bpN:p3:gen-continuation-compact | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-max@L59-L59 | T_+ = ∞ if the trajectory stays in a compact subset
EDGE: bpN:p3:gen-symmetry | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-max@L59-L59 | time reversal (b) for T_−
EDGE: bpN:p3:gen-uniqueness | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-max@L60-L60 | uniqueness on an interval J ∋ 0
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-max@L58-L58 | The field is C¹ on Ω, as checked in the proof preamble L56
EDGE: bpN:p1:ext-restrict | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-max@L58-L58 | Use C¹ after restriction of scalars, as checked in the proof preamble L56
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: flow_a (KAM/Canonical/Flow.lean)
LEAN_NOTE: audit C5-2 PASS WITH NOTES; flow_a gives all four (a) clauses
NOTE: SOURCE_GAP: L59 prints T₋>−1, whereas existence on [−1,1] requires T₋<−1. Time reversal is named, so this appears to be a sign typo; the graph must not silently certify a corrected printed conclusion. Owner/writer source ruling required.

NODE: stepN:p5:fl-picard
KIND: step
TITLE: (b) Picard iterates
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-picard@L62-L64
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-picard@L62-L64
CONTRACT_ID: stepN:p5:fl-picard
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; z₀∈Ω^{1/2}; choose η>0 with B̄_ν(z₀,1/2+η)⊂Ω; Λ:=sup_{B̄_ν(z₀,1/2+η)}¦DF¦_ν; y₀(t,z):=z, y_{k+1}(t,z):=z+∫₀ᵗF(y_k(τ,z))dτ
SOURCE_QUANTIFIERS: N; ν; Ω; F; ε∈[0,1/2]; then local data in source order: z_0; η; Λ; k
SOURCE_CONCLUSION: Picard iterates y_k satisfy ν(y_k(t,z)−z) ≤ ¦t¦ε, y_k continuous, y_k(t,·) holomorphic, D_zy_k continuous; F is Λ-Lipschitz on the ball
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:ext-mvt, bpN:p4:ext-param, K:bp:p1:holomorphic-regularity
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-picard@L62-L62 | The derivative supremum Λ gives the Lipschitz bound on the convex ball
EDGE: bpN:p4:ext-param | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-picard@L64-L64 | holomorphy and continuity of D_zy_k from the parameter integral
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-picard@L62-L62 | DF is continuous, so its supremum on the compact larger ball is finite
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: ParamHyp, ParamHyp.intervalIntegral, ParamHyp.id_add (KAM/Canonical/FlowRegularIntegral.lean); picard, picard_zero, picard_succ, picard_regular, exists_gaugeInterior_gt' (KAM/Canonical/FlowPicard.lean)
LEAN_NOTE: audit C5-3 PASS WITH NOTES; rows fl-picard
NOTE: -

NODE: stepN:p5:fl-limit
KIND: step
TITLE: (b) Convergence and identification
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-limit@L66-L67
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-limit@L66-L67
CONTRACT_ID: stepN:p5:fl-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; z₀,η,Λ and the Picard iterates denote the data constructed at L62–64 (their convergence and regularity are not additional premises)
SOURCE_QUANTIFIERS: N; ν; Ω; F; ε∈[0,1/2]; then local data in source order: z_0; η
SOURCE_CONCLUSION: y_k → y_∞ uniformly, y_∞(t,z) = X^t(z); X^t continuous, holomorphic on B_ν(z_0,η), D_zX^t jointly continuous (D_zy_k → D_zX^t uniformly on B_ν(z_0,η/2)), and Y(t) = 1 + ∫DF(X^τw)Y(τ)dτ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:fl-picard, stepN:p5:fl-max, bpN:p4:ext-weier, bpN:p4:ext-param
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:fl-picard | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-limit@L66-L66 | the iterates y_k and the Lipschitz constant Λ
EDGE: stepN:p5:fl-max | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-limit@L66-L66 | y_∞(t,z) = X^t(z) by (a) (uniqueness)
EDGE: bpN:p4:ext-weier | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-limit@L67-L67 | uniform limit of holomorphic maps is holomorphic and derivatives converge
EDGE: bpN:p4:ext-param | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-limit@L67-L67 | differentiation under the integral for the equation for Y
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: flow_integral_eq, picard_flow_estimate (KAM/Canonical/FlowPicardConverge.lean); flow_paramHyp_local, flow_paramHyp, flow_b (KAM/Canonical/FlowRegular.lean)
LEAN_NOTE: audit C5-3 PASS WITH NOTES; rows fl-limit
NOTE: -

NODE: stepN:p5:fl-inverse
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-inverse@L69-L70
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-inverse@L69-L70
CONTRACT_ID: stepN:p5:fl-inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; z∈Ω¹; w:=X¹(z); ¦t¦≤1
SOURCE_QUANTIFIERS: N; ν; Ω; F; ε∈[0,1/2]; then local data in source order: z; w; t
SOURCE_CONCLUSION: w ∈ Ω^{1/2}, X^{−1}(X^1z) = z, X^1(X^{−1}z) = z, and ¦DX^t(z)−1¦_ν ≤ 2ε
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:fl-max, bpN:p3:gen-uniqueness, bpN:p3:gen-symmetry, stepN:p5:fl-limit, bpN:p4:general-cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:fl-max | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-inverse@L69-L70 | displacement ν(w−z) ≤ ε and ν(G) ≤ ε by (a)
EDGE: bpN:p3:gen-uniqueness | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-inverse@L69-L69 | t ↦ γ_z(1+t) equals γ_w on [−1,0]
EDGE: bpN:p3:gen-symmetry | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-inverse@L69-L69 | The reverse composition is obtained by time reversal, item (b)
EDGE: stepN:p5:fl-limit | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-inverse@L70-L70 | G = X^t − id holomorphic by (b)
EDGE: bpN:p4:general-cauchy | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-inverse@L70-L70 | Lemma general-cauchy with R = ½: ¦DG(z)¦_ν ≤ 2ε
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:fl-symmetry
KIND: step
TITLE: (d),(e)
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-symmetry@L72-L73
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-symmetry@L72-L73
CONTRACT_ID: stepN:p5:fl-symmetry
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; (d) τ with Ω+τ=Ω and F(w+τ)=F(w); (e) N=2n and F is real at real points
SOURCE_QUANTIFIERS: N; ν; Ω; F; ε∈[0,1/2]; then local data in source order: τ; z; x
SOURCE_CONCLUSION: (d) Ω^{1/2}+τ = Ω^{1/2} and X^t(z+τ) = X^t(z)+τ; (e) X^t(x) ∈ ℝ^N for x ∈ Ω^{1/2}∩ℝ^N
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-symmetry, bpN:p3:gen-uniqueness, stepN:p5:fl-symmetry#real-restriction, stepN:p5:fl-max
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-symmetry | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-symmetry@L72-L72 | (c): translation of a solution is a solution
EDGE: bpN:p3:gen-uniqueness | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-symmetry@L72-L72 | γ_z + τ equals γ_{z+τ} by uniqueness
EDGE: stepN:p5:fl-symmetry#real-restriction | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-symmetry@L73-L73 | C¹ real restriction on W required before the real ODE argument
EDGE: stepN:p5:fl-max | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-symmetry@L73-L73 | (a) applied to E = ℝ^N, W = Ω∩ℝ^N: real solution on [−1,1]
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: Partial: (d) flow_d (KAM/Canonical/Flow.lean, audit C5-2 PASS WITH NOTES) proved; (e) real restriction not yet audited
NOTE: -

NODE: bpN:p5:symplectic
KIND: lemma
TITLE: Symplectic flow
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:symplectic@L76-L81
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:symplectic@L82-L88
CONTRACT_ID: bpN:p5:symplectic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lemma flow with N = 2n, Ω ⊂ ℂⁿ×ℂⁿ, F = X_φ with φ holomorphic on Ω, ν(F) ≤ ε ≤ ½; z ∈ Ω^{1/2}; ¦t¦ ≤ 1
SOURCE_QUANTIFIERS: n; ν; Ω; φ; ε; z; t
SOURCE_CONCLUSION: Y = DX^t(z) satisfies YᵀJY = J, YJYᵀ = J, det Y = ±1 (Yᵀ the plain transpose)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:sy-var, stepN:p5:sy-field, stepN:p5:sy-conserve, bpN:p5:flow, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:sy-var | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:symplectic@L83-L83 | proof step
EDGE: stepN:p5:sy-field | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:symplectic@L85-L85 | proof step
EDGE: stepN:p5:sy-conserve | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:symplectic@L87-L87 | proof step
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:symplectic@L77-L77 | the flow X^t, Ω^{1/2} of Lemma flow
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:symplectic@L77-L77 | F = X_φ, J
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: symplectic (KAM/Canonical/Symplectic.lean)
LEAN_NOTE: audit C5-5 PASS WITH NOTES
NOTE: -

NODE: stepN:p5:sy-var
KIND: step
TITLE: Variational equation
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-var@L83-L83
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-var@L83-L83
CONTRACT_ID: stepN:p5:sy-var
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; N=2n; Ω ⊂ ℂⁿ×ℂⁿ; F=X_φ with φ holomorphic on Ω; z∈Ω^{1/2}; ¦t¦≤1; Y:=DX^t(z)
SOURCE_QUANTIFIERS: n; ν; Ω; φ; ε∈[0,1/2]; z∈Ω^{1/2}; ¦t¦≤1
SOURCE_CONCLUSION: Y = DX^t(z) is C¹ with Y' = DF(X^tz)Y, Y(0) = 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:flow, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-var@L83-L83 | (b): regularity of the flow and the integral equation for Y
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-var@L83-L83 | Uses X_φ, J, the scaled norm, or the iterated Poisson brackets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:sy-field
KIND: step
TITLE: The field
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-field@L85-L85
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-field@L85-L85
CONTRACT_ID: stepN:p5:sy-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F = J∇φ, φ holomorphic
SOURCE_QUANTIFIERS: φ
SOURCE_CONCLUSION: DF = JS with S = D∇φ the symmetric Hessian, and DFᵀJ + J DF = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:ext-schwarz, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:ext-schwarz | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-field@L85-L85 | S symmetric (Schwarz)
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-field@L85-L85 | F = X_φ = J∇φ, J² = −1, Jᵀ = −J
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5
REVIEWER: sol-review-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:sy-conserve
KIND: step
TITLE: Conservation
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-conserve@L87-L87
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-conserve@L87-L87
CONTRACT_ID: stepN:p5:sy-conserve
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; N=2n; Ω ⊂ ℂⁿ×ℂⁿ; F=X_φ with φ holomorphic on Ω; z∈Ω^{1/2}; ¦t¦≤1; Y:=DX^t(z)
SOURCE_QUANTIFIERS: n; ν; Ω; φ; ε∈[0,1/2]; z∈Ω^{1/2}; ¦t¦≤1
SOURCE_CONCLUSION: d/dt(YᵀJY) = 0 so YᵀJY = J, det Y² = 1, YJYᵀ = J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:sy-var, stepN:p5:sy-field, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:sy-var | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-conserve@L87-L87 | the variational equation for Y
EDGE: stepN:p5:sy-field | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-conserve@L87-L87 | DFᵀJ + J DF = 0
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:sy-conserve@L87-L87 | Uses X_φ, J, the scaled norm, or the iterated Poisson brackets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p5:canonical
KIND: corollary
TITLE: Canonical maps: bracket invariance and conjugation
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical@L90-L98
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical@L99-L105
CONTRACT_ID: bpN:p5:canonical
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of Lemma symplectic; z ∈ Ω^{1/2}; Φ = X^t (¦t¦ ≤ 1); u, v, H holomorphic on a neighbourhood of Φ(z); for (c): y: J → Ω^{1/2} with ẏ = X_{H∘Φ}(y) and H holomorphic near Φ(y(J))
SOURCE_QUANTIFIERS: Ω; φ; z; t; u, v, H; y; J
SOURCE_CONCLUSION: u∘Φ is holomorphic near z and (a) {u∘Φ,v∘Φ}(z) = {u,v}(Φ(z)); (b) DΦ(z)X_{H∘Φ}(z) = X_H(Φ(z)); (c) x = Φ∘y satisfies ẋ = X_H(x)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:ca-chain, stepN:p5:ca-a, stepN:p5:ca-b, bpN:p5:symplectic, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:ca-chain | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical@L100-L100 | proof step
EDGE: stepN:p5:ca-a | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical@L102-L102 | proof step (a)
EDGE: stepN:p5:ca-b | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical@L104-L104 | proof step (b),(c)
EDGE: bpN:p5:symplectic | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical@L91-L91 | setting of Lemma symplectic
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical@L91-L92 | {·,·} and X_H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: canonical_bracket, canonical_field, canonical_orbit (KAM/Canonical/Symplectic.lean)
LEAN_NOTE: audit C5-5 PASS WITH NOTES; (a),(b),(c)
NOTE: The paragraph after the proof (L106, 'for real data …') is mapped to no node: no proof cites it (see coverage p5:prose-L106-L106)

NODE: stepN:p5:ca-chain
KIND: step
TITLE: Chain rule
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-chain@L100-L100
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-chain@L100-L100
CONTRACT_ID: stepN:p5:ca-chain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; N=2n; Ω ⊂ ℂⁿ×ℂⁿ; F=X_φ with φ holomorphic on Ω; z∈Ω^{1/2}; ¦t¦≤1; Φ=X^t; u,v,H holomorphic near Φ(z)
SOURCE_QUANTIFIERS: n; ν; Ω; φ; ε∈[0,1/2]; z∈Ω^{1/2}; ¦t¦≤1; Φ:=X^t; u,v,H; then y,J for (c)
SOURCE_CONCLUSION: Φ holomorphic and ∇(u∘Φ) = DΦᵀ(∇u)∘Φ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:flow, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-chain@L100-L100 | (b): X^t holomorphic
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-chain@L100-L100 | ∇ notation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:ca-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-a@L102-L102
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-a@L102-L102
CONTRACT_ID: stepN:p5:ca-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; N=2n; Ω ⊂ ℂⁿ×ℂⁿ; F=X_φ with φ holomorphic on Ω; z∈Ω^{1/2}; ¦t¦≤1; Φ=X^t; u,v,H holomorphic near Φ(z)
SOURCE_QUANTIFIERS: n; ν; Ω; φ; ε∈[0,1/2]; z∈Ω^{1/2}; ¦t¦≤1; Φ:=X^t; u,v,H; then y,J for (c)
SOURCE_CONCLUSION: {u∘Φ,v∘Φ}(z) = ∇uᵀ Y J Yᵀ ∇v = ∇uᵀJ∇v = {u,v}(Φ(z))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:symplectic, stepN:p5:ca-chain, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:symplectic | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-a@L102-L102 | YJYᵀ = J
EDGE: stepN:p5:ca-chain | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-a@L102-L102 | ∇(u∘Φ) = DΦᵀ(∇u)∘Φ
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-a@L102-L102 | {u,v} = ∇uᵀJ∇v
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:ca-b
KIND: step
TITLE: (b),(c)
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-b@L104-L104
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-b@L104-L104
CONTRACT_ID: stepN:p5:ca-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; N=2n; Ω ⊂ ℂⁿ×ℂⁿ; F=X_φ with φ holomorphic on Ω; z∈Ω^{1/2}; ¦t¦≤1; Φ=X^t; u,v,H holomorphic near Φ(z); for (c) y:J→Ω^{1/2} solves ẏ=X_{H∘Φ}(y), H holomorphic near Φ(y(J))
SOURCE_QUANTIFIERS: n; ν; Ω; φ; ε∈[0,1/2]; z∈Ω^{1/2}; ¦t¦≤1; Φ:=X^t; u,v,H; then y,J for (c)
SOURCE_CONCLUSION: DΦ X_{H∘Φ} = Y J Yᵀ(∇H)∘Φ = X_H∘Φ; and for (c) ẋ = DΦ(y)ẏ = X_H(x)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:symplectic, stepN:p5:ca-chain, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:symplectic | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-b@L104-L104 | YJYᵀ = J
EDGE: stepN:p5:ca-chain | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-b@L104-L104 | chain rule ∇(H∘Φ) and Φ differentiable
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ca-b@L104-L104 | X_H = J∇H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p5:lie-derivative
KIND: lemma
TITLE: Derivative along the flow
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:lie-derivative@L110-L114
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:lie-derivative@L115-L119
CONTRACT_ID: bpN:p5:lie-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Ω ⊂ ℂⁿ×ℂⁿ, φ, F = X_φ, ε ≤ ½ as in Lemma symplectic; Ω_1 ⊂ Ω open; u holomorphic on Ω_1; z ∈ Ω^{1/2} with X^t(z) ∈ Ω_1 for ¦t¦ ≤ 1
SOURCE_QUANTIFIERS: Ω; φ; ε; Ω_1; u; z; j ≥ 0
SOURCE_CONCLUSION: g(t) = u(X^t(z)) is C^∞ on [−1,1] and g^{(j)}(t) = (ad^j_φu)(X^t(z)) for all j ≥ 0 (each ad^j_φu holomorphic on Ω_1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:ld-one, stepN:p5:ld-ind, bpN:p5:flow, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:ld-one | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:lie-derivative@L116-L116 | proof step
EDGE: stepN:p5:ld-ind | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:lie-derivative@L118-L118 | proof step
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:lie-derivative@L111-L111 | the flow X^t, Ω^{1/2}
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:lie-derivative@L112-L112 | ad^j_φ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-delta-N-b
REVIEWER: sol-delta2-N-b
LEAN_STATUS: PROVED
LEAN_REF: lie_derivative, hasDerivAt_comp_flow, hasDerivAt_adPow_flow (KAM/Canonical/Lie.lean)
LEAN_NOTE: audit C5-6 PASS WITH NOTES
NOTE: The phrase “as in Lemma symplectic” imports the displayed field/domain hypotheses only. No symplecticity conclusion is consumed by the scalar chain-rule/induction proof, so it is not a dependency on that theorem.

NODE: stepN:p5:ld-one
KIND: step
TITLE: One derivative
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ld-one@L116-L116
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ld-one@L116-L116
CONTRACT_ID: stepN:p5:ld-one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; N=2n; Ω ⊂ ℂⁿ×ℂⁿ; F=X_φ with φ holomorphic on Ω; Ω₁⊂Ω open; u holomorphic on Ω₁; z∈Ω^{1/2}; X^t(z)∈Ω₁ for ¦t¦≤1; replace u by any holomorphic v on Ω₁; γ:=X^·(z)
SOURCE_QUANTIFIERS: n; ν; Ω; φ; ε∈[0,1/2]; Ω₁⊂Ω; u (or h,f₀ in ta-poschel); z with the trajectory in Ω₁; then the derivative/Taylor order
SOURCE_CONCLUSION: d/dt v(γ(t)) = Dv(γ)·X_φ(γ) = {v,φ}(γ(t)), continuous in t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:setting, bpN:p5:flow
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ld-one@L116-L116 | {v,φ} = Dv·X_φ
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ld-one@L116-L116 | (a): γ has derivative X_φ(γ)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: hasDerivAt_comp_flow (KAM/Canonical/Lie.lean)
LEAN_NOTE: audit C5-6 PASS WITH NOTES; row One flow derivative
NOTE: -

NODE: stepN:p5:ld-ind
KIND: step
TITLE: Induction
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ld-ind@L118-L118
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ld-ind@L118-L118
CONTRACT_ID: stepN:p5:ld-ind
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; N=2n; Ω ⊂ ℂⁿ×ℂⁿ; F=X_φ with φ holomorphic on Ω; Ω₁⊂Ω open; u holomorphic on Ω₁; z∈Ω^{1/2}; X^t(z)∈Ω₁ for ¦t¦≤1; j≥0; v:=ad^j_φu (holomorphy is established by induction)
SOURCE_QUANTIFIERS: n; ν; Ω; φ; ε∈[0,1/2]; Ω₁⊂Ω; u (or h,f₀ in ta-poschel); z with the trajectory in Ω₁; then the derivative/Taylor order
SOURCE_CONCLUSION: apply the previous step to v = ad^j_φu: g^{(j+1)} = (ad^{j+1}_φu)(X^t z), by induction g ∈ C^∞
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:ld-one, K:bp:p1:holomorphic-regularity, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:ld-one | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ld-ind@L118-L118 | the one-derivative step
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ld-ind@L118-L118 | ad^j_φu holomorphic on Ω_1
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ld-ind@L118-L118 | ad^j_φ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: hasDerivAt_adPow_flow, lie_derivative (KAM/Canonical/Lie.lean)
LEAN_NOTE: audit C5-6 PASS WITH NOTES; row Iterated flow derivative
NOTE: -

NODE: bpN:p5:taylor
KIND: lemma
TITLE: Taylor with integral remainder along the flow
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:taylor@L121-L132
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:taylor@L133-L137
CONTRACT_ID: bpN:p5:taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of Lemma lie-derivative; N ≥ 1; for the displayed formula (eq:poschel): h, f_0 holomorphic on Ω_1 and the trajectory of z stays in Ω_1
SOURCE_QUANTIFIERS: Ω; φ; Ω_1; u; z; N; h, f_0
SOURCE_CONCLUSION: u(X^1z) = Σ_{j<N}(1/j!)(ad^j_φu)(z) + R_N(z) with R_N(z) = ∫_0^1(1−t)^{N−1}/(N−1)!·(ad^N_φu)(X^tz)dt and ¦R_N(z)¦ ≤ (1/N!)max_{0≤t≤1}¦(ad^N_φu)(X^tz)¦; in particular (h+f_0)(X^1z) = h(z) + {h,φ}(z) + f_0(z) + ∫_0^1{(1−t){h,φ}+f_0, φ}(X^tz)dt
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:ta-taylor, stepN:p5:ta-poschel, bpN:p5:lie-derivative, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:ta-taylor | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:taylor@L134-L134 | proof step
EDGE: stepN:p5:ta-poschel | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:taylor@L136-L136 | proof step
EDGE: bpN:p5:lie-derivative | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:taylor@L122-L122 | setting of Lemma lie-derivative
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:taylor@L124-L125 | Uses the iterated brackets or Hamiltonian flow of the fixed convention
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-delta-N-b
REVIEWER: sol-delta2-N-b
LEAN_STATUS: PROVED
LEAN_REF: taylor_lie, taylor_poschel, taylor_integral_aux, hasDerivAt_taylorWeight (KAM/Canonical/Lie.lean)
LEAN_NOTE: audit C5-6 PASS WITH NOTES
NOTE: -

NODE: stepN:p5:ta-taylor
KIND: step
TITLE: Taylor
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ta-taylor@L134-L134
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ta-taylor@L134-L134
CONTRACT_ID: stepN:p5:ta-taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^{2n}; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; Ω ⊂ ℂⁿ×ℂⁿ; F=X_φ with φ holomorphic on Ω; Ω₁⊂Ω open; u holomorphic on Ω₁; z∈Ω^{1/2}; X^t(z)∈Ω₁ for ¦t¦≤1; N≥1
SOURCE_QUANTIFIERS: n; ν; Ω; φ; ε∈[0,1/2]; Ω₁⊂Ω; u (or h,f₀ in ta-poschel); z with the trajectory in Ω₁; then the derivative/Taylor order
SOURCE_CONCLUSION: u(X^1z) = Σ_{j<N}(ad^j_φu)(z)/j! + R_N(z) with the stated integral form and bound 1/N! (∫_0^1(1−t)^{N−1}/(N−1)! dt = 1/N!)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:lie-derivative, K:bp:p1:ext-integral, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:lie-derivative | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ta-taylor@L134-L134 | g^{(j)}(0) = (ad^j_φu)(z), g^{(N)}(t) = (ad^N_φu)(X^tz)
EDGE: K:bp:p1:ext-integral | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ta-taylor@L134-L134 | FTC and integral bounds used in the source-indicated induction with integration by parts; the imported statement does not itself assert Taylor's formula
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ta-taylor@L134-L134 | Uses X_φ, J, the scaled norm, or the iterated Poisson brackets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-delta-N-b
REVIEWER: sol-delta2-N-b
LEAN_STATUS: PROVED
LEAN_REF: taylor_lie, taylor_integral_aux (KAM/Canonical/Lie.lean)
LEAN_NOTE: audit C5-6 PASS WITH NOTES; row taylor_lie
NOTE: -

NODE: stepN:p5:ta-poschel
KIND: step
TITLE: The displayed formula
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ta-poschel@L136-L136
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ta-poschel@L136-L136
CONTRACT_ID: stepN:p5:ta-poschel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ν a complex norm on ℂ^N; Ω open; F holomorphic on Ω; ν(F)≤ε on Ω with 0≤ε≤1/2; N=2n; Ω ⊂ ℂⁿ×ℂⁿ; F=X_φ with φ holomorphic on Ω; Ω₁⊂Ω open; u holomorphic on Ω₁; z∈Ω^{1/2}; X^t(z)∈Ω₁ for ¦t¦≤1; h,f₀ holomorphic on Ω₁ (in place of u)
SOURCE_QUANTIFIERS: n; ν; Ω; φ; ε∈[0,1/2]; Ω₁⊂Ω; u (or h,f₀ in ta-poschel); z with the trajectory in Ω₁; then the derivative/Taylor order
SOURCE_CONCLUSION: the displayed formula (h+f_0)(X^1z) = h + {h,φ} + f_0 + ∫_0^1{(1−t){h,φ}+f_0,φ}(X^tz)dt
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:ta-taylor, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:ta-taylor | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ta-poschel@L136-L136 | Taylor's formula for N = 2 (h) and N = 1 (f_0)
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ta-poschel@L136-L136 | ad²h = {{h,φ},φ}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: taylor_poschel (KAM/Canonical/Lie.lean)
LEAN_NOTE: audit C5-6 PASS WITH NOTES; row taylor_poschel
NOTE: -

NODE: bpN:p5:adjoint
KIND: lemma
TITLE: Iterated brackets
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:adjoint@L141-L145
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:adjoint@L146-L155
CONTRACT_ID: bpN:p5:adjoint
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: φ ∈ 𝒪(r',s'), u ∈ 𝒪(r,s) with finite norms; 0 < ρ < r, 0 < σ < s; r+ρ ≤ r'; s+σ ≤ s'; η = 2¦φ¦_{r',s'}/(ρσ); h ≥ 1
SOURCE_QUANTIFIERS: D, n; r, s, r', s'; φ, u; ρ, σ; h
SOURCE_CONCLUSION: ¦ad^h_φu¦_{r−ρ,s−σ} ≤ (2h²/(eρσ))^h (h!/(2h)!) ¦φ¦_{r',s'}^h ¦u¦_{r,s}, hence (1/h!)¦ad^h_φu¦_{r−ρ,s−σ} ≤ (eη/4)^h ¦u¦_{r,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:ad-setup, stepN:p5:ad-step, stepN:p5:ad-product, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:ad-setup | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:adjoint@L147-L147 | proof step
EDGE: stepN:p5:ad-step | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:adjoint@L149-L151 | proof step
EDGE: stepN:p5:ad-product | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:adjoint@L153-L154 | proof step
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:adjoint@L142-L142 | 𝒪(r,s), ¦·¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:adjoint@L142-L142 | V_rD, 𝒟_{r,s}
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:adjoint@L141-L141 | ad^h_φ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: adjoint_bound (KAM/Canonical/Adjoint.lean)
LEAN_NOTE: audit C5-7 PASS WITH NOTES
NOTE: -

NODE: stepN:p5:ad-setup
KIND: step
TITLE: Setup
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-setup@L147-L147
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-setup@L147-L147
CONTRACT_ID: stepN:p5:ad-setup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; φ∈𝒪(r′,s′), u∈𝒪(r,s), both of finite norm; 0<ρ<r, 0<σ<s; r+ρ≤r′, s+σ≤s′; η:=2¦φ¦_{r′,s′}/(ρσ); h≥1; κ:=ρ/h, λ:=σ/h; r_i:=r−iκ, s_i:=s−iλ for 0≤i≤h
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: h; i
SOURCE_CONCLUSION: r_h = r−ρ, s_h = s−σ and ad^i_φu ∈ 𝒪(r_i,s_i) by induction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:bracket, bpN:p5:setting, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:bracket | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-setup@L147-L147 | induction: the bracket maps 𝒪-functions into the class with loss (κ,λ)
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-setup@L147-L147 | ad^i_φ
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-setup@L147-L147 | class 𝒪(r_i,s_i)
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-setup@L147-L147 | Uses the analytic domains or the action neighbourhood in the source context
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:ad-step
KIND: step
TITLE: One step
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-step@L149-L151
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-step@L149-L151
CONTRACT_ID: stepN:p5:ad-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; φ∈𝒪(r′,s′), u∈𝒪(r,s), both of finite norm; 0<ρ<r, 0<σ<s; r+ρ≤r′, s+σ≤s′; η:=2¦φ¦_{r′,s′}/(ρσ); h≥1; κ:=ρ/h, λ:=σ/h; r_i:=r−iκ, s_i:=s−iλ; 1≤i≤h
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: i
SOURCE_CONCLUSION: ¦ad^i_φu¦_{r_i,s_i} ≤ (2/(e(h+i)κλ))¦φ¦_{r',s'}¦ad^{i−1}_φu¦_{r_{i−1},s_{i−1}}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:bracket, bpN:p5:setting, stepN:p5:ad-setup, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:bracket | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-step@L149-L150 | Lemma bracket with (u,v;r_0,s_0;r,s;ρ,σ) → (φ, ad^{i−1}u; r',s'; r_{i−1},s_{i−1}; κ,λ)
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-step@L149-L149 | ad^i_φ = {ad^{i−1}_φu,φ} = −{φ, ad^{i−1}_φu} (antisymmetry)
EDGE: stepN:p5:ad-setup | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-step@L149-L149 | r_i, s_i, κ, λ, ad^{i−1}u ∈ 𝒪(r_{i−1},s_{i−1})
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-step@L150-L150 | ¦·¦_{r_i,s_i}
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-step@L150-L150 | Uses the analytic domains or the action neighbourhood in the source context
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:ad-product
KIND: step
TITLE: Product
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-product@L153-L154
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-product@L153-L154
CONTRACT_ID: stepN:p5:ad-product
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; φ∈𝒪(r′,s′), u∈𝒪(r,s), both of finite norm; 0<ρ<r, 0<σ<s; r+ρ≤r′, s+σ≤s′; η:=2¦φ¦_{r′,s′}/(ρσ); h≥1; κ:=ρ/h, λ:=σ/h; r_i:=r−iκ, s_i:=s−iλ
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: h
SOURCE_CONCLUSION: first estimate ¦ad^h_φu¦ ≤ (2h²/(eρσ))^h(h!/(2h)!)¦φ¦^h¦u¦, and (1/h!)¦ad^h_φu¦ ≤ (eη/4)^h¦u¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:ad-step, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:ad-step | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-product@L153-L153 | the per-step bound multiplied over i
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-product@L154-L154 | Uses 𝒪 or its finite weighted norm, including the inherited source data
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-product@L154-L154 | Uses the analytic domains or the action neighbourhood in the source context
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ad-product@L154-L154 | Uses X_φ, J, the scaled norm, or the iterated Poisson brackets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p5:composition
KIND: theorem
TITLE: Lemma B.5: $\abs{u\circ X^1_\phi}\le(1-\eta)^{-1}\abs u$
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition@L157-L168
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition@L169-L181
CONTRACT_ID: bpN:p5:composition
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; 0 < ρ < r ≤ r'−ρ; 0 < σ < s ≤ s'−σ; φ ∈ 𝒪(r',s') with finite norm; η = 2¦φ¦_{r',s'}/(ρσ) ≤ ½; Ω = 𝒟_{r'−ρ,s'−σ} ⊃ 𝒟_{r,s}; ν = ν_{ρ,σ}; (ii) u ∈ 𝒪(r,s) with finite norm; (iv) φ and u real on real points
SOURCE_QUANTIFIERS: D, n; r, s, r', s'; ρ, σ; φ; u; t
SOURCE_CONCLUSION: (i) ν(X_φ) ≤ η/2 ≤ ¼ on Ω; the flow X^t (¦t¦ ≤ 1) is defined on Ω^{1/2} ⊃ 𝒟_{r−ρ,s−σ} with X^t(𝒟_{r−ρ,s−σ}) ⊂ 𝒟_{r,s}; (ii) Σ_h(1/h!)ad^h_φu converges in ¦·¦_{r−ρ,s−σ} to S ∈ 𝒪(r−ρ,s−σ), S = u∘X^1_φ on 𝒟_{r−ρ,s−σ}, and ¦u∘X^1_φ¦_{r−ρ,s−σ} ≤ (1−eη/4)^{−1}¦u¦_{r,s} ≤ (1−2¦φ¦_{r',s'}/(ρσ))^{−1}¦u¦_{r,s}; (iii) the same for X^t (¦t¦ ≤ 1) with η replaced by ¦t¦η; (iv) u∘X^1_φ is real on real points of 𝒟_{r−ρ,s−σ}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:co-field, stepN:p5:co-series, stepN:p5:co-remainder, stepN:p5:co-t, bpN:p5:flow, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:co-field | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition@L170-L171 | proof step (i)
EDGE: stepN:p5:co-series | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition@L173-L174 | proof step: the series
EDGE: stepN:p5:co-remainder | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition@L176-L178 | proof step: the remainder tends to 0 (identifies S = u∘X^1)
EDGE: stepN:p5:co-t | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition@L180-L180 | proof step (iii),(iv)
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition@L160-L160 | the flow X^t of Lemma flow
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition@L158-L160 | 𝒪(r',s'), ¦·¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition@L158-L159 | Ω = 𝒟_{r'−ρ,s'−σ} ⊃ 𝒟_{r,s}
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition@L159-L159 | ν = ν_{ρ,σ}, X_φ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5
REVIEWER: sol-review-N-b
LEAN_STATUS: PROVED
LEAN_REF: ComposeData, composition_domain (KAM/Canonical/CompositionDomain.lean); composition_series, composition_t, composition_real (KAM/Canonical/Composition.lean)
LEAN_NOTE: audit C5-8 PASS WITH NOTES; (i)-(iv)
NOTE: Edge to remark bpN:p5:route (the decision for the Lie series route) dropped: a route decision, not a use. The \sourcegap at L167 (Pöschel does not prove the equality u∘X^1 = Σ ad^h/h!) is filled by stepN:p5:co-remainder, so no SOURCE_GAP node (coverage p5:sourcegap-L167)

NODE: stepN:p5:co-field
KIND: step
TITLE: The field and the domain
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-field@L170-L171
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-field@L170-L171
CONTRACT_ID: stepN:p5:co-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; 0<ρ<r≤r′−ρ; 0<σ<s≤s′−σ; φ∈𝒪(r′,s′) with finite norm; η:=2¦φ¦_{r′,s′}/(ρσ)≤1/2; Ω:=𝒟_{r′−ρ,s′−σ}; ν:=ν_{ρ,σ}; z∈𝒟_{r−ρ,s−σ}; ε:=η/2
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: z; ε = η/2
SOURCE_CONCLUSION: 𝒟_{r,s} ⊂ Ω; ν(X_φ) ≤ ¦φ¦/(ρσ) = η/2 =: ε ≤ ¼ on Ω; B̄_ν(z,½) = P̄(z;σ/2,ρ/2) ⊂ 𝒟_{r,s} ⊂ Ω so z ∈ Ω^{1/2}; X^t(z) ∈ P̄(z;εσ,ερ) ⊂ 𝒟_{r,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:vf-bound, bpN:p4:domains, bpN:p5:flow, bpN:p5:setting, bpN:p4:norm
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:vf-bound | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-field@L170-L171 | ν(X_φ) ≤ ¦φ¦/(ρσ) on Ω
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-field@L171-L171 | (b): P̄(z;·,·) ⊂ 𝒟 and 𝒟_{r,s} ⊂ Ω (monotonicity)
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-field@L171-L171 | (a): displacement ν(X^t(z)−z) ≤ ¦t¦ε
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-field@L171-L171 | closed ν-ball = P̄(z;cσ,cρ)
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-field@L170-L170 | φ ∈ 𝒪(r',s')
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:co-series
KIND: step
TITLE: The series
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-series@L173-L174
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-series@L173-L174
CONTRACT_ID: stepN:p5:co-series
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; 0<ρ<r≤r′−ρ; 0<σ<s≤s′−σ; φ∈𝒪(r′,s′) with finite norm; η:=2¦φ¦_{r′,s′}/(ρσ)≤1/2; Ω:=𝒟_{r′−ρ,s′−σ}; ν:=ν_{ρ,σ}; u∈𝒪(r,s) with finite norm
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: h
SOURCE_CONCLUSION: (1/h!)ad^h_φu ∈ 𝒪(r−ρ,s−σ) with norm ≤ (eη/4)^h¦u¦; the series converges in the norm and uniformly on 𝒟_{r−ρ,s−σ} to S, holomorphic, periodic, with ¦S¦_{r−ρ,s−σ} ≤ (1−eη/4)^{−1}¦u¦_{r,s} ≤ (1−η)^{−1}¦u¦_{r,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:adjoint, bpN:p4:sup-weighted, bpN:p4:ext-weier, bpN:p4:ext-series, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:adjoint | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-series@L173-L173 | norm bound (eη/4)^h¦u¦ of each term
EDGE: bpN:p4:sup-weighted | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-series@L173-L173 | (a): norm convergence implies uniform convergence
EDGE: bpN:p4:ext-weier | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-series@L174-L174 | S holomorphic as a uniform limit
EDGE: bpN:p4:ext-series | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-series@L174-L174 | termwise integration: Fourier coefficients of S are the sums of coefficients
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-series@L174-L174 | ¦S¦_{r−ρ,s−σ} = sup Σ¦Ŝ_k¦e^{2π¦k¦₁(s−σ)}
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-series@L173-L173 | 𝒟_{r−ρ,s−σ}
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-series@L173-L173 | Uses X_φ, J, the scaled norm, or the iterated Poisson brackets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:co-remainder
KIND: step
TITLE: The remainder tends to $0$
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-remainder@L176-L178
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-remainder@L176-L178
CONTRACT_ID: stepN:p5:co-remainder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; 0<ρ<r≤r′−ρ; 0<σ<s≤s′−σ; φ∈𝒪(r′,s′) with finite norm; η:=2¦φ¦_{r′,s′}/(ρσ)≤1/2; Ω:=𝒟_{r′−ρ,s′−σ}; ν:=ν_{ρ,σ}; u∈𝒪(r,s) with finite norm; z∈𝒟_{r−ρ,s−σ}; t∈[0,1]; w:=X^t(z); ε:=η/2; ρ̂:=(1−ε)ρ, σ̂:=(1−ε)σ, η̂:=η/(1−ε)² (the bound η̂≤8/9 is proved here)
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: z; t; N
SOURCE_CONCLUSION: ¦R_N(z)¦ ≤ (eη̂/4)^N¦u¦_{r,s} → 0, hence u(X^1z) = Σ_j(1/j!)(ad^j_φu)(z) = S(z) on 𝒟_{r−ρ,s−σ}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:co-field, bpN:p5:adjoint, bpN:p4:sup-weighted, bpN:p5:taylor, stepN:p5:co-series, bpN:p4:domains, bpN:p4:norm, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:co-field | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-remainder@L176-L176 | w ∈ 𝒟_{r−ρ̂,s−σ̂} and the trajectory stays in 𝒟_{r,s}
EDGE: bpN:p5:adjoint | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-remainder@L177-L177 | with losses (ρ̂,σ̂): ¦ad^Nu¦ ≤ N!(eη̂/4)^N¦u¦
EDGE: bpN:p4:sup-weighted | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-remainder@L177-L177 | B.1(a) bounds the value of ad^N_φu along the trajectory
EDGE: bpN:p5:taylor | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-remainder@L178-L178 | Taylor with integral remainder R_N
EDGE: stepN:p5:co-series | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-remainder@L178-L178 | S = Σ(1/j!)ad^j u, the limit identified with u(X^1z)
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-remainder@L176-L176 | 𝒟_{r−ρ̂,s−σ̂} ⊂ 𝒟_{r,s}
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-remainder@L177-L177 | ¦u¦_{r,s}
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-remainder@L177-L177 | Uses X_φ, J, the scaled norm, or the iterated Poisson brackets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: This step supplies the identification u∘X^1 = Σ ad^h/h! that Pos93 does not prove (\sourcegap L167)

NODE: stepN:p5:co-t
KIND: step
TITLE: (iii), (iv)
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-t@L180-L180
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-t@L180-L180
CONTRACT_ID: stepN:p5:co-t
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; 0<ρ<r≤r′−ρ; 0<σ<s≤s′−σ; φ∈𝒪(r′,s′) with finite norm; η:=2¦φ¦_{r′,s′}/(ρσ)≤1/2; Ω:=𝒟_{r′−ρ,s′−σ}; ν:=ν_{ρ,σ}; u∈𝒪(r,s) with finite norm; ¦t¦≤1; for (iv) φ,u real at real points
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: t
SOURCE_CONCLUSION: X^t_φ = X^1_{tφ}, so (iii) is (ii) for tφ with η → ¦t¦η; (iv) by Lemma flow(e)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:flow, stepN:p5:co-series, stepN:p5:co-remainder, bpN:p5:setting, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-t@L180-L180 | (e) reality; uniqueness (a) for X^t_φ = X^1_{tφ}
EDGE: stepN:p5:co-series | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-t@L180-L180 | (ii) applied to tφ: norm bound
EDGE: stepN:p5:co-remainder | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-t@L180-L180 | (ii) applied to tφ: identification with u∘X^1_{tφ}
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-t@L180-L180 | X_{tφ} = tX_φ
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-t@L180-L180 | Uses 𝒪 or its finite weighted norm, including the inherited source data
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:co-t@L180-L180 | Uses the analytic domains or the action neighbourhood in the source context
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p5:transform
KIND: proposition
TITLE: Lie transform with first-order remainder, in the weighted norm
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:transform@L183-L190
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:transform@L191-L201
CONTRACT_ID: bpN:p5:transform
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of Theorem composition; h ∈ 𝒪(r,s) (any norm, possibly ∞) with w := {h,φ} ∈ 𝒪(r,s) of finite norm; f_0 ∈ 𝒪(r,s) with finite norm
SOURCE_QUANTIFIERS: D, n; r, s, r', s'; ρ, σ; φ; h, f_0; w
SOURCE_CONCLUSION: on 𝒟_{r−ρ,s−σ}: (h+f_0)∘X^1_φ = h + w + f_0 + ℛ with ℛ = Σ_{j≥1}((1/(j+1)!)ad^j_φw + (1/j!)ad^j_φf_0) = ∫_0^1{(1−t)w+f_0,φ}∘X^t_φ dt; the series converges in ¦·¦_{r−ρ,s−σ}, ℛ ∈ 𝒪(r−ρ,s−σ), ¦ℛ¦_{r−ρ,s−σ} ≤ Σ_{j≥1}(eη/4)^j(¦w¦_{r,s}/(j+1)+¦f_0¦_{r,s}) ≤ (η/(1−η))(½¦w¦_{r,s}+¦f_0¦_{r,s})
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:tr-h, stepN:p5:tr-f, stepN:p5:tr-sum, stepN:p5:tr-int, bpN:p5:composition, bpN:p5:taylor, bpN:p4:norm, bpN:p5:setting, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:tr-h | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:transform@L192-L194 | proof step
EDGE: stepN:p5:tr-f | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:transform@L196-L196 | proof step
EDGE: stepN:p5:tr-sum | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:transform@L198-L198 | proof step
EDGE: stepN:p5:tr-int | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:transform@L200-L200 | proof step
EDGE: bpN:p5:composition | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:transform@L184-L184 | setting of Theorem composition (data, η ≤ ½, flow X^t)
EDGE: bpN:p5:taylor | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:transform@L188-L188 | The integral form is explicitly identified with Lemma taylor, equation poschel
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:transform@L184-L188 | ¦·¦_{r,s}, 𝒪(r,s)
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:transform@L185-L186 | {h,φ}, ad^j_φ
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:transform@L184-L184 | The statement uses 𝒟 and the inherited domain data directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: liftRemainder, transform (KAM/Canonical/Transform.lean)
LEAN_NOTE: audit C5-9 PASS WITH NOTES
NOTE: -

NODE: stepN:p5:tr-h
KIND: step
TITLE: Derivatives of $h$
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-h@L192-L194
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-h@L192-L194
CONTRACT_ID: stepN:p5:tr-h
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; 0<ρ<r≤r′−ρ; 0<σ<s≤s′−σ; φ∈𝒪(r′,s′) with finite norm; η:=2¦φ¦_{r′,s′}/(ρσ)≤1/2; Ω:=𝒟_{r′−ρ,s′−σ}; ν:=ν_{ρ,σ}; h∈𝒪(r,s), possibly infinite norm; w:={h,φ}∈𝒪(r,s) of finite norm; f₀∈𝒪(r,s) of finite norm; z∈𝒟_{r−ρ,s−σ}; N≥2
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: z; N
SOURCE_CONCLUSION: h∘X^1 = h + Σ_{i≥0}(1/(i+1)!)ad^i_φw pointwise (remainder R'_N ≤ ((N−1)!/N!)(eη̂/4)^{N−1}¦w¦ → 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:lie-derivative, bpN:p5:taylor, stepN:p5:co-field, stepN:p5:co-remainder, bpN:p5:adjoint, bpN:p5:setting, bpN:p4:norm, bpN:p4:domains
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:lie-derivative | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-h@L193-L193 | g(t) = h(X^tz), g^{(j)} = (ad^{j−1}_φw)(X^tz)
EDGE: bpN:p5:taylor | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-h@L193-L193 | Taylor's formula to order N for h
EDGE: stepN:p5:co-field | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-h@L193-L193 | the trajectory stays in 𝒟_{r,s} = Ω_1
EDGE: stepN:p5:co-remainder | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-h@L194-L194 | bound of the remainder with the losses (ρ̂,σ̂)
EDGE: bpN:p5:adjoint | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-h@L194-L194 | Lemma adjoint with u = w
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-h@L192-L192 | ad^1_φh = {h,φ} = w
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-h@L193-L193 | Uses 𝒪 or its finite weighted norm, including the inherited source data
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-h@L193-L193 | Uses the analytic domains or the action neighbourhood in the source context
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:tr-f
KIND: step
TITLE: Derivatives of $f_0$
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-f@L196-L196
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-f@L196-L196
CONTRACT_ID: stepN:p5:tr-f
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; 0<ρ<r≤r′−ρ; 0<σ<s≤s′−σ; φ∈𝒪(r′,s′) with finite norm; η:=2¦φ¦_{r′,s′}/(ρσ)≤1/2; Ω:=𝒟_{r′−ρ,s′−σ}; ν:=ν_{ρ,σ}; h∈𝒪(r,s), possibly infinite norm; w:={h,φ}∈𝒪(r,s) of finite norm; f₀∈𝒪(r,s) of finite norm
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: f_0
SOURCE_CONCLUSION: f_0∘X^1 = Σ_{j≥0}(1/j!)ad^j_φf_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:composition, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:composition | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-f@L196-L196 | (ii) applied to f_0
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-f@L196-L196 | Uses 𝒪 or its finite weighted norm, including the inherited source data
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-f@L196-L196 | Uses the analytic domains or the action neighbourhood in the source context
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-f@L196-L196 | Uses X_φ, J, the scaled norm, or the iterated Poisson brackets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:tr-sum
KIND: step
TITLE: Sum and bound
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-sum@L198-L198
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-sum@L198-L198
CONTRACT_ID: stepN:p5:tr-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; 0<ρ<r≤r′−ρ; 0<σ<s≤s′−σ; φ∈𝒪(r′,s′) with finite norm; η:=2¦φ¦_{r′,s′}/(ρσ)≤1/2; Ω:=𝒟_{r′−ρ,s′−σ}; ν:=ν_{ρ,σ}; h∈𝒪(r,s), possibly infinite norm; w:={h,φ}∈𝒪(r,s) of finite norm; f₀∈𝒪(r,s) of finite norm
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: j
SOURCE_CONCLUSION: the first identity with ℛ as stated; (1/j!)¦ad^jw¦ ≤ (eη/4)^j¦w¦, so ¦ℛ¦ ≤ Σ_{j≥1}(eη/4)^j(¦w¦/(j+1)+¦f_0¦) ≤ (η/(1−η))(½¦w¦+¦f_0¦); convergence in norm and ℛ ∈ 𝒪(r−ρ,s−σ) as in co-series
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:tr-h, stepN:p5:tr-f, bpN:p5:adjoint, stepN:p5:co-series, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:tr-h | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-sum@L198-L198 | the expansion of h∘X^1
EDGE: stepN:p5:tr-f | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-sum@L198-L198 | the expansion of f_0∘X^1
EDGE: bpN:p5:adjoint | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-sum@L198-L198 | (1/j!)¦ad^j_φw¦ ≤ (eη/4)^j¦w¦
EDGE: stepN:p5:co-series | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-sum@L198-L198 | convergence and membership of 𝒪(r−ρ,s−σ) as in Step co-series
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-sum@L198-L198 | Uses 𝒪 or its finite weighted norm, including the inherited source data
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-sum@L198-L198 | Uses the analytic domains or the action neighbourhood in the source context
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-sum@L198-L198 | Uses X_φ, J, the scaled norm, or the iterated Poisson brackets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:tr-int
KIND: step
TITLE: Integral form
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-int@L200-L200
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-int@L200-L200
CONTRACT_ID: stepN:p5:tr-int
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; 0<ρ<r≤r′−ρ; 0<σ<s≤s′−σ; φ∈𝒪(r′,s′) with finite norm; η:=2¦φ¦_{r′,s′}/(ρσ)≤1/2; Ω:=𝒟_{r′−ρ,s′−σ}; ν:=ν_{ρ,σ}; h∈𝒪(r,s), possibly infinite norm; w:={h,φ}∈𝒪(r,s) of finite norm; f₀∈𝒪(r,s) of finite norm; z∈𝒟_{r−ρ,s−σ}
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: z
SOURCE_CONCLUSION: ℛ = ∫_0^1{(1−t)w+f_0,φ}∘X^t_φ dt (integral form)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:taylor, stepN:p5:co-field, bpN:p4:domains, bpN:p5:setting, bpN:p4:norm
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:taylor | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-int@L200-L200 | eq poschel (displayed Taylor formula)
EDGE: stepN:p5:co-field | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-int@L200-L200 | the trajectory stays in 𝒟_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-int@L200-L200 | Uses the analytic domains or the action neighbourhood in the source context
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-int@L200-L200 | Uses X_φ, J, the scaled norm, or the iterated Poisson brackets
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:tr-int@L200-L200 | the transform context fixes h,w,f₀ in 𝒪(r,s) and the finite weighted norms of w,f₀
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-delta-N-b
REVIEWER: sol-delta2-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p5:composition-integral
KIND: corollary
TITLE: Integral remainders in the weighted norm
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition-integral@L203-L206
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition-integral@L207-L211
CONTRACT_ID: bpN:p5:composition-integral
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of Theorem composition; v_t ∈ 𝒪(r,s) (0 ≤ t ≤ 1) with finite norms and V = sup_t¦v_t¦_{r,s} < ∞; (t,z) ↦ v_t(z) and (t,z) ↦ Dv_t(z) continuous on [0,1]×𝒟_{r,s}
SOURCE_QUANTIFIERS: D, n; r, s, r', s'; ρ, σ; φ; (v_t)_t; V
SOURCE_CONCLUSION: G(z) = ∫_0^1 v_t(X^t_φz)dt lies in 𝒪(r−ρ,s−σ) and ¦G¦_{r−ρ,s−σ} ≤ (1−η)^{−1}V
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:ci-integrand, stepN:p5:ci-coeff, bpN:p5:composition, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:ci-integrand | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition-integral@L208-L208 | proof step
EDGE: stepN:p5:ci-coeff | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition-integral@L210-L210 | proof step
EDGE: bpN:p5:composition | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition-integral@L204-L204 | setting of Theorem composition
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition-integral@L204-L206 | 𝒪(r,s), ¦·¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition-integral@L204-L204 | The statement uses 𝒟 and the inherited domain data directly
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:composition-integral@L204-L204 | Uses the iterated brackets or Hamiltonian flow of the fixed convention
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: PROVED
LEAN_REF: composition_integral (KAM/Canonical/CompositionIntegral.lean)
LEAN_NOTE: audit C5-8 PASS WITH NOTES
NOTE: -

NODE: stepN:p5:ci-integrand
KIND: step
TITLE: Integrand
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-integrand@L208-L208
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-integrand@L208-L208
CONTRACT_ID: stepN:p5:ci-integrand
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; 0<ρ<r≤r′−ρ; 0<σ<s≤s′−σ; φ∈𝒪(r′,s′) with finite norm; η:=2¦φ¦_{r′,s′}/(ρσ)≤1/2; Ω:=𝒟_{r′−ρ,s′−σ}; ν:=ν_{ρ,σ}; v_t∈𝒪(r,s) for 0≤t≤1; V:=sup_t¦v_t¦_{r,s}<∞; v_t and Dv_t jointly continuous on [0,1]×𝒟_{r,s}; t∈[0,1]; g_t:=v_t∘X^t
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: t
SOURCE_CONCLUSION: g_t ∈ 𝒪(r−ρ,s−σ) with ¦g_t¦ ≤ (1−t η)^{−1}V ≤ (1−η)^{−1}V; (t,z) ↦ g_t(z) and D_zg_t = Dv_t(X^tz)D_zX^t(z) continuous
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:composition, bpN:p5:flow, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:composition | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-integrand@L208-L208 | (iii): ¦v_t∘X^t¦ ≤ (1−tη)^{−1}¦v_t¦
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-integrand@L208-L208 | (b): joint continuity of X^t and D_zX^t
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-integrand@L208-L208 | ¦·¦_{r−ρ,s−σ}
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-integrand@L208-L208 | Uses the analytic domains or the action neighbourhood in the source context
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-integrand@L208-L208 | Uses X_φ, J, the scaled norm, or the iterated Poisson brackets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:ci-coeff
KIND: step
TITLE: Holomorphy and coefficients
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-coeff@L210-L210
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-coeff@L210-L210
CONTRACT_ID: stepN:p5:ci-coeff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; 0<ρ<r≤r′−ρ; 0<σ<s≤s′−σ; φ∈𝒪(r′,s′) with finite norm; η:=2¦φ¦_{r′,s′}/(ρσ)≤1/2; Ω:=𝒟_{r′−ρ,s′−σ}; ν:=ν_{ρ,σ}; v_t∈𝒪(r,s) for 0≤t≤1; V:=sup_t¦v_t¦_{r,s}<∞; v_t and Dv_t jointly continuous on [0,1]×𝒟_{r,s}; g_t:=v_t∘X^t; k∈ℤⁿ; I∈V_{r−ρ}D
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: t; k; I
SOURCE_CONCLUSION: G holomorphic and periodic; Ĝ_k(I) = ∫_0^1(ĝ_t)_k(I)dt, so ¦G¦_{I,s−σ} ≤ ∫_0^1¦g_t¦_{I,s−σ}dt ≤ (1−η)^{−1}V
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p4:ext-param, bpN:p4:ext-series, stepN:p5:ci-integrand, bpN:p4:norm, bpN:p4:domains, K:bp:p1:ext-integral, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p4:ext-param | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-coeff@L210-L210 | holomorphy of the parameter integral G
EDGE: bpN:p4:ext-series | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-coeff@L210-L210 | Tonelli for the nonnegative coefficient norm sum
EDGE: stepN:p5:ci-integrand | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-coeff@L210-L210 | the functions g_t and their bound
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-coeff@L210-L210 | û_k(I), ¦·¦_{I,s−σ}
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-coeff@L210-L210 | Uses the analytic domains or the action neighbourhood in the source context
EDGE: K:bp:p1:ext-integral | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-coeff@L210-L210 | Fubini for the continuous complex-valued integrand on [0,1]×[0,1]^n and the integral norm inequality
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:ci-coeff@L210-L210 | X^t_φ in the parameter integrand and the inherited Hamiltonian/scaled-norm setting
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-delta-N-b
REVIEWER: sol-delta2-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpN:p5:canonical-map
KIND: proposition
TITLE: Iterative-Lemma package for $\Phi$
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical-map@L215-L225
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical-map@L226-L232
CONTRACT_ID: bpN:p5:canonical-map
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; φ ∈ 𝒪(r,s) with finite norm; 0 < ρ < r/2, 0 < σ < s/2; ε := ¦φ¦_{r,s}/(ρσ) ≤ ½; Ω = 𝒟_{r−ρ,s−σ}, ν = ν_{ρ,σ}; Φ = X^1_φ, Ψ = X^{−1}_φ (Lemma flow)
SOURCE_QUANTIFIERS: D, n; r, s; ρ, σ; φ; t ∈ [−1,1]; k ∈ ℤⁿ
SOURCE_CONCLUSION: (a) ν(X_φ) ≤ ε on Ω; Φ, Ψ defined and holomorphic on 𝒟_{r−3ρ/2,s−3σ/2} ⊂ Ω^{1/2} into Ω; ν(X^t−id) ≤ ¦t¦ε; ¦Φ_θ−θ¦_∞ ≤ ¦φ¦/ρ, ¦Φ_I−I¦_∞ ≤ ¦φ¦/(eσ) (same for Ψ); (b) Φ(θ+k,I) = Φ(θ,I)+(k,0), Φ real on real points if φ is; (c) on 𝒟_{r−2ρ,s−2σ}: ¦DΦ−1¦_ν ≤ 2ε; (d) (DΦ)ᵀJDΦ = J and Corollary canonical holds for Φ; (e) Ψ∘Φ = id = Φ∘Ψ on 𝒟_{r−2ρ,s−2σ} and Φ(𝒟_{r−2ρ,s−2σ}) ⊂ 𝒟_{r−3ρ/2,s−3σ/2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p5:cm-field, stepN:p5:cm-ab, stepN:p5:cm-cde, bpN:p5:flow, bpN:p5:canonical, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p5:cm-field | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical-map@L227-L227 | proof step
EDGE: stepN:p5:cm-ab | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical-map@L229-L229 | proof step (a),(b)
EDGE: stepN:p5:cm-cde | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical-map@L231-L231 | proof step (c)-(e)
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical-map@L216-L216 | Φ, Ψ are time-±1 maps of Lemma flow
EDGE: bpN:p5:canonical | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical-map@L221-L221 | Item (d) invokes Corollary canonical
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical-map@L216-L216 | 𝒪(r,s), ¦·¦_{r,s}
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical-map@L216-L217 | Ω = 𝒟_{r−ρ,s−σ}
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#bpN:p5:canonical-map@L216-L216 | ν = ν_{ρ,σ}, X_φ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-delta-N-b
REVIEWER: sol-delta2-N-b
LEAN_STATUS: PROVED
LEAN_REF: CanonData, canonical_map_a, canonical_map_b, canonical_map_c, canonical_map_d, canonical_map_e (KAM/Canonical/CanonicalMap.lean)
LEAN_NOTE: audit C5-10 PASS WITH NOTES; (d) corollary-canonical part via Symplectic lemmas per audit
NOTE: -

NODE: stepN:p5:cm-field
KIND: step
TITLE: Field
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-field@L227-L227
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-field@L227-L227
CONTRACT_ID: stepN:p5:cm-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; φ∈𝒪(r,s) with finite norm; 0<ρ<r/2, 0<σ<s/2; ε:=¦φ¦_{r,s}/(ρσ)≤1/2; Ω:=𝒟_{r−ρ,s−σ}; ν:=ν_{ρ,σ}; Φ:=X^1_φ; Ψ:=X^{−1}_φ; c≥3/2 with the target widths positive; z∈𝒟_{r−cρ,s−cσ}
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: z; c
SOURCE_CONCLUSION: ν(X_φ) ≤ ε on Ω (open); B̄_ν(z,c−1) = P̄(z;(c−1)σ,(c−1)ρ) ⊂ Ω, so 𝒟_{r−3ρ/2,s−3σ/2} ⊂ Ω^{1/2} and 𝒟_{r−2ρ,s−2σ} ⊂ Ω^1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:vf-bound, bpN:p4:domains, bpN:p5:flow, bpN:p5:setting, bpN:p4:norm
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:vf-bound | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-field@L227-L227 | ν(X_φ) ≤ ε
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-field@L227-L227 | (b): polydisc inclusion and openness of Ω
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-field@L227-L227 | Ω^c defined in Lemma flow
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-field@L227-L227 | closed ν-ball = P̄(z;cσ,cρ)
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-field@L227-L227 | Uses 𝒪 or its finite weighted norm, including the inherited source data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:cm-ab
KIND: step
TITLE: (a),(b)
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-ab@L229-L229
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-ab@L229-L229
CONTRACT_ID: stepN:p5:cm-ab
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; φ∈𝒪(r,s) with finite norm; 0<ρ<r/2, 0<σ<s/2; ε:=¦φ¦_{r,s}/(ρσ)≤1/2; Ω:=𝒟_{r−ρ,s−σ}; ν:=ν_{ρ,σ}; Φ:=X^1_φ; Ψ:=X^{−1}_φ; z∈𝒟_{r−3ρ/2,s−3σ/2}; ¦t¦≤1; k∈ℤⁿ; for reality φ real at real points
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: z; t; k
SOURCE_CONCLUSION: Φ, Ψ holomorphic with X^t(z) ∈ P̄(z;εσ,ερ) ⊂ 𝒟_{r−ρ,s−σ}; Φ(θ+k,I) = Φ(θ,I)+(k,0); reality; ¦X^t_θ−θ¦ ≤ ¦t¦¦φ¦/ρ, ¦X^t_I−I¦ ≤ ¦t¦¦φ¦/(eσ); Ψ = X^1_{−φ}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:flow, bpN:p5:vf-bound, K:bp:p1:ext-mvt, stepN:p5:cm-field, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-ab@L229-L229 | (a),(b),(d),(e): existence, displacement, regularity, translations, reality
EDGE: bpN:p5:vf-bound | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-ab@L229-L229 | componentwise bounds ¦∂_Iφ¦ ≤ ¦φ¦/ρ, ¦∂_θφ¦ ≤ ¦φ¦/(eσ)
EDGE: K:bp:p1:ext-mvt | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-ab@L229-L229 | mean value inequality along the trajectory
EDGE: stepN:p5:cm-field | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-ab@L229-L229 | 𝒟_{r−3ρ/2,s−3σ/2} ⊂ Ω^{1/2} (hypothesis of Lemma flow)
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-ab@L229-L229 | Uses 𝒪 or its finite weighted norm, including the inherited source data
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-ab@L229-L229 | Uses the analytic domains or the action neighbourhood in the source context
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-ab@L229-L229 | Uses X_φ, J, the scaled norm, or the iterated Poisson brackets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:cm-cde
KIND: step
TITLE: (c)--(e)
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-cde@L231-L231
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-cde@L231-L231
CONTRACT_ID: stepN:p5:cm-cde
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D ⊂ ℂⁿ; φ∈𝒪(r,s) with finite norm; 0<ρ<r/2, 0<σ<s/2; ε:=¦φ¦_{r,s}/(ρσ)≤1/2; Ω:=𝒟_{r−ρ,s−σ}; ν:=ν_{ρ,σ}; Φ:=X^1_φ; Ψ:=X^{−1}_φ; z∈𝒟_{r−2ρ,s−2σ} (membership in Ω¹ is supplied by cm-field)
SOURCE_QUANTIFIERS: D,n; r,s,r′,s′ when present; ρ,σ; φ; then u or h,w,f₀ or (v_t), with exactly SOURCE_HYPOTHESES; then local data in source order: z
SOURCE_CONCLUSION: (c) ¦DΦ−1¦_ν ≤ 2ε; (d) DΦᵀJ DΦ = J and Corollary canonical; (e) Ψ(Φz) = z = Φ(Ψz) and Φ(z) ∈ B̄_ν(z,ε) ⊂ 𝒟_{r−3ρ/2,s−3σ/2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p5:flow, stepN:p5:cm-field, bpN:p5:symplectic, bpN:p5:canonical, bpN:p4:norm, bpN:p4:domains, bpN:p5:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p5:flow | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-cde@L231-L231 | (c): inverse and derivative bound for z ∈ Ω^1
EDGE: stepN:p5:cm-field | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-cde@L231-L231 | 𝒟_{r−2ρ,s−2σ} ⊂ Ω^1
EDGE: bpN:p5:symplectic | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-cde@L231-L231 | (d): (DΦ)ᵀJDΦ = J
EDGE: bpN:p5:canonical | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-cde@L231-L231 | (d): bracket invariance and conjugation
EDGE: bpN:p4:norm | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-cde@L231-L231 | Uses 𝒪 or its finite weighted norm, including the inherited source data
EDGE: bpN:p4:domains | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-cde@L231-L231 | Uses the analytic domains or the action neighbourhood in the source context
EDGE: bpN:p5:setting | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:cm-cde@L231-L231 | Uses X_φ, J, the scaled norm, or the iterated Poisson brackets
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p5+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepN:p5:fl-symmetry#real-restriction
KIND: step
TITLE: Real restriction on the general open domain Ω
STATEMENT_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-symmetry@L73-L73
PROOF_SOURCE: blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-symmetry@L73-L73
CONTRACT_ID: stepN:p5:fl-symmetry#real-restriction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Ω ⊂ ℂ^N open; F holomorphic on Ω and F(x) ∈ ℝ^N on W := Ω∩ℝ^N
SOURCE_QUANTIFIERS: N; Ω; F
SOURCE_CONCLUSION: F restricted to W is C¹ as a real-valued map on the open real set W
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:holomorphic-regularity, bpN:p1:ext-restrict
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:holomorphic-regularity | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-symmetry@L73-L73 | holomorphy supplies real smoothness before restriction
EDGE: bpN:p1:ext-restrict | blueprint-N/parts/p5-canonical-maps.tex#stepN:p5:fl-symmetry@L73-L73 | available scalar-restriction input for the intended general-domain bridge
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-N-b
REVIEWER: sol-delta-N-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L73 cites K:bp:p1:real-restriction, whose statement is on an entire strip T_ρ, whereas Ω is arbitrary. The strip hypothesis is not supplied. This node exposes the general-domain, real-codomain restriction bridge; the available inputs are recorded, but the blueprint does not state this extension of the cited lemma. No additional hypothesis on Ω is introduced.
