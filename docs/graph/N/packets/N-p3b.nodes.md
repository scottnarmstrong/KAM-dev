NODE: bpN:p3:gen-exit
KIND: lemma
TITLE: First exit
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-exit@L328-L341
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-exit@L342-L350
CONTRACT_ID: bpN:p3:gen-exit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: IsSolIn F W J z with J an interval, 0 ∈ J; V ⊂ E open; z(0) ∈ V; A = {t ∈ J : t ≥ 0, z(t) ∉ V}; only continuity of z on J is used (F and W play no role)
SOURCE_QUANTIFIERS: E; F; W; J; z; V; A
SOURCE_CONCLUSION: exactly one of: (i) A = ∅, i.e. z(t) ∈ V for all t ∈ J, t ≥ 0; (ii) t* = min A exists, t* > 0, t* ∈ J, z(t) ∈ V on [0,t*), z(t*) ∈ ∂V = V̄∖V, and t* = sup{t ∈ J : t ≥ 0, z([0,t]) ⊂ V}; the same backwards in time
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-sol, bpN:p3:gen-symmetry, stepN:p3:exit-closed, stepN:p3:exit-min, stepN:p3:exit-bdry, stepN:p3:exit-sup
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-exit@L329-L329 | hypothesis IsSolIn F W J z
EDGE: bpN:p3:gen-symmetry | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-exit@L338-L338 | the backward-time assertion explicitly invokes reversal here; L340 is only provenance
EDGE: stepN:p3:exit-closed | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-exit@L343-L343 | A closed
EDGE: stepN:p3:exit-min | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-exit@L345-L345 | t* = min A
EDGE: stepN:p3:exit-bdry | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-exit@L347-L347 | boundary point
EDGE: stepN:p3:exit-sup | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-exit@L349-L349 | supremum formula
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_exit, KAM.ODE.exitSet (KAM/ODE/Exit.lean)
LEAN_NOTE: audit N3-45 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:exit-closed
KIND: step
TITLE: Closedness
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-closed@L343-L343
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-closed@L343-L343
CONTRACT_ID: stepN:p3:exit-closed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; IsSolIn F W J z; J an interval containing 0; V subset E open; z(0) in V; A={t in J:t>=0 and z(t) notin V}
SOURCE_QUANTIFIERS: A
SOURCE_CONCLUSION: A is closed in J ∩ [0,∞)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-sol#consequences, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-sol#consequences | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-closed@L343-L343 | z continuous on J (consequence (ii))
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-closed@L343-L343 | the source solution supplies continuity and membership; earlier step conclusions are not new premises
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: BYPASSED
LEAN_REF: KAM.ODE.gen_exit (KAM/ODE/Exit.lean)
LEAN_NOTE: Lean gen_exit (Exit.lean L36-104) replaces closedness of A in J cap [0,inf) by closedness of exitSet cap Icc 0 a for an actual a in A and compactness (hclosed, hcpt, L56-68); audit N3-45-audit-1.md L25 and bullet L256 (minimization on a compact segment). Route taken: compact-segment minimisation in gen_exit.
NOTE: -

NODE: stepN:p3:exit-min
KIND: step
TITLE: The minimum
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-min@L345-L345
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-min@L345-L345
CONTRACT_ID: stepN:p3:exit-min
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; IsSolIn F W J z; J an interval containing 0; V subset E open; z(0) in V; A={t in J:t>=0 and z(t) notin V}; branch A nonempty
SOURCE_QUANTIFIERS: t* = inf A
SOURCE_CONCLUSION: t* ∈ J, t* ∈ A, so z(t*) ∉ V, and t* > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:exit-closed, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:exit-closed | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-min@L345-L345 | by closedness t* ∈ A
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-min@L345-L345 | the source solution supplies continuity and membership; earlier step conclusions are not new premises
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_exit (KAM/ODE/Exit.lean)
LEAN_NOTE: IsLeast (exitSet J z V) t_star, 0<t_star, t_star in J (Exit.lean L68-78). Audit N3-45-audit-1.md L25 and bullet L256 (global leastness, positivity).
NOTE: -

NODE: stepN:p3:exit-bdry
KIND: step
TITLE: Boundary point
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-bdry@L347-L347
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-bdry@L347-L347
CONTRACT_ID: stepN:p3:exit-bdry
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; IsSolIn F W J z; J an interval containing 0; V subset E open; z(0) in V; A={t in J:t>=0 and z(t) notin V}; branch A nonempty; tstar=inf A is the local object constructed in exit-min
SOURCE_QUANTIFIERS: t ∈ [0,t*)
SOURCE_CONCLUSION: z(t) ∈ V on [0,t*) and z(t*) ∈ V̄∖V = ∂V
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:exit-min, bpN:p3:gen-sol#consequences, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:exit-min | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-bdry@L347-L347 | t* and z(t*) ∉ V
EDGE: bpN:p3:gen-sol#consequences | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-bdry@L347-L347 | continuity of z at t*
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-bdry@L347-L347 | the source solution supplies continuity and membership; earlier step conclusions are not new premises
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_exit (KAM/ODE/Exit.lean)
LEAN_NOTE: hbelow: z t in V on [0,t_star); hfront: z t_star in frontier V by left closure limit (Exit.lean L79-89). Audit N3-45-audit-1.md L25 and bullet L256.
NOTE: -

NODE: stepN:p3:exit-sup
KIND: step
TITLE: The supremum formula
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-sup@L349-L349
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-sup@L349-L349
CONTRACT_ID: stepN:p3:exit-sup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E finite-dimensional real normed space; IsSolIn F W J z; J an interval containing 0; V subset E open; z(0) in V; A={t in J:t>=0 and z(t) notin V}; branch A nonempty; tstar=inf A is the local object constructed in exit-min
SOURCE_QUANTIFIERS: t ∈ J, t ≥ 0
SOURCE_CONCLUSION: z([0,t]) ⊂ V iff t < t*, so the supremum equals t*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:exit-min, stepN:p3:exit-bdry, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:exit-min | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-sup@L349-L349 | t* = min A
EDGE: stepN:p3:exit-bdry | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-sup@L349-L349 | z(t) ∈ V on [0,t*)
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:exit-sup@L349-L349 | the source solution supplies continuity and membership; earlier step conclusions are not new premises
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.gen_exit (KAM/ODE/Exit.lean)
LEAN_NOTE: t_star = sSup of {t in J, 0<=t, z[0,t] in V}, both inequalities (Exit.lean L90-104). Audit N3-45-audit-1.md L25 and bullet L256.
NOTE: -

NODE: bpN:p3:ham-smooth
KIND: lemma
TITLE: Regularity of $X_H$
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-smooth@L377-L381
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-smooth@L382-L386
CONTRACT_ID: bpN:p3:ham-smooth
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P = ℝⁿ × ℝⁿ (max norm); W ⊂ P open; H : P → ℝ is C^{k+1} on W, k ≥ 0; X_H the frozen hamiltonianVectorField
SOURCE_QUANTIFIERS: n; W; H; k
SOURCE_CONCLUSION: X_H is C^k on W; for k ≥ 1 it is C¹ (hence locally Lipschitz) on W, and H is differentiable at every point of W
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:vf#hamiltonianVectorField, stepN:p3:hs-deriv, stepN:p3:hs-comp
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-smooth@L378-L378 | the Ck conclusion is about the frozen X_H
EDGE: stepN:p3:hs-deriv | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-smooth@L383-L383 | DH is C^k
EDGE: stepN:p3:hs-comp | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-smooth@L385-L385 | components of X_H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.ham_smooth, KAM.ODE.ham_smooth_c1 (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: audit N3-2 PASS WITH NOTES
NOTE: prose-L372-L375 (phase space P, X_H, partials) is recorded here and in ham-energy, ham-periodic, ham-reduction

NODE: stepN:p3:hs-deriv
KIND: step
TITLE: Derivative is $C^k$
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:hs-deriv@L383-L383
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:hs-deriv@L383-L383
CONTRACT_ID: stepN:p3:hs-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H C^{k+1} on the open set W
SOURCE_QUANTIFIERS: H; W
SOURCE_CONCLUSION: DH : W → L(P,ℝ) is C^k on W
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ext-calc
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ext-calc | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:hs-deriv@L383-L383 | ContDiffOn.fderiv_of_isOpen
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.ham_smooth (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: fderiv H is C^k on open W (hH.fderiv_of_isOpen, Hamiltonian.lean L47). Audit N3-2-audit-1.md L24 (Part 3 L377-385).
NOTE: -

NODE: stepN:p3:hs-comp
KIND: step
TITLE: Components
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:hs-comp@L385-L385
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:hs-comp@L385-L385
CONTRACT_ID: stepN:p3:hs-comp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P=R^n x R^n with max norm; W subset P open; H:P->R is C^{k+1} on W, k>=0; X_H is the frozen Hamiltonian vector field
SOURCE_QUANTIFIERS: n,W,H,k fixed as in ham-smooth; each component i; DH is the derivative, with its Ck regularity proved by hs-deriv
SOURCE_CONCLUSION: each coordinate of X_H is ± DH composed with a continuous linear evaluation, hence C^k, and X_H is C^k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:hs-deriv, bpN:p0:vf#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:hs-deriv | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:hs-comp@L385-L385 | DH is C^k
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:hs-comp@L385-L385 | coordinates of X_H in terms of DH
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.ham_smooth (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: Each coordinate is fderiv H applied to a fixed vector (clm_apply) and its negative; ContDiffOn.prodMk (Hamiltonian.lean L48-52). Audit N3-2-audit-1.md L24.
NOTE: -

NODE: bpN:p3:ham-energy
KIND: theorem
TITLE: Energy conservation
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-energy@L388-L393
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-energy@L394-L400
CONTRACT_ID: bpN:p3:ham-energy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H : P → ℝ; J ⊂ ℝ an interval; z : ℝ → P with H differentiable at z(t) and z having derivative X_H(z(t)) at t, for every t ∈ J; no regularity of H and no confinement beyond this
SOURCE_QUANTIFIERS: n; H; J; z
SOURCE_CONCLUSION: t ↦ H(z(t)) is constant on J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:vf#hamiltonianVectorField, stepN:p3:en-chain, stepN:p3:en-cancel, stepN:p3:en-const
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-energy@L389-L389 | z' = X_H(z) with the frozen hamiltonianVectorField
EDGE: stepN:p3:en-chain | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-energy@L395-L395 | derivative of H∘z
EDGE: stepN:p3:en-cancel | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-energy@L397-L397 | DH(z)[X_H(z)] = 0
EDGE: stepN:p3:en-const | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-energy@L399-L399 | constancy
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.ham_energy (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: audit N3-2 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:en-chain
KIND: step
TITLE: Chain rule
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:en-chain@L395-L395
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:en-chain@L395-L395
CONTRACT_ID: stepN:p3:en-chain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H differentiable at z(t), z' = X_H(z(t))
SOURCE_QUANTIFIERS: t ∈ J
SOURCE_CONCLUSION: d/dt H(z(t)) = DH(z(t))[X_H(z(t))]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ext-calc, bpN:p0:vf#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ext-calc | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:en-chain@L395-L395 | chain rule HasFDerivAt.comp_hasDerivAt
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:en-chain@L395-L395 | the chain-rule expression uses the frozen X_H at the visited point
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.ham_energy (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: chain rule inside ham_energy; audit N3-2 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:en-cancel
KIND: step
TITLE: Cancellation
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:en-cancel@L397-L397
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:en-cancel@L397-L397
CONTRACT_ID: stepN:p3:en-cancel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ℓ = DH(z) linear; X_H(z) = (a,b) with a_i = ℓ(0,e_i), b_i = −ℓ(e_i,0)
SOURCE_QUANTIFIERS: z = z(t)
SOURCE_CONCLUSION: ℓ(a,b) = 0 by linearity (the two sums cancel)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:vf#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:en-cancel@L397-L397 | components a_i, b_i of X_H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.clm_ham_zero (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: private helper (with clm_fst_eq, clm_snd_eq); audit N3-2 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:en-const
KIND: step
TITLE: Constancy
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:en-const@L399-L399
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:en-const@L399-L399
CONTRACT_ID: stepN:p3:en-const
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P=R^n x R^n; H:P->R; J an interval; z:R->P; for every t in J, H differentiable at z(t) and z has two-sided derivative X_H(z(t)) at t; take s<t in J
SOURCE_QUANTIFIERS: s < t in J
SOURCE_CONCLUSION: H(z(t)) = H(z(s))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:en-chain, stepN:p3:en-cancel, bpN:p3:ext-calc
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:en-chain | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:en-const@L399-L399 | H∘z differentiable with derivative DH(z)[X_H(z)]
EDGE: stepN:p3:en-cancel | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:en-const@L399-L399 | that derivative is 0
EDGE: bpN:p3:ext-calc | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:en-const@L399-L399 | continuous with right derivative 0 implies constant
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.ham_energy (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: segment constancy inside ham_energy; audit N3-2 PASS WITH NOTES
NOTE: -

NODE: bpN:p3:ham-periodic
KIND: lemma
TITLE: Periodicity in the angles passes to solutions
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-periodic@L402-L407
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-periodic@L408-L412
CONTRACT_ID: bpN:p3:ham-periodic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W ⊂ P open with W + (k,0) = W for k ∈ ℤⁿ; H : P → ℝ with H(θ+k,I) = H(θ,I) on W; (second part) IsSolIn X_H W J z
SOURCE_QUANTIFIERS: n; W; H; k ∈ ℤⁿ; J; z
SOURCE_CONCLUSION: X_H(θ+k,I) = X_H(θ,I) on W; hence IsSolIn X_H W J (z+(k,0)) for every k and H∘(z+(k,0)) = H∘z
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:vf#hamiltonianVectorField, bpN:p3:gen-sol, stepN:p3:per-field, stepN:p3:per-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-periodic@L403-L403 | X_H as frozen hamiltonianVectorField
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-periodic@L405-L405 | predicate IsSolIn X_H W J z
EDGE: stepN:p3:per-field | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-periodic@L409-L409 | periodicity of the field
EDGE: stepN:p3:per-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-periodic@L411-L411 | solutions translate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.ham_periodic (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: audit N3-2 PASS WITH NOTES; H-identity stated only for t in J (design correction)
NOTE: -

NODE: stepN:p3:per-field
KIND: step
TITLE: Field
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:per-field@L409-L409
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:per-field@L409-L409
CONTRACT_ID: stepN:p3:per-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P=R^n x R^n; W subset P open, W+(k,0)=W for all integer k; H:P->R integer-periodic in angles on W; fix k in Z^n and put tau_k(x)=x+(k,0)
SOURCE_QUANTIFIERS: n,W,H as in ham-periodic; every k in Z^n; every x in W
SOURCE_CONCLUSION: DH = DH∘τ_k on W (fderiv; both sides 0 where H is not differentiable), so X_H∘τ_k = X_H on W
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ext-calc, bpN:p0:vf#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ext-calc | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:per-field@L409-L409 | derivative of a translate (chain rule)
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:per-field@L409-L409 | evaluate DH on (0,e_i), (e_i,0) to get X_H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.ham_periodic (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: hX (Hamiltonian.lean L127-135): eventual equality of H and H(.+shift) gives fderiv equality, hence X_H periodic on W. Audit N3-2-audit-1.md L30 (Part 3 L402-411).
NOTE: -

NODE: stepN:p3:per-sol
KIND: step
TITLE: Solutions
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:per-sol@L411-L411
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:per-sol@L411-L411
CONTRACT_ID: stepN:p3:per-sol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P=R^n x R^n; W subset P open, W+(k,0)=W for all integer k; H:P->R integer-periodic in angles on W; IsSolIn X_H W J z; fix k in Z^n
SOURCE_QUANTIFIERS: n,W,H fixed as in ham-periodic; every J subset R,z:R->P satisfying the source solution premise; every k in Z^n with v=(k,0)
SOURCE_CONCLUSION: IsSolIn X_H W J (z+(k,0)) (space translation)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-symmetry, stepN:p3:per-field, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-symmetry | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:per-sol@L411-L411 | space translation gen-symmetry(c) with v = (k,0), F = X_H
EDGE: stepN:p3:per-field | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:per-sol@L411-L411 | F(x+v) = F(x) on W
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:per-sol@L411-L411 | the translated curve is a solution for the same source predicate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.ham_periodic (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: gen_symmetry_translate with v=angleShift k (Hamiltonian.lean L136-138). Audit N3-2-audit-1.md L30.
NOTE: -

NODE: bpN:p3:ham-reduction
KIND: proposition
TITLE: Track N and track I Hamiltonian predicates
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-reduction@L416-L427
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-reduction@L428-L432
CONTRACT_ID: bpN:p3:ham-reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H : P → ℝ; U ⊂ ℝⁿ open; W ⊂ P open with ℝⁿ × U ⊂ W; H C² on W; W_U = ℝⁿ × U
SOURCE_QUANTIFIERS: n; H; U; W; then for every J ⊂ ℝ and z : ℝ → P
SOURCE_CONCLUSION: IsSolutionOn H U J z ⇔ IsSolIn X_H W_U J z ⇔ IsHamiltonianSolutionOn H U J z, and X_H is C¹ on W_U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:sol#IsSolutionOn, I:bpI:p0:hamsol#IsHamiltonianSolutionOn, bpN:p3:gen-sol, bpN:p0:vf#hamiltonianVectorField, stepN:p3:red-mem, stepN:p3:red-diff
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:sol#IsSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-reduction@L420-L420 | frozen predicate KAM.Nekhoroshev.IsSolutionOn
EDGE: I:bpI:p0:hamsol#IsHamiltonianSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-reduction@L421-L421 | frozen predicate KAM.Iso.IsHamiltonianSolutionOn (track I)
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-reduction@L420-L420 | general predicate IsSolIn
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-reduction@L420-L420 | X_H, frozen hamiltonianVectorField
EDGE: stepN:p3:red-mem | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-reduction@L429-L429 | membership clause
EDGE: stepN:p3:red-diff | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-reduction@L431-L431 | differentiability is implied
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.ham_reduction (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: audit N3-2 PASS WITH NOTES; stronger (U need not be open)
NOTE: kept as one node (SPEC ruling); \frozen tags name IsSolutionOn and IsHamiltonianSolutionOn; the two predicates have the same formula up to naming of the action set

NODE: stepN:p3:red-mem
KIND: step
TITLE: Membership
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:red-mem@L429-L429
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:red-mem@L429-L429
CONTRACT_ID: stepN:p3:red-mem
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W_U = ℝⁿ × U
SOURCE_QUANTIFIERS: t
SOURCE_CONCLUSION: z(t)₂ ∈ U ⇔ z(t) ∈ W_U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.ham_reduction (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: Membership iff in ham_reduction (Hamiltonian.lean L160-168: mem_univ times (h t ht).1 and back). Audit N3-2-audit-1.md L32 (Part 3 L416-431, preserves the frozen action membership).
NOTE: -

NODE: stepN:p3:red-diff
KIND: step
TITLE: Differentiability is free
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:red-diff@L431-L431
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:red-diff@L431-L431
CONTRACT_ID: stepN:p3:red-diff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P=R^n x R^n; U subset R^n open; W subset P open with R^n x U subset W; H:P->R is C2 on W; W_U=R^n x U; for the pointwise differentiability clause consider t with z(t) in W_U; red-mem supplies the membership equivalence, not an additional premise
SOURCE_QUANTIFIERS: n,H,U,W fixed as in ham-reduction; every J subset R and z:R->P; at each t in J with z(t) in W_U the differentiability guard follows
SOURCE_CONCLUSION: DifferentiableAt ℝ H (z t) holds automatically, so IsSolutionOn and IsHamiltonianSolutionOn coincide with IsSolIn X_H W_U; X_H is C¹ on W_U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ham-smooth, stepN:p3:red-mem, bpN:p0:sol#IsSolutionOn, I:bpI:p0:hamsol#IsHamiltonianSolutionOn, bpN:p3:gen-sol, bpN:p0:vf#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ham-smooth | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:red-diff@L431-L431 | C² gives H differentiable and X_H C¹ (k = 1)
EDGE: stepN:p3:red-mem | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:red-diff@L431-L431 | membership clause
EDGE: bpN:p0:sol#IsSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:red-diff@L431-L431 | differentiability clause of the frozen predicate
EDGE: I:bpI:p0:hamsol#IsHamiltonianSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:red-diff@L431-L431 | same formula in track I's predicate
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:red-diff@L431-L431 | the predicate equivalence explicitly includes IsSolIn
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:red-diff@L431-L431 | the regularity conclusion concerns X_H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.ODE.diff_of_mem (KAM/ODE/Hamiltonian.lean)
LEAN_NOTE: private helper; audit N3-2 PASS WITH NOTES
NOTE: -

NODE: bpN:p3:s-N#data
KIND: definition
TITLE: Standing data of the section on the track-N statements
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:s-N@L472-L477
PROOF_SOURCE: -
CONTRACT_ID: bpN:p3:s-N#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: R, s > 0; h : ℂⁿ → ℂ with IsAnalyticIntegrable R s h; ε ≥ 0; f : ℂⁿ×ℂⁿ → ℂ with IsAnalyticPerturbation R s ε f; H = H_{h,f}; U ⊂ B(0,R+s) open (in N-HEAD-C, U = B(0,R))
SOURCE_QUANTIFIERS: R, s; h; ε; f; U
SOURCE_CONCLUSION: defines the standing data of §s-N: H = H_{h,f}; W_s = ℝⁿ × B(0,R+s) ⊂ P (open), with B(0,R+s) = 𝓑_s(R) by Remark rdomain-eq; U an open subset of B(0,R+s)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p0:integrable#IsAnalyticIntegrable, bpN:p0:pert#IsAnalyticPerturbation, bpN:p0:realH#realHamiltonian, bpN:p0:rdomain-eq
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p0:integrable#IsAnalyticIntegrable | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:s-N#data@L473-L473 | h satisfies the analytic integrable predicate
EDGE: bpN:p0:pert#IsAnalyticPerturbation | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:s-N#data@L474-L474 | f satisfies the size-eps perturbation predicate
EDGE: bpN:p0:realH#realHamiltonian | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:s-N#data@L475-L475 | H is defined to be H_{h,f}
EDGE: bpN:p0:rdomain-eq | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:s-N#data@L475-L475 | the real action domain equals B(0,R+s)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.Data, KAM.Nekhoroshev.Wdom (KAM/Nekhoroshev/Interfaces/Setting.lean)
LEAN_NOTE: Definition node: W_s = Wdom (literal univ x ball 0 (R+s), audit P1-1-audit-1.md L21,L45 and P1-2-audit-1.md L20,L54, PASS); H = frozen realHamiltonian; B(0,R+s)=B_s(R) is rdomain-eq (PROVED); U open subset is the hypothesis of the consuming theorems (N3-10b-audit-1.md L26-35). Same refs as p1:s-holo#data.
NOTE: section data for coverage item p3:prose-L472-L477; consumers: holo-input, local-exist, uniqueness-closed, confinement-glue

NODE: bpN:p3:holo-input
KIND: lemma
TITLE: Input from Part 1: $H$ is smooth on $W_s$
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:holo-input@L479-L483
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:holo-input@L484-L490
CONTRACT_ID: bpN:p3:holo-input
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data of §s-N (bpN:p3:s-N#data): R, s > 0; h with IsAnalyticIntegrable R s h; ε ≥ 0; f with IsAnalyticPerturbation R s ε f; H = H_{h,f}; W_s = ℝⁿ × B(0,R+s)
SOURCE_QUANTIFIERS: R, s; h; f; ε
SOURCE_CONCLUSION: H_{h,f} is C^∞ (in particular C²) on the open set W_s; X_H = X_{h+f} on W_s ∩ (ℝⁿ×ℝⁿ); H(θ+k,I) = H(θ,I) for (θ,I) ∈ W_s, k ∈ ℤⁿ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:s-N#data, bpN:p0:vf#hamiltonianVectorField, stepN:p3:hi-cite
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:s-N#data | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:holo-input@L479-L479 | standing data of §s-N (h, f, H, W_s)
EDGE: bpN:p0:vf#hamiltonianVectorField | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:holo-input@L480-L480 | X_H = X_{h+f} with the frozen hamiltonianVectorField
EDGE: stepN:p3:hi-cite | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:holo-input@L485-L485 | citation of Part 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.holo_input (KAM/Nekhoroshev/Interfaces/HoloReal.lean)
LEAN_NOTE: audit P1-2 PASS WITH NOTES; smoothness, field identity, periodicity
NOTE: hi-reg and hi-per ('for orientation', repeating the argument of bpN:p1:holo-real) are not nodes; forward pointer: bpN:p1:holo-real(b)-(d) is the proof, cited at hi-cite

NODE: stepN:p3:hi-cite
KIND: step
TITLE: Citation
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:hi-cite@L485-L485
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:hi-cite@L485-L485
CONTRACT_ID: stepN:p3:hi-cite
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source standing data bpN:p3:s-N#data (R,s>0; h with IsAnalyticIntegrable R s h; eps>=0; f with IsAnalyticPerturbation R s eps f; H=H_{h,f}; W_s=R^n x B(0,R+s); U open and contained in B(0,R+s))
SOURCE_QUANTIFIERS: n and the source section data R,s,h,eps,f,U first; then all points in W_s and all k in Z^n as in holo-input
SOURCE_CONCLUSION: H_{h,f} is C-infinity, hence C2, on the open W_s; the real frozen field X_H equals the complex Hamiltonian field X_{h+f} at included real points of W_s; H(theta+k,I)=H(theta,I) on W_s for every integer k; these are exactly holo-real(b),(c),(d)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p1:holo-real, bpN:p3:s-N#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p1:holo-real | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:hi-cite@L485-L485 | (b), (c), (d) are exactly the three claims
EDGE: bpN:p3:s-N#data | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:hi-cite@L485-L485 | match the fixed analytic h,f,H and real domain with the Part 1 lemma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.holo_input (KAM/Nekhoroshev/Interfaces/HoloReal.lean)
LEAN_NOTE: holo_input (HoloReal.lean L352-361) is exactly holo_real_b,c,d: C-infty on Wdom, X_H = X_{h+f} at real points, angle periodicity. Audit P1-2-audit-1.md L48 (PASS).
NOTE: -

NODE: bpN:p3:local-exist
KIND: theorem
TITLE: Local existence and uniqueness for $\texttt{IsSolutionOn}$
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:local-exist@L502-L507
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:local-exist@L508-L511
CONTRACT_ID: bpN:p3:local-exist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data of §s-N (bpN:p3:s-N#data), U ⊂ B(0,R+s) open; t₀ ∈ ℝ; z₀ ∈ ℝⁿ × U; for uniqueness: J an interval, t₀ ∈ J, y₁, y₂ with IsSolutionOn H U J y_i and y₁(t₀) = y₂(t₀)
SOURCE_QUANTIFIERS: R, s; h; f; ε; U; t₀; z₀ (resp. J, y₁, y₂)
SOURCE_CONCLUSION: there are ε' > 0 and y : ℝ → P with y(t₀) = z₀ and IsSolutionOn H U (t₀−ε',t₀+ε') y (both time directions); and y₁ = y₂ on J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:s-N#data, bpN:p0:sol#IsSolutionOn, stepN:p3:le-red, stepN:p3:le-apply
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:s-N#data | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:local-exist@L503-L504 | standing data of §s-N (H, U)
EDGE: bpN:p0:sol#IsSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:local-exist@L504-L505 | the source local-existence and uniqueness clauses use IsSolutionOn here
EDGE: stepN:p3:le-red | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:local-exist@L509-L509 | reduction to the general predicate
EDGE: stepN:p3:le-apply | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:local-exist@L510-L510 | existence and uniqueness
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-delta-N-c
REVIEWER: sol-delta2-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.ODE.local_exist (KAM/Nekhoroshev/ODE/Specialization.lean)
LEAN_NOTE: audit N3-10b PASS
NOTE: -

NODE: stepN:p3:le-red
KIND: step
TITLE: Reduction
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-red@L509-L509
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-red@L509-L509
CONTRACT_ID: stepN:p3:le-red
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source standing data bpN:p3:s-N#data (R,s>0; h with IsAnalyticIntegrable R s h; eps>=0; f with IsAnalyticPerturbation R s eps f; H=H_{h,f}; W_s=R^n x B(0,R+s); U open and contained in B(0,R+s)); for existence t0 in R and z0 in R^n x U; for uniqueness J an interval containing t0, IsSolutionOn H U J y_i and y_1(t0)=y_2(t0)
SOURCE_QUANTIFIERS: the source section data first; then every J subset R and z:R->P
SOURCE_CONCLUSION: IsSolutionOn H U J z iff IsSolIn X_H (R^n x U) J z, for all J,z; X_H is C1 on the open R^n x U, by ham-reduction with W=W_s and the C2 input supplied by holo-input
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ham-reduction, bpN:p3:holo-input, bpN:p3:s-N#data, bpN:p0:sol#IsSolutionOn, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ham-reduction | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-red@L509-L509 | Proposition ham-reduction with W = W_s
EDGE: bpN:p3:holo-input | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-red@L509-L509 | H is C² on W_s
EDGE: bpN:p3:s-N#data | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-red@L509-L509 | W_s and U ⊂ B(0,R+s)
EDGE: bpN:p0:sol#IsSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-red@L509-L509 | convert the frozen solution predicate to the general predicate
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-red@L509-L509 | the converted predicate is IsSolIn
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.ODE.local_exist (KAM/Nekhoroshev/ODE/Specialization.lean)
LEAN_NOTE: Private reduction (Specialization.lean L64-77): ham_reduction with W=Wdom, C2 from holo_input. Audit N3-10b-audit-1.md L30 and counterchecks L142.
NOTE: -

NODE: stepN:p3:le-apply
KIND: step
TITLE: Existence, uniqueness
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-apply@L510-L510
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-apply@L510-L510
CONTRACT_ID: stepN:p3:le-apply
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source standing data bpN:p3:s-N#data (R,s>0; h with IsAnalyticIntegrable R s h; eps>=0; f with IsAnalyticPerturbation R s eps f; H=H_{h,f}; W_s=R^n x B(0,R+s); U open and contained in B(0,R+s)); for existence t0 in R and z0 in R^n x U; for uniqueness J an interval containing t0, IsSolutionOn H U J y_i and y_1(t0)=y_2(t0)
SOURCE_QUANTIFIERS: the source section data first; for existence every t0 in R,z0 in R^n x U, then epslocal>0,y; independently for uniqueness every interval J containing t0 and y_1,y_2 with the stated initial equality and source solution predicates
SOURCE_CONCLUSION: there exist epslocal>0 and y:R->P with y(t0)=z0 and IsSolutionOn H U (t0-epslocal,t0+epslocal) y; any y_1,y_2 satisfying IsSolutionOn H U J y_i and y_1(t0)=y_2(t0) agree on the whole interval J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-local, bpN:p3:gen-uniqueness, stepN:p3:le-red, bpN:p3:s-N#data, bpN:p0:sol#IsSolutionOn, bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-local | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-apply@L510-L510 | local existence for X_H on ℝⁿ × U
EDGE: bpN:p3:gen-uniqueness | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-apply@L510-L510 | uniqueness on every interval
EDGE: stepN:p3:le-red | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-apply@L510-L510 | reduction to IsSolIn
EDGE: bpN:p3:s-N#data | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-apply@L510-L510 | the local-time and uniqueness application uses the fixed H,U and their analytic setting
EDGE: bpN:p0:sol#IsSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-apply@L510-L510 | the local theorem constructs and compares frozen Hamiltonian solutions
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:le-apply@L510-L510 | apply the general existence and uniqueness results after reduction
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.ODE.local_exist (KAM/Nekhoroshev/ODE/Specialization.lean)
LEAN_NOTE: local_exist L100-114: gen_local and gen_uniqueness through the reduction iff. Audit N3-10b-audit-1.md L30.
NOTE: -

NODE: bpN:p3:uniqueness-closed
KIND: theorem
TITLE: Uniqueness on closed intervals
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:uniqueness-closed@L535-L539
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:uniqueness-closed@L540-L542
CONTRACT_ID: bpN:p3:uniqueness-closed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data of §s-N; L ≥ 0; y₁, y₂ with y₁(0) = y₂(0) and IsSolutionOn H U [−L,L] y_i
SOURCE_QUANTIFIERS: R, s; h; f; ε; U; L; y₁, y₂
SOURCE_CONCLUSION: y₁ = y₂ on [−L,L]; in particular a solution on [−L,L] agrees with every solution on a larger interval with the same initial value; no confinement of y assumed
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:s-N#data, bpN:p0:sol#IsSolutionOn, stepN:p3:uc-apply
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:s-N#data | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:uniqueness-closed@L535-L535 | standing data of §s-N (H, U)
EDGE: bpN:p0:sol#IsSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:uniqueness-closed@L536-L536 | frozen predicate IsSolutionOn
EDGE: stepN:p3:uc-apply | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:uniqueness-closed@L541-L541 | apply local-exist (uniqueness part)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.ODE.uniqueness_closed (KAM/Nekhoroshev/ODE/Specialization.lean)
LEAN_NOTE: audit N3-10b PASS
NOTE: -

NODE: stepN:p3:uc-apply
KIND: step
TITLE: Apply
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-apply@L541-L541
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-apply@L541-L541
CONTRACT_ID: stepN:p3:uc-apply
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source standing data bpN:p3:s-N#data (R,s>0; h with IsAnalyticIntegrable R s h; eps>=0; f with IsAnalyticPerturbation R s eps f; H=H_{h,f}; W_s=R^n x B(0,R+s); U open and contained in B(0,R+s)); Ltime>=0; y_1(0)=y_2(0); IsSolutionOn H U [-Ltime,Ltime] y_i (i=1,2)
SOURCE_QUANTIFIERS: the section data first; every Ltime>=0 and y_1,y_2 satisfying the source premises; instantiate J=[-Ltime,Ltime], t0=0
SOURCE_CONCLUSION: y_1=y_2 on [-Ltime,Ltime], by the uniqueness clause of local-exist; this also gives agreement with a solution on a larger interval after restriction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:local-exist, bpN:p3:s-N#data, bpN:p0:sol#IsSolutionOn
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:local-exist | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-apply@L541-L541 | uniqueness part with J = [−L,L], t₀ = 0
EDGE: bpN:p3:s-N#data | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-apply@L541-L541 | the local-exist theorem uses the standing analytic H,U setting
EDGE: bpN:p0:sol#IsSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:uc-apply@L541-L541 | the compared curves satisfy the frozen Hamiltonian solution predicate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.ODE.uniqueness_closed (KAM/Nekhoroshev/ODE/Specialization.lean)
LEAN_NOTE: uniqueness_closed L174-186 applies gen_uniqueness (the same uniqueness clause as local_exist) on Icc(-L,L) with t0=0; L<0 handled as empty. Audit N3-10b-audit-1.md L34,L148.
NOTE: -

NODE: bpN:p3:confinement-glue
KIND: theorem
TITLE: Confinement glue
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:confinement-glue@L544-L552
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:confinement-glue@L553-L557
CONTRACT_ID: bpN:p3:confinement-glue
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data of §s-N; θ₀ ∈ ℝⁿ; I₀ ∈ U; τ > 0; ρ > 0 with B̄(I₀,ρ) ⊂ U; for every open interval J ∋ 0 and y with y(0) = (θ₀,I₀) and IsSolutionOn H U J y: ¦y(t)₂−I₀¦ ≤ ρ for t ∈ J, ¦t¦ ≤ τ
SOURCE_QUANTIFIERS: R, s; h; f; ε; U; θ₀, I₀; τ; ρ; then z; L ∈ [0,τ]; y
SOURCE_CONCLUSION: there is z with z(0) = (θ₀,I₀), IsSolutionOn H U [−τ,τ] z and ¦z(t)₂−I₀¦ ≤ ρ for ¦t¦ ≤ τ; and for every L ∈ [0,τ] and y with y(0) = z(0) and IsSolutionOn H U [−L,L] y, y = z on [−L,L]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:s-N#data, bpN:p0:sol#IsSolutionOn, stepN:p3:cg-set, stepN:p3:cg-glue
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:s-N#data | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:confinement-glue@L544-L544 | standing data of §s-N (H, U)
EDGE: bpN:p0:sol#IsSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:confinement-glue@L545-L545 | frozen predicate IsSolutionOn in hypothesis and conclusion
EDGE: stepN:p3:cg-set | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:confinement-glue@L554-L554 | compact confinement set
EDGE: stepN:p3:cg-glue | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:confinement-glue@L555-L555 | general glue
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b
REVIEWER: sol-review-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.ODE.confinement_glue (KAM/Nekhoroshev/ODE/Specialization.lean)
LEAN_NOTE: audit N3-10b PASS
NOTE: constants: ρ = Cε^{1/(2n)} when used in Part 10; the proof does not cite local-exist/continuation (SPEC check)

NODE: stepN:p3:cg-set
KIND: step
TITLE: Compact confinement set
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-set@L554-L554
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-set@L554-L554
CONTRACT_ID: stepN:p3:cg-set
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source standing data bpN:p3:s-N#data (R,s>0; h with IsAnalyticIntegrable R s h; eps>=0; f with IsAnalyticPerturbation R s eps f; H=H_{h,f}; W_s=R^n x B(0,R+s); U open and contained in B(0,R+s)); theta0 in R^n; I0 in U; tau,rho>0; closedBall(I0,rho) subset U; every IsSolutionOn H U J y on an open interval J containing 0 through (theta0,I0) has abs(y(t)_2-I0)<=rho whenever t in J and abs(t)<=tau
SOURCE_QUANTIFIERS: the source section data, theta0,I0,tau,rho and the a priori hypothesis; define K=closedBall(I0,rho) and Phi=R^n x K; then choose uniform delta,M,L
SOURCE_CONCLUSION: K=closedBall(I0,rho) is compact and contained in U; Phi=R^n x K has uniform data (delta,M,L) for some delta in (0,1] and M,L>=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:gen-uniform-periodic, bpN:p3:ham-periodic, bpN:p3:holo-input, bpN:p3:ham-reduction, bpN:p3:s-N#data, bpN:p3:ext-compact, bpN:p3:gen-uniform
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:gen-uniform-periodic | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-set@L554-L554 | uniform data for ℝⁿ × K
EDGE: bpN:p3:ham-periodic | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-set@L554-L554 | X_H periodic in the angles
EDGE: bpN:p3:holo-input | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-set@L554-L554 | H is C² and 1-periodic in θ on W_s, hypotheses of ham-periodic and ham-smooth
EDGE: bpN:p3:ham-reduction | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-set@L554-L554 | X_H is C¹ on ℝⁿ × U, hypothesis of gen-uniform-periodic
EDGE: bpN:p3:s-N#data | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-set@L554-L554 | H,U and W_s are the standing section objects needed for all regularity/periodicity premises
EDGE: bpN:p3:ext-compact | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-set@L554-L554 | the closed finite-dimensional action ball K is compact
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-set@L554-L554 | the conclusion is uniform data for the cylinder Phi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.ODE.confinement_glue (KAM/Nekhoroshev/ODE/Specialization.lean)
LEAN_NOTE: confinement_glue L202: gen_uniform_periodic with isCompact_closedBall I0 rho and hball gives delta<=1 and uniform data of univ x K. Audit N3-10b-audit-1.md L35 and counterchecks L146-148.
NOTE: -

NODE: stepN:p3:cg-glue
KIND: step
TITLE: General glue
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-glue@L555-L556
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-glue@L555-L556
CONTRACT_ID: stepN:p3:cg-glue
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the source standing data bpN:p3:s-N#data (R,s>0; h with IsAnalyticIntegrable R s h; eps>=0; f with IsAnalyticPerturbation R s eps f; H=H_{h,f}; W_s=R^n x B(0,R+s); U open and contained in B(0,R+s)); theta0 in R^n; I0 in U; tau,rho>0; closedBall(I0,rho) subset U; every IsSolutionOn H U J y on an open interval J containing 0 through (theta0,I0) has abs(y(t)_2-I0)<=rho whenever t in J and abs(t)<=tau; K and Phi are defined as in cg-set, with uniform data provided by that dependency
SOURCE_QUANTIFIERS: the source section data, theta0,I0,tau,rho and the a priori hypothesis; K,Phi from cg-set; then a constructed solution z; afterwards every Ltime in [0,tau] and comparison solution y
SOURCE_CONCLUSION: the a priori hypothesis is equivalent, by ham-reduction, to confinement of every IsSolIn X_H (R^n x U) J y through (theta0,I0) in Phi for abs(t)<=tau on open J; gen-confinement yields z with z(0)=(theta0,I0), IsSolutionOn H U [-tau,tau] z, action displacement <=rho there, and agreement with every IsSolutionOn H U [-Ltime,Ltime] y through z(0) for all Ltime in [0,tau]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpN:p3:ham-reduction, bpN:p3:gen-confinement, stepN:p3:cg-set, bpN:p3:s-N#data, bpN:p3:gen-uniform, bpN:p3:gen-sol, bpN:p0:sol#IsSolutionOn
ROUTES: -
ROUTE_FOR: -
EDGE: bpN:p3:ham-reduction | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-glue@L555-L555 | IsSolutionOn H U ⇔ IsSolIn X_H (ℝⁿ×U)
EDGE: bpN:p3:gen-confinement | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-glue@L556-L556 | Theorem gen-confinement gives z and uniqueness
EDGE: stepN:p3:cg-set | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-glue@L555-L555 | uniform data of Φ
EDGE: bpN:p3:s-N#data | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-glue@L555-L556 | the reduction and confinement application use the standing H,U and open domain
EDGE: bpN:p3:gen-uniform | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-glue@L555-L556 | uniform data for Phi discharge gen-confinement
EDGE: bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-glue@L555-L556 | the a priori hypothesis is converted for every general solution on an open interval
EDGE: bpN:p0:sol#IsSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:cg-glue@L555-L556 | convert the source hypothesis and the resulting closed-interval conclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-N-p3b+sol-review-N-c
REVIEWER: sol-delta-N-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Nekhoroshev.ODE.confinement_glue (KAM/Nekhoroshev/ODE/Specialization.lean)
LEAN_NOTE: confinement_glue L203-212: hconf translated through the reduction iff and mem set, then gen_confinement. Audit N3-10b-audit-1.md L35 and counterchecks L146-148.
NOTE: -
