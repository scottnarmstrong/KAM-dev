NODE: bpW:w1:transport
KIND: definition
TITLE: Weights, transport and coefficient maps
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:transport@L30-L39
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a, p in R; K in {R, C}; a >= 0 for l^{a,p}_K
SOURCE_QUANTIFIERS: a, p, K
SOURCE_CONCLUSION: defines omega_{a,p}(j) = j^p e^{aj} > 0 (frozen ellWeight a p j), l^2_K = l^2(N_+;K), tau_{a,p} : l^{a,p}_K -> l^2_K, (tau w)_j = omega_{a,p}(j) w_j, kappa_{a,p} : l^2_K -> l^{a,p}_K, (kappa y)_j = y_j/omega_{a,p}(j); y represents w = kappa y (weighted coordinates); a map A : l^{a,p} -> l^{a',p'} is represented by hat A = tau_{a',p'} o A o kappa_{a,p}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:ellap#ellWeight, bpW:w0:ellap#coeff, bpW:w0:ellap#spaces
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w1-sequences.tex#bpW:w1:transport@L31-L31 | omega_{a,p}(j) is the frozen ellWeight a p j
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:transport@L51-L51 | kappa_{1,1} is the frozen coeff in the realization table
EDGE: bpW:w0:ellap#spaces | blueprint-W/parts/w1-sequences.tex#bpW:w1:transport@L33-L33 | the general weighted spaces are taken from Definition bpW:w0:ellap
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a
REVIEWER: sol-delta-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-lp
KIND: external
TITLE: $\ell^2$ spaces
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-lp@L72-L77
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-lp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: l^2(iota;K) is a Hilbert space for every index type (lp.instInnerProductSpace, lp.completeSpace) with <f,g> = sum conj(f_i) g_i; ¦f_i¦ <= ¦¦f¦¦; membership and norm bounds follow from bounds on finite partial sums; f = sum_i f_i e_i, e_i = lp.single 2 i 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-series
KIND: external
TITLE: Series
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-series@L78-L80
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-series
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: sum_{k>=1} k^{-2} = pi^2/6; sum_{k>=1} k^{-sigma} < infinity for sigma > 1; Tonelli for nonnegative double series and Fubini for absolutely summable ones
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-analytic
KIND: external
TITLE: Analytic maps
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-analytic@L81-L88
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: a continuous multilinear map is analytic (a continuous polynomial) everywhere; continuous linear and bilinear maps are analytic; compositions and pairs of analytic maps are analytic; a continuous bilinear map applied to two analytic maps is analytic; C-analytic maps are R-analytic; analytic maps are Frechet differentiable
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-onevar
KIND: external
TITLE: One complex variable, Banach values
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-onevar@L89-L98
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-onevar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: for a complete complex normed space F: the Cauchy estimate (phi continuous on the closed disc of radius R > 0, holomorphic inside, ¦¦phi¦¦ <= B on the circle implies ¦¦phi'(c)¦¦ <= B/R); the Cauchy integral formula (valid for complete F; K's bp:p1:ext-cauchy, provenance), in particular the formula for phi'(c); continuous linear maps commute with Bochner integrals; the norm is attained by norm-one functionals; holomorphic maps on open subsets of C are analytic; a locally uniform limit of holomorphic maps on an open subset of C is holomorphic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-unifderiv
KIND: external
TITLE: Uniform limits and derivatives
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-unifderiv@L99-L102
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-unifderiv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: if f_k -> f pointwise on an open set U of a normed space over K, each f_k is differentiable on U and Df_k -> g uniformly on U, then f is differentiable on U with Df = g; the mean value inequality on convex sets (K's bp:p1:ext-mvt, provenance)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-integral
KIND: external
TITLE: Integrals
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-integral@L103-L108
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-integral
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: Bochner integrals of continuous maps of a compact interval or box into a complete space; ¦¦int F¦¦ <= int ¦¦F¦¦; differentiation under the integral sign with a dominating bound on the derivative (a.e.-strongly measurable integrand and derivative, measurability from continuity); dominated convergence (K's bp:p1:ext-integral, provenance)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-ode
KIND: external
TITLE: ODE
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-ode@L109-L111
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-ode
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: Picard-Lindelof existence and uniqueness for Lipschitz fields in a Banach space; Gronwall's inequality
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-fourier
KIND: external
TITLE: Fourier analysis
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-fourier@L112-L116
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-fourier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: the characters e^{inx}, n in Z, form a Hilbert basis of L^2 of R/2piZ with normalized Haar measure, and e^{2 pi i k.x}, k in Z^n, one of L^2(R^n/Z^n); Parseval; continuous periodic functions with absolutely summable coefficients are the sums of their Fourier series (K's bp:p1:ext-fourier, provenance)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:space
KIND: lemma
TITLE: The weighted spaces
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L131-L145
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L147-L163
CONTRACT_ID: bpW:w1:space
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p in R, K in {R, C}
SOURCE_QUANTIFIERS: for all a >= 0, p
SOURCE_CONCLUSION: (i) tau_{a,p}, kappa_{a,p} are mutually inverse K-linear bijections, ¦¦tau w¦¦_{l^2} = ¦¦w¦¦_{a,p}; l^{a,p}_K with <w,w'>_{a,p} = sum omega^2 conj(w_j) w'_j is a Hilbert space isometric to l^2_K, complete and separable; (ii) ¦(kappa y)_j¦ <= ¦¦y¦¦/omega_{a,p}(j) and y -> (kappa y)_j is the continuous linear functional omega^{-1} ev_j; (iii) ¦¦y - P_N y¦¦ -> 0 for the truncations P_N; (iv) for K = R, a = p = 1, kappa_{1,1} is the frozen coeff, and WaveSpace = l^2_R x l^2_R with its product (max) norm is isometric to E_{1,1} with ¦¦(q,p)¦¦_E = max(¦¦q¦¦_{1,1}, ¦¦p¦¦_{1,1}) via kappa_{1,1} x kappa_{1,1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, stepW:w1:iso, stepW:w1:sep, stepW:w1:coord, stepW:w1:frozen, bpW:w0:ellap#coeff, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L134-L134 | tau, kappa and the weights
EDGE: stepW:w1:iso | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L148-L148 | proof step
EDGE: stepW:w1:sep | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L153-L153 | proof step
EDGE: stepW:w1:coord | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L157-L157 | proof step
EDGE: stepW:w1:frozen | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L160-L160 | proof step
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L141-L141 | the frozen coeff occurs directly here
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L141-L141 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:iso
KIND: step
TITLE: Isometry
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L148-L152
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L148-L152
CONTRACT_ID: stepW:w1:iso
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:space: a >= 0, p in R, K in {R, C}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:space (for all a >= 0, p); within the step: w in l^{a,p}_K; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦tau w¦¦^2 = ¦¦w¦¦_{a,p}^2; tau, kappa are mutually inverse; the inner product and completeness transport from l^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, bpW:w0:ellap#ellWeight, bpW:w1:ext-lp, bpW:w0:ellap#spaces
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L149-L149 | tau, kappa, omega
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L149-L149 | the norm of Definition bpW:w0:ellap
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L152-L152 | inner product and completeness of l^2
EDGE: bpW:w0:ellap#spaces | blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L149-L149 | the weighted norm identity directly invokes the general spaces definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a
REVIEWER: sol-delta-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:sep
KIND: step
TITLE: Separability
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sep@L153-L156
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sep@L153-L156
CONTRACT_ID: stepW:w1:sep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:space: a >= 0, p in R, K in {R, C}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:space (for all a >= 0, p); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: finitely supported sequences with rational (Gaussian rational) entries form a countable dense set, so l^{a,p}_K is separable (not consumed by later milestones)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:coord
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:coord | blueprint-W/parts/w1-sequences.tex#stepW:w1:sep@L155-L155 | density by the truncation statement (iii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a
REVIEWER: sol-delta-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:coord
KIND: step
TITLE: Coordinates and truncation
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L157-L159
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L157-L159
CONTRACT_ID: stepW:w1:coord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:space: a >= 0, p in R, K in {R, C}; local data: y in l^2_K
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:space (for all a >= 0, p); within the step: j, N; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) ¦(kappa y)_j¦ <= ¦¦y¦¦/omega(j); (iii) ¦¦y - P_N y¦¦^2 = sum_{j>N} ¦y_j¦^2 -> 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-lp, bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L158-L158 | ¦y_j¦ <= ¦¦y¦¦
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L158-L158 | kappa divides by omega(j)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:frozen
KIND: step
TITLE: Frozen case
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L160-L162
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L160-L162
CONTRACT_ID: stepW:w1:frozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:space: a >= 0, p in R, K in {R, C}; local data: K = R, a = p = 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:space (for all a >= 0, p); within the step: y, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: coeff y j = y_j/omega_{1,1}(j) by the frozen definition, and Mathlib's product norm is the max norm, giving (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:ellap#coeff, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L161-L161 | unfolds the frozen coeff
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L162-L162 | the frozen WaveSpace with the product (max) norm
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:coordinatewise
KIND: lemma
TITLE: Derivatives of coordinates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L167-L177
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L179-L189
CONTRACT_ID: bpW:w1:coordinatewise
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c : R -> l^2_K differentiable at t; weights (a,p), (a',p') with a >= a', p >= p'; iota the inclusion of Lemma bpW:w1:embed, represented by hat iota; v in l^2_K
SOURCE_QUANTIFIERS: for all such c, t, v
SOURCE_CONCLUSION: (a) for every j, t -> (kappa_{a,p} c(t))_j has derivative (kappa_{a',p'} v)_j at t iff (b) hat iota c'(t) = v; in particular for differentiable K : R^2 -> WaveSpace and X^w of Proposition bpW:w1:hamfield(v), the frozen conclusion (4) of KAM.Wave.nlw2 at (I,theta) (the HasDerivAt of t -> coeff (K(theta + t nu)).i j at 0) is equivalent to hat iota(DK(theta) nu) = X^w(K(theta)), hat iota representing E_{1,1} subset E_{1,0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:embed, bpW:w1:hamfield, bpW:w0:ellap#coeff, stepW:w1:coordder, stepW:w1:coordcomp, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L169-L169 | the inclusion iota and its representative
EDGE: bpW:w1:hamfield | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L174-L174 | the field X^w of (v)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L174-L174 | the coefficients coeff in the frozen conclusion (4)
EDGE: stepW:w1:coordder | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L180-L180 | proof step
EDGE: stepW:w1:coordcomp | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L184-L184 | proof step
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L173-L173 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The statement speaks of the *form* of the frozen conclusion (4) of nlw2; that is not a use of the root (no edge to bpW:wh:nlw2, which would create a cycle once W8 is added).

NODE: stepW:w1:coordder
KIND: step
TITLE: Coordinates of the derivative
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L180-L183
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L180-L183
CONTRACT_ID: stepW:w1:coordder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:coordinatewise: c : R -> l^2_K differentiable at t; weights (a,p), (a',p') with a >= a', p >= p'; iota the inclusion of Lemma bpW:w1:embed, represented by hat iota; v in l^2_K; local data: c differentiable at t
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:coordinatewise (for all such c, t, v); within the step: j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the coordinate curve t -> (kappa_{a,p} c(t))_j has derivative (kappa_{a,p} c'(t))_j = (kappa_{a',p'} hat iota c'(t))_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:space, bpW:w1:embed
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L181-L181 | (ii): the coordinate is a continuous linear functional
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L183-L183 | (iii): the inclusion does not change coefficients
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:coordcomp
KIND: step
TITLE: Comparison
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L184-L188
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L184-L188
CONTRACT_ID: stepW:w1:coordcomp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:coordinatewise: c : R -> l^2_K differentiable at t; weights (a,p), (a',p') with a >= a', p >= p'; iota the inclusion of Lemma bpW:w1:embed, represented by hat iota; v in l^2_K
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:coordinatewise (for all such c, t, v); within the step: j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (a) iff (b) by injectivity of kappa_{a',p'}; for the frozen statement, c(t) = K(theta + t nu) componentwise at t = 0 with (a,p) = (1,1), (a',p') = (1,0), compared with Proposition bpW:w1:hamfield(v)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:coordder, bpW:w1:space, bpW:w1:hamfield
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:coordder | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L185-L185 | the derivative of the coordinates
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L186-L186 | injectivity of kappa ((i))
EDGE: bpW:w1:hamfield | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L188-L188 | (v): the coordinates of X^w are the right sides of (4)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:multiplier
KIND: lemma
TITLE: Diagonal multipliers
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L192-L198
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L200-L204
CONTRACT_ID: bpW:w1:multiplier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu : N_+ -> K and M >= 0 with ¦mu_j¦ <= M for all j
SOURCE_QUANTIFIERS: for all mu, M
SOURCE_CONCLUSION: D_mu y = (mu_j y_j) is bounded linear on l^2_K with ¦¦D_mu¦¦ <= M and ¦¦D_mu¦¦ >= ¦mu_j¦ for every j; a diagonal map w -> (m_j w_j) from l^{a,p}_K to l^{a',p'}_K has representative D_mu with mu_j = m_j omega_{a',p'}(j)/omega_{a,p}(j); it is bounded with norm <= M when ¦mu_j¦ <= M, and unbounded if (mu_j) is unbounded
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-lp, bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L202-L202 | norm bounds from finite partial sums
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L203-L203 | the representative tau o (m .) o kappa
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:embed
KIND: lemma
TITLE: Embeddings
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L207-L216
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L218-L223
CONTRACT_ID: bpW:w1:embed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= a' >= 0, p, p' in R
SOURCE_QUANTIFIERS: for all such weights; w
SOURCE_CONCLUSION: (i) if p >= p', l^{a,p}_K subset l^{a',p'}_K with ¦¦w¦¦_{a',p'} <= ¦¦w¦¦_{a,p}, representative D_mu, mu_j = j^{p'-p} e^{(a'-a)j} in (0,1]; (ii) if a > a' and sigma = p' - p > 0, ¦¦w¦¦_{a',p'} <= (sigma/(e(a-a')))^sigma ¦¦w¦¦_{a,p}; (iii) the inclusions do not change coefficients (kappa_{a',p'} D_mu = kappa_{a,p}), are injective and compose
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:multiplier, bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L219-L219 | m_j = 1, mu_j = omega_{a',p'}(j)/omega_{a,p}(j)
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L222-L222 | the identity mu_j/omega_{a',p'}(j) = 1/omega_{a,p}(j)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:diag
KIND: lemma
TITLE: Frequency multipliers and the linear flow
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L226-L241
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L243-L258
CONTRACT_ID: bpW:w1:diag
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p in R, r in R; lambda^r the multiplier w -> (lambda_j^r w_j)
SOURCE_QUANTIFIERS: for all a, p, r; t, s in R
SOURCE_CONCLUSION: (i) lambda^r is bounded l^{a,p+r}_K -> l^{a,p}_K, norm (1+m)^{r/2} for r >= 0 (attained at j = 1), at most 1 for r < 0, representative D_mu with mu_j = (lambda_j/j)^r, an isomorphism with inverse lambda^{-r}; (ii) for r > 0 it is not bounded l^{a,p} -> l^{a,p}; (iii) R_t z = (e^{-i lambda_j t} z_j) is a linear isometry of l^{a,p}_C, R_{t+s} = R_t R_s, t -> R_t z continuous; (iv) the real linear flow L_t(q,p) = (cos(lambda t)q + sin(lambda t)p, -sin(lambda t)q + cos(lambda t)p) preserves ¦¦q¦¦^2 + ¦¦p¦¦^2, ¦¦L_t(q,p)¦¦_E <= sqrt2 ¦¦(q,p)¦¦_E, L_{t+s} = L_t L_s, every coordinate solves dq_j = lambda_j p_j, dp_j = -lambda_j q_j, and in the coordinates z of Definition bpW:w0:z, L_t is R_t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lam, bpW:w0:z, stepW:w1:ratio, stepW:w1:rot, stepW:w1:realflow
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L227-L227 | the multiplier lambda^r
EDGE: bpW:w0:z | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L239-L239 | the complex coordinates z
EDGE: stepW:w1:ratio | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L244-L244 | proof step
EDGE: stepW:w1:rot | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L249-L249 | proof step
EDGE: stepW:w1:realflow | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L253-L253 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:ratio
KIND: step
TITLE: Ratio
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L244-L248
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L244-L248
CONTRACT_ID: stepW:w1:ratio
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:diag: a >= 0, p in R, r in R; lambda^r the multiplier w -> (lambda_j^r w_j)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:diag (for all a, p, r; t, s in R); within the step: j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: mu_j = (lambda_j/j)^r with 1 < lambda_j/j <= sqrt(1+m), equality at j = 1; so ¦mu_j¦ <= (1+m)^{r/2} = mu_1 (r >= 0), ¦mu_j¦ <= 1 (r < 0); the inverse is the same with -r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:multiplier, bpW:w0:basis#lambda-facts, bpW:w0:mass, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L245-L245 | the representative and its norm
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L246-L246 | j < lambda_j
EDGE: bpW:w0:mass | blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L246-L246 | lambda_j^2 = j^2 + m <= (1+m) j^2
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L245-L245 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:rot
KIND: step
TITLE: Unboundedness and rotations
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L249-L252
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L249-L252
CONTRACT_ID: stepW:w1:rot
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:diag: a >= 0, p in R, r in R; lambda^r the multiplier w -> (lambda_j^r w_j); local data: t, s in R; z in l^{a,p}_C
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:diag (for all a, p, r; t, s in R); within the step: t, s; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) for r > 0, lambda_j^r tends to infinity and lambda^r is unbounded on the same weighted space; (iii) for every real t,s, R_t is an isometry, the group law holds, and t -> R_t z is continuous by dominated convergence for series
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:multiplier, bpW:w1:ext-series, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L250-L250 | R_t is a multiplier D_mu with ¦mu_j¦ = 1
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L252-L252 | dominated convergence for series (Tonelli/Fubini for series)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L250-L250 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a
REVIEWER: sol-delta-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:realflow
KIND: step
TITLE: Real flow
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L253-L257
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L253-L257
CONTRACT_ID: stepW:w1:realflow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:diag: a >= 0, p in R, r in R; lambda^r the multiplier w -> (lambda_j^r w_j); local data: (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:diag (for all a, p, r; t, s in R); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: coordinatewise rotation: q_j(t)^2 + p_j(t)^2 = q_j^2 + p_j^2, hence the norm identity and max(¦¦q(t)¦¦,¦¦p(t)¦¦)^2 <= ¦¦q¦¦^2 + ¦¦p¦¦^2 <= 2¦¦(q,p)¦¦_E^2; derivatives and group law by trigonometry; z_j(t) = e^{-i lambda_j t} z_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:z, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:z | blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L257-L257 | z_j = (q_j + i p_j)/sqrt 2
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L257-L257 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:linfty
KIND: definition
TITLE: Sup-weighted sequences
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:linfty@L263-L270
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:linfty
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: p in R; Pi subset R^2; L >= 0
SOURCE_QUANTIFIERS: p, Pi, L
SOURCE_CONCLUSION: defines l^p_infty (real sequences with ¦w¦_p = sup_j ¦w_j¦ j^p < infinity, realized as lp infinity by w -> (j^p w_j)) and L-Lipschitz maps Pi -> l^p_infty (max norm on R^2); P96-K's Lipschitz semi-norm is the least such L
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:tails
KIND: lemma
TITLE: Spectral asymptotics of the wave normal frequencies
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L273-L282
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L284-L289
CONTRACT_ID: bpW:w1:tails
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: b = (1/lambda_1, 1/lambda_2); Omega_j(xi) = lambda_j + (3/(2 pi lambda_j))<b,xi> (j >= 3, xi in R^2); bar Omega_j = j; tilde Omega_j = Omega_j - bar Omega_j
SOURCE_QUANTIFIERS: for all xi, zeta in R^2; i, j >= 3
SOURCE_CONCLUSION: ¦tilde Omega(xi)¦_1 <= m/2 + (3/(2pi))¦<b,xi>¦ and ¦tilde Omega(xi) - tilde Omega(zeta)¦_1 <= (3/(2pi))(1/lambda_1 + 1/lambda_2)¦xi - zeta¦; so P96-K Assumption B holds with d = 1, delta = -1, and p - bar p <= delta holds with equality for bar p = p + 1; ¦Omega_i(xi) - Omega_j(xi) - (i-j)¦ <= (m + (3/pi)¦<b,xi>¦)/min(i,j)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w1:linfty, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L275-L275 | Omega = lambda_N + B xi with the corrected B
EDGE: bpW:w1:linfty | blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L277-L277 | the norm ¦.¦_1 of l^1_infty and the Lipschitz condition
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L285-L285 | lambda_j - j = m/(lambda_j + j) in (0, m/(2j)]; lambda_j > j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L274-L274 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:twosided-transport
KIND: definition
TITLE: Two-sided transport
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-transport@L297-L303
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:twosided-transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a >= 0, s in R
SOURCE_QUANTIFIERS: a, s
SOURCE_CONCLUSION: defines omega^b_{a,s}(l) = <l>^s e^{a¦l¦} and the realization of l^{a,s}_b as lp (Int -> C) 2 via c -> (omega^b(l) c_l) (an isometry as in Lemma bpW:w1:space); (c*d)_l = sum_i c_i d_{l-i} when sum_i ¦c_i¦¦d_{l-i}¦ < infinity for all l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:twosided, bpW:w1:space
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:twosided | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-transport@L299-L299 | the space l^{a,s}_b and the convolution
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-transport@L300-L300 | the isometry argument
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:twosided
KIND: lemma
TITLE: Passage between one- and two-sided sequences
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L306-L322
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L324-L337
CONTRACT_ID: bpW:w1:twosided
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p in R
SOURCE_QUANTIFIERS: for all a, p; q; X; z, zbar
SOURCE_CONCLUSION: (i) (E^+- q)_l = (+-1)^{[l<0]} q_¦l¦/sqrt(lambda_¦l¦) (l != 0), 0 at l = 0, is linear l^{a,p}_C -> l^{a,p+1/2}_b with norm <= sqrt2 ¦¦q¦¦_{a,p}, also for the majorant ¦E^+ q¦; the even x_l = ¦q_¦l¦¦/sqrt(¦l¦) has ¦¦x¦¦_{a,p+1/2}^2 = 2¦¦q¦¦_{a,p}^2; (ii) for X in l^{a,p+1/2}_b, (X_l/sqrt(lambda_l))_{l>=1} lies in l^{a,p+1}_C with norm <= (sum_{l>=1} l^{2p+1} e^{2al} ¦X_l¦^2)^{1/2} <= ¦¦X¦¦_{a,p+1/2}, and <= ¦¦X¦¦/sqrt2 if ¦X¦ is even; (iii) J(z,zbar) (z on j >= 1, zbar on -j, 0 at 0) is a linear isometry from l^{a,p}_C x l^{a,p}_C with (¦¦z¦¦^2 + ¦¦zbar¦¦^2)^{1/2} onto {w in l^{a,p}_b : w_0 = 0}, ¦¦J(z,zbar)¦¦ <= sqrt2 max(¦¦z¦¦,¦¦zbar¦¦)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:twosided-transport, bpW:w0:basis#lam, stepW:w1:ext, stepW:w1:restr, stepW:w1:pair
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:twosided-transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L311-L311 | the two-sided weights
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L309-L309 | the factor 1/sqrt(lambda_¦l¦)
EDGE: stepW:w1:ext | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L325-L325 | proof step
EDGE: stepW:w1:restr | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L330-L330 | proof step
EDGE: stepW:w1:pair | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L335-L335 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:ext
KIND: step
TITLE: Extensions
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L325-L329
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L325-L329
CONTRACT_ID: stepW:w1:ext
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:twosided: a >= 0, p in R; local data: q in l^{a,p}_C
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:twosided (for all a, p; q; X; z, zbar); within the step: q; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦E^+- q¦¦^2 = 2 sum j^{2p+1} e^{2aj} ¦q_j¦^2/lambda_j <= 2¦¦q¦¦^2; the majorant has the same norm; with sqrt(¦l¦) the factor j/lambda_j becomes 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L327-L329 | j/lambda_j < 1
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L326-L326 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a+claude-suborch-W-r2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Writer revision r2 (wave-1 corpus update, inp 99afc128 blueprint cleanup): the step text now says the computation is self-contained (every a >= 0, p in R) and only analogous to the W0 step; consistent with the existing record, which has no edge to the W0 step.

NODE: stepW:w1:restr
KIND: step
TITLE: Restriction
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L330-L334
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L330-L334
CONTRACT_ID: stepW:w1:restr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:twosided: a >= 0, p in R; local data: X in l^{a,p+1/2}_b
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:twosided (for all a, p; q; X; z, zbar); within the step: X; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum_{l>=1} l^{2p+2} e^{2al} ¦X_l¦^2/lambda_l <= sum_{l>=1} l^{2p+1} e^{2al} ¦X_l¦^2; for even ¦X¦ at most half the full sum
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L331-L331 | l/lambda_l < 1
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L331-L331 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a+claude-suborch-W-r2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Writer revision r2 (wave-1 corpus update, inp 99afc128 blueprint cleanup): the step text now says the computation is self-contained (every a >= 0, p in R) and only analogous to the W0 step; consistent with the existing record, which has no edge to the W0 step.

NODE: stepW:w1:pair
KIND: step
TITLE: Pairing
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:pair@L335-L336
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:pair@L335-L336
CONTRACT_ID: stepW:w1:pair
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:twosided: a >= 0, p in R; local data: z, zbar in l^{a,p}_C
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:twosided (for all a, p; q; X; z, zbar); within the step: z, zbar; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦J(z,zbar)¦¦^2 = sum_{j>=1} omega_{a,p}(j)^2 (¦z_j¦^2 + ¦zbar_j¦^2) since <+-j> = j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:twosided-transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:twosided-transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:pair@L336-L336 | the two-sided weight <l>
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:young
KIND: lemma
TITLE: Young and $\ell^1$ control
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L341-L351
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L353-L369
CONTRACT_ID: bpW:w1:young
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (i) X in l^2(Z), Y in l^1(Z); (ii) s > 1/2, a >= 0, Y in l^{a,s}_b; (iii) nonnegative X, Y, Z in l^{0,s}_b with s > 1/2; complex c, d
SOURCE_QUANTIFIERS: for all such sequences
SOURCE_CONCLUSION: (i) each sum_i ¦X_i¦¦Y_{l-i}¦ converges and ¦¦X*Y¦¦_{l^2} <= ¦¦X¦¦_{l^2} ¦¦Y¦¦_{l^1}; (ii) sum_l <l>^{-2s} = 1 + 2 zeta(2s) < infinity and ¦¦Y¦¦_{l^1} <= (1+2zeta(2s))^{1/2} ¦¦Y¦¦_{0,s} <= (1+2zeta(2s))^{1/2} ¦¦Y¦¦_{a,s}; (iii) convolution of nonnegative sequences is commutative, associative and monotone; ¦c*d¦ <= ¦c¦*¦d¦ pointwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:twosided-transport, stepW:w1:cs, stepW:w1:youngsum, stepW:w1:l1, stepW:w1:rules
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:twosided-transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L345-L345 | the norms ¦¦.¦¦_{a,s} and the convolution
EDGE: stepW:w1:cs | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L354-L354 | proof step
EDGE: stepW:w1:youngsum | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L358-L358 | proof step
EDGE: stepW:w1:l1 | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L361-L361 | proof step
EDGE: stepW:w1:rules | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L365-L365 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:cs
KIND: step
TITLE: Weighted Cauchy--Schwarz
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cs@L354-L357
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cs@L354-L357
CONTRACT_ID: stepW:w1:cs
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:young: (i) X in l^2(Z), Y in l^1(Z); (ii) s > 1/2, a >= 0, Y in l^{a,s}_b; (iii) nonnegative X, Y, Z in l^{0,s}_b with s > 1/2; complex c, d; local data: X in l^2, Y in l^1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:young (for all such sequences); within the step: l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (sum_i ¦X_i¦¦Y_{l-i}¦)^2 <= ¦¦Y¦¦_1 sum_i ¦X_i¦^2 ¦Y_{l-i}¦, finite
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:youngsum
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L358-L360
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L358-L360
CONTRACT_ID: stepW:w1:youngsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:young: (i) X in l^2(Z), Y in l^1(Z); (ii) s > 1/2, a >= 0, Y in l^{a,s}_b; (iii) nonnegative X, Y, Z in l^{0,s}_b with s > 1/2; complex c, d
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:young (for all such sequences); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum_l ¦(X*Y)_l¦^2 <= ¦¦Y¦¦_1^2 ¦¦X¦¦_2^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:cs, bpW:w1:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:cs | blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L360-L360 | sums the pointwise bound over l
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L359-L359 | exchange of the nonnegative double sum (Tonelli)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:l1
KIND: step
TITLE: $\ell^1$ control
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:l1@L361-L364
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:l1@L361-L364
CONTRACT_ID: stepW:w1:l1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:young: (i) X in l^2(Z), Y in l^1(Z); (ii) s > 1/2, a >= 0, Y in l^{a,s}_b; (iii) nonnegative X, Y, Z in l^{0,s}_b with s > 1/2; complex c, d
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:young (for all such sequences); within the step: Y; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum_l <l>^{-2s} = 1 + 2 sum_{l>=1} l^{-2s} < infinity and ¦¦Y¦¦_1 <= (1+2zeta(2s))^{1/2} ¦¦Y¦¦_{0,s} <= (1+2zeta(2s))^{1/2} ¦¦Y¦¦_{a,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:l1@L362-L362 | sum k^{-sigma} < infinity for sigma = 2s > 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:rules
KIND: step
TITLE: Algebraic rules
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L365-L368
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L365-L368
CONTRACT_ID: stepW:w1:rules
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:young: (i) X in l^2(Z), Y in l^1(Z); (ii) s > 1/2, a >= 0, Y in l^{a,s}_b; (iii) nonnegative X, Y, Z in l^{0,s}_b with s > 1/2; complex c, d
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:young (for all such sequences); within the step: X, Y, Z; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: absolute convergence of the double series allows rearrangement (associativity); commutativity by i -> l - i; monotonicity and ¦c*d¦ <= ¦c¦*¦d¦ termwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:l1, bpW:w1:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:l1 | blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L366-L366 | (ii) puts the sequences in l^1 cap l^2
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L367-L367 | Fubini for absolutely summable double series
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a
REVIEWER: sol-delta-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:algebra
KIND: lemma
TITLE: Convolution algebra
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L372-L375
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L377-L381
CONTRACT_ID: bpW:w1:algebra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, s >= 1, c, d (, e) in l^{a,s}_b
SOURCE_QUANTIFIERS: for all such a, s, c, d, e
SOURCE_CONCLUSION: ¦¦c*d¦¦_{a,s} <= K_s ¦¦c¦¦ ¦¦d¦¦ with K_s = 2^s(1+2zeta(2s))^{1/2}, and ¦¦c*d*e¦¦_{a,s} <= K_s^2 ¦¦c¦¦ ¦¦d¦¦ ¦¦e¦¦
CONSTANT_SCOPE: K_s depends only on s
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:algebra, bpW:w1:young
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:algebra | blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L378-L378 | the two-factor bound is Lemma bpW:w0n:algebra
EDGE: bpW:w1:young | blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L379-L379 | (iii): associativity for the three-factor form
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:selection
KIND: lemma
TITLE: Selection-rule trilinear maps
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L398-L412
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L414-L439
CONTRACT_ID: bpW:w1:selection
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b
SOURCE_QUANTIFIERS: for all such a, p, M, c and arguments
SOURCE_CONCLUSION: (a) T_c(q,q',q'')_l = sum c_ijkl q_i q'_j q''_k converge absolutely and ¦¦T_c¦¦_{a,p+1} <= 2 M K_s^2 prod ¦¦q¦¦_{a,p}; (b) T_c(w,w',w'')_l (l != 0) converge absolutely, T_c(.)_0 = 0, ¦¦T_c¦¦_{a,p+1} <= 64 M K_s^2 prod ¦¦w¦¦_{a,p}; T_c is trilinear, symmetric if c is symmetric in its first three indices
CONSTANT_SCOPE: the bounds depend only on M and s (through K_s)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:maj1, stepW:w1:sel1, stepW:w1:smooth1, stepW:w1:maj2, stepW:w1:sel2, stepW:w1:smooth2
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:maj1 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L415-L415 | proof step
EDGE: stepW:w1:sel1 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L418-L418 | proof step
EDGE: stepW:w1:smooth1 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L424-L424 | proof step
EDGE: stepW:w1:maj2 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L427-L427 | proof step
EDGE: stepW:w1:sel2 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L431-L431 | proof step
EDGE: stepW:w1:smooth2 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L435-L435 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:maj1
KIND: step
TITLE: One-sided majorant
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj1@L415-L417
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj1@L415-L417
CONTRACT_ID: stepW:w1:maj1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:selection: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b; local data: x_i = ¦q_¦i¦¦/sqrt(¦i¦), x_0 = 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:selection (for all such a, p, M, c and arguments); within the step: q, q', q''; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: x is even with ¦¦x¦¦_{a,s} = sqrt2 ¦¦q¦¦_{a,p}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:twosided
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:twosided | blueprint-W/parts/w1-sequences.tex#stepW:w1:maj1@L417-L417 | (i): the even sequence x
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:sel1
KIND: step
TITLE: One-sided selection
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L418-L423
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L418-L423
CONTRACT_ID: stepW:w1:sel1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:selection: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:selection (for all such a, p, M, c and arguments); within the step: l >= 1; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum_{i,j,k} ¦c_ijkl q_i q'_j q''_k¦ <= M l^{-1/2} X_l with X = x*x'*x'', finite and even
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:maj1, stepW:w0n:selection, bpW:w1:young, bpW:w1:algebra
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:maj1 | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L420-L420 | the even majorants
EDGE: stepW:w0n:selection | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L422-L422 | the injectivity argument of the W0 selection step
EDGE: bpW:w1:young | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L422-L422 | X is finite (Young, l^1 control)
EDGE: bpW:w1:algebra | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L423-L423 | X lies in l^{a,s}_b
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:smooth1
KIND: step
TITLE: One-sided smoothing
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L424-L426
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L424-L426
CONTRACT_ID: stepW:w1:smooth1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:selection: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:selection (for all such a, p, M, c and arguments); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦T_c¦¦_{a,p+1}^2 <= (M^2/2) ¦¦X¦¦_{a,s}^2 and ¦¦X¦¦_{a,s} <= K_s^2 ¦¦x¦¦ ¦¦x'¦¦ ¦¦x''¦¦ = 2^{3/2} K_s^2 prod ¦¦q¦¦; hence ¦¦T_c¦¦ <= 2 M K_s^2 prod ¦¦q¦¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:sel1, bpW:w1:algebra, stepW:w1:maj1
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:sel1 | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L425-L425 | the pointwise bound by M l^{-1/2} X_l
EDGE: bpW:w1:algebra | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L426-L426 | three-factor algebra bound
EDGE: stepW:w1:maj1 | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L426-L426 | ¦¦x¦¦ = sqrt2 ¦¦q¦¦
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:maj2
KIND: step
TITLE: Two-sided majorant
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj2@L427-L430
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj2@L427-L430
CONTRACT_ID: stepW:w1:maj2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:selection: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b; local data: tilde x_i = (¦w_i¦ + ¦w_{-i}¦)/sqrt(¦i¦), tilde x_0 = 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:selection (for all such a, p, M, c and arguments); within the step: w, w', w''; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: tilde x is even with ¦¦tilde x¦¦_{a,s}^2 <= 4 ¦¦w¦¦_{a,p}^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:twosided-transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:twosided-transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:maj2@L429-L429 | the two-sided weights
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:sel2
KIND: step
TITLE: Two-sided selection
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel2@L431-L434
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel2@L431-L434
CONTRACT_ID: stepW:w1:sel2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:selection: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:selection (for all such a, p, M, c and arguments); within the step: l != 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: each of the eight eps-terms is at most (tilde x*tilde x'*tilde x'')_l =: tilde X_l, so ¦T_c(w,w',w'')_l¦ <= 8 M ¦l¦^{-1/2} tilde X_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:maj2
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:maj2 | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel2@L433-L433 | ¦w_i¦/sqrt(¦i¦) <= tilde x_{i'}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:smooth2
KIND: step
TITLE: Two-sided smoothing
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L435-L438
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L435-L438
CONTRACT_ID: stepW:w1:smooth2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:selection: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:selection (for all such a, p, M, c and arguments); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦T_c¦¦_{a,p+1}^2 <= 64 M^2 ¦¦tilde X¦¦_{a,s}^2, ¦¦tilde X¦¦ <= 8 K_s^2 prod ¦¦w¦¦, so ¦¦T_c¦¦ <= 64 M K_s^2 prod ¦¦w¦¦; trilinearity and symmetry termwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:sel2, bpW:w1:algebra, stepW:w1:maj2
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:sel2 | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L436-L436 | the pointwise bound
EDGE: bpW:w1:algebra | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L437-L437 | three-factor algebra bound
EDGE: stepW:w1:maj2 | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L437-L437 | ¦¦tilde x¦¦ <= 2 ¦¦w¦¦
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:trilinear
KIND: theorem
TITLE: The cubic map as a continuous trilinear map
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L443-L462
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L464-L484
CONTRACT_ID: bpW:w1:trilinear
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2, C_* = K_{p+1/2}^2/pi, K in {R, C}; for (iii) a >= a' >= 0, p >= p' >= 1/2; for (iv) y in l^2_R, l >= 1 (and a > 0 for the general case)
SOURCE_QUANTIFIERS: for all such a, p, K
SOURCE_CONCLUSION: (i) there is a unique continuous symmetric K-trilinear map T^{a,p}_K : (l^2_K)^3 -> l^2_K with kappa_{a,p+1} T^{a,p}_K(y,y',y'') = T(kappa y, kappa y', kappa y'') (T of Theorem bpW:w0n:cubic-bound) and ¦¦T^{a,p}_K¦¦ <= C_*; (ii) T_C(iota y, ...) = iota T_R(y, ...) and conj(T_C(z,z',z'')) = T_C(conj z, ...); (iii) T^{a',p'}(hat iota y, ...) = hat iota' T^{a,p}(y, ...); (iv) cubicGrad m hm y l = T^{1,1}_R(y,y,y)_l/omega_{1,2}(l), i.e. G_q(kappa_{1,1} y) = kappa_{1,2} T^{1,1}_R(y,y,y); for a > 0, p >= 1/2 likewise G_q(kappa_{a,p} y) = kappa_{a,p+1} T^{a,p}_R(y,y,y)
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, bpW:w1:complexification, bpW:w0:Gq#cubicGrad, stepW:w1:tricoord, stepW:w1:tricont, stepW:w1:trireal, stepW:w1:trifrozen, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L449-L449 | kappa, omega
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L451-L451 | iota and conjugation
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L458-L458 | the frozen cubicGrad in (iv)
EDGE: stepW:w1:tricoord | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L465-L465 | proof step
EDGE: stepW:w1:tricont | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L471-L471 | proof step
EDGE: stepW:w1:trireal | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L475-L475 | proof step
EDGE: stepW:w1:trifrozen | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L479-L479 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L467-L467 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L480-L480 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:tricoord
KIND: step
TITLE: Coordinates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L465-L470
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L465-L470
CONTRACT_ID: stepW:w1:tricoord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:trilinear: a >= 0, p >= 1/2, C_* = K_{p+1/2}^2/pi, K in {R, C}; for (iii) a >= a' >= 0, p >= p' >= 1/2; for (iv) y in l^2_R, l >= 1 (and a > 0 for the general case); local data: y, y', y'' in l^2_K; q = kappa_{a,p} y etc.
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:trilinear (for all such a, p, K); within the step: y, y', y''; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: each T(q,q',q'')_l is an absolutely convergent tsum over N_+^3, T(q,q',q'') in l^{a,p+1}_K with norm <= C_* prod ¦¦y¦¦; define T(y,y',y'') = tau_{a,p+1} T(q,q',q'')
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, bpW:w0:basis#lam
ROUTES: stepW:w1:tricoord#via-cubic-bound, stepW:w1:tricoord#via-selection
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L470-L470 | tau_{a,p+1} and the weighted coordinates
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L467-L467 | lambda occurs directly here (frozen lam)
EDGE: stepW:w1:tricoord#via-cubic-bound | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L466-L466 | first derivation: Theorem bpW:w0n:cubic-bound
EDGE: stepW:w1:tricoord#via-selection | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L467-L467 | equivalent derivation: Lemma bpW:w1:selection(a)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:tricont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L471-L474
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L471-L474
CONTRACT_ID: stepW:w1:tricont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:trilinear: a >= 0, p >= 1/2, C_* = K_{p+1/2}^2/pi, K in {R, C}; for (iii) a >= a' >= 0, p >= p' >= 1/2; for (iv) y in l^2_R, l >= 1 (and a > 0 for the general case)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:trilinear (for all such a, p, K); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: trilinear and symmetric termwise; continuous with norm <= C_* (MultilinearMap.mkContinuous); unique since kappa_{a,p+1} is injective
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:tricoord, bpW:w0n:quartic-coeff, bpW:w1:space
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:tricoord | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L473-L473 | the bound C_* prod ¦¦y¦¦
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L472-L472 | symmetry of g
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L474-L474 | kappa is injective ((i))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:trireal
KIND: step
TITLE: Real structure and compatibility
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L475-L478
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L475-L478
CONTRACT_ID: stepW:w1:trireal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:trilinear: a >= 0, p >= 1/2, C_* = K_{p+1/2}^2/pi, K in {R, C}; for (iii) a >= a' >= 0, p >= p' >= 1/2; for (iv) y in l^2_R, l >= 1 (and a > 0 for the general case)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:trilinear (for all such a, p, K); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) real coefficients commute with iota and conjugation; (iii) both sides have coefficients T(q,q',q'')
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:complexification, bpW:w1:embed, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L477-L477 | iota and conjugation
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L478-L478 | (iii): inclusions do not change coefficients
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L476-L476 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:trifrozen
KIND: step
TITLE: Frozen identification
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L479-L483
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L479-L483
CONTRACT_ID: stepW:w1:trifrozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:trilinear: a >= 0, p >= 1/2, C_* = K_{p+1/2}^2/pi, K in {R, C}; for (iii) a >= a' >= 0, p >= p' >= 1/2; for (iv) y in l^2_R, l >= 1 (and a > 0 for the general case); local data: y in l^2_R, a = p = 1 (or a > 0)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:trilinear (for all such a, p, K); within the step: y, l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: reconU m hm y = U_m(kappa_{1,1} y) (absolutely convergent tsum), the interval integral is that of Definition bpW:w0:Gq, so cubicGrad m hm y l = G_q(kappa_{1,1} y)_l = T(q,q,q)_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:reconstruction#reconU, bpW:w0n:recon-bounded, bpW:w0:Gq#cubicGrad, bpW:w0n:gradient, bpW:w0:ellap#coeff, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L480-L480 | unfolds the frozen reconU
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L481-L481 | the tsum converges absolutely
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L482-L482 | unfolds the frozen cubicGrad
EDGE: bpW:w0n:gradient | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L483-L483 | G_q(q)_l = T(q,q,q)_l for a > 0
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L480-L480 | kappa_{1,1} = coeff
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L482-L482 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:cubic-analytic
KIND: corollary
TITLE: Analyticity and Lipschitz bounds of the cubic gradient
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L487-L501
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L503-L517
CONTRACT_ID: bpW:w1:cubic-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y)
SOURCE_QUANTIFIERS: for all y, y', h, k
SOURCE_CONCLUSION: (i) N is K-analytic on l^2_K, ¦¦N(y)¦¦ <= C_* ¦¦y¦¦^3; (ii) DN(y)h = 3T(y,y,h), D^2N(y)(h,k) = 6T(y,h,k), D^3N = 6T, ¦¦DN(y)¦¦ <= 3C_*¦¦y¦¦^2, ¦¦D^2N(y)¦¦ <= 6C_*¦¦y¦¦; (iii) ¦¦N(y) - N(y')¦¦ <= 3C_* ¦¦y-y'¦¦ max(¦¦y¦¦,¦¦y'¦¦)^2; (iv) G^w(y)_l = omega_{1,2}(l) cubicGrad m hm y l is N for (a,p) = (1,1), K = R, real analytic with ¦¦G^w(y)¦¦ <= C_m ¦¦y¦¦^3, C_m = 8(1+2zeta(3))/pi; G_q(kappa_{1,1} y) has weighted coordinates G^w(y) at (1,2), (l^{-1} G^w(y)_l) at (1,1), (l^{-2} G^w(y)_l) at (1,0)
CONSTANT_SCOPE: C_* depends only on p; C_m independent of m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:trilinear, bpW:w0:Gq#cubicGrad, stepW:w1:can, stepW:w1:cder, stepW:w1:clip, stepW:w1:cfrozen
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L488-L488 | T and C_*
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L496-L496 | the frozen cubicGrad in (iv)
EDGE: stepW:w1:can | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L504-L504 | proof step
EDGE: stepW:w1:cder | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L506-L506 | proof step
EDGE: stepW:w1:clip | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L511-L511 | proof step
EDGE: stepW:w1:cfrozen | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L514-L514 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:can
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:can@L504-L505
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:can@L504-L505
CONTRACT_ID: stepW:w1:can
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cubic-analytic: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cubic-analytic (for all y, y', h, k); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: N = T o Delta, Delta(y) = (y,y,y) continuous linear, is analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-analytic, bpW:w1:trilinear
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:can@L505-L505 | continuous multilinear maps and compositions are analytic
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:can@L505-L505 | continuity of the named trilinear map is supplied by the theorem
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a
REVIEWER: sol-delta-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:cder
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cder@L506-L510
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cder@L506-L510
CONTRACT_ID: stepW:w1:cder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cubic-analytic: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cubic-analytic (for all y, y', h, k); within the step: y, h; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: DN(y)h = 3T(y,y,h), the higher derivatives likewise, with the stated bounds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:trilinear
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:cder@L508-L508 | symmetry and the bound C_* ((i))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a
REVIEWER: sol-delta-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:clip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:clip@L511-L513
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:clip@L511-L513
CONTRACT_ID: stepW:w1:clip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cubic-analytic: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cubic-analytic (for all y, y', h, k); within the step: y, y'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: N(y) - N(y') = T(y-y',y,y) + T(y',y-y',y) + T(y',y',y-y'), so the Lipschitz bound 3C_* ¦¦y-y'¦¦ max^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:trilinear
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:clip@L513-L513 | the bound C_*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a
REVIEWER: sol-delta-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:cfrozen
KIND: step
TITLE: Frozen form
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L514-L516
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L514-L516
CONTRACT_ID: stepW:w1:cfrozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cubic-analytic: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y); local data: (a,p) = (1,1), K = R
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cubic-analytic (for all y, y', h, k); within the step: y, l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) from Theorem bpW:w1:trilinear(iv), omega_{1,1}/omega_{1,2} = l^{-1}, omega_{1,0}/omega_{1,2} = l^{-2}, and C_* = K_{3/2}^2/pi = C_m
CONSTANT_SCOPE: C_m independent of m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:trilinear, bpW:w0n:cubic-bound, bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L515-L515 | (iv) frozen identification
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L516-L516 | C_m = K_{3/2}^2/pi
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L515-L515 | the weight ratios
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:gradient-identity
KIND: proposition
TITLE: Gradient identity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L521-L534
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L536-L552
CONTRACT_ID: bpW:w1:gradient-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a > 0, p >= 1/2; G(q) = (1/4) int_0^pi U_m(q)^4 for q in l^{a,p}; <u,v>_0 = sum_j u_j v_j (unweighted), absolutely convergent for u in l^{a,p+1}, v in l^{a,p}
SOURCE_QUANTIFIERS: for all a > 0, p >= 1/2; q, h in l^{a,p}; y, h in l^2_R for (iii)
SOURCE_CONCLUSION: (i) G(q) = (1/4)<G_q(q),q>_0 = (1/4) Q(q,q,q,q), Q(q_1,..,q_4) = <T(q_1,q_2,q_3),q_4>_0 symmetric continuous 4-linear with ¦Q¦ <= C_* prod ¦¦q_i¦¦; (ii) G is real analytic on l^{a,p} and DG(q)h = <G_q(q),h>_0; (iii) G_q(q) is not the Riesz gradient of G for l^{a,p} (that is (omega^{-2} G_q(q)_j)); in frozen coordinates, G^w(y) = G(kappa_{1,1} y), DG^w(y)h = sum_j cubicGrad m hm y j . coeff h j and nabla^{l^2} G^w(y) = (G^w(y)_j/(omega_{1,1}(j) omega_{1,2}(j)))_j
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:H, bpW:w0n:cubic-bound, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff, stepW:w1:quartic, stepW:w1:gradder, stepW:w1:gradw, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:H | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L522-L522 | G(q) = (1/4) int U_m(q)^4
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L527-L527 | the trilinear map T
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L531-L531 | frozen cubicGrad in (iii)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L531-L531 | frozen coeff in (iii)
EDGE: stepW:w1:quartic | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L537-L537 | proof step
EDGE: stepW:w1:gradder | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L543-L543 | proof step
EDGE: stepW:w1:gradw | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L547-L547 | proof step
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L522-L522 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:quartic
KIND: step
TITLE: Quartic form
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L537-L542
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L537-L542
CONTRACT_ID: stepW:w1:quartic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:gradient-identity: a > 0, p >= 1/2; G(q) = (1/4) int_0^pi U_m(q)^4 for q in l^{a,p}; <u,v>_0 = sum_j u_j v_j (unweighted), absolutely convergent for u in l^{a,p+1}, v in l^{a,p}; local data: q in l^{a,p}, a > 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:gradient-identity (for all a > 0, p >= 1/2; q, h in l^{a,p}; y, h in l^2_R for (iii)); within the step: q_1, ..., q_4; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: G(q) = (1/4) sum_l q_l T(q,q,q)_l; Q is well defined, symmetric, and ¦Q¦ <= C_* prod ¦¦q_i¦¦
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient, bpW:w0n:quartic-coeff, bpW:w1:embed, bpW:w0n:cubic-bound
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:gradient | blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L538-L538 | G as an absolutely convergent quartic sum
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L540-L540 | symmetry of g
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L541-L541 | ¦¦u¦¦_{0,0} <= ¦¦u¦¦_{a,p+1}, ¦¦v¦¦_{0,0} <= ¦¦v¦¦_{a,p}
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L542-L542 | the bound on T
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:gradder
KIND: step
TITLE: Derivative
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L543-L546
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L543-L546
CONTRACT_ID: stepW:w1:gradder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:gradient-identity: a > 0, p >= 1/2; G(q) = (1/4) int_0^pi U_m(q)^4 for q in l^{a,p}; <u,v>_0 = sum_j u_j v_j (unweighted), absolutely convergent for u in l^{a,p+1}, v in l^{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:gradient-identity (for all a > 0, p >= 1/2; q, h in l^{a,p}; y, h in l^2_R for (iii)); within the step: q, h; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: G = (1/4) Q o (q -> (q,q,q,q)) is analytic and DG(q)h = Q(q,q,q,h) = <T(q,q,q),h>_0 = <G_q(q),h>_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:quartic, bpW:w1:ext-analytic, bpW:w1:trilinear, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:quartic | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L544-L544 | the quartic form Q
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L544-L544 | continuous multilinear maps are analytic
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L546-L546 | (iv): T(q,q,q) = G_q(q)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L545-L545 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:gradw
KIND: step
TITLE: Weighted coordinates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L547-L551
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L547-L551
CONTRACT_ID: stepW:w1:gradw
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:gradient-identity: a > 0, p >= 1/2; G(q) = (1/4) int_0^pi U_m(q)^4 for q in l^{a,p}; <u,v>_0 = sum_j u_j v_j (unweighted), absolutely convergent for u in l^{a,p+1}, v in l^{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:gradient-identity (for all a > 0, p >= 1/2; q, h in l^{a,p}; y, h in l^2_R for (iii)); within the step: y, h; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the Riesz gradient is (omega^{-2} G_q(q)_j); in frozen coordinates DG^w(y)h and nabla^{l^2} G^w(y) as stated
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:gradder, bpW:w1:cubic-analytic, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:gradder | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L548-L548 | DG(q)h = <G_q(q),h>_0
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L550-L550 | (iv): G^w and the weighted coordinates of G_q(kappa y)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L548-L548 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:hamfield
KIND: proposition
TITLE: The Hamiltonian field
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L555-L575
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L577-L598
CONTRACT_ID: bpW:w1:hamfield
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a > 0, p >= 1/2
SOURCE_QUANTIFIERS: for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j
SOURCE_CONCLUSION: (i) X_Lambda(q,p) = (lambda p, -lambda q) is bounded E_{a,p} -> E_{a,p-1} with norm <= sqrt(1+m), not bounded E_{a,p} -> E_{a,p}; (ii) X_G(q,p) = (0, -G_q(q)) is real analytic E_{a,p} -> E_{a,p+1}, ¦¦X_G¦¦ <= C_* ¦¦q¦¦^3, with the bounds of Corollary bpW:w1:cubic-analytic; its complex extension is C-analytic E^C_{a,p} -> E^C_{a,p+1}; (iii) X_H = X_Lambda + X_G is real analytic E_{a,p} -> E_{a,p-1}; (iv) H = Lambda + G is real analytic on E_{a,p}, DH(q,p)(0,e_j) = lambda_j p_j, DH(q,p)(e_j,0) = lambda_j q_j + G_q(q)_j, i.e. X_H = (d_p H, -d_q H), the system (bpW:w0:coeffsys); (v) for a = p = 1, with D = D_mu, mu_j = lambda_j/j, S = D_{(1/j)}, X^w(y,y') = (D y', -D y - S^2 G^w(y)) on WaveSpace represents X_H : E_{1,1} -> E_{1,0}, is real analytic on WaveSpace, and has j-th coordinates omega_{1,0}(j)(lambda_j coeff y' j, -lambda_j coeff y j - cubicGrad m hm y j)
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:H, bpW:w0:eqmotion, bpW:w1:cubic-analytic, bpW:w0:ellap#WaveSpace, bpW:w0:ellap#coeff, bpW:w0:Gq#cubicGrad, stepW:w1:hlin, stepW:w1:hnonlin, stepW:w1:hsum, stepW:w1:hham, stepW:w1:hfrozen, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:H | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L565-L565 | H = Lambda + G
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L567-L567 | the system (bpW:w0:coeffsys)
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L562-L562 | the bounds of the cubic gradient
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L569-L569 | X^w : WaveSpace -> WaveSpace
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L572-L572 | the coordinates in terms of coeff
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L572-L572 | the coordinates in terms of cubicGrad
EDGE: stepW:w1:hlin | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L578-L578 | proof step
EDGE: stepW:w1:hnonlin | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L580-L580 | proof step
EDGE: stepW:w1:hsum | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L583-L583 | proof step
EDGE: stepW:w1:hham | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L586-L586 | proof step
EDGE: stepW:w1:hfrozen | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L593-L593 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L558-L558 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hlin
KIND: step
TITLE: Linear part
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hlin@L578-L579
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hlin@L578-L579
CONTRACT_ID: stepW:w1:hlin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:hamfield: a > 0, p >= 1/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:hamfield (for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i) from Lemma bpW:w1:diag(i)-(ii) with r = 1 componentwise; the max norm is preserved under componentwise bounds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:diag
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:diag | blueprint-W/parts/w1-sequences.tex#stepW:w1:hlin@L579-L579 | (i)-(ii) with r = 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hnonlin
KIND: step
TITLE: Nonlinear part
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L580-L582
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L580-L582
CONTRACT_ID: stepW:w1:hnonlin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:hamfield: a > 0, p >= 1/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:hamfield (for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) from Corollary bpW:w1:cubic-analytic and Theorem bpW:w1:trilinear(iv) in the second component, composed with the projection (q,p) -> q; complex version from (ii) of the theorem
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cubic-analytic, bpW:w1:trilinear
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L581-L581 | analyticity and bounds of N
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L581-L581 | (iv) identification with G_q and (ii) complex version
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hsum
KIND: step
TITLE: Sum
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L583-L585
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L583-L585
CONTRACT_ID: stepW:w1:hsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:hamfield: a > 0, p >= 1/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:hamfield (for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: X_G maps into E_{a,p+1} subset E_{a,p-1}; a bounded linear plus an analytic map is analytic, giving (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:embed, stepW:w1:hlin, stepW:w1:hnonlin, bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L584-L584 | E_{a,p+1} subset E_{a,p-1}
EDGE: stepW:w1:hlin | blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L585-L585 | X_Lambda bounded linear
EDGE: stepW:w1:hnonlin | blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L585-L585 | X_G analytic
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L585-L585 | sums of analytic maps
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a
REVIEWER: sol-delta-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hham
KIND: step
TITLE: Hamiltonian
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L586-L592
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L586-L592
CONTRACT_ID: stepW:w1:hham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:hamfield: a > 0, p >= 1/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:hamfield (for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j); within the step: (q,p), j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Lambda is the diagonal of beta(q,q') = sum lambda_j q_j q'_j with ¦beta¦ <= sqrt(1+m) ¦¦q¦¦ ¦¦q'¦¦, a bounded quadratic form on E_{a,p}; DLambda(q,p)(h,k) = <lambda q,h>_0 + <lambda p,k>_0; with Proposition bpW:w1:gradient-identity(ii), evaluation at (e_j,0), (0,e_j) gives (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w1:embed, bpW:w1:gradient-identity, bpW:w0:basis#lam, bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L588-L588 | lambda_j <= sqrt(1+m) j
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L589-L589 | ¦¦q¦¦_{0,1/2} <= ¦¦q¦¦_{a,p} for p >= 1/2
EDGE: bpW:w1:gradient-identity | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L591-L591 | (ii): DG(q)h = <G_q(q),h>_0
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L587-L587 | lambda occurs directly here (frozen lam)
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L590-L590 | analyticity of the bounded quadratic form uses the continuous multilinear external
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a
REVIEWER: sol-delta-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hfrozen
KIND: step
TITLE: Frozen form
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L593-L597
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L593-L597
CONTRACT_ID: stepW:w1:hfrozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:hamfield: a > 0, p >= 1/2; local data: a = p = 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:hamfield (for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j); within the step: y, y', j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the coordinates of X_H(kappa y, kappa y') times omega_{1,0}(j) = e^j are (lambda_j/j) y'_j and -(lambda_j/j) y_j - j^{-2} G^w(y)_j; D, S bounded, so X^w is a polynomial map on WaveSpace, analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cubic-analytic, bpW:w1:multiplier, bpW:w0:basis#lambda-facts, bpW:w1:ext-analytic, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L595-L595 | (iv): e^j cubicGrad_j = j^{-2} G^w(y)_j
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L596-L596 | D and S are bounded
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L596-L596 | lambda_j/j <= sqrt(1+m)
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L597-L597 | polynomial maps are analytic
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L594-L594 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L595-L595 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L597-L597 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:tricoord#via-cubic-bound
KIND: route
TITLE: Coordinates of the trilinear map via Theorem bpW:w0n:cubic-bound
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L466-L470
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L466-L466
CONTRACT_ID: stepW:w1:tricoord#via-cubic-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as in Step stepW:w1:tricoord
SOURCE_QUANTIFIERS: y, y', y''
SOURCE_CONCLUSION: the conclusion of Step stepW:w1:tricoord
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:cubic-bound
ROUTES: -
ROUTE_FOR: stepW:w1:tricoord
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L466-L466 | absolute convergence and the bound C_*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:tricoord#via-selection
KIND: route
TITLE: Coordinates of the trilinear map via Lemma bpW:w1:selection(a)
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L466-L470
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L467-L468
CONTRACT_ID: stepW:w1:tricoord#via-selection
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as in Step stepW:w1:tricoord
SOURCE_QUANTIFIERS: y, y', y''
SOURCE_CONCLUSION: the conclusion of Step stepW:w1:tricoord
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:selection, bpW:w0n:quartic-coeff, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: stepW:w1:tricoord
EDGE: bpW:w1:selection | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L467-L467 | (a) with M = 1/(2pi)
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L468-L468 | the bound after (bpW:w0n:g-signed) gives the hypothesis on c
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L468-L468 | lambda >= j gives the (ijkl)^{-1/2} decay
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L467-L467 | the coefficient formula explicitly uses lambda
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w1a
REVIEWER: sol-delta-W-w1a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: "equivalently Lemma bpW:w1:selection(a) with c_ijkl = g_ijkl (lambda lambda lambda lambda)^{-1/2}, M = 1/(2pi)": the text offers it as a sufficient alternative to cubic-bound.

NODE: bpW:w1:ext-rect
KIND: external
TITLE: Cauchy's theorem for rectangles, Banach values
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-rect@L117-L125
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-rect
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: for a complete complex normed space F, f : C -> F and z, w in C with f complex differentiable on the closed rectangle [Re z, Re w] x [Im z, Im w], the oriented boundary integral vanishes (Complex.integral_boundary_rect_eq_zero_of_differentiableOn; interval integrals oriented; K's bp:p1:ext-rectangle, provenance); Fubini for continuous integrands on a box (MeasureTheory.integral_prod)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W-r2
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: New labelled external added by the blueprint cleanup (inp 99afc128).
