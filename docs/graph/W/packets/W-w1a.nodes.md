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
DEPS: bpW:w0:ellap#ellWeight, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w1-sequences.tex#bpW:w1:transport@L31-L31 | omega_{a,p}(j) is the frozen ellWeight a p j
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:transport@L33-L33 | the spaces l^{a,p}_K of Definition bpW:w0:ellap; kappa_{1,1} is the frozen coeff (realization table L51)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:space
KIND: lemma
TITLE: The weighted spaces
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L122-L136
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L138-L154
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
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L125-L125 | tau, kappa and the weights
EDGE: stepW:w1:iso | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L139-L139 | proof step
EDGE: stepW:w1:sep | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L144-L144 | proof step
EDGE: stepW:w1:coord | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L148-L148 | proof step
EDGE: stepW:w1:frozen | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L151-L151 | proof step
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L132-L132 | the frozen coeff occurs directly here
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L132-L132 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:iso
KIND: step
TITLE: Isometry
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L139-L143
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L139-L143
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
DEPS: bpW:w1:transport, bpW:w0:ellap#ellWeight, bpW:w1:ext-lp
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L140-L140 | tau, kappa, omega
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L140-L140 | the norm of Definition bpW:w0:ellap
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L143-L143 | inner product and completeness of l^2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:sep
KIND: step
TITLE: Separability
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sep@L144-L147
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sep@L144-L147
CONTRACT_ID: stepW:w1:sep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:space: a >= 0, p in R, K in {R, C}; local data: (iii) of the lemma
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
EDGE: stepW:w1:coord | blueprint-W/parts/w1-sequences.tex#stepW:w1:sep@L146-L146 | density by the truncation statement (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:coord
KIND: step
TITLE: Coordinates and truncation
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L148-L150
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L148-L150
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
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L149-L149 | ¦y_j¦ <= ¦¦y¦¦
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L149-L149 | kappa divides by omega(j)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:frozen
KIND: step
TITLE: Frozen case
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L151-L153
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L151-L153
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
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L152-L152 | unfolds the frozen coeff
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L153-L153 | the frozen WaveSpace with the product (max) norm
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:coordinatewise
KIND: lemma
TITLE: Derivatives of coordinates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L158-L168
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L170-L180
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
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L160-L160 | the inclusion iota and its representative
EDGE: bpW:w1:hamfield | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L165-L165 | the field X^w of (v)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L165-L165 | the coefficients coeff in the frozen conclusion (4)
EDGE: stepW:w1:coordder | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L171-L171 | proof step
EDGE: stepW:w1:coordcomp | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L175-L175 | proof step
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L164-L164 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The statement speaks of the *form* of the frozen conclusion (4) of nlw2; that is not a use of the root (no edge to bpW:wh:nlw2, which would create a cycle once W8 is added).

NODE: stepW:w1:coordder
KIND: step
TITLE: Coordinates of the derivative
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L171-L174
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L171-L174
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
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L172-L172 | (ii): the coordinate is a continuous linear functional
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L174-L174 | (iii): the inclusion does not change coefficients
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:coordcomp
KIND: step
TITLE: Comparison
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L175-L179
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L175-L179
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
EDGE: stepW:w1:coordder | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L176-L176 | the derivative of the coordinates
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L177-L177 | injectivity of kappa ((i))
EDGE: bpW:w1:hamfield | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L179-L179 | (v): the coordinates of X^w are the right sides of (4)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:multiplier
KIND: lemma
TITLE: Diagonal multipliers
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L183-L189
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L191-L195
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
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L193-L193 | norm bounds from finite partial sums
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L194-L194 | the representative tau o (m .) o kappa
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:embed
KIND: lemma
TITLE: Embeddings
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L198-L207
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L209-L214
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
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L210-L210 | m_j = 1, mu_j = omega_{a',p'}(j)/omega_{a,p}(j)
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L213-L213 | the identity mu_j/omega_{a',p'}(j) = 1/omega_{a,p}(j)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:diag
KIND: lemma
TITLE: Frequency multipliers and the linear flow
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L217-L232
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L234-L249
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
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L218-L218 | the multiplier lambda^r
EDGE: bpW:w0:z | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L230-L230 | the complex coordinates z
EDGE: stepW:w1:ratio | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L235-L235 | proof step
EDGE: stepW:w1:rot | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L240-L240 | proof step
EDGE: stepW:w1:realflow | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L244-L244 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:ratio
KIND: step
TITLE: Ratio
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L235-L239
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L235-L239
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
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L236-L236 | the representative and its norm
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L237-L237 | j < lambda_j
EDGE: bpW:w0:mass | blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L237-L237 | lambda_j^2 = j^2 + m <= (1+m) j^2
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L236-L236 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:rot
KIND: step
TITLE: Unboundedness and rotations
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L240-L243
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L240-L243
CONTRACT_ID: stepW:w1:rot
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:diag: a >= 0, p in R, r in R; lambda^r the multiplier w -> (lambda_j^r w_j); local data: t, s in R; z in l^{a,p}_C
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:diag (for all a, p, r; t, s in R); within the step: t, s; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) lambda_j^r -> infinity; (iii) R_t = D_mu with ¦mu_j¦ = 1 is an isometry, group law coordinatewise, and t -> R_t z continuous by dominated convergence for series
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:multiplier, bpW:w1:ext-series, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L241-L241 | R_t is a multiplier D_mu with ¦mu_j¦ = 1
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L243-L243 | dominated convergence for series (Tonelli/Fubini for series)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L241-L241 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:realflow
KIND: step
TITLE: Real flow
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L244-L248
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L244-L248
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
EDGE: bpW:w0:z | blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L248-L248 | z_j = (q_j + i p_j)/sqrt 2
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L248-L248 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:linfty
KIND: definition
TITLE: Sup-weighted sequences
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:linfty@L254-L261
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:tails
KIND: lemma
TITLE: Spectral asymptotics of the wave normal frequencies
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L264-L273
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L275-L280
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
EDGE: bpW:w0n:AB | blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L266-L266 | Omega = lambda_N + B xi with the corrected B
EDGE: bpW:w1:linfty | blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L268-L268 | the norm ¦.¦_1 of l^1_infty and the Lipschitz condition
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L276-L276 | lambda_j - j = m/(lambda_j + j) in (0, m/(2j)]; lambda_j > j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L265-L265 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:twosided-transport
KIND: definition
TITLE: Two-sided transport
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-transport@L288-L294
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
EDGE: bpW:w0:twosided | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-transport@L290-L290 | the space l^{a,s}_b and the convolution
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-transport@L291-L291 | the isometry argument
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:twosided
KIND: lemma
TITLE: Passage between one- and two-sided sequences
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L297-L313
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L315-L325
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
EDGE: bpW:w1:twosided-transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L302-L302 | the two-sided weights
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L300-L300 | the factor 1/sqrt(lambda_¦l¦)
EDGE: stepW:w1:ext | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L316-L316 | proof step
EDGE: stepW:w1:restr | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L320-L320 | proof step
EDGE: stepW:w1:pair | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L323-L323 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:ext
KIND: step
TITLE: Extensions
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L316-L319
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L316-L319
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
DEPS: bpW:w0:basis#lambda-facts, stepW:w0n:majorant, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L318-L318 | j/lambda_j < 1
EDGE: stepW:w0n:majorant | blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L319-L319 | this is the majorant step of W0
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L317-L317 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:restr
KIND: step
TITLE: Restriction
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L320-L322
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L320-L322
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
DEPS: bpW:w0:basis#lambda-facts, stepW:w0n:smoothing, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L321-L321 | l/lambda_l < 1
EDGE: stepW:w0n:smoothing | blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L322-L322 | this is the smoothing step of W0
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L321-L321 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:pair
KIND: step
TITLE: Pairing
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:pair@L323-L324
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:pair@L323-L324
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
EDGE: bpW:w1:twosided-transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:pair@L324-L324 | the two-sided weight <l>
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:young
KIND: lemma
TITLE: Young and $\ell^1$ control
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L329-L339
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L341-L357
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
EDGE: bpW:w1:twosided-transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L333-L333 | the norms ¦¦.¦¦_{a,s} and the convolution
EDGE: stepW:w1:cs | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L342-L342 | proof step
EDGE: stepW:w1:youngsum | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L346-L346 | proof step
EDGE: stepW:w1:l1 | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L349-L349 | proof step
EDGE: stepW:w1:rules | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L353-L353 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:cs
KIND: step
TITLE: Weighted Cauchy--Schwarz
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cs@L342-L345
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cs@L342-L345
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:youngsum
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L346-L348
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L346-L348
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
EDGE: stepW:w1:cs | blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L348-L348 | sums the pointwise bound over l
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L347-L347 | exchange of the nonnegative double sum (Tonelli)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:l1
KIND: step
TITLE: $\ell^1$ control
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:l1@L349-L352
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:l1@L349-L352
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
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:l1@L350-L350 | sum k^{-sigma} < infinity for sigma = 2s > 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:rules
KIND: step
TITLE: Algebraic rules
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L353-L356
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L353-L356
CONTRACT_ID: stepW:w1:rules
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:young: (i) X in l^2(Z), Y in l^1(Z); (ii) s > 1/2, a >= 0, Y in l^{a,s}_b; (iii) nonnegative X, Y, Z in l^{0,s}_b with s > 1/2; complex c, d; local data: sequences in l^1 cap l^2 by (ii)
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
EDGE: stepW:w1:l1 | blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L354-L354 | (ii) puts the sequences in l^1 cap l^2
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L355-L355 | Fubini for absolutely summable double series
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:algebra
KIND: lemma
TITLE: Convolution algebra
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L360-L363
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L365-L369
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
EDGE: bpW:w0n:algebra | blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L366-L366 | the two-factor bound is Lemma bpW:w0n:algebra
EDGE: bpW:w1:young | blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L367-L367 | (iii): associativity for the three-factor form
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:selection
KIND: lemma
TITLE: Selection-rule trilinear maps
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L386-L400
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L402-L427
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
EDGE: stepW:w1:maj1 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L403-L403 | proof step
EDGE: stepW:w1:sel1 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L406-L406 | proof step
EDGE: stepW:w1:smooth1 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L412-L412 | proof step
EDGE: stepW:w1:maj2 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L415-L415 | proof step
EDGE: stepW:w1:sel2 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L419-L419 | proof step
EDGE: stepW:w1:smooth2 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L423-L423 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:maj1
KIND: step
TITLE: One-sided majorant
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj1@L403-L405
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj1@L403-L405
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
EDGE: bpW:w1:twosided | blueprint-W/parts/w1-sequences.tex#stepW:w1:maj1@L405-L405 | (i): the even sequence x
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:sel1
KIND: step
TITLE: One-sided selection
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L406-L411
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L406-L411
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
EDGE: stepW:w1:maj1 | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L408-L408 | the even majorants
EDGE: stepW:w0n:selection | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L410-L410 | the injectivity argument of the W0 selection step
EDGE: bpW:w1:young | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L410-L410 | X is finite (Young, l^1 control)
EDGE: bpW:w1:algebra | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L411-L411 | X lies in l^{a,s}_b
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:smooth1
KIND: step
TITLE: One-sided smoothing
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L412-L414
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L412-L414
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
EDGE: stepW:w1:sel1 | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L413-L413 | the pointwise bound by M l^{-1/2} X_l
EDGE: bpW:w1:algebra | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L414-L414 | three-factor algebra bound
EDGE: stepW:w1:maj1 | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L414-L414 | ¦¦x¦¦ = sqrt2 ¦¦q¦¦
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:maj2
KIND: step
TITLE: Two-sided majorant
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj2@L415-L418
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj2@L415-L418
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
EDGE: bpW:w1:twosided-transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:maj2@L417-L417 | the two-sided weights
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:sel2
KIND: step
TITLE: Two-sided selection
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel2@L419-L422
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel2@L419-L422
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
EDGE: stepW:w1:maj2 | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel2@L421-L421 | ¦w_i¦/sqrt(¦i¦) <= tilde x_{i'}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:smooth2
KIND: step
TITLE: Two-sided smoothing
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L423-L426
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L423-L426
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
EDGE: stepW:w1:sel2 | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L424-L424 | the pointwise bound
EDGE: bpW:w1:algebra | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L425-L425 | three-factor algebra bound
EDGE: stepW:w1:maj2 | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L425-L425 | ¦¦tilde x¦¦ <= 2 ¦¦w¦¦
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:trilinear
KIND: theorem
TITLE: The cubic map as a continuous trilinear map
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L431-L450
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L452-L472
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
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L437-L437 | kappa, omega
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L439-L439 | iota and conjugation
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L446-L446 | the frozen cubicGrad in (iv)
EDGE: stepW:w1:tricoord | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L453-L453 | proof step
EDGE: stepW:w1:tricont | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L459-L459 | proof step
EDGE: stepW:w1:trireal | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L463-L463 | proof step
EDGE: stepW:w1:trifrozen | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L467-L467 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L455-L455 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L468-L468 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:tricoord
KIND: step
TITLE: Coordinates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L453-L458
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L453-L458
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
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L458-L458 | tau_{a,p+1} and the weighted coordinates
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L455-L455 | lambda occurs directly here (frozen lam)
EDGE: stepW:w1:tricoord#via-cubic-bound | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L454-L454 | first derivation: Theorem bpW:w0n:cubic-bound
EDGE: stepW:w1:tricoord#via-selection | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L455-L455 | equivalent derivation: Lemma bpW:w1:selection(a)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:tricont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L459-L462
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L459-L462
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
EDGE: stepW:w1:tricoord | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L461-L461 | the bound C_* prod ¦¦y¦¦
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L460-L460 | symmetry of g
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L462-L462 | kappa is injective ((i))
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:trireal
KIND: step
TITLE: Real structure and compatibility
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L463-L466
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L463-L466
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
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L465-L465 | iota and conjugation
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L466-L466 | (iii): inclusions do not change coefficients
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L464-L464 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:trifrozen
KIND: step
TITLE: Frozen identification
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L467-L471
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L467-L471
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
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L468-L468 | unfolds the frozen reconU
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L469-L469 | the tsum converges absolutely
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L470-L470 | unfolds the frozen cubicGrad
EDGE: bpW:w0n:gradient | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L471-L471 | G_q(q)_l = T(q,q,q)_l for a > 0
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L468-L468 | kappa_{1,1} = coeff
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L470-L470 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:cubic-analytic
KIND: corollary
TITLE: Analyticity and Lipschitz bounds of the cubic gradient
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L475-L489
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L491-L505
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
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L476-L476 | T and C_*
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L484-L484 | the frozen cubicGrad in (iv)
EDGE: stepW:w1:can | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L492-L492 | proof step
EDGE: stepW:w1:cder | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L494-L494 | proof step
EDGE: stepW:w1:clip | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L499-L499 | proof step
EDGE: stepW:w1:cfrozen | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L502-L502 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:can
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:can@L492-L493
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:can@L492-L493
CONTRACT_ID: stepW:w1:can
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cubic-analytic: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y); local data: T continuous trilinear
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cubic-analytic (for all y, y', h, k); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: N = T o Delta, Delta(y) = (y,y,y) continuous linear, is analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:can@L493-L493 | continuous multilinear maps and compositions are analytic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:cder
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cder@L494-L498
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cder@L494-L498
CONTRACT_ID: stepW:w1:cder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cubic-analytic: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y); local data: T symmetric trilinear with ¦¦T¦¦ <= C_*
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
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:cder@L496-L496 | symmetry and the bound C_* ((i))
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:clip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:clip@L499-L501
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:clip@L499-L501
CONTRACT_ID: stepW:w1:clip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cubic-analytic: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y); local data: T trilinear
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
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:clip@L501-L501 | the bound C_*
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:cfrozen
KIND: step
TITLE: Frozen form
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L502-L504
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L502-L504
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
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L503-L503 | (iv) frozen identification
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L504-L504 | C_m = K_{3/2}^2/pi
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L503-L503 | the weight ratios
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:gradient-identity
KIND: proposition
TITLE: Gradient identity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L509-L522
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L524-L540
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
EDGE: bpW:w0:H | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L510-L510 | G(q) = (1/4) int U_m(q)^4
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L515-L515 | the trilinear map T
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L519-L519 | frozen cubicGrad in (iii)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L519-L519 | frozen coeff in (iii)
EDGE: stepW:w1:quartic | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L525-L525 | proof step
EDGE: stepW:w1:gradder | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L531-L531 | proof step
EDGE: stepW:w1:gradw | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L535-L535 | proof step
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L510-L510 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:quartic
KIND: step
TITLE: Quartic form
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L525-L530
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L525-L530
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
EDGE: bpW:w0n:gradient | blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L526-L526 | G as an absolutely convergent quartic sum
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L528-L528 | symmetry of g
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L529-L529 | ¦¦u¦¦_{0,0} <= ¦¦u¦¦_{a,p+1}, ¦¦v¦¦_{0,0} <= ¦¦v¦¦_{a,p}
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L530-L530 | the bound on T
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:gradder
KIND: step
TITLE: Derivative
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L531-L534
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L531-L534
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
EDGE: stepW:w1:quartic | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L532-L532 | the quartic form Q
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L532-L532 | continuous multilinear maps are analytic
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L534-L534 | (iv): T(q,q,q) = G_q(q)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L533-L533 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:gradw
KIND: step
TITLE: Weighted coordinates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L535-L539
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L535-L539
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
EDGE: stepW:w1:gradder | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L536-L536 | DG(q)h = <G_q(q),h>_0
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L538-L538 | (iv): G^w and the weighted coordinates of G_q(kappa y)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L536-L536 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:hamfield
KIND: proposition
TITLE: The Hamiltonian field
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L543-L563
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L565-L586
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
EDGE: bpW:w0:H | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L553-L553 | H = Lambda + G
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L555-L555 | the system (bpW:w0:coeffsys)
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L550-L550 | the bounds of the cubic gradient
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L557-L557 | X^w : WaveSpace -> WaveSpace
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L560-L560 | the coordinates in terms of coeff
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L560-L560 | the coordinates in terms of cubicGrad
EDGE: stepW:w1:hlin | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L566-L566 | proof step
EDGE: stepW:w1:hnonlin | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L568-L568 | proof step
EDGE: stepW:w1:hsum | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L571-L571 | proof step
EDGE: stepW:w1:hham | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L574-L574 | proof step
EDGE: stepW:w1:hfrozen | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L581-L581 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L546-L546 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hlin
KIND: step
TITLE: Linear part
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hlin@L566-L567
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hlin@L566-L567
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
EDGE: bpW:w1:diag | blueprint-W/parts/w1-sequences.tex#stepW:w1:hlin@L567-L567 | (i)-(ii) with r = 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hnonlin
KIND: step
TITLE: Nonlinear part
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L568-L570
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L568-L570
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
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L569-L569 | analyticity and bounds of N
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L569-L569 | (iv) identification with G_q and (ii) complex version
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hsum
KIND: step
TITLE: Sum
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L571-L573
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L571-L573
CONTRACT_ID: stepW:w1:hsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:hamfield: a > 0, p >= 1/2; local data: (i), (ii)
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
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L572-L572 | E_{a,p+1} subset E_{a,p-1}
EDGE: stepW:w1:hlin | blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L573-L573 | X_Lambda bounded linear
EDGE: stepW:w1:hnonlin | blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L573-L573 | X_G analytic
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L573-L573 | sums of analytic maps
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hham
KIND: step
TITLE: Hamiltonian
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L574-L580
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L574-L580
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
DEPS: bpW:w0:basis#lambda-facts, bpW:w1:embed, bpW:w1:gradient-identity, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L576-L576 | lambda_j <= sqrt(1+m) j
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L577-L577 | ¦¦q¦¦_{0,1/2} <= ¦¦q¦¦_{a,p} for p >= 1/2
EDGE: bpW:w1:gradient-identity | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L579-L579 | (ii): DG(q)h = <G_q(q),h>_0
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L575-L575 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hfrozen
KIND: step
TITLE: Frozen form
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L581-L585
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L581-L585
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
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L583-L583 | (iv): e^j cubicGrad_j = j^{-2} G^w(y)_j
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L584-L584 | D and S are bounded
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L584-L584 | lambda_j/j <= sqrt(1+m)
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L585-L585 | polynomial maps are analytic
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L582-L582 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L583-L583 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L585-L585 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:tricoord#via-cubic-bound
KIND: route
TITLE: Coordinates of the trilinear map via Theorem bpW:w0n:cubic-bound
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L454-L458
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L454-L454
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
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L454-L454 | absolute convergence and the bound C_*
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:tricoord#via-selection
KIND: route
TITLE: Coordinates of the trilinear map via Lemma bpW:w1:selection(a)
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L454-L458
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L455-L456
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
DEPS: bpW:w1:selection, bpW:w0n:quartic-coeff, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: stepW:w1:tricoord
EDGE: bpW:w1:selection | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L455-L455 | (a) with M = 1/(2pi)
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L456-L456 | the bound after (bpW:w0n:g-signed) gives the hypothesis on c
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L456-L456 | lambda >= j gives the (ijkl)^{-1/2} decay
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: "equivalently Lemma bpW:w1:selection(a) with c_ijkl = g_ijkl (lambda lambda lambda lambda)^{-1/2}, M = 1/(2pi)": the text offers it as a sufficient alternative to cubic-bound.
