NODE: bpP:p6:ext-chain
KIND: external
TITLE: bpP:p6:ext-chain
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:ext-chain@L28-L28
PROOF_SOURCE: -
CONTRACT_ID: bpP:p6:ext-chain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: functions between finite-dimensional real spaces (Mathlib level)
SOURCE_QUANTIFIERS: none (a library fact quantified over its own variables)
SOURCE_CONCLUSION: chain, product, quotient and finite-sum rules for HasDerivAt/HasFDerivAt; componentwise derivative into a finite product (hasDerivAt_pi); fderiv of a differentiable map is its derivative; polynomials are C-infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p6:ext-sqrt
KIND: external
TITLE: bpP:p6:ext-sqrt
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:ext-sqrt@L29-L29
PROOF_SOURCE: -
CONTRACT_ID: bpP:p6:ext-sqrt
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none (a library fact quantified over its own variables)
SOURCE_CONCLUSION: sqrt is C-infinity on (0,infinity) with derivative 1/(2 sqrt x); x -> 1/x is C-infinity on R minus {0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p6:ext-top
KIND: external
TITLE: bpP:p6:ext-top
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:ext-top@L30-L30
PROOF_SOURCE: -
CONTRACT_ID: bpP:p6:ext-top
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: continuous maps between topological spaces; finite families of open sets; finitely many reals
SOURCE_QUANTIFIERS: none (a library fact quantified over its own variables)
SOURCE_CONCLUSION: preimages of open sets under continuous maps are open; finite intersections of open sets are open; R is totally ordered and finite minima/maxima exist
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p6:ext-sum
KIND: external
TITLE: bpP:p6:ext-sum
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:ext-sum@L31-L31
PROOF_SOURCE: -
CONTRACT_ID: bpP:p6:ext-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: finite index sets and finite sums
SOURCE_QUANTIFIERS: none (a library fact quantified over its own variables)
SOURCE_CONCLUSION: finite-sum algebra: Fin.sum_univ_succ, Finset.sum_comm, splitting sum_j = sum_{j<i} + sum_{j>i}, and sum_{j!=i} = sum_j minus the term j = i
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p6:ext-tri
KIND: external
TITLE: bpP:p6:ext-tri
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:ext-tri@L32-L32
PROOF_SOURCE: -
CONTRACT_ID: bpP:p6:ext-tri
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u,w in a normed space
SOURCE_QUANTIFIERS: none (a library fact quantified over its own variables)
SOURCE_CONCLUSION: reverse triangle inequality: ¦¦u¦ - ¦w¦¦ <= ¦u - w¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p6:ext-meas
KIND: external
TITLE: bpP:p6:ext-meas
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:ext-meas@L33-L33
PROOF_SOURCE: -
CONTRACT_ID: bpP:p6:ext-meas
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: bounded subsets of R^N; boxes; the product measure on Ph_d = R^d x R^d
SOURCE_QUANTIFIERS: none (a library fact quantified over its own variables)
SOURCE_CONCLUSION: bounded sets of R^N have finite Lebesgue measure; volume on Ph_d is Lebesgue measure on R^{2d}; a box prod[-r_k,r_k] has measure prod 2r_k; measure is monotone
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p6:plane
KIND: lemma
TITLE: Planar length
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:plane@L38-L45
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:plane@L46-L50
CONTRACT_ID: bpP:p6:plane
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v,w in R^2; c in R; l the planar length
SOURCE_QUANTIFIERS: v,w in R^2, c in R
SOURCE_CONCLUSION: (a) l(v)>=0, l(v)^2=sq(v)=v.v, l(v)=0 iff v=0, l(-v)=l(v), l(cv)=¦c¦l(v), l(v+w)<=l(v)+l(w); (b) ¦v¦_inf <= l(v) <= sqrt2 ¦v¦_inf; (c) on R^2 minus {0} l and 1/l are C-infinity with Dl(v)h=(v.h)/l(v), D(1/l)(v)h=-(v.h)/l(v)^3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:pl-a, stepP:p6:pl-b, stepP:p6:pl-c, bpP:p0:plane#planeLength, bpP:p0:plane#planeSq, bpP:p0:plane#planeDot
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:pl-a | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:plane@L47-L47 | proof step (a)
EDGE: stepP:p6:pl-b | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:plane@L48-L48 | proof step (b)
EDGE: stepP:p6:pl-c | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:plane@L49-L49 | proof step (c)
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:plane@L41-L41 | l is planeLength
EDGE: bpP:p0:plane#planeSq | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:plane@L41-L41 | sq is planeSq
EDGE: bpP:p0:plane#planeDot | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:plane@L41-L41 | v.w is planeDot
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: PROVED
LEAN_REF: planeLength_nonneg, planeLength_sq, planeLength_eq_zero_iff, planeLength_neg, planeLength_smul, planeLength_add_le, norm_le_planeLength, planeLength_le_sqrt_two_mul_norm, analyticAt_planeLength, analyticAt_inv_planeLength, hasFDerivAt_planeLength, hasFDerivAt_inv_planeLength (KAM/Kepler/Plane.lean)
LEAN_NOTE: audit KEP-1 PASS (addendum); steps pl-* not named, left
NOTE: -

NODE: stepP:p6:pl-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-a@L47-L47
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-a@L47-L47
CONTRACT_ID: stepP:p6:pl-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v,w in R^2, c in R
SOURCE_QUANTIFIERS: v,w,c
SOURCE_CONCLUSION: the algebraic properties (a) of l, with the triangle inequality from Cauchy-Schwarz
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:plane#planeLength, bpP:p0:plane#planeDot
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-a@L47-L47 | algebra of sqrt(v1^2+v2^2), the definition of l
EDGE: bpP:p0:plane#planeDot | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-a@L47-L47 | Cauchy-Schwarz v.w <= l(v)l(w) in the dot product
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: PROVED
LEAN_REF: planeLength_algebra (KAM/Planetary/Newtonian/LeftoverNodes.lean)
LEAN_NOTE: audit GAP-LREF PASS WITH NOTES (bundle export)
NOTE: -

NODE: stepP:p6:pl-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-b@L48-L48
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-b@L48-L48
CONTRACT_ID: stepP:p6:pl-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v in R^2
SOURCE_QUANTIFIERS: v
SOURCE_CONCLUSION: ¦v¦_inf <= l(v) <= sqrt2 ¦v¦_inf
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:plane#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-b@L48-L48 | v_k^2 <= l(v)^2 <= 2 max_k v_k^2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: PROVED
LEAN_REF: planeLength_norm_bounds (KAM/Planetary/Newtonian/LeftoverNodes.lean)
LEAN_NOTE: audit GAP-LREF PASS WITH NOTES (bundle export)
NOTE: -

NODE: stepP:p6:pl-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-c@L49-L49
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-c@L49-L49
CONTRACT_ID: stepP:p6:pl-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v in R^2 with v!=0; h in R^2; sq, l and dot are the frozen planar definitions
SOURCE_QUANTIFIERS: v in R^2 minus {0}, h in R^2
SOURCE_CONCLUSION: l and 1/l are C-infinity there with Dl(v)h=(v.h)/l(v) and D(1/l)=-Dl/l^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:ext-sqrt, bpP:p6:ext-chain, bpP:p0:plane#planeSq, bpP:p0:plane#planeLength, bpP:p0:plane#planeDot
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:ext-sqrt | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-c@L49-L49 | sqrt is C-infinity on (0,infinity) with derivative 1/(2 sqrt x)
EDGE: bpP:p6:ext-chain | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-c@L49-L49 | chain and quotient rules
EDGE: bpP:p0:plane#planeSq | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-c@L49-L49 | sq is planeSq
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-c@L49-L49 | R3: the derivative formulas use the literal planar length and scalar product
EDGE: bpP:p0:plane#planeDot | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:pl-c@L49-L49 | R3: the derivative formulas use the literal planar length and scalar product
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: planeLength_smooth_deriv (KAM/Planetary/Newtonian/LeftoverNodes.lean)
LEAN_NOTE: audit GAP-LREF PASS WITH NOTES (bundle export)
NOTE: -

NODE: bpP:p6:domain
KIND: lemma
TITLE: Collision-free domain; regularity
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:domain@L54-L56
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:domain@L57-L60
CONTRACT_ID: bpP:p6:domain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); H_mov=movingHamiltonian G m0 m mu; H_fix=fixedHamiltonian G m0 m eps
SOURCE_QUANTIFIERS: fixed data (n,G,m0,m,mu,eps); then the points of W
SOURCE_CONCLUSION: W is open; H_mov and H_fix are C-infinity on W (differentiable at every point of W with continuous Frechet derivative)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:dom-open, stepP:p6:dom-smooth, bpP:p6:conv#data, bpP:p0:movham#movingHamiltonian, bpP:p0:fixham#fixedHamiltonian
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:dom-open | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:domain@L58-L58 | proof step Openness
EDGE: stepP:p6:dom-smooth | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:domain@L59-L59 | proof step Smoothness
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:domain@L55-L55 | W and the data of Part 6
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:domain@L55-L55 | H_mov is movingHamiltonian
EDGE: bpP:p0:fixham#fixedHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:domain@L55-L55 | H_fix is fixedHamiltonian
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: PROVED
LEAN_REF: collisionFreeDomain, isOpen_collisionFreeDomain, analyticOnNhd_movingHamiltonian, analyticOnNhd_fixedHamiltonian, differentiableAt_movingHamiltonian, differentiableAt_fixedHamiltonian (KAM/Planetary/Newtonian/Models.lean)
LEAN_NOTE: audit P6-1 PASS WITH NOTES; steps dom-* not named, left
NOTE: -

NODE: stepP:p6:dom-open
KIND: step
TITLE: Openness
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-open@L58-L58
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-open@L58-L58
CONTRACT_ID: stepP:p6:dom-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); H_mov=movingHamiltonian G m0 m mu; H_fix=fixedHamiltonian G m0 m eps
SOURCE_QUANTIFIERS: q
SOURCE_CONCLUSION: W is open
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:plane, bpP:p6:ext-top, bpP:p0:nocoll#NoCollision, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-open@L58-L58 | Lemma plane(a): positivity of sq iff nonzero length
EDGE: bpP:p6:ext-top | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-open@L58-L58 | preimages of open sets and finite intersections are open
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-open@L58-L58 | NoColl as the finite conjunction
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-open@L58-L58 | W is defined in the conventions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: isOpen_collisionFreeDomain (KAM/Planetary/Newtonian/Models.lean)
LEAN_NOTE: LEAN_REF audit LREF-P-audit-1 CLOSABLE
NOTE: -

NODE: stepP:p6:dom-smooth
KIND: step
TITLE: Smoothness
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-smooth@L59-L59
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-smooth@L59-L59
CONTRACT_ID: stepP:p6:dom-smooth
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); H_mov=movingHamiltonian G m0 m mu; H_fix=fixedHamiltonian G m0 m eps
SOURCE_QUANTIFIERS: z in W
SOURCE_CONCLUSION: H_mov and H_fix are C-infinity on W
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:plane, bpP:p6:ext-chain, bpP:p0:movham#movingHamiltonian, bpP:p0:fixham#fixedHamiltonian, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-smooth@L59-L59 | Lemma plane(c): 1/l is C-infinity off 0
EDGE: bpP:p6:ext-chain | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-smooth@L59-L59 | finite sums, products and compositions of C-infinity maps
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-smooth@L59-L59 | terms of H_mov
EDGE: bpP:p0:fixham#fixedHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-smooth@L59-L59 | terms of H_fix
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:dom-smooth@L59-L59 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: hamiltonians_contDiffOn (KAM/Planetary/Newtonian/LeftoverNodes.lean)
LEAN_NOTE: audit GAP-LREF PASS WITH NOTES (bundle export) (C^infinity form)
NOTE: -

NODE: bpP:p6:split
KIND: lemma
TITLE: Splitting; the identity of Part~0
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:split@L62-L67
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:split@L68-L70
CONTRACT_ID: bpP:p6:split
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); H_Kep(q,p)=sum_i[l(p_i)^2/(2m_i)-G m0 m_i/l(q_i)]; f_mov, f_fix as displayed for z in W
SOURCE_QUANTIFIERS: fixed data; then all z in Ph_{2n} (Lean total functions)
SOURCE_CONCLUSION: H_mov=H_Kep+mu f_mov and H_fix=H_Kep+eps f_fix; H_mov(z)-H_fix(z) at eps=mu equals mu l(P)^2/(2m0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:sp-alg, bpP:p0:movham#movingHamiltonian, bpP:p0:fixham#fixedHamiltonian, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:sp-alg | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:split@L69-L69 | proof step Algebra
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:split@L65-L65 | H_mov is movingHamiltonian
EDGE: bpP:p0:fixham#fixedHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:split@L65-L65 | H_fix is fixedHamiltonian
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:split@L63-L63 | p_i, P, W of the conventions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: PROVED
LEAN_REF: keplerPart, pairPotential, fMov, fFix, movingHamiltonian_split, fixedHamiltonian_split, moving_sub_fixed (KAM/Planetary/Newtonian/Models.lean)
LEAN_NOTE: audit P6-1 PASS WITH NOTES; step sp-alg not named, left
NOTE: -

NODE: stepP:p6:sp-alg
KIND: step
TITLE: Algebra
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:sp-alg@L69-L69
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:sp-alg@L69-L69
CONTRACT_ID: stepP:p6:sp-alg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); H_Kep(q,p)=sum_i[l(p_i)^2/(2m_i)-G m0 m_i/l(q_i)]; f_mov, f_fix as displayed for z in W
SOURCE_QUANTIFIERS: z in Ph_{2n}
SOURCE_CONCLUSION: kinetic part of H_mov is sum l(p_i)^2/(2m_i)+(mu/m0)(1/2)l(P)^2; potential parts agree; difference at eps=mu is mu l(P)^2/(2m0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:plane, bpP:p0:movham#movingHamiltonian, bpP:p0:fixham#fixedHamiltonian, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:sp-alg@L69-L69 | Lemma plane(a): l(P)^2 expansion by bilinearity
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:sp-alg@L69-L69 | kinetic and potential parts of H_mov
EDGE: bpP:p0:fixham#fixedHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:sp-alg@L69-L69 | pair-potential terms of H_fix
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:sp-alg@L69-L69 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: sp_alg (KAM/Planetary/Newtonian/HamiltonNodes.lean)
LEAN_NOTE: audit GAP-P6a PASS WITH NOTES (node PASS)
NOTE: -

NODE: bpP:p6:kepler-part
KIND: claim
TITLE: Kepler part; mass dictionary
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:kepler-part@L71-L73
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:kepler-part@L71-L73
CONTRACT_ID: bpP:p6:kepler-part
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); split; k=G m0
SOURCE_QUANTIFIERS: fixed data; planet index i<n
SOURCE_CONCLUSION: H_mov and H_fix share the unperturbed part H_Kep (perturbations mu f_mov, eps f_fix with f independent of the coupling); each summand of H_Kep is m_i E_k(q_i,p_i/m_i) with k=G m0 (notation of bpI:p7:scaling), which supplies the Kepler orbit, the action m_i sqrt(k a) and the mean values used in Part 7; H_Kep keeps the planet mass m_i, not the reduced mass
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:split, bpI:p7:scaling, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:split | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:kepler-part@L72-L72 | the splitting H=H_Kep+mu f
EDGE: bpI:p7:scaling | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:kepler-part@L72-L72 | mass dictionary of the Kepler energy E_k used to rewrite each summand of H_Kep
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:kepler-part@L72-L72 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-delta-P-h
REVIEWER: sol-delta2-P-d
LEAN_STATUS: PROVED
LEAN_REF: keplerPart, keplerPart_eq_sum, movingHamiltonian_split, fixedHamiltonian_split (KAM/Planetary/Newtonian/Models.lean)
LEAN_NOTE: audit P6-1 PASS WITH NOTES
NOTE: remark kept: its stated facts (H_Kep = sum m_i E_{k}, planet mass not reduced mass) are consumed by Part 7 stepP:p7:pc-dec and bpP:p7:same-chart and by Part 8 stepP:p8:l64-a. CROSS-OWNERSHIP CANDIDATE: bpI:p7:scaling is a genuine use (mass dictionary).

NODE: bpP:p6:action-reaction
KIND: lemma
TITLE: Action--reaction
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:action-reaction@L75-L77
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:action-reaction@L78-L80
CONTRACT_ID: bpP:p6:action-reaction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); NoColl(q)
SOURCE_QUANTIFIERS: q with NoColl(q)
SOURCE_CONCLUSION: sum_i m_i f_i(q)=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:plane, bpP:p6:ext-sum, bpP:p0:nocoll#NoCollision, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:action-reaction@L79-L79 | Lemma plane(a): l even gives a_ji=-a_ij
EDGE: bpP:p6:ext-sum | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:action-reaction@L79-L79 | swapping the summation indices
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:action-reaction@L76-L76 | hypothesis NoColl(q)
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:action-reaction@L76-L76 | f_i is the planet-planet kernel
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: PROVED
LEAN_REF: sum_mass_smul_fKernel (KAM/Planetary/Newtonian/Models.lean)
LEAN_NOTE: audit P6-1 PASS WITH NOTES
NOTE: -

NODE: bpP:p6:hamilton-eqs
KIND: proposition
TITLE: Hamilton equations of $H_{\rm mov}$ and $H_{\rm fix}$
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:hamilton-eqs@L82-L92
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:hamilton-eqs@L93-L101
CONTRACT_ID: bpP:p6:hamilton-eqs
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); z=(q,p) in W; X_H=(d_pH,-d_qH) of Definition bpP:p0:hamsymp; block form of vectors of R^{2n} (index 2i+c)
SOURCE_QUANTIFIERS: fixed data; z=(q,p) in W; then, for the curve statement, a curve z:J->W and t in J
SOURCE_CONCLUSION: X_Hmov(z)=((p_i/m_i+(mu/m0)P)_i,(-G m0 m_i g_i(q)+mu G m_i f_i(q))_i); X_Hfix(z)=((p_i/m_i)_i,(-G m0 m_i g_i(q)+eps G m_i f_i(q))_i); a curve z:J->W has derivative X_H(z(t)) at t iff q_i'=p_i/m_i+(mu/m0)P (resp. p_i/m_i) and p_i'=-G m0 m_i g_i(q)+mu G m_i f_i(q) (resp. with eps), componentwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:he-dir, stepP:p6:he-coef, stepP:p6:he-fix, stepP:p6:he-curve, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p6:domain, bpP:p0:movham#movingHamiltonian, bpP:p0:fixham#fixedHamiltonian, bpP:p6:conv#data, bpP:p0:body#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:he-dir | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:hamilton-eqs@L94-L94 | proof step Directional derivative
EDGE: stepP:p6:he-coef | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:hamilton-eqs@L98-L98 | proof step Collect coefficients
EDGE: stepP:p6:he-fix | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:hamilton-eqs@L99-L99 | proof step H_fix
EDGE: stepP:p6:he-curve | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:hamilton-eqs@L100-L100 | proof step The curve statement
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:hamilton-eqs@L83-L83 | X_H convention
EDGE: bpP:p6:domain | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:hamilton-eqs@L90-L90 | differentiability of H on W
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:hamilton-eqs@L85-L85 | H_mov
EDGE: bpP:p0:fixham#fixedHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:hamilton-eqs@L88-L88 | H_fix
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:hamilton-eqs@L83-L83 | W, g_i, f_i and the data
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:hamilton-eqs@L83-L83 | block form of vectors of R^{2n}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: PROVED
LEAN_REF: hamilton_eqs_moving (KAM/Planetary/Newtonian/HamiltonNodes.lean)
LEAN_NOTE: audit GAP-P6a PASS WITH NOTES (node PASS)
NOTE: -

NODE: stepP:p6:he-dir
KIND: step
TITLE: Directional derivative
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-dir@L94-L97
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-dir@L94-L97
CONTRACT_ID: stepP:p6:he-dir
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); z=(q,p) in W; X_H=(d_pH,-d_qH) of Definition bpP:p0:hamsymp; block form of vectors of R^{2n} (index 2i+c)
SOURCE_QUANTIFIERS: z in W; (dq,dp) in Ph_{2n}
SOURCE_CONCLUSION: DT(p)dp=sum dp_i.(p_i/m_i+(mu/m0)P) and DV(q)dq=G m0 sum m_i q_i.dq_i/l(q_i)^3+mu G sum_{i<j} m_i m_j (q_i-q_j).(dq_i-dq_j)/l(q_i-q_j)^3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:domain, bpP:p6:ext-chain, bpP:p6:plane, bpP:p0:movham#movingHamiltonian, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:domain | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-dir@L94-L94 | H_mov is differentiable at z
EDGE: bpP:p6:ext-chain | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-dir@L94-L94 | chain rule and polynomial derivative
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-dir@L94-L94 | Lemma plane(c): derivative of 1/l
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-dir@L94-L94 | splitting H_mov=T+V
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-dir@L94-L94 | W and P
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: fderiv_movingHamiltonian_dir (KAM/Planetary/Newtonian/HamiltonNodes.lean)
LEAN_NOTE: audit GAP-P6a PASS WITH NOTES (node PASS)
NOTE: -

NODE: stepP:p6:he-coef
KIND: step
TITLE: Collect coefficients
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-coef@L98-L98
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-coef@L98-L98
CONTRACT_ID: stepP:p6:he-coef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); z=(q,p) in W; X_H=(d_pH,-d_qH) of Definition bpP:p0:hamsymp; block form of vectors of R^{2n} (index 2i+c)
SOURCE_QUANTIFIERS: z in W; index (i,c)
SOURCE_CONCLUSION: d_{q_i}H_mov=G m0 m_i g_i-mu G m_i f_i and d_{p_i}H_mov=p_i/m_i+(mu/m0)P; hence the formula for X_Hmov(z)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:he-dir, bpP:p6:plane, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:he-dir | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-coef@L98-L98 | the derivatives DT, DV
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-coef@L98-L98 | l(q_i-q_j)=l(q_j-q_i): evenness
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-coef@L98-L98 | components of X_H are DH(z)(0,e) and -DH(z)(e,0)
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-coef@L98-L98 | f_i definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: fderiv_movingHamiltonian_partials (KAM/Planetary/Newtonian/HamiltonNodes.lean)
LEAN_NOTE: audit GAP-P6a PASS WITH NOTES (node PASS)
NOTE: -

NODE: stepP:p6:he-fix
KIND: step
TITLE: $H_{\rm fix}$
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-fix@L99-L99
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-fix@L99-L99
CONTRACT_ID: stepP:p6:he-fix
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); z=(q,p) in W; X_H=(d_pH,-d_qH) of Definition bpP:p0:hamsymp; block form of vectors of R^{2n} (index 2i+c)
SOURCE_QUANTIFIERS: z in W
SOURCE_CONCLUSION: formula for X_Hfix(z)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:he-dir, stepP:p6:he-coef, bpP:p0:fixham#fixedHamiltonian, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:he-dir | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-fix@L99-L99 | the same computation
EDGE: stepP:p6:he-coef | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-fix@L99-L99 | the same coefficient collection
EDGE: bpP:p0:fixham#fixedHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-fix@L99-L99 | definition of H_fix
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-fix@L99-L99 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: hamilton_eqs_fixed, fixedField_blocks (KAM/Planetary/Newtonian/HamiltonNodes.lean); hamiltonianVectorField_fixed (KAM/Planetary/Newtonian/Models.lean)
LEAN_NOTE: LEAN_REF audit LREF-P-audit-1 CLOSABLE (first component of hamilton_eqs_fixed G m0 m eps)
NOTE: -

NODE: stepP:p6:he-curve
KIND: step
TITLE: The curve statement
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-curve@L100-L100
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-curve@L100-L100
CONTRACT_ID: stepP:p6:he-curve
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); z=(q,p) in W; X_H=(d_pH,-d_qH) of Definition bpP:p0:hamsymp; block form of vectors of R^{2n} (index 2i+c)
SOURCE_QUANTIFIERS: curve z=(q,p):J->W; t in J
SOURCE_CONCLUSION: z has derivative X_H(z(t)) at t iff each coordinate has the corresponding derivative
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:ext-chain, stepP:p6:he-coef, stepP:p6:he-fix, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:ext-chain | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-curve@L100-L100 | a curve into R^N has a derivative iff each coordinate does
EDGE: stepP:p6:he-coef | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-curve@L100-L100 | compare with the displayed X_Hmov
EDGE: stepP:p6:he-fix | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-curve@L100-L100 | compare with the displayed X_Hfix
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-curve@L100-L100 | definition of X_H
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:he-curve@L100-L100 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: hasDerivAt_iff_bodyVector (KAM/Planetary/Newtonian/HamiltonNodes.lean)
LEAN_NOTE: audit GAP-P6a PASS WITH NOTES (node PASS)
NOTE: -

NODE: bpP:p6:bary-algebra
KIND: lemma
TITLE: Algebra of the barycentric maps
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:bary-algebra@L138-L146
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:bary-algebra@L147-L151
CONTRACT_ID: bpP:p6:bary-algebra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); mu>=0; q,p in R^{2n}; M*=m0+mu sum m_i>0; M=mass_mu=actualMasses; Q=barycentricPositions m0 m mu q; V=barycentricVelocities m0 m mu p; P=sum p_i
SOURCE_QUANTIFIERS: fixed data; mu>=0; q,p in R^{2n}
SOURCE_CONCLUSION: (a) Q_0=x_0=-(mu/M*)sum m_i q_i, Q_i-Q_0=q_i, Q_j-Q_i=q_j-q_i, hence l(Q_i-Q_0)=l(q_i), l(Q_j-Q_i)=l(q_j-q_i) for every mu; (b) V_0=-(mu/m0)P, V_i=p_i/m_i, V_i-V_0=p_i/m_i+(mu/m0)P; (c) sum_k M_k Q_k=0 and sum_k M_k V_k=0; (d) l(x_0)<=(mu/m0)sum m_i l(q_i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:ba-ab, stepP:p6:ba-c, stepP:p6:ba-d, bpP:p0:barycentric#actualMasses, bpP:p0:barycentric#barycentricPositions, bpP:p0:barycentric#barycentricVelocities, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:ba-ab | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:bary-algebra@L148-L148 | proof step (a),(b)
EDGE: stepP:p6:ba-c | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:bary-algebra@L149-L149 | proof step (c)
EDGE: stepP:p6:ba-d | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:bary-algebra@L150-L150 | proof step (d)
EDGE: bpP:p0:barycentric#actualMasses | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:bary-algebra@L139-L139 | M=actualMasses
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:bary-algebra@L139-L139 | Q=barycentricPositions
EDGE: bpP:p0:barycentric#barycentricVelocities | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:bary-algebra@L139-L139 | V=barycentricVelocities
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:bary-algebra@L139-L139 | q,p,P and the data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: PROVED
LEAN_REF: barycentricPositions_succ_sub_zero, barycentricPositions_succ_sub_succ, barycentricPositions_zero, barycentricVelocities_zero, barycentricVelocities_succ, barycentricVelocities_succ_sub_zero, sum_actualMasses_smul_barycentricPositions, sum_actualMasses_smul_barycentricVelocities, planeLength_barycentricPositions_zero_le (KAM/Planetary/Newtonian/Barycentric.lean)
LEAN_NOTE: audit P6-2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:ba-ab
KIND: step
TITLE: (a),(b)
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-ab@L148-L148
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-ab@L148-L148
CONTRACT_ID: stepP:p6:ba-ab
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); mu>=0; q,p in R^{2n}; M*=m0+mu sum m_i>0; M=mass_mu=actualMasses; Q=barycentricPositions m0 m mu q; V=barycentricVelocities m0 m mu p; P=sum p_i
SOURCE_QUANTIFIERS: mu>=0; planets i,j
SOURCE_CONCLUSION: Q_0=x_0, Q_i=x_0+q_i, V_0=-(mu/m0)P, V_i=p_i/m_i; differences Q_j-Q_i=q_j-q_i; equal lengths
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:barycentric#barycentricPositions, bpP:p0:barycentric#barycentricVelocities, bpP:p6:plane, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-ab@L148-L148 | unfold barycentricPositions
EDGE: bpP:p0:barycentric#barycentricVelocities | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-ab@L148-L148 | unfold barycentricVelocities
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-ab@L148-L148 | l is even
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-ab@L148-L148 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: barycentricPositions_succ_sub_zero, barycentricPositions_succ_sub_succ, barycentricPositions_zero, barycentricVelocities_zero, barycentricVelocities_succ, barycentricVelocities_succ_sub_zero (KAM/Planetary/Newtonian/Barycentric.lean)
LEAN_NOTE: audit P6-2 PASS WITH NOTES; named bary-algebra (a),(b)
NOTE: -

NODE: stepP:p6:ba-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-c@L149-L149
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-c@L149-L149
CONTRACT_ID: stepP:p6:ba-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); mu>=0; q,p in R^{2n}; M*=m0+mu sum m_i>0; M=mass_mu=actualMasses; Q=barycentricPositions m0 m mu q; V=barycentricVelocities m0 m mu p; P=sum p_i
SOURCE_QUANTIFIERS: mu>=0
SOURCE_CONCLUSION: sum M_k Q_k=0 and sum M_k V_k=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:ba-ab, bpP:p0:barycentric#actualMasses, bpP:p0:barycentric#barycentricPositions, bpP:p0:barycentric#barycentricVelocities, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:ba-ab | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-c@L149-L149 | the formulas Q_i=x_0+q_i, V_0, V_i
EDGE: bpP:p0:barycentric#actualMasses | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-c@L149-L149 | masses M_k
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-c@L149-L149 | x_0
EDGE: bpP:p0:barycentric#barycentricVelocities | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-c@L149-L149 | V_0
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-c@L149-L149 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: sum_actualMasses_smul_barycentricPositions, sum_actualMasses_smul_barycentricVelocities (KAM/Planetary/Newtonian/Barycentric.lean)
LEAN_NOTE: audit P6-2 PASS WITH NOTES; named bary-algebra (c)
NOTE: -

NODE: stepP:p6:ba-d
KIND: step
TITLE: (d)
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-d@L150-L150
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-d@L150-L150
CONTRACT_ID: stepP:p6:ba-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); mu>=0; q,p in R^{2n}; M*=m0+mu sum m_i>0; M=mass_mu=actualMasses; Q=barycentricPositions m0 m mu q; V=barycentricVelocities m0 m mu p; P=sum p_i
SOURCE_QUANTIFIERS: mu>=0
SOURCE_CONCLUSION: l(x_0)<=(mu/m0)sum m_i l(q_i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:plane, stepP:p6:ba-ab, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-d@L150-L150 | Lemma plane(a): homogeneity and triangle inequality of l
EDGE: stepP:p6:ba-ab | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-d@L150-L150 | formula for x_0
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ba-d@L150-L150 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: planeLength_barycentricPositions_zero_le (KAM/Planetary/Newtonian/Barycentric.lean)
LEAN_NOTE: audit P6-2 PASS WITH NOTES; named bary-algebra (d)
NOTE: -

NODE: bpP:p6:reconstruction
KIND: proposition
TITLE: Reconstruction: moving Sun $\Rightarrow$ Newton, on any set of times
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L153-L168
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L169-L178
CONTRACT_ID: bpP:p6:reconstruction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); G,m0>0; m_i>0; mu>=0; J subset R arbitrary; z=(q,p):R->Ph_{2n} such that for all t in J: (R1) NoColl(q(t)); (R2) z has derivative X_Hmov(z(t)) at t, H_mov=movingHamiltonian G m0 m mu; M=mass_mu; Q(t)=barycentricPositions m0 m mu q(t); V(t)=barycentricVelocities m0 m mu p(t)
SOURCE_QUANTIFIERS: G,m0,m_i,mu; J; z; then every t in J and every pair k!=l of Fin(n+1)
SOURCE_CONCLUSION: for every t in J and k!=l: (a) l(Q_l(t)-Q_k(t))>0; (b) Q_k has derivative V_k(t) at t; (c) V_k has derivative sum_{l!=k} G M_l (Q_l-Q_k)/l(Q_l-Q_k)^3 at t; consequently IsNewtonSolutionOn (G*M) J Q V, and for J=R IsNewtonSolution G (actualMasses m0 m mu) Q V; for G=m0=1, (R1)-(R2) are IsMovingSolutionOn m mu J z
CONSTANT_SCOPE: none (G, m0, m_i, mu, J and z are free data; no constant is produced)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:rc-coords, stepP:p6:rc-a, stepP:p6:rc-sun, stepP:p6:rc-planets, stepP:p6:rc-vplanet, stepP:p6:rc-vsun, stepP:p6:rc-pack, bpP:p0:movham#movingHamiltonian, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p0:nocoll#NoCollision, bpP:p6:domain, bpP:p0:barycentric#actualMasses, bpP:p0:barycentric#barycentricPositions, bpP:p0:barycentric#barycentricVelocities, bpP:p0:newton#IsNewtonSolution, bpP:p0:d25-newton#IsNewtonSolutionOn, bpP:p0:d25-movsol#IsMovingSolutionOn, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:rc-coords | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L170-L170 | proof step Coordinates of the equations
EDGE: stepP:p6:rc-a | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L172-L172 | proof step (a)
EDGE: stepP:p6:rc-sun | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L173-L173 | proof step (b), Sun
EDGE: stepP:p6:rc-planets | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L174-L174 | proof step (b), planets
EDGE: stepP:p6:rc-vplanet | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L175-L175 | proof step (c), planets
EDGE: stepP:p6:rc-vsun | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L176-L176 | proof step (c), Sun
EDGE: stepP:p6:rc-pack | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L177-L177 | proof step Packaging
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L157-L157 | H_mov
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L157-L157 | X_Hmov in (R2)
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L156-L156 | (R1)
EDGE: bpP:p6:domain | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L159-L159 | differentiability of H_mov at z(t) is automatic
EDGE: bpP:p0:barycentric#actualMasses | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L159-L159 | M=actualMasses
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L159-L159 | Q
EDGE: bpP:p0:barycentric#barycentricVelocities | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L159-L159 | V
EDGE: bpP:p0:newton#IsNewtonSolution | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L165-L165 | all-time frozen predicate for J=R
EDGE: bpP:p0:d25-newton#IsNewtonSolutionOn | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L165-L165 | interval predicate IsNewtonSolutionOn
EDGE: bpP:p0:d25-movsol#IsMovingSolutionOn | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L159-L159 | for G=m0=1, (R1)-(R2) are IsMovingSolutionOn
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction@L154-L154 | data of Part 6
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.reconstruction_all_time (KAM/Planetary/Newtonian/Reconstruction.lean)
LEAN_NOTE: package P6-3; audit-1 mathematics PASS, hygiene closed by P6-3-audit-2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:rc-coords
KIND: step
TITLE: Coordinates of the equations
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-coords@L170-L171
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-coords@L170-L171
CONTRACT_ID: stepP:p6:rc-coords
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); G,m0>0; m_i>0; mu>=0; J subset R arbitrary; z=(q,p):R->Ph_{2n} such that for all t in J: (R1) NoColl(q(t)); (R2) z has derivative X_Hmov(z(t)) at t, H_mov=movingHamiltonian G m0 m mu; M=mass_mu; Q(t)=barycentricPositions m0 m mu q(t); V(t)=barycentricVelocities m0 m mu p(t)
SOURCE_QUANTIFIERS: t in J
SOURCE_CONCLUSION: q_i'=p_i/m_i+(mu/m0)P=:a_i and p_i'=-G m0 m_i g_i(q)+mu G m_i f_i(q)=:b_i at t; bodyVector(q(.),i) and every linear combination of these have the stated derivatives
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:hamilton-eqs, bpP:p6:ext-chain, bpP:p0:body#bodyVector, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:hamilton-eqs | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-coords@L170-L170 | curve statement of the Hamilton equations
EDGE: bpP:p6:ext-chain | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-coords@L171-L171 | derivative of a coordinate projection and of linear combinations
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-coords@L171-L171 | bodyVector is a coordinate projection
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-coords@L170-L170 | g_i, f_i, P
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: rc_coords_moving (KAM/Planetary/Newtonian/HamiltonNodes.lean)
LEAN_NOTE: audit GAP-P6a PASS WITH NOTES (node PASS)
NOTE: -

NODE: stepP:p6:rc-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-a@L172-L172
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-a@L172-L172
CONTRACT_ID: stepP:p6:rc-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); G,m0>0; m_i>0; mu>=0; J subset R arbitrary; z=(q,p):R->Ph_{2n} such that for all t in J: (R1) NoColl(q(t)); (R2) z has derivative X_Hmov(z(t)) at t, H_mov=movingHamiltonian G m0 m mu; M=mass_mu; Q(t)=barycentricPositions m0 m mu q(t); V(t)=barycentricVelocities m0 m mu p(t)
SOURCE_QUANTIFIERS: t in J; i!=j
SOURCE_CONCLUSION: l(Q_i-Q_0)=l(q_i)>0, l(Q_j-Q_i)=l(q_j-q_i)>0, l(Q_0-Q_i)=l(Q_i-Q_0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:bary-algebra, bpP:p0:nocoll#NoCollision, bpP:p6:plane, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:bary-algebra | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-a@L172-L172 | (a): lengths of differences of barycentric positions
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-a@L172-L172 | NoCollision gives positivity
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-a@L172-L172 | l is even
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-a@L172-L172 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: rc_a_lengths (KAM/Planetary/Newtonian/AssemblyNodes.lean)
LEAN_NOTE: audit GAP-P6b round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:rc-sun
KIND: step
TITLE: (b), Sun
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-sun@L173-L173
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-sun@L173-L173
CONTRACT_ID: stepP:p6:rc-sun
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); G,m0>0; m_i>0; mu>=0; J subset R arbitrary; z=(q,p):R->Ph_{2n} such that for all t in J: (R1) NoColl(q(t)); (R2) z has derivative X_Hmov(z(t)) at t, H_mov=movingHamiltonian G m0 m mu; M=mass_mu; Q(t)=barycentricPositions m0 m mu q(t); V(t)=barycentricVelocities m0 m mu p(t)
SOURCE_QUANTIFIERS: t in J
SOURCE_CONCLUSION: Q_0 has derivative -(mu/m0)P=V_0 at t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:rc-coords, bpP:p6:ext-chain, bpP:p6:bary-algebra, bpP:p0:barycentric#barycentricPositions, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:rc-coords | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-sun@L173-L173 | a_i, the derivative of q_i
EDGE: bpP:p6:ext-chain | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-sun@L173-L173 | derivative of a constant multiple of a sum
EDGE: bpP:p6:bary-algebra | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-sun@L173-L173 | (b): V_0=-(mu/m0)P
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-sun@L173-L173 | x_0 formula
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-sun@L173-L173 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: rc_sun_hasDerivAt (KAM/Planetary/Newtonian/AssemblyNodes.lean)
LEAN_NOTE: audit GAP-P6b round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:rc-planets
KIND: step
TITLE: (b), planets
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-planets@L174-L174
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-planets@L174-L174
CONTRACT_ID: stepP:p6:rc-planets
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); G,m0>0; m_i>0; mu>=0; J subset R arbitrary; z=(q,p):R->Ph_{2n} such that for all t in J: (R1) NoColl(q(t)); (R2) z has derivative X_Hmov(z(t)) at t, H_mov=movingHamiltonian G m0 m mu; M=mass_mu; Q(t)=barycentricPositions m0 m mu q(t); V(t)=barycentricVelocities m0 m mu p(t)
SOURCE_QUANTIFIERS: t in J; planet i
SOURCE_CONCLUSION: Q_i has derivative V_i at t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:rc-sun, stepP:p6:rc-coords, bpP:p6:bary-algebra, bpP:p6:conv#data, bpP:p6:ext-chain
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:rc-sun | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-planets@L174-L174 | Q_0'=V_0
EDGE: stepP:p6:rc-coords | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-planets@L174-L174 | q_i'=a_i
EDGE: bpP:p6:bary-algebra | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-planets@L174-L174 | (b): V_i-V_0=a_i
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-planets@L174-L174 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:ext-chain | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-planets@L174-L174 | R3: differentiation of a sum or constant multiple is used in this step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: rc_planets_hasDerivAt (KAM/Planetary/Newtonian/AssemblyNodes.lean)
LEAN_NOTE: audit GAP-P6b round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:rc-vplanet
KIND: step
TITLE: (c), planets
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vplanet@L175-L175
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vplanet@L175-L175
CONTRACT_ID: stepP:p6:rc-vplanet
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); G,m0>0; m_i>0; mu>=0; J subset R arbitrary; z=(q,p):R->Ph_{2n} such that for all t in J: (R1) NoColl(q(t)); (R2) z has derivative X_Hmov(z(t)) at t, H_mov=movingHamiltonian G m0 m mu; M=mass_mu; Q(t)=barycentricPositions m0 m mu q(t); V(t)=barycentricVelocities m0 m mu p(t)
SOURCE_QUANTIFIERS: t in J; planet i
SOURCE_CONCLUSION: V_i has derivative sum_{l!=i} G M_l (Q_l-Q_i)/l(Q_l-Q_i)^3 at t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:rc-coords, stepP:p6:rc-a, bpP:p6:bary-algebra, bpP:p6:ext-sum, bpP:p0:barycentric#actualMasses, bpP:p6:conv#data, bpP:p6:ext-chain
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:rc-coords | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vplanet@L175-L175 | p_i'=b_i
EDGE: stepP:p6:rc-a | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vplanet@L175-L175 | lengths of differences
EDGE: bpP:p6:bary-algebra | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vplanet@L175-L175 | Q_0-Q_i=-q_i and Q_j-Q_i=q_j-q_i
EDGE: bpP:p6:ext-sum | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vplanet@L175-L175 | Fin.sum_univ_succ splitting l=0 and l=succ(j)
EDGE: bpP:p0:barycentric#actualMasses | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vplanet@L175-L175 | M_0=m0, M_j=mu m_j
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vplanet@L175-L175 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:ext-chain | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vplanet@L175-L175 | R3: differentiation of a sum or constant multiple is used in this step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: rc_vplanet_hasDerivAt (KAM/Planetary/Newtonian/AssemblyNodes.lean)
LEAN_NOTE: audit GAP-P6b round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:rc-vsun
KIND: step
TITLE: (c), Sun
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vsun@L176-L176
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vsun@L176-L176
CONTRACT_ID: stepP:p6:rc-vsun
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); G,m0>0; m_i>0; mu>=0; J subset R arbitrary; z=(q,p):R->Ph_{2n} such that for all t in J: (R1) NoColl(q(t)); (R2) z has derivative X_Hmov(z(t)) at t, H_mov=movingHamiltonian G m0 m mu; M=mass_mu; Q(t)=barycentricPositions m0 m mu q(t); V(t)=barycentricVelocities m0 m mu p(t)
SOURCE_QUANTIFIERS: t in J
SOURCE_CONCLUSION: V_0 has derivative sum_{l>=1} G M_l (Q_l-Q_0)/l(Q_l-Q_0)^3 at t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:rc-coords, bpP:p6:action-reaction, bpP:p6:bary-algebra, bpP:p0:barycentric#actualMasses, bpP:p6:conv#data, bpP:p6:ext-chain
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:rc-coords | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vsun@L176-L176 | p_i'=b_i
EDGE: bpP:p6:action-reaction | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vsun@L176-L176 | sum m_i f_i=0
EDGE: bpP:p6:bary-algebra | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vsun@L176-L176 | (a) Q_i-Q_0=q_i and (b) V_0
EDGE: bpP:p0:barycentric#actualMasses | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vsun@L176-L176 | M_l=mu m_l
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vsun@L176-L176 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:ext-chain | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-vsun@L176-L176 | R3: differentiation of a sum or constant multiple is used in this step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: rc_vsun_hasDerivAt (KAM/Planetary/Newtonian/AssemblyNodes.lean)
LEAN_NOTE: audit GAP-P6b round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:rc-pack
KIND: step
TITLE: Packaging
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-pack@L177-L177
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-pack@L177-L177
CONTRACT_ID: stepP:p6:rc-pack
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); G,m0>0; m_i>0; mu>=0; J subset R arbitrary; z=(q,p):R->Ph_{2n} such that for all t in J: (R1) NoColl(q(t)); (R2) z has derivative X_Hmov(z(t)) at t, H_mov=movingHamiltonian G m0 m mu; M=mass_mu; Q(t)=barycentricPositions m0 m mu q(t); V(t)=barycentricVelocities m0 m mu p(t)
SOURCE_QUANTIFIERS: t in J; J=R for the all-time predicate
SOURCE_CONCLUSION: the three clauses are the conjuncts of IsNewtonSolutionOn (G*M) J Q V and, for J=R, of IsNewtonSolution G (actualMasses m0 m mu) Q V; mu=0 included
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:rc-a, stepP:p6:rc-sun, stepP:p6:rc-planets, stepP:p6:rc-vplanet, stepP:p6:rc-vsun, bpP:p0:newton#IsNewtonSolution, bpP:p0:d25-newton#IsNewtonSolutionOn, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:rc-a | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-pack@L177-L177 | clause (a)
EDGE: stepP:p6:rc-sun | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-pack@L177-L177 | clause (b) for the Sun
EDGE: stepP:p6:rc-planets | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-pack@L177-L177 | clause (b) for planets
EDGE: stepP:p6:rc-vplanet | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-pack@L177-L177 | clause (c) for planets
EDGE: stepP:p6:rc-vsun | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-pack@L177-L177 | clause (c) for the Sun
EDGE: bpP:p0:newton#IsNewtonSolution | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-pack@L177-L177 | frozen all-time predicate
EDGE: bpP:p0:d25-newton#IsNewtonSolutionOn | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-pack@L177-L177 | interval predicate with G absorbed in the masses
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rc-pack@L177-L177 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: reconstruction_pack (KAM/Planetary/Newtonian/LeftoverNodes.lean)
LEAN_NOTE: audit GAP-LREF PASS WITH NOTES (bundle export)
NOTE: -

NODE: bpP:p6:units
KIND: claim
TITLE: Units and the D25 predicates
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:units@L179-L181
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:units@L179-L181
CONTRACT_ID: bpP:p6:units
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 6 physical data n>=1, G,m0>0, m_i>0, mu>=0; G=m0=1 for the D25 specialization; the frozen predicates IsMovingSolutionOn (G=m0=1) and IsNewtonSolutionOn (G=1 in the force formula, arbitrary mass array)
SOURCE_QUANTIFIERS: J subset R; m, mu; z
SOURCE_CONCLUSION: general-G application of Proposition reconstruction uses the mass array G*M_k; if z satisfies IsMovingSolutionOn m mu J then IsNewtonSolutionOn (actualMasses 1 m mu) J Q V for Q=barycentricPositions 1 m mu q, V=barycentricVelocities 1 m mu p; J need not be open or connected
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:reconstruction, bpP:p0:d25-movsol#IsMovingSolutionOn, bpP:p0:d25-newton#IsNewtonSolutionOn, bpP:p0:barycentric#actualMasses, bpP:p0:barycentric#barycentricPositions, bpP:p0:barycentric#barycentricVelocities, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:reconstruction | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:units@L180-L180 | the proposition whose normalised application is stated
EDGE: bpP:p0:d25-movsol#IsMovingSolutionOn | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:units@L180-L180 | IsMovingSolutionOn fixes G=m0=1
EDGE: bpP:p0:d25-newton#IsNewtonSolutionOn | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:units@L180-L180 | IsNewtonSolutionOn absorbs G into the mass array
EDGE: bpP:p0:barycentric#actualMasses | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:units@L180-L180 | actualMasses 1 m mu
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:units@L180-L180 | barycentricPositions 1 m mu
EDGE: bpP:p0:barycentric#barycentricVelocities | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:units@L180-L180 | barycentricVelocities 1 m mu
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:units@L180-L180 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-delta-P-h
REVIEWER: sol-delta2-P-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.isNewtonSolutionOn_of_isMovingSolutionOn (KAM/Planetary/Newtonian/Reconstruction.lean)
LEAN_NOTE: package P6-3; audit-1 mathematics PASS, hygiene closed by P6-3-audit-2 PASS WITH NOTES
NOTE: remark kept: consumed by Part 14a stepP:p14:amd-b. Its mention of N:bpN:p3:newton-reduction ("covers only the all-time predicates ... is not needed here") is a does-not-apply comparison and is not an edge.

NODE: bpP:p6:reconstruction-fixed
KIND: proposition
TITLE: Reconstruction: fixed Sun
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed@L183-L189
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed@L190-L192
CONTRACT_ID: bpP:p6:reconstruction-fixed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; G,m0>0; m_i>0; eps in R (overrides the default eps>=0 of bpP:p6:conv#data); J subset R arbitrary; z=(q,p):R->Ph_{2n} with, for every t in J, NoColl(q(t)) and derivative X_Hfix(z(t)) at t; H_fix=fixedHamiltonian G m0 m eps; Q_i=q_i and V_i=p_i/m_i
SOURCE_QUANTIFIERS: G,m0,m_i,eps; J; z; then every t in J
SOURCE_CONCLUSION: for all t in J: l(Q_i(t))>0 for every i; l(Q_j(t)-Q_i(t))>0 for i!=j; Q_i has derivative V_i(t); V_i has derivative -G m0 Q_i/l(Q_i)^3+eps sum_{j!=i} G m_j (Q_j-Q_i)/l(Q_j-Q_i)^3; for J=R this is IsFixedSolution G m0 m eps Q V
CONSTANT_SCOPE: none (free data)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:rf-eq, bpP:p0:fixham#fixedHamiltonian, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p0:nocoll#NoCollision, bpP:p0:fixedsol#IsFixedSolution, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:rf-eq | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed@L191-L191 | proof step Equations
EDGE: bpP:p0:fixham#fixedHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed@L184-L184 | H_fix
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed@L184-L184 | X_Hfix
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed@L184-L184 | NoColl hypothesis
EDGE: bpP:p0:fixedsol#IsFixedSolution | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed@L186-L186 | IsFixedSolution for J=R
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed@L184-L184 | data of Part 6
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.reconstruction_fixed_all_time (KAM/Planetary/Newtonian/Reconstruction.lean)
LEAN_NOTE: package P6-3; audit-1 mathematics PASS, hygiene closed by P6-3-audit-2 PASS WITH NOTES
NOTE: The current L184 has separate universal index quantifiers, matching the frozen predicate. The arbitrary-real-eps application at L191 is exposed by bpP:p6:reconstruction-fixed#real-eps.

NODE: stepP:p6:rf-eq
KIND: step
TITLE: Equations
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rf-eq@L191-L191
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rf-eq@L191-L191
CONTRACT_ID: stepP:p6:rf-eq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; G,m0>0; m_i>0; eps in R (overrides the default eps>=0 of bpP:p6:conv#data); J subset R arbitrary; z=(q,p):R->Ph_{2n} with, for every t in J, NoColl(q(t)) and derivative X_Hfix(z(t)) at t; H_fix=fixedHamiltonian G m0 m eps; Q_i=q_i and V_i=p_i/m_i
SOURCE_QUANTIFIERS: t in J
SOURCE_CONCLUSION: q_i'=p_i/m_i, p_i'=-G m0 m_i g_i+eps G m_i f_i; positivity of lengths; V_i'=-G m0 q_i/l(q_i)^3+eps G f_i(q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:nocoll#NoCollision, bpP:p6:plane, bpP:p0:fixedsol#IsFixedSolution, bpP:p6:conv#data, bpP:p6:reconstruction-fixed#real-eps
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rf-eq@L191-L191 | positivity from NoCollision
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rf-eq@L191-L191 | l is even
EDGE: bpP:p0:fixedsol#IsFixedSolution | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rf-eq@L191-L191 | the displayed expression is the IsFixedSolution clause
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rf-eq@L191-L191 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:reconstruction-fixed#real-eps | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:rf-eq@L191-L191 | R4: missing extension of the fixed-Sun Hamilton equations from eps>=0 to eps in R
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: fixedField_rf_eq (KAM/Planetary/Newtonian/HamiltonNodes.lean)
LEAN_NOTE: audit GAP-P6a PASS WITH NOTES (node PASS)
NOTE: -

NODE: bpP:p6:orbit-transfer
KIND: corollary
TITLE: Orbit transfer for tori
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L194-L202
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L203-L206
CONTRACT_ID: bpP:p6:orbit-transfer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0 unless otherwise stated); d=2n; K:R^d->Ph_{2n}; w in R^d; (a) IsPhysTorus(H_mov,w,K) and NoColl(K(phi)_1) for all phi; (b) IsPhysTorus(H_fix,w,K) and NoColl(K(phi)_1) for all phi; Q=barycentricPositions m0 m mu, V=barycentricVelocities m0 m mu
SOURCE_QUANTIFIERS: n, K, w; then every phi
SOURCE_CONCLUSION: (a) for every phi, IsNewtonSolution G (actualMasses m0 m mu) (t -> Q(K(phi+tw)_1)) (t -> V(K(phi+tw)_2)); (b) IsFixedSolution G m0 m eps (t -> body(K(phi+tw)_1)) (t -> (1/m_i)body(K(phi+tw)_2)) for all phi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:ot-curve, stepP:p6:ot-apply, bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:movham#movingHamiltonian, bpP:p0:fixham#fixedHamiltonian, bpP:p0:nocoll#NoCollision, bpP:p0:newton#IsNewtonSolution, bpP:p0:fixedsol#IsFixedSolution, bpP:p0:barycentric#actualMasses, bpP:p0:barycentric#barycentricPositions, bpP:p0:barycentric#barycentricVelocities, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:ot-curve | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L204-L204 | proof step The curve
EDGE: stepP:p6:ot-apply | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L205-L205 | proof step Apply
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L197-L197 | IsPhysTorus hypothesis
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L197-L197 | H_mov
EDGE: bpP:p0:fixham#fixedHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L200-L200 | H_fix
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L197-L197 | NoColl hypothesis
EDGE: bpP:p0:newton#IsNewtonSolution | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L198-L198 | conclusion (a)
EDGE: bpP:p0:fixedsol#IsFixedSolution | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L200-L200 | conclusion (b)
EDGE: bpP:p0:barycentric#actualMasses | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L198-L198 | actualMasses
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L199-L199 | Q
EDGE: bpP:p0:barycentric#barycentricVelocities | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L199-L199 | V
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:orbit-transfer@L197-L200 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-delta-P-h
REVIEWER: sol-delta2-P-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.orbit_transfer_moving, orbit_transfer_fixed (KAM/Planetary/Newtonian/Reconstruction.lean)
LEAN_NOTE: package P6-3; audit-1 mathematics PASS, hygiene closed by P6-3-audit-2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:ot-curve
KIND: step
TITLE: The curve
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ot-curve@L204-L204
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ot-curve@L204-L204
CONTRACT_ID: stepP:p6:ot-curve
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0 unless otherwise stated); d=2n; K:R^d->Ph_{2n}; w in R^d; (a) IsPhysTorus(H_mov,w,K) and NoColl(K(phi)_1) for all phi; (b) IsPhysTorus(H_fix,w,K) and NoColl(K(phi)_1) for all phi; Q=barycentricPositions m0 m mu, V=barycentricVelocities m0 m mu
SOURCE_QUANTIFIERS: phi; t in R
SOURCE_CONCLUSION: (R1) and (R2) of Prop reconstruction hold for z at every t in R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p6:conv#data, bpP:p0:nocoll#NoCollision
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ot-curve@L204-L204 | clause (viii): s -> K(phi+sw) has derivative X_H at s=t
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ot-curve@L204-L204 | X_H in clause (viii)
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ot-curve@L204-L204 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ot-curve@L204-L204 | R3: R1 is the collision hypothesis evaluated at phi+t w
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: ot_curve (KAM/Planetary/Newtonian/AssemblyNodes.lean)
LEAN_NOTE: audit GAP-P6b round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:ot-apply
KIND: step
TITLE: Apply
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ot-apply@L205-L205
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ot-apply@L205-L205
CONTRACT_ID: stepP:p6:ot-apply
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0 unless otherwise stated); d=2n; K:R^d->Ph_{2n}; w in R^d; (a) IsPhysTorus(H_mov,w,K) and NoColl(K(phi)_1) for all phi; (b) IsPhysTorus(H_fix,w,K) and NoColl(K(phi)_1) for all phi; Q=barycentricPositions m0 m mu, V=barycentricVelocities m0 m mu
SOURCE_QUANTIFIERS: phi
SOURCE_CONCLUSION: IsNewtonSolution (resp. IsFixedSolution) along the orbit
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:ot-curve, bpP:p6:reconstruction, bpP:p6:reconstruction-fixed, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:ot-curve | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ot-apply@L205-L205 | (R1)-(R2) with J=R
EDGE: bpP:p6:reconstruction | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ot-apply@L205-L205 | Proposition reconstruction with J=R
EDGE: bpP:p6:reconstruction-fixed | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ot-apply@L205-L205 | Proposition reconstruction-fixed with J=R for (b)
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ot-apply@L205-L205 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: orbit_transfer_pack (KAM/Planetary/Newtonian/LeftoverNodes.lean)
LEAN_NOTE: audit GAP-LREF PASS WITH NOTES (bundle export)
NOTE: -

NODE: bpP:p6:tube-constants
KIND: definition
TITLE: Axis constants; tube radius; $d$, $D$
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-constants@L210-L216
PROOF_SOURCE: -
CONTRACT_ID: bpP:p6:tube-constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1 as fixed by bpP:p6:conv#data; a in R^n with a_i>0 pairwise distinct (n=2: 0<a_0<a_1); eta>0
SOURCE_QUANTIFIERS: n; a; eta (then the constants a_max, gamma_a, zeta_*, d, D)
SOURCE_CONCLUSION: defines a_max=max a_i, gamma_a=min{min a_i, min_{i!=j}¦a_i-a_j¦}>0 (pair minimum omitted for n=1), zeta_*=min{eta,gamma_a/6}, d=gamma_a/2, D=2a_max+gamma_a; then 0<d<D
CONSTANT_SCOPE: d, D depend only on a (not on eta, G, m0, m, mu, eps); zeta_* only on (a, eta)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:ext-top, bpP:p6:conv#data, bpP:p6:tube-constants#a-max
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:ext-top | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-constants@L212-L212 | finite minima/maxima exist, so gamma_a>0 and a_max are defined
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-constants@L211-L212 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:tube-constants#a-max | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-constants@L212-L212 | R5: a_max is the finite maximum subdefinition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-delta-P-h
REVIEWER: sol-delta2-P-d
LEAN_STATUS: PROVED
LEAN_REF: AxisData, axisMax, axisGap, axisData_canonical, tubeRadius, tubeD, tubeBigD, tubeRadius_pos, tubeD_lt_tubeBigD (KAM/Planetary/Newtonian/Tube.lean)
LEAN_NOTE: audit P6-4 PASS WITH NOTES
NOTE: -

NODE: bpP:p6:tube-geometry
KIND: lemma
TITLE: Tube geometry
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L218-L228
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L229-L235
CONTRACT_ID: bpP:p6:tube-geometry
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G,m0>0; m_i>0; a, eta, zeta_*, d, D as in Definition bpP:p6:tube-constants; 0<zeta<=zeta_*; z=(q,p) in U_zeta (circularTube of radius zeta)
SOURCE_QUANTIFIERS: fixed data and axes; then zeta in (0,zeta_*]; then z in U_zeta
SOURCE_CONCLUSION: (a) U_zeta subset U_{zeta_*} subset U_eta; (b) exists phi in R^n with l(q_i-a_i e(phi_i))<sqrt2 zeta for all i; (c) a_i-sqrt2 zeta<l(q_i)<a_i+sqrt2 zeta and ¦a_i-a_j¦-2sqrt2 zeta<l(q_j-q_i)<a_i+a_j+2sqrt2 zeta; (d) d<=l(q_i)<=D, d<=l(q_j-q_i)<=D, in particular NoColl(q); (e) for every mu>=0, PairBounds(d,D; barycentricPositions m0 m mu q) with the same d,D, and PairBounds(d,D;(0,q_0,...,q_{n-1}))
CONSTANT_SCOPE: d, D depend only on a; zeta_* on (a,eta); none depends on mu, G, m0, m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:tg-a, stepP:p6:tg-b, stepP:p6:tg-c, stepP:p6:tg-d, stepP:p6:tg-e, bpP:p6:tube-constants, bpP:p0:circular#circularTube, bpP:p0:circular#circularPoint, bpP:p0:nocoll#NoCollision, bpP:p0:nocoll#PairBounds, bpP:p0:barycentric#barycentricPositions, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:tg-a | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L230-L230 | proof step (a)
EDGE: stepP:p6:tg-b | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L231-L231 | proof step (b)
EDGE: stepP:p6:tg-c | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L232-L232 | proof step (c)
EDGE: stepP:p6:tg-d | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L233-L233 | proof step (d)
EDGE: stepP:p6:tg-e | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L234-L234 | proof step (e)
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L219-L219 | a, eta, zeta_*, d, D
EDGE: bpP:p0:circular#circularTube | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L219-L219 | U_zeta
EDGE: bpP:p0:circular#circularPoint | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L222-L222 | circ(phi)
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L225-L225 | conclusion NoColl(q)
EDGE: bpP:p0:nocoll#PairBounds | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L226-L226 | conclusion PairBounds
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L226-L226 | barycentric positions
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-geometry@L219-L219 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-delta-P-h
REVIEWER: sol-delta2-P-d
LEAN_STATUS: PROVED
LEAN_REF: circularTube_mono, circularTube_euclidean, circularTube_distances, circularTube_pair_bounds, circularTube_pairBounds_barycentric, circularTube_pairBounds_fixed (KAM/Planetary/Newtonian/Tube.lean)
LEAN_NOTE: audit P6-4 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:tg-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-a@L230-L230
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-a@L230-L230
CONTRACT_ID: stepP:p6:tg-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G,m0>0; m_i>0; a, eta, zeta_*, d, D as in Definition bpP:p6:tube-constants; 0<zeta<=zeta_*; z=(q,p) in U_zeta (circularTube of radius zeta)
SOURCE_QUANTIFIERS: 0<zeta<=zeta_*
SOURCE_CONCLUSION: U_zeta subset U_zeta_* subset U_eta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:circular#circularTube, bpP:p6:tube-constants, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:circular#circularTube | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-a@L230-L230 | tube defined by a strict norm bound, monotone in the radius
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-a@L230-L230 | zeta_*=min{eta,gamma_a/6}
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-a@L230-L230 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: circularTube_mono (KAM/Planetary/Newtonian/Tube.lean)
LEAN_NOTE: audit P6-4 PASS WITH NOTES; named tube-geometry (a)
NOTE: -

NODE: stepP:p6:tg-b
KIND: step
TITLE: (b) Max norm to Euclidean norm
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-b@L231-L231
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-b@L231-L231
CONTRACT_ID: stepP:p6:tg-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G,m0>0; m_i>0; a, eta, zeta_*, d, D as in Definition bpP:p6:tube-constants; 0<zeta<=zeta_*; z=(q,p) in U_zeta (circularTube of radius zeta)
SOURCE_QUANTIFIERS: z in U_zeta
SOURCE_CONCLUSION: exists phi with l(q_i-a_i e(phi_i))<sqrt2 zeta for all i
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:plane, bpP:p0:circular#circularTube, bpP:p0:circular#circularPoint, bpP:p0:body#bodyVector, bpP:p6:conv#data, bpP:p6:tube-constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-b@L231-L231 | Lemma plane(b): l<=sqrt2 ¦.¦_inf
EDGE: bpP:p0:circular#circularTube | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-b@L231-L231 | norm bound defining the tube
EDGE: bpP:p0:circular#circularPoint | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-b@L231-L231 | coordinates of circ(phi)
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-b@L231-L231 | q_(i,c) coordinates
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-b@L231-L231 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-b@L231-L231 | R1: uses the chosen axes or tube constants zeta_*, d, D directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: circularTube_euclidean (KAM/Planetary/Newtonian/Tube.lean)
LEAN_NOTE: audit P6-4 PASS WITH NOTES; named tube-geometry (b)
NOTE: -

NODE: stepP:p6:tg-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-c@L232-L232
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-c@L232-L232
CONTRACT_ID: stepP:p6:tg-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G,m0>0; m_i>0; a, eta, zeta_*, d, D as in Definition bpP:p6:tube-constants; 0<zeta<=zeta_*; z=(q,p) in U_zeta (circularTube of radius zeta)
SOURCE_QUANTIFIERS: z in U_zeta; i!=j
SOURCE_CONCLUSION: distance bounds (c)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:tg-b, bpP:p6:ext-tri, bpP:p6:plane, bpP:p0:circular#circularPoint, bpP:p6:conv#data, bpP:p6:tube-constants
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:tg-b | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-c@L232-L232 | l(q_i-u_i)<sqrt2 zeta
EDGE: bpP:p6:ext-tri | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-c@L232-L232 | reverse triangle inequality
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-c@L232-L232 | Lemma plane(a): triangle inequality
EDGE: bpP:p0:circular#circularPoint | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-c@L232-L232 | l(u_i)=a_i
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-c@L232-L232 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-c@L232-L232 | R1: uses the chosen axes or tube constants zeta_*, d, D directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: circularTube_distances (KAM/Planetary/Newtonian/Tube.lean)
LEAN_NOTE: audit P6-4 PASS WITH NOTES; named tube-geometry (c)
NOTE: -

NODE: stepP:p6:tg-d
KIND: step
TITLE: (d) Numerics
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-d@L233-L233
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-d@L233-L233
CONTRACT_ID: stepP:p6:tg-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G,m0>0; m_i>0; a, eta, zeta_*, d, D as in Definition bpP:p6:tube-constants; 0<zeta<=zeta_*; z=(q,p) in U_zeta (circularTube of radius zeta)
SOURCE_QUANTIFIERS: z in U_zeta
SOURCE_CONCLUSION: d<=l(q_i)<=D, d<=l(q_j-q_i)<=D, hence NoColl(q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:tg-c, bpP:p6:tube-constants, bpP:p0:nocoll#NoCollision, bpP:p6:plane, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:tg-c | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-d@L233-L233 | the distance bounds (c)
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-d@L233-L233 | definitions of gamma_a, d, D
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-d@L233-L233 | NoColl(q)
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-d@L233-L233 | l(q_i-q_j)=l(q_j-q_i)
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-d@L233-L233 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: circularTube_pair_bounds (KAM/Planetary/Newtonian/Tube.lean)
LEAN_NOTE: audit P6-4 PASS WITH NOTES; named tube-geometry (d)
NOTE: -

NODE: stepP:p6:tg-e
KIND: step
TITLE: (e) Exact $\mu$-independence
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-e@L234-L234
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-e@L234-L234
CONTRACT_ID: stepP:p6:tg-e
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G,m0>0; m_i>0; a, eta, zeta_*, d, D as in Definition bpP:p6:tube-constants; 0<zeta<=zeta_*; z=(q,p) in U_zeta (circularTube of radius zeta)
SOURCE_QUANTIFIERS: z in U_zeta; every mu>=0
SOURCE_CONCLUSION: PairBounds(d,D;Q) for Q=barycentricPositions m0 m mu q, and for the fixed-Sun configuration (0,q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:bary-algebra, stepP:p6:tg-d, bpP:p0:nocoll#PairBounds, bpP:p0:barycentric#barycentricPositions, bpP:p6:plane, bpP:p6:conv#data, bpP:p6:tube-constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:bary-algebra | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-e@L234-L234 | (a): l(Q_i-Q_0)=l(q_i), l(Q_j-Q_i)=l(q_j-q_i) for all mu
EDGE: stepP:p6:tg-d | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-e@L234-L234 | bounds (d) for q
EDGE: bpP:p0:nocoll#PairBounds | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-e@L234-L234 | PairBounds asks d<=l(Q_l-Q_k)<=D for all ordered pairs
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-e@L234-L234 | barycentricPositions
EDGE: bpP:p6:plane | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-e@L234-L234 | evenness of l
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-e@L234-L234 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:tg-e@L234-L234 | R1: uses the chosen axes or tube constants zeta_*, d, D directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: circularTube_pairBounds_barycentric, circularTube_pairBounds_fixed (KAM/Planetary/Newtonian/Tube.lean)
LEAN_NOTE: audit P6-4 PASS WITH NOTES; named tube-geometry (e)
NOTE: -

NODE: bpP:p6:newton-in-tube
KIND: corollary
TITLE: Newton solutions staying in the tube, on any set of times
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:newton-in-tube@L240-L242
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:newton-in-tube@L243-L245
CONTRACT_ID: bpP:p6:newton-in-tube
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); z:R->Ph_{2n}; J subset R; mu>=0; 0<zeta<=zeta_*; for all t in J: z(t) in U_zeta and z has derivative X_Hmov(z(t)) at t
SOURCE_QUANTIFIERS: data and axes (tube-constants); J; z; mu; zeta; then every t in J
SOURCE_CONCLUSION: (R1)-(R2) of Prop reconstruction hold; IsNewtonSolutionOn (G*mass_mu) J Q V holds; PairBounds(d,D;Q(t)) for every t in J with d,D of Def tube-constants; the analogous statement holds for H_fix with Prop reconstruction-fixed
CONSTANT_SCOPE: d, D, zeta_* from tube-constants (depend on a, eta only)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:reconstruction, bpP:p6:reconstruction-fixed, bpP:p6:tube-constants, bpP:p6:tube-geometry, bpP:p0:movham#movingHamiltonian, bpP:p0:circular#circularTube, bpP:p0:d25-newton#IsNewtonSolutionOn, bpP:p0:nocoll#PairBounds, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:reconstruction | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:newton-in-tube@L241-L241 | (R1)-(R2) give IsNewtonSolutionOn
EDGE: bpP:p6:reconstruction-fixed | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:newton-in-tube@L241-L241 | analogous statement for H_fix
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:newton-in-tube@L241-L241 | zeta_*, d, D
EDGE: bpP:p6:tube-geometry | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:newton-in-tube@L244-L244 | (d) gives (R1); (e) gives the pair bounds
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:newton-in-tube@L241-L241 | H_mov
EDGE: bpP:p0:circular#circularTube | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:newton-in-tube@L241-L241 | U_zeta
EDGE: bpP:p0:d25-newton#IsNewtonSolutionOn | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:newton-in-tube@L241-L241 | conclusion IsNewtonSolutionOn
EDGE: bpP:p0:nocoll#PairBounds | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:newton-in-tube@L241-L241 | conclusion PairBounds
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:newton-in-tube@L241-L241 | G, m0, m_i>0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: PROVED
LEAN_REF: newton_in_tube, fixed_in_tube (KAM/Planetary/Newtonian/Tube.lean)
LEAN_NOTE: audit P6-4 PASS WITH NOTES; newton_in_tube applies reconstruction (P6-3, audit FAIL on hygiene only)
NOTE: -

NODE: bpP:p6:measure-positive
KIND: lemma
TITLE: $0<\meas S<\infty$
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:measure-positive@L249-L255
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:measure-positive@L256-L259
CONTRACT_ID: bpP:p6:measure-positive
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1 as fixed by bpP:p6:conv#data; G,m0>0; m_i>0; a_i>0; eta>0; (b) Psi a c-chart on an open O subset Ph_{2n} with lattice compatibility (Q1)-(Q2) of Theorem bpP:p1:torus-transport for sigma_k=0 (d=2n); A subset O Lebesgue measurable with A+iota_k=A for all k in Z^{2n} and meas A>0
SOURCE_QUANTIFIERS: G,m0,m_i,a_i,eta; then (a) every S subset U_eta; (b) Psi, O, A
SOURCE_CONCLUSION: (a) U_eta is bounded (¦z_1¦_inf<a_max+eta, ¦z_2¦_inf<P_max+eta, P_max=max m_i sqrt(G m0/a_i)); every S subset U_eta has meas S<=(2(a_max+eta))^{2n}(2(P_max+eta))^{2n}<infinity; (b) S=Psi(A) is measurable (Borel if A is Borel) and 0<meas S=c^{2n} meas(A cap Q) (Q unit cell); if S subset U_eta then 0<meas S<infinity
CONSTANT_SCOPE: none beyond the displayed bounds (a_max, P_max depend on a, m, G, m0)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:mp-a, stepP:p6:mp-b, bpP:p1:torus-transport, bpP:p1:liouville-lattice, bpP:p1:chart, bpP:p0:circular#circularTube, bpP:p0:circular#circularPoint, bpP:p6:conv#data, bpP:p6:tube-constants#a-max
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:mp-a | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:measure-positive@L257-L257 | proof step (a)
EDGE: stepP:p6:mp-b | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:measure-positive@L258-L258 | proof step (b)
EDGE: bpP:p1:torus-transport | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:measure-positive@L253-L253 | lattice compatibility (Q1)-(Q2)
EDGE: bpP:p1:liouville-lattice | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:measure-positive@L253-L253 | unit-cell measure formula
EDGE: bpP:p1:chart | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:measure-positive@L253-L253 | c-chart Psi
EDGE: bpP:p0:circular#circularTube | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:measure-positive@L252-L252 | U_eta
EDGE: bpP:p0:circular#circularPoint | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:measure-positive@L252-L252 | circ(phi)
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:measure-positive@L250-L252 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:tube-constants#a-max | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:measure-positive@L252-L252 | R5: uses a_max=max_i a_i, without assuming pairwise distinct axes or the gap constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-delta-P-h
REVIEWER: sol-delta2-P-d
LEAN_STATUS: PROVED
LEAN_REF: measure_positive (KAM/Planetary/Newtonian/AssemblyNodes.lean)
LEAN_NOTE: audit GAP-P6b round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:mp-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-a@L257-L257
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-a@L257-L257
CONTRACT_ID: stepP:p6:mp-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; G,m0>0; m_i>0; a_i>0; eta>0; z in U_eta; circ is the frozen reference configuration
SOURCE_QUANTIFIERS: z in U_eta
SOURCE_CONCLUSION: U_eta lies in the stated box; every subset has measure <= box volume
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:circular#circularPoint, bpP:p0:circular#circularTube, bpP:p6:ext-meas, bpP:p6:conv#data, bpP:p6:tube-constants#a-max
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:circular#circularPoint | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-a@L257-L257 | coordinates of circ(phi)
EDGE: bpP:p0:circular#circularTube | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-a@L257-L257 | z in U_eta: ¦¦z-circ(phi)¦¦<eta
EDGE: bpP:p6:ext-meas | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-a@L257-L257 | bounded sets have finite measure; box volume; monotonicity
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-a@L257-L257 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:tube-constants#a-max | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-a@L257-L257 | R5: uses a_max=max_i a_i, without assuming pairwise distinct axes or the gap constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: mp_a_box (KAM/Planetary/Newtonian/AssemblyNodes.lean)
LEAN_NOTE: audit GAP-P6b round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:mp-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-b@L258-L258
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-b@L258-L258
CONTRACT_ID: stepP:p6:mp-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1 as fixed by bpP:p6:conv#data; G,m0>0; m_i>0; a_i>0; eta>0; (b) Psi a c-chart on an open O subset Ph_{2n} with lattice compatibility (Q1)-(Q2) of Theorem bpP:p1:torus-transport for sigma_k=0 (d=2n); A subset O Lebesgue measurable with A+iota_k=A for all k in Z^{2n} and meas A>0
SOURCE_QUANTIFIERS: Psi, O, A as in (b)
SOURCE_CONCLUSION: measurability, formula, 0<meas Psi(A) iff 0<meas A; and with (a), 0<meas S<infinity for S subset U_eta
CONSTANT_SCOPE: none beyond the displayed bounds (a_max, P_max depend on a, m, G, m0)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:liouville-lattice, stepP:p6:mp-a, bpP:p6:conv#data, bpP:p1:chart
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:liouville-lattice | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-b@L258-L258 | measurability, formula and positivity
EDGE: stepP:p6:mp-a | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-b@L258-L258 | finiteness from (a)
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-b@L258-L258 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p1:chart | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:mp-b@L258-L258 | R1: the conditional measure result uses the source c-chart package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-delta-P-h
REVIEWER: sol-delta2-P-d
LEAN_STATUS: PROVED
LEAN_REF: mp_b_measure, mp_b_measurableSet (KAM/Planetary/Newtonian/AssemblyNodes.lean)
LEAN_NOTE: audit GAP-P6b round 2 PASS WITH NOTES; audit-1 F1 closed
NOTE: -

NODE: bpP:p6:movkol-assembly
KIND: proposition
TITLE: Physical clauses of $\operatorname{MovKol}$
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:movkol-assembly@L266-L273
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:movkol-assembly@L274-L279
CONTRACT_ID: bpP:p6:movkol-assembly
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); a_i>0 pairwise distinct; eta>0; zeta_*,d,D as in Def tube-constants; mu>=0; S subset Ph_{2n} with (S1) MeasurableSet S (Borel) and S subset U_{zeta_*}; (S2) every z in S has w in R^{2n}, K, theta with K(theta)=z, K(R^{2n}) subset S and IsPhysTorus(H_mov,w,K)
SOURCE_QUANTIFIERS: G,m0,m,a,eta; mu; S; then (conclusion)
SOURCE_CONCLUSION: MovKol(G,m0,m,a,mu,eta,d,D,S) (Definition bpP:p0:movkol)
CONSTANT_SCOPE: d, D depend on a only (may be fixed before mu_0 and mu); zeta_* on (a,eta)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:ma-tube, stepP:p6:ma-coll, stepP:p6:ma-newton, stepP:p6:ma-pair, bpP:p6:tube-constants, bpP:p0:movkol#MovingKolmogorovSet, bpP:p0:circular#circularTube, bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:movham#movingHamiltonian, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:ma-tube | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:movkol-assembly@L275-L275 | proof step Tube and set
EDGE: stepP:p6:ma-coll | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:movkol-assembly@L276-L276 | proof step Collision
EDGE: stepP:p6:ma-newton | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:movkol-assembly@L277-L277 | proof step Newton
EDGE: stepP:p6:ma-pair | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:movkol-assembly@L278-L278 | proof step Pair bounds
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:movkol-assembly@L267-L267 | zeta_*, d, D
EDGE: bpP:p0:movkol#MovingKolmogorovSet | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:movkol-assembly@L272-L272 | conclusion MovKol
EDGE: bpP:p0:circular#circularTube | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:movkol-assembly@L269-L269 | U_zeta_*
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:movkol-assembly@L270-L270 | IsPhysTorus in (S2)
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:movkol-assembly@L270-L270 | H_mov
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:movkol-assembly@L267-L267 | data of Part 6
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: PROVED
LEAN_REF: movingKolmogorovSet_of_tube (KAM/Planetary/Newtonian/Assembly.lean)
LEAN_NOTE: audit P6-5 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:ma-tube
KIND: step
TITLE: Tube and set
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-tube@L275-L275
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-tube@L275-L275
CONTRACT_ID: stepP:p6:ma-tube
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); a_i>0 pairwise distinct; eta>0; zeta_*,d,D as in Def tube-constants; mu>=0; S subset Ph_{2n} with (S1) MeasurableSet S (Borel) and S subset U_{zeta_*}; (S2) every z in S has w in R^{2n}, K, theta with K(theta)=z, K(R^{2n}) subset S and IsPhysTorus(H_mov,w,K)
SOURCE_QUANTIFIERS: z in S
SOURCE_CONCLUSION: S subset U_eta and S measurable
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:tube-geometry, bpP:p0:circular#circularTube, bpP:p6:conv#data, bpP:p6:tube-constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:tube-geometry | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-tube@L275-L275 | (a): U_zeta_* subset U_eta
EDGE: bpP:p0:circular#circularTube | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-tube@L275-L275 | tube clause of MovKol
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-tube@L275-L275 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-tube@L275-L275 | R1: uses the chosen axes or tube constants zeta_*, d, D directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: ma_tube (KAM/Planetary/Newtonian/AssemblyNodes.lean)
LEAN_NOTE: audit GAP-P6b round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:ma-coll
KIND: step
TITLE: Collision
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-coll@L276-L276
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-coll@L276-L276
CONTRACT_ID: stepP:p6:ma-coll
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); a_i>0 pairwise distinct; eta>0; zeta_*,d,D as in Def tube-constants; mu>=0; S subset Ph_{2n} with (S1) MeasurableSet S (Borel) and S subset U_{zeta_*}; (S2) every z in S has w in R^{2n}, K, theta with K(theta)=z, K(R^{2n}) subset S and IsPhysTorus(H_mov,w,K)
SOURCE_QUANTIFIERS: z in S; phi in R^{2n}
SOURCE_CONCLUSION: NoColl(K(phi)_1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:tube-geometry, bpP:p0:nocoll#NoCollision, bpP:p6:conv#data, bpP:p6:tube-constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:tube-geometry | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-coll@L276-L276 | (d): tube points are collision free
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-coll@L276-L276 | NoColl clause
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-coll@L276-L276 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-coll@L276-L276 | R1: uses the chosen axes or tube constants zeta_*, d, D directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: ma_coll (KAM/Planetary/Newtonian/AssemblyNodes.lean)
LEAN_NOTE: audit GAP-P6b round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p6:ma-newton
KIND: step
TITLE: Newton
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-newton@L277-L277
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-newton@L277-L277
CONTRACT_ID: stepP:p6:ma-newton
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); a_i>0 pairwise distinct; eta>0; zeta_*,d,D as in Def tube-constants; mu>=0; S subset Ph_{2n} with (S1) MeasurableSet S (Borel) and S subset U_{zeta_*}; (S2) every z in S has w in R^{2n}, K, theta with K(theta)=z, K(R^{2n}) subset S and IsPhysTorus(H_mov,w,K)
SOURCE_QUANTIFIERS: z in S; phi
SOURCE_CONCLUSION: IsNewtonSolution G (actualMasses m0 m mu) of the orbit through K(phi)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:orbit-transfer, stepP:p6:ma-coll, bpP:p0:phystorus#IsPhysicalTorus, bpP:p6:conv#data, bpP:p6:tube-constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:orbit-transfer | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-newton@L277-L277 | Corollary (a)
EDGE: stepP:p6:ma-coll | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-newton@L277-L277 | its hypothesis NoColl(K(phi)_1)
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-newton@L277-L277 | IsPhysTorus in (S2)
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-newton@L277-L277 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-newton@L277-L277 | R1: uses the chosen axes or tube constants zeta_*, d, D directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: ma_newton (KAM/Planetary/Newtonian/AssemblyNewtonNodes.lean)
LEAN_NOTE: audit GAP-PX PASS WITH NOTES
NOTE: -

NODE: stepP:p6:ma-pair
KIND: step
TITLE: Pair bounds
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-pair@L278-L278
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-pair@L278-L278
CONTRACT_ID: stepP:p6:ma-pair
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p6:conv#data (n>=1; G,m0>0; m_i>0; mu,eps>=0; planar length l; collision-free set W); a_i>0 pairwise distinct; eta>0; zeta_*,d,D as in Def tube-constants; mu>=0; S subset Ph_{2n} with (S1) MeasurableSet S (Borel) and S subset U_{zeta_*}; (S2) every z in S has w in R^{2n}, K, theta with K(theta)=z, K(R^{2n}) subset S and IsPhysTorus(H_mov,w,K)
SOURCE_QUANTIFIERS: z in S; phi; t
SOURCE_CONCLUSION: PairBounds(d,D;barycentric positions of K(phi+tw)_1) for every orbit point
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:tube-geometry, bpP:p0:nocoll#PairBounds, bpP:p6:conv#data, bpP:p6:tube-constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:tube-geometry | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-pair@L278-L278 | (e) at K(phi)
EDGE: bpP:p0:nocoll#PairBounds | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-pair@L278-L278 | PairBounds clause
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-pair@L278-L278 | R1: direct use of the Part 6 data (n, positive masses, physical parameters, W or force/block notation)
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#stepP:p6:ma-pair@L278-L278 | R1: uses the chosen axes or tube constants zeta_*, d, D directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: ma_pair (KAM/Planetary/Newtonian/AssemblyNodes.lean)
LEAN_NOTE: audit GAP-P6b round 2 PASS WITH NOTES
NOTE: -

NODE: bpP:p6:conv#data
KIND: definition
TITLE: Conventions of Part 6 (data, W, g_i, f_i)
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:conv#data@L20-L24
PROOF_SOURCE: -
CONTRACT_ID: bpP:p6:conv#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; G,m0>0; m_i>0 (i<n); mu,eps>=0 unless said otherwise; l is the planar length (Definition bpP:p0:plane); q_i=q^(i), p_i=p^(i) in R^2, P=sum_i p_i
SOURCE_QUANTIFIERS: n; G, m0; m_i; mu, eps (fixed in the whole part); q,p in R^{2n}
SOURCE_CONCLUSION: defines the collision-free phase set W={(q,p) in Ph_{2n}: NoColl(q)}, the force kernels g_i(q)=q_i/l(q_i)^3 and f_i(q)=sum_{j!=i} m_j (q_j-q_i)/l(q_j-q_i)^3 for NoColl(q), and the indexing planet i <-> succ(i), Sun <-> 0 in Fin(n+1)
CONSTANT_SCOPE: none (all of G, m0, m_i, mu, eps, n are free data of the part)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:plane#planeLength, bpP:p0:nocoll#NoCollision, bpP:p0:phase#Phase, bpP:p0:body#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:conv#data@L20-L20 | l is the planar length (planeLength)
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:conv#data@L21-L21 | W is defined by NoColl
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:conv#data@L21-L21 | W is a subset of the phase space Ph_{2n}
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:conv#data@L20-L20 | q_i = q^(i) is the body block of q (bodyVector)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p6
REVIEWER: sol-review-P-h
LEAN_STATUS: PROVED
LEAN_REF: collisionFreeDomain, gKernel, fKernel, ofBodies (KAM/Planetary/Newtonian/Models.lean)
LEAN_NOTE: audit P6-1 PASS WITH NOTES
NOTE: created from p6:prose-L20-L24 (SPEC section data); consumers: domain, split, action-reaction, hamilton-eqs and steps, bary-algebra, reconstruction(-fixed) and steps, newton-in-tube

NODE: bpP:p6:tube-constants#a-max
KIND: definition
TITLE: Finite maximum of the axes
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-constants#a-max@L212-L212
PROOF_SOURCE: -
CONTRACT_ID: bpP:p6:tube-constants#a-max
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; a in R^n (typing data for the maximum notation)
SOURCE_QUANTIFIERS: n; a
SOURCE_CONCLUSION: defines a_max=max_i a_i
CONSTANT_SCOPE: a_max depends only on a
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:ext-top, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:ext-top | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-constants#a-max@L212-L212 | finite nonempty maxima exist
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:tube-constants#a-max@L212-L212 | the part fixes n>=1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: axisMax (KAM/Planetary/Newtonian/Tube.lean)
LEAN_NOTE: audit P6-4 PASS WITH NOTES
NOTE: Definitional projection of the displayed a_max notation. Unlike gamma_a, this maximum is meaningful without pairwise distinctness; measure-positive(a) uses only this notation, not the distinct-axis bounds. No new estimate or hypothesis is introduced.

NODE: bpP:p6:reconstruction-fixed#real-eps
KIND: step
TITLE: Unpaid arbitrary-real-epsilon Hamilton-equation bridge
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed#real-eps@L191-L191
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed#real-eps@L191-L191
CONTRACT_ID: bpP:p6:reconstruction-fixed#real-eps
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; G,m0>0; m_i>0; eps in R (overrides the default eps>=0 of bpP:p6:conv#data); J subset R arbitrary; z=(q,p):R->Ph_{2n} with, for every t in J, NoColl(q(t)) and derivative X_Hfix(z(t)) at t; H_fix=fixedHamiltonian G m0 m eps; Q_i=q_i and V_i=p_i/m_i
SOURCE_QUANTIFIERS: n,G,m0,m; eps in R; J; z; t in J
SOURCE_CONCLUSION: the fixed-Sun derivative hypothesis implies q_i'=p_i/m_i and p_i'=-G m0 m_i g_i+eps G m_i f_i for every real eps, including eps<0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p6:hamilton-eqs, bpP:p6:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p6:hamilton-eqs | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed#real-eps@L191-L191 | cited formula is available with the default eps>=0
EDGE: bpP:p6:conv#data | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:reconstruction-fixed#real-eps@L191-L191 | supplies the kernels and the default parameter scope
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-h
REVIEWER: sol-delta-P-h
LEAN_STATUS: PROVED
LEAN_REF: fixedField_equations (KAM/Planetary/Newtonian/HamiltonNodes.lean)
LEAN_NOTE: audit GAP-P6a PASS WITH NOTES (node PASS)
NOTE: SOURCE_GAP: L184 explicitly permits eps in R, but hamilton-eqs at L82-L92 inherits eps>=0 from L20 and does not state the negative-eps case. L191 applies that result without providing the extension. The algebra suggests an extension, but this review does not supply it. Preserve the arbitrary-real-eps source contract.

NODE: bpP:p6:fixkol-assembly
KIND: proposition
TITLE: Physical clauses of $\operatorname{FixKol}$
STATEMENT_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:fixkol-assembly@L281-L283
PROOF_SOURCE: blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:fixkol-assembly@L282-L282
CONTRACT_ID: bpP:p6:fixkol-assembly
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G, m0 > 0; m_i > 0; a_i > 0 pairwise distinct; eta > 0; zeta_*, d, D of bpP:p6:tube-constants; eps in R (in place of mu); S in Ph(2n) with (S1) S measurable (Borel) and S in U_zeta_*; (S2) every z in S has w in R^2n, K, theta with K(theta) = z, K(R^2n) in S and IsPhysTorus(H_fix, w, K), H_fix = fixedHamiltonian (the hypotheses of bpP:p6:movkol-assembly with H_fix and eps in place of H_mov and mu)
SOURCE_QUANTIFIERS: data (G, m0, m, a, eta) and zeta_*, d, D first; then eps and S
SOURCE_CONCLUSION: FixKol(G, m0, m, a, eps, eta, d, D, S) holds
CONSTANT_SCOPE: d, D depend on a only (zeta_* on (a, eta)); the dependence on the coupling is confined to (S1)-(S2)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p6:ma-tube, stepP:p6:ma-coll, stepP:p6:ma-pair, bpP:p6:orbit-transfer, bpP:p6:tube-geometry, bpP:p6:tube-constants, bpP:p0:fixkol#FixedKolmogorovSet, bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:fixham#fixedHamiltonian
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p6:ma-tube | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:fixkol-assembly@L282-L282 | the proof is that of Prop movkol-assembly: tube and set (S subset U_zeta_* subset U_eta, measurability)
EDGE: stepP:p6:ma-coll | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:fixkol-assembly@L282-L282 | collision-freeness NoColl by tube-geometry (d), replayed
EDGE: stepP:p6:ma-pair | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:fixkol-assembly@L282-L282 | pair bounds by tube-geometry (e), replayed
EDGE: bpP:p6:orbit-transfer | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:fixkol-assembly@L282-L282 | Cor orbit-transfer (b) replaces (a): IsFixedSol from the physical torus
EDGE: bpP:p6:tube-geometry | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:fixkol-assembly@L282-L282 | the fixed-Sun case of Lemma tube-geometry (e)
EDGE: bpP:p6:tube-constants | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:fixkol-assembly@L282-L282 | zeta_*, d, D of the common hypotheses
EDGE: bpP:p0:fixkol#FixedKolmogorovSet | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:fixkol-assembly@L281-L281 | FixKol in the conclusion
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:fixkol-assembly@L282-L282 | IsPhysTorus in (S2)
EDGE: bpP:p0:fixham#fixedHamiltonian | blueprint-P/parts/p6-newtonian-models.tex#bpP:p6:fixkol-assembly@L282-L282 | H_fix
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: writer-pfixed-revision+sonnet-extract-pfixed
REVIEWER: sol-review-P-w
LEAN_STATUS: PROVED
LEAN_REF: fixedKolmogorovSet_of_tube (KAM/Planetary/Newtonian/Assembly.lean)
LEAN_NOTE: audit P6-5 PASS WITH NOTES
NOTE: restored by the P-FIXED revision (was EXCLUDED as P-FIXED-only); consumers stepP:p13:n2-phys, stepP:p13:ng-phys, Part 11 L240; proof inline (L282); source fields filled by sonnet-extract-pfixed
