NODE: bpP:p4:ext-tonelli
KIND: external
TITLE: Tonelli
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:ext-tonelli@L11-L11
PROOF_SOURCE: -
CONTRACT_ID: bpP:p4:ext-tonelli
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: R subset R^N Borel; j <= N; every section of R along the j-th coordinate (other coordinates fixed) has outer measure <= delta; the projection of R forgetting the j-th coordinate lies in a set of measure <= P
SOURCE_QUANTIFIERS: N, R, j, delta, P given; (second sentence) any set of diameter <= delta in R
SOURCE_CONCLUSION: meas R <= delta*P; a set of diameter <= delta in R has outer measure <= delta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p4:ext-deriv
KIND: external
TITLE: bpP:p4:ext-deriv
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:ext-deriv@L13-L13
PROOF_SOURCE: -
CONTRACT_ID: bpP:p4:ext-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f real analytic on an open set (first sentence); f of class C^1 (second sentence)
SOURCE_QUANTIFIERS: f and its open domain given
SOURCE_CONCLUSION: the derivative of a real analytic function on an open set is real analytic (hence C^1); a C^1 function is continuously differentiable and locally Lipschitz
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p4:ext-conn
KIND: external
TITLE: bpP:p4:ext-conn
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:ext-conn@L14-L14
PROOF_SOURCE: -
CONTRACT_ID: bpP:p4:ext-conn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V subset R^a; C a connected set meeting both V and its complement
SOURCE_QUANTIFIERS: V, C given
SOURCE_CONCLUSION: C meets the boundary of V
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpP:p4:collar
KIND: lemma
TITLE: Collar
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:collar@L22-L29
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:collar@L30-L37
CONTRACT_ID: bpP:p4:collar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V subset R^a open, connected, bounded; A, d > 0 with the collar bound meas{I: exists J in boundary V, ¦I-J¦ < t} <= A t for 0 < t < d (hboundary); D_t and N_s as in bpP:p4:conv#data; max norm
SOURCE_QUANTIFIERS: V, A, d fixed (data of bpP:p0:pg); then (a) t > 0, (b) 0 < t < d, (c) 0 < s < t (and s < t < d for the measure bound)
SOURCE_CONCLUSION: (a) D_t is compact, D_t subset V and V minus D_t = {I in V: dist(I, boundary V) < t}; (b) meas(V minus D_t) <= A t, hence meas D_t >= meas V - A t; (c) N_s(D_t) subset V and N_s(D_t) minus D_t subset V minus D_t, so meas(N_s(D_t) minus D_t) <= A t
CONSTANT_SCOPE: none (A, d from the data)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:conv#data, stepP:p4:co-compact, stepP:p4:co-meas, stepP:p4:co-nbhd
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:conv#data | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:collar@L24-L26 | definitions of D_t and N_s, and the hypothesis hboundary used in (b)
EDGE: stepP:p4:co-compact | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:collar@L31-L31 | proof step (a)
EDGE: stepP:p4:co-meas | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:collar@L33-L33 | proof step (b)
EDGE: stepP:p4:co-nbhd | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:collar@L35-L35 | proof step (c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: collar, ext_conn, realNbhd_joinedActions, domain_collar_helper (KAM/Planetary/PGMeasure/Collar.lean)
LEAN_NOTE: audit P4-CO PASS WITH NOTES (audit 1 FAIL hygiene only, fixed by orchestrator addendum)
NOTE: -

NODE: stepP:p4:co-compact
KIND: step
TITLE: (a) Compact
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:co-compact@L31-L32
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:co-compact@L31-L32
CONTRACT_ID: stepP:p4:co-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: t > 0; V open and bounded; D_t as in bpP:p4:conv#data; continuity of the distance to the boundary
SOURCE_QUANTIFIERS: t > 0 given
SOURCE_CONCLUSION: D_t is bounded and closed (so compact), D_t subset V, and V minus D_t = {I in V: dist(I, boundary V) < t} (by definition)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:conv#data | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:co-compact@L32-L32 | definition of D_t
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: collar (KAM/Planetary/PGMeasure/Collar.lean)
LEAN_NOTE: audit P4-CO PASS WITH NOTES (audit 1 FAIL hygiene only, fixed by orchestrator addendum); named by audit
NOTE: -

NODE: stepP:p4:co-meas
KIND: step
TITLE: (b) Measure
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:co-meas@L33-L34
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:co-meas@L33-L34
CONTRACT_ID: stepP:p4:co-meas
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < t < d; the collar bound hboundary; D_t; monotonicity and subadditivity of meas
SOURCE_QUANTIFIERS: 0 < t < d
SOURCE_CONCLUSION: V minus D_t lies in {I: exists J in boundary V, ¦I-J¦ < t}, so meas(V minus D_t) <= A t and meas D_t >= meas V - A t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:conv#data, K:bp:p1:ext-lebesgue
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:conv#data | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:co-meas@L34-L34 | the hypothesis hboundary and the set D_t
EDGE: K:bp:p1:ext-lebesgue | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:co-meas@L34-L34 | meas V <= meas D_t + meas(V minus D_t) (monotone, subadditive)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: collar (KAM/Planetary/PGMeasure/Collar.lean)
LEAN_NOTE: audit P4-CO PASS WITH NOTES (audit 1 FAIL hygiene only, fixed by orchestrator addendum); named by audit
NOTE: -

NODE: stepP:p4:co-nbhd
KIND: step
TITLE: (c) Neighbourhoods
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:co-nbhd@L35-L36
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:co-nbhd@L35-L36
CONTRACT_ID: stepP:p4:co-nbhd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < s < t; J in D_t; B = {x: ¦x-J¦ < s}; V open; connected set meeting V and its complement meets the boundary
SOURCE_QUANTIFIERS: 0 < s < t, J in D_t
SOURCE_CONCLUSION: B is convex hence connected, contains J in V and misses the boundary of V, so B subset V; hence N_s(D_t) subset V and N_s(D_t) minus D_t subset V minus D_t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:ext-conn, bpP:p4:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:ext-conn | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:co-nbhd@L36-L36 | a connected ball meeting V and missing its boundary lies in V
EDGE: bpP:p4:conv#data | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:co-nbhd@L35-L36 | definitions of N_s and D_t
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: collar (KAM/Planetary/PGMeasure/Collar.lean)
LEAN_NOTE: audit P4-CO PASS WITH NOTES (audit 1 FAIL hygiene only, fixed by orchestrator addendum); named by audit
NOTE: -

NODE: bpP:p4:lip-compact
KIND: lemma
TITLE: Uniform Lipschitz bounds on compact sets
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lip-compact@L41-L43
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lip-compact@L44-L49
CONTRACT_ID: bpP:p4:lip-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Theta subset R^p and K subset R^m compact; O subset R^p x R^m open with Theta x K subset O; f: O -> R^q continuous, x -> f(theta, x) of class C^1 and D_x f jointly continuous on O (p = 0 allowed)
SOURCE_QUANTIFIERS: p, m, q, Theta, K, O, f given; then there is Lambda
SOURCE_CONCLUSION: there is Lambda with ¦f(theta,x) - f(theta,x')¦ <= Lambda ¦x - x'¦ for all theta in Theta, x, x' in K
CONSTANT_SCOPE: Lambda depends on (Theta, K, O, f) only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p4:lc-contra, stepP:p4:lc-local
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p4:lc-contra | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lip-compact@L45-L45 | proof step
EDGE: stepP:p4:lc-local | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lip-compact@L47-L47 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: lip_compact, lip_compact_c1 (KAM/Planetary/PGMeasure/CompactLipschitz.lean)
LEAN_NOTE: audit P4-LI PASS WITH NOTES
NOTE: -

NODE: stepP:p4:lc-contra
KIND: step
TITLE: Contradiction
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:lc-contra@L45-L46
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:lc-contra@L45-L46
CONTRACT_ID: stepP:p4:lc-contra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: negation of the claim: theta_m, x_m != x_m' with ¦f(theta_m,x_m) - f(theta_m,x_m')¦ > m ¦x_m - x_m'¦; f bounded on the compact Theta x K
SOURCE_QUANTIFIERS: m in N, sequences theta_m in Theta, x_m, x_m' in K
SOURCE_CONCLUSION: ¦x_m - x_m'¦ -> 0 and, along a subsequence, theta_m -> theta*, x_m, x_m' -> x* (compactness)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: lip_compact (KAM/Planetary/PGMeasure/CompactLipschitz.lean)
LEAN_NOTE: audit P4-LI PASS WITH NOTES; proof of lip_compact
NOTE: -

NODE: stepP:p4:lc-local
KIND: step
TITLE: Local bound
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:lc-local@L47-L48
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:lc-local@L47-L48
CONTRACT_ID: stepP:p4:lc-local
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the sequences of stepP:p4:lc-contra; O open; D_x f jointly continuous
SOURCE_QUANTIFIERS: delta > 0 with closed polydisc around (theta*, x*) in O; M_* := sup of ¦D_x f¦ over it; m large
SOURCE_CONCLUSION: for large m the segment [x_m, x_m'] lies in B_delta(x*), so the mean value inequality gives ¦f(theta_m,x_m) - f(theta_m,x_m')¦ <= M_* ¦x_m - x_m'¦, contradicting the choice for m > M_*
CONSTANT_SCOPE: M_* is local to the chosen closed delta-neighbourhood in O; no uniform dependence beyond that choice is asserted
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p4:lc-contra, K:bp:p1:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p4:lc-contra | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:lc-local@L48-L48 | sequences and limit point (theta*, x*) produced by the contradiction step
EDGE: K:bp:p1:ext-mvt | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:lc-local@L48-L48 | mean value inequality on a convex ball (replaces the alias item bpP:p4:ext-mvt)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4+sol-review-P-f
REVIEWER: sol-delta-P-f
LEAN_STATUS: PROVED
LEAN_REF: lip_local (KAM/Planetary/PGMeasure/CompactLipschitz.lean)
LEAN_NOTE: audit P4-LI PASS WITH NOTES; private helper named by audit
NOTE: -

NODE: bpP:p4:lip-inverse
KIND: lemma
TITLE: Lipschitz inverse of the fast frequency
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lip-inverse@L51-L54
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lip-inverse@L55-L60
CONTRACT_ID: bpP:p4:lip-inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: HasFastDiffeo(H_0, W) (bpP:p0:fastdiffeo); closure of V subset W; V bounded; omega_{H_0} = fastFrequency H_0; g the frozen inverse
SOURCE_QUANTIFIERS: H_0, W, V fixed; then the conclusions with L_g, R_y, Lambda_g
SOURCE_CONCLUSION: omega_{H_0} is continuous on W; Y_0 := omega_{H_0}(closure V) is compact and contained in the open set omega_{H_0}(W); g(omega_{H_0}(I)) = I on W; there is L_g < infinity with ¦g(y) - g(y')¦ <= L_g ¦y - y'¦ for y, y' in Y_0; R_y := max_{Y_0} ¦y¦, Lambda_g := max{1, L_g}
CONSTANT_SCOPE: L_g, R_y, Lambda_g depend only on (H_0, V, W)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:fastdiffeo#HasFastDiffeomorphism, bpP:p0:fastfreq#fastFrequency, stepP:p4:li-cont, stepP:p4:li-lip
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:fastdiffeo#HasFastDiffeomorphism | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lip-inverse@L52-L52 | hypothesis HasFastDiffeo(H_0, W) (clauses (i) to (iii))
EDGE: bpP:p0:fastfreq#fastFrequency | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lip-inverse@L52-L52 | omega_{H_0} = fastFrequency H_0
EDGE: stepP:p4:li-cont | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lip-inverse@L56-L56 | proof step
EDGE: stepP:p4:li-lip | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lip-inverse@L58-L58 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: lip_inverse (KAM/Planetary/PGMeasure/CompactLipschitz.lean)
LEAN_NOTE: audit P4-LI PASS WITH NOTES
NOTE: -

NODE: stepP:p4:li-cont
KIND: step
TITLE: Continuity and compactness
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:li-cont@L56-L57
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:li-cont@L56-L57
CONTRACT_ID: stepP:p4:li-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: HasFastDiffeo clauses (i) H_0 analytic on W and (ii) omega_{H_0}(W) open; closure of V compact
SOURCE_QUANTIFIERS: H_0, W, V given
SOURCE_CONCLUSION: omega_{H_0} is analytic, hence continuous, on W; Y_0 is compact and lies in the open set omega_{H_0}(W)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:ext-deriv, bpP:p0:fastdiffeo#HasFastDiffeomorphism, bpP:p0:fastfreq#fastFrequency, bpP:p1:ext-borel
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:ext-deriv | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:li-cont@L57-L57 | the derivative of a real analytic function is real analytic
EDGE: bpP:p0:fastdiffeo#HasFastDiffeomorphism | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:li-cont@L57-L57 | clauses (i) and (ii)
EDGE: bpP:p0:fastfreq#fastFrequency | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:li-cont@L57-L57 | omega_{H_0} is the derivative of H_0
EDGE: bpP:p1:ext-borel | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:li-cont@L57-L57 | the continuous image Y_0 of the compact closure of V is compact
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4+sol-review-P-f
REVIEWER: sol-delta-P-f
LEAN_STATUS: PROVED
LEAN_REF: lip_inverse (KAM/Planetary/PGMeasure/CompactLipschitz.lean)
LEAN_NOTE: audit P4-LI PASS WITH NOTES; proof of lip_inverse
NOTE: -

NODE: stepP:p4:li-lip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:li-lip@L58-L59
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:li-lip@L58-L59
CONTRACT_ID: stepP:p4:li-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g is C^1 on the open set omega_{H_0}(W) containing the compact Y_0 (clause (iii))
SOURCE_QUANTIFIERS: none beyond the statement
SOURCE_CONCLUSION: g is Lipschitz on Y_0 with some constant L_g (Lemma lip-compact with p = 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:lip-compact, bpP:p0:fastdiffeo#HasFastDiffeomorphism, stepP:p4:li-cont
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:lip-compact | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:li-lip@L59-L59 | applied with p = 0
EDGE: bpP:p0:fastdiffeo#HasFastDiffeomorphism | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:li-lip@L59-L59 | clause (iii): g is C^1 on omega_{H_0}(W)
EDGE: stepP:p4:li-cont | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:li-lip@L58-L59 | Y_0 compact and contained in omega_{H_0}(W)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: lip_inverse (KAM/Planetary/PGMeasure/CompactLipschitz.lean)
LEAN_NOTE: audit P4-LI PASS WITH NOTES; proof of lip_inverse
NOTE: -

NODE: bpP:p4:freq
KIND: definition
TITLE: Frequency map of the averaged system
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:freq@L72-L76
PROOF_SOURCE: -
CONTRACT_ID: bpP:p4:freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: H_0: R^a -> R; mu > 0; P_0(mu,.), Omega(mu,.), beta(mu,.) of class C^1 near D (D subset R^a); I in R^a, xi in R^b
SOURCE_QUANTIFIERS: mu > 0 fixed; (I, xi) in R^a x R^b
SOURCE_CONCLUSION: defines N_mu(I,xi) = P_0 + Omega.xi + (1/2) xi.beta xi, G_mu := grad_I N_mu, omega^s_mu := Omega + beta xi = grad_xi N_mu and the frequency map omega_mu(I,xi) := (omega_{H_0}(I) + mu G_mu(I,xi), mu omega^s_mu(I,xi)) = grad(H_0 + mu N_mu); dictionary: omega_mu/2pi lies in D_{gamma_1,gamma_2,tau} iff omega_mu lies in D_{2pi gamma_1, 2pi gamma_2, tau}, so with alpha_i = 2pi gamma_i, D minus D^dio = {J in D: omega_mu(J) not in D_{alpha_1,alpha_2,tau}}
CONSTANT_SCOPE: none (P_0, Omega, beta are the averaged data; no constants)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:fastfreq#fastFrequency, bpP:p3:period-dictionary, bpP:p1:dio-basic, bpP:p1:two-scale, bpP:p3:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:fastfreq#fastFrequency | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:freq@L74-L74 | omega_{H_0} in the frequency map
EDGE: bpP:p3:period-dictionary | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:freq@L75-L75 | h = (H_0 + mu N_mu)/2pi and omega_0 = omega_mu/2pi
EDGE: bpP:p1:dio-basic | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:freq@L75-L75 | cone property (c) of the two-scale Diophantine condition
EDGE: bpP:p1:two-scale | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:freq@L75-L75 | the set D_{alpha_1,alpha_2,tau}
EDGE: bpP:p3:conv#data | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:freq@L75-L75 | D^dio := omega_0^{-1}(D_{gamma_1,gamma_2,tau}) intersect D and the conventions of Part 3
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: secularPolynomial, slowFrequency, freq (KAM/Planetary/PGMeasure/Setting.lean)
LEAN_NOTE: audit P4-S PASS WITH NOTES
NOTE: -

NODE: bpP:p4:data
KIND: definition
TITLE: Standing data (S4)
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:data@L78-L86
PROOF_SOURCE: -
CONTRACT_ID: bpP:p4:data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: tau > n = a + b; D subset V compact with meas D > 0; lambda_0, mu_1 > 0; Lambda_N >= 1, L_beta >= 1; G_mu, omega^s_mu, beta as in bpP:p4:freq; R_y, L_g, Lambda_g of bpP:p4:lip-inverse
SOURCE_QUANTIFIERS: tau, D, lambda_0, mu_1, Lambda_N, L_beta fixed; (N1) to (N3) hold for all mu in (0, mu_1], I, I' in D, ¦xi¦, ¦xi'¦ <= lambda_0, nu in R^b
SOURCE_CONCLUSION: defines (S4): (N1) ¦G_mu(I,xi) - G_mu(I',xi)¦ and ¦omega^s_mu(I,xi) - omega^s_mu(I',xi)¦ <= Lambda_N ¦I - I'¦; (N2) ¦G_mu(I,xi) - G_mu(I,xi')¦ <= Lambda_N ¦xi - xi'¦; (N3) ¦nu¦ <= L_beta ¦beta(mu,I)^T nu¦; M := 2 b Lambda_N L_beta and mu_1 <= (2(1+M) a Lambda_N Lambda_g)^{-1}
CONSTANT_SCOPE: Lambda_N, L_beta, mu_1, lambda_0 do not depend on mu in (0, mu_1], I or xi; R_y, L_g, Lambda_g depend on (H_0, V, W) only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:freq, bpP:p4:lip-inverse, bpP:p4:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:freq | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:data@L79-L84 | G_mu, omega^s_mu, beta of the averaged frequency map in (N1) to (N3)
EDGE: bpP:p4:lip-inverse | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:data@L85-L85 | constants R_y, L_g, Lambda_g in mu_1 and M
EDGE: bpP:p4:conv#data | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:data@L79-L79 | V and the compact D subset V
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: MeasureData (KAM/Planetary/PGMeasure/Setting.lean)
LEAN_NOTE: audit P4-S PASS WITH NOTES
NOTE: standing data (S4). The pre-extracted candidate to bpP:p4:beta-inverse is dropped: (N3) only names the lemma that supplies the constant in Part 5.

NODE: bpP:p4:affine-slab
KIND: lemma
TITLE: Slab with offset
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:affine-slab@L88-L90
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:affine-slab@L91-L93
CONTRACT_ID: bpP:p4:affine-slab
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ell in R^N minus {0}, c in R, lambda, a' > 0
SOURCE_QUANTIFIERS: N >= 1, ell, c, lambda, a' given
SOURCE_CONCLUSION: meas{x in [-lambda, lambda]^N: ¦ell.x + c¦ < a'} <= 2 a' (2 lambda)^{N-1} / ¦ell¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:ext-tonelli
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:ext-tonelli | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:affine-slab@L92-L92 | each section in the coordinate x_i with ¦ell_i¦ = ¦ell¦ lies in an interval of length 2a'/¦ell_i¦; Tonelli
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: affine_slab, affine_slab_of_coord (KAM/Planetary/PGMeasure/AffineSlab.lean)
LEAN_NOTE: audit P4-AF PASS WITH NOTES
NOTE: the pre-extracted candidate K:bp:p4:slab ("cf.", a model only) is deleted as a comparison.

NODE: bpP:p4:lattice-tail
KIND: lemma
TITLE: Lattice sums
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lattice-tail@L95-L98
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lattice-tail@L99-L102
CONTRACT_ID: bpP:p4:lattice-tail
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b >= 1 integers and n = a + b (Part 4 conventions); tau > n (so tau - 1 > n - 1 and tau > b - 1); (b) real m >= 1
SOURCE_QUANTIFIERS: n, b, tau fixed; (b) then m
SOURCE_CONCLUSION: (a) sum over k in Z^n minus 0 of ¦k¦_1^{-tau} <= S_1 := 2 3^{n-1} (tau+1-n)/(tau-n); sum over k_2 in Z^b minus 0 of ¦k_2¦_1^{-tau-1} <= S_2 := 2 3^{b-1} (tau+2-b)/(tau+1-b); (b) sum over ¦k¦_1 > m of ¦k¦_1^{-tau-1} <= C_T (2/m)^{tau+1-n}, C_T := 2 3^{n-1}/(tau+1-n)
CONSTANT_SCOPE: S_1, S_2, C_T depend on (n, b, tau) only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p4:lt-a, stepP:p4:lt-b
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p4:lt-a | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lattice-tail@L100-L100 | proof step (a)
EDGE: stepP:p4:lt-b | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:lattice-tail@L101-L101 | proof step (b)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4+sol-review-P-f
REVIEWER: sol-delta-P-f
LEAN_STATUS: PROVED
LEAN_REF: latticeWeight, lattice_tail, latticeS (KAM/Planetary/PGMeasure/LatticeTail.lean)
LEAN_NOTE: audit P4-LT PASS WITH NOTES
NOTE: -

NODE: stepP:p4:lt-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:lt-a@L100-L100
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:lt-a@L100-L100
CONTRACT_ID: stepP:p4:lt-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b >= 1 and n = a + b; tau > n; K lattice sum with (n, tau - 1) (valid as tau - 1 > n - 1) and with (b, tau) (valid as tau > b - 1)
SOURCE_QUANTIFIERS: n, b, tau fixed
SOURCE_CONCLUSION: sums S_1 and S_2 bounds of part (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p4:lattice-sum
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p4:lattice-sum | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:lt-a@L100-L100 | Z^n sum with exponent tau-1 and Z^b sum with exponent tau
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4+sol-review-P-f
REVIEWER: sol-delta-P-f
LEAN_STATUS: PROVED
LEAN_REF: lattice_tail (KAM/Planetary/PGMeasure/LatticeTail.lean)
LEAN_NOTE: audit P4-LT PASS WITH NOTES; named by audit
NOTE: -

NODE: stepP:p4:lt-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:lt-b@L101-L101
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:lt-b@L101-L101
CONTRACT_ID: stepP:p4:lt-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: tau > n; m >= 1 real; lattice count of {¦k¦_1 = l}
SOURCE_QUANTIFIERS: m >= 1 given; l ranges over integers > m
SOURCE_CONCLUSION: the tail sum is <= 2 3^{n-1} sum_{l > m} l^{-p} (p = tau + 2 - n > 1) <= 2 3^{n-1} (m/2)^{1-p}/(p-1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p4:lattice-count
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p4:lattice-count | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:lt-b@L101-L101 | number of lattice points with ¦k¦_1 = l is at most 2 3^{n-1} l^{n-1}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4+sol-review-P-f
REVIEWER: sol-delta-P-f
LEAN_STATUS: PROVED
LEAN_REF: lattice_tail, tail_finset_le (KAM/Planetary/PGMeasure/LatticeTail.lean)
LEAN_NOTE: audit P4-LT PASS WITH NOTES; named by audit
NOTE: -

NODE: bpP:p4:two-scale-diophantine-measure
KIND: proposition
TITLE: Two-scale Diophantine measure
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L104-L112
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L113-L141
CONTRACT_ID: bpP:p4:two-scale-diophantine-measure
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (S4) of bpP:p4:data; 0 < lambda <= lambda_0; Q subset (-lambda, lambda)^b Borel; mu in (0, mu_1]; alpha_1, alpha_2 > 0; omega_mu the frequency map of bpP:p4:freq; D_{alpha_1,alpha_2,tau} the two-scale set of bpP:p1:two-scale; R := {(I,xi) in D x Q: omega_mu(I,xi) not in D_{alpha_1,alpha_2,tau}}, gamma := alpha_2/mu
SOURCE_QUANTIFIERS: the data of (S4) (a, b, tau, H_0, V, W, D, lambda_0, mu_1, Lambda_N, L_beta) fixed first; then lambda, Q, mu, alpha_1, alpha_2; c_1, c_2 defined from the data
SOURCE_CONCLUSION: meas R <= [c_1 alpha_1 (1 + mu^{tau-n}/lambda) + c_2 gamma/lambda] meas(D) (2 lambda)^b, with c_1 := (Lambda_g^n/meas D) max{4 (2R_y)^{a-1} S_1, 4 b^2 L_beta (2R_y)^a C_T (4 Lambda_N Lambda_g)^{tau+1-n}} and c_2 := b L_beta S_2
CONSTANT_SCOPE: c_1, c_2 depend on (a, b, tau, H_0, V, W, Lambda_N, L_beta, D) only, not on mu, lambda, Q, alpha_i
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:data, bpP:p4:freq, bpP:p1:two-scale, bpP:p4:lip-inverse, stepP:p4:dm-slow, stepP:p4:dm-y, stepP:p4:dm-A, stepP:p4:dm-Bstruct, stepP:p4:dm-B, stepP:p4:dm-sum, bpP:p4:lattice-tail
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:data | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L105-L105 | standing data (S4), (N1) to (N3), mu_1, Lambda_N, L_beta
EDGE: bpP:p4:freq | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L106-L106 | omega_mu and G_mu, omega^s_mu in F_k
EDGE: bpP:p1:two-scale | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L106-L106 | the set D_{alpha_1,alpha_2,tau} and the thresholds alpha_k
EDGE: bpP:p4:lip-inverse | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L114-L114 | F_k is continuous by (N1), (N2) and the Lipschitz inverse g, so R_k is Borel
EDGE: stepP:p4:dm-slow | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L118-L118 | proof step: case k_1 = 0
EDGE: stepP:p4:dm-y | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L121-L121 | proof step: change to frequency coordinates
EDGE: stepP:p4:dm-A | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L125-L125 | proof step: case K_A
EDGE: stepP:p4:dm-Bstruct | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L130-L130 | proof step: structure of K_B
EDGE: stepP:p4:dm-B | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L133-L133 | proof step: case K_B
EDGE: stepP:p4:dm-sum | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L139-L139 | proof step: sum
EDGE: bpP:p4:lattice-tail | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:two-scale-diophantine-measure@L109-L109 | S_1, S_2 and C_T in the displayed definitions of c_1 and c_2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4+sol-review-P-f
REVIEWER: sol-delta-P-f
LEAN_STATUS: PROVED
LEAN_REF: two_scale_diophantine_measure, measure_c1, measure_c2, resonanceBad_eq (KAM/Planetary/PGMeasure/TwoScale.lean)
LEAN_NOTE: composite of audits P4-RAM PASS WITH NOTES + P4-R0 PASS WITH NOTES + P4-RB PASS WITH NOTES
NOTE: -

NODE: stepP:p4:dm-slow
KIND: step
TITLE: Case $k_1=0$ (slow resonances)
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-slow@L118-L119
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-slow@L118-L119
CONTRACT_ID: stepP:p4:dm-slow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: k = (0, k_2) != 0; F_k = mu k_2.(Omega + beta xi), ¦k¦_1 = ¦k_2¦_1; (N3); I fixed; Tonelli in I; threshold mu gamma ¦k_2¦_1^{-tau}
SOURCE_QUANTIFIERS: k_2 in Z^b minus 0, I in D, xi in [-lambda, lambda]^b
SOURCE_CONCLUSION: meas R^{(0)} <= meas D (2 lambda)^b b L_beta S_2 gamma/lambda (no injectivity of omega_mu is used)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:affine-slab, bpP:p4:lattice-tail, bpP:p4:data, bpP:p4:freq, bpP:p4:ext-tonelli
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:affine-slab | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-slow@L119-L119 | xi-slice measure of the slab with ell = beta^T k_2 and offset k_2.Omega
EDGE: bpP:p4:lattice-tail | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-slow@L119-L119 | sum of ¦k_2¦_1^{-tau-1} bounded by S_2
EDGE: bpP:p4:data | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-slow@L119-L119 | (N3): beta^T k_2 != 0 and ¦beta^T k_2¦ >= ¦k_2¦_1/(b L_beta)
EDGE: bpP:p4:freq | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-slow@L119-L119 | F_k = mu k_2.omega^s_mu when k_1 = 0
EDGE: bpP:p4:ext-tonelli | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-slow@L119-L119 | integration in I of the xi-sections
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: slow_resonance_measure_le, beta_inverse (KAM/Planetary/PGMeasure/ResonanceSlow.lean)
LEAN_NOTE: audit P4-R0 PASS WITH NOTES
NOTE: -

NODE: stepP:p4:dm-y
KIND: step
TITLE: Change to frequency coordinates
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-y@L121-L123
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-y@L121-L123
CONTRACT_ID: stepP:p4:dm-y
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Phi(I,xi) = (omega_{H_0}(I), xi) injective and continuous on D x [-lambda, lambda]^b with inverse (g(y), xi) Lambda_g-Lipschitz on Y_0 x R^b; (N1); R_k as in the proof of the proposition
SOURCE_QUANTIFIERS: k != 0 with k_1 != 0 or k_2 arbitrary; y, y' in Y := omega_{H_0}(D) subset [-R_y, R_y]^a
SOURCE_CONCLUSION: R_k' := Phi(R_k) is Borel and meas R_k <= Lambda_g^n meas R_k'; on R_k' the function is F_k(y,xi) = k_1.y + mu G_k(y,xi) with ¦G_k(y,xi) - G_k(y',xi)¦ <= Lambda_N Lambda_g ¦k¦_1 ¦y - y'¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:lip-inverse, bpP:p1:ext-borel, K:bp:p1:lip-image, bpP:p4:data, bpP:p4:freq
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:lip-inverse | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-y@L122-L123 | g is Lambda_g-Lipschitz on Y_0 and g(omega_{H_0}(I)) = I
EDGE: bpP:p1:ext-borel | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-y@L122-L122 | Borel image under an injective continuous map (the item bpP:p4:ext-mvt is an alias)
EDGE: K:bp:p1:lip-image | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-y@L122-L122 | meas R_k <= Lambda_g^n meas R_k' in R^n
EDGE: bpP:p4:data | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-y@L123-L123 | (N1) with Lambda_N
EDGE: bpP:p4:freq | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-y@L122-L123 | G_mu, omega^s_mu composed with g
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: pullMap, volume_pullMap_image_le, mem_pullMap_image_of_resonant (KAM/Planetary/PGMeasure/ResonanceFast/Pullback.lean)
LEAN_NOTE: audit P4-RAM PASS WITH NOTES
NOTE: -

NODE: stepP:p4:dm-A
KIND: step
TITLE: Case $\mathcal K_A$ (slicing in $y_j$)
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-A@L125-L128
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-A@L125-L128
CONTRACT_ID: stepP:p4:dm-A
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: k in K_A := {k_1 != 0: mu Lambda_N Lambda_g ¦k¦_1 <= ¦k_1¦_inf/2}; j with ¦k_{1,j}¦ = ¦k_1¦_inf >= 1; R_k' of dm-y; alpha_k = alpha_1 ¦k¦_1^{-tau}
SOURCE_QUANTIFIERS: k in K_A, j <= a
SOURCE_CONCLUSION: every y_j-section of R_k' has diameter <= 4 alpha_k; meas R_k' <= 4 alpha_1 ¦k¦_1^{-tau} (2R_y)^{a-1} (2 lambda)^b; meas R^{(A)} <= Lambda_g^n 4 S_1 (2R_y)^{a-1} alpha_1 (2 lambda)^b
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p4:dm-y, bpP:p4:ext-tonelli, bpP:p4:lattice-tail, bpP:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p4:dm-y | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-A@L126-L128 | coordinates y, F_k = k_1.y + mu G_k and the Lipschitz bound of G_k
EDGE: bpP:p4:ext-tonelli | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-A@L127-L127 | short sections plus projection in [-R_y,R_y]^{a-1} x [-lambda,lambda]^b
EDGE: bpP:p4:lattice-tail | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-A@L127-L127 | sum of ¦k¦_1^{-tau} bounded by S_1
EDGE: bpP:p4:data | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-A@L126-L127 | Lambda_N, Lambda_g in the definition of K_A
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4+sol-review-P-f
REVIEWER: sol-delta-P-f
LEAN_STATUS: PROVED
LEAN_REF: fast_modes_measure_le (KAM/Planetary/PGMeasure/ResonanceFast.lean)
LEAN_NOTE: audit P4-RAM PASS WITH NOTES
NOTE: -

NODE: stepP:p4:dm-Bstruct
KIND: step
TITLE: Structure of $\mathcal K_B$
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-Bstruct@L130-L131
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-Bstruct@L130-L131
CONTRACT_ID: stepP:p4:dm-Bstruct
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: k in K_B (k_1 != 0 and mu Lambda_N Lambda_g ¦k¦_1 > ¦k_1¦_inf/2); mu <= mu_1 <= (2(1+M) a Lambda_N Lambda_g)^{-1}, M = 2 b Lambda_N L_beta
SOURCE_QUANTIFIERS: k in K_B
SOURCE_CONCLUSION: (i) ¦k¦_1 > K_mu := (2 mu Lambda_N Lambda_g)^{-1} >= 1; (ii) ¦k_2¦_1 > M ¦k_1¦_1, hence ¦k¦_1 < 2b ¦k_2¦_inf and Lambda_N ¦k_1¦_1 <= ¦k_2¦_inf/(2 L_beta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:data | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-Bstruct@L130-L131 | M, mu_1, Lambda_N, L_beta and the bound mu <= mu_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: large_mode_structure (KAM/Planetary/PGMeasure/ResonanceLarge/Structure.lean)
LEAN_NOTE: audit P4-RB PASS WITH NOTES
NOTE: -

NODE: stepP:p4:dm-B
KIND: step
TITLE: Case $\mathcal K_B$ (slicing in $\xi_j$)
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-B@L133-L138
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-B@L133-L138
CONTRACT_ID: stepP:p4:dm-B
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: k in K_B, j <= b; R_{k,j} the part of R_k' with ¦(beta^T k_2)_j¦ >= ¦k_2¦_inf/L_beta; (N2), (N3); omega^s_mu affine in xi; the structure of dm-Bstruct
SOURCE_QUANTIFIERS: k in K_B, j <= b, then sum over j and over ¦k¦_1 > K_mu
SOURCE_CONCLUSION: meas R^{(B)} <= Lambda_g^n (2 lambda)^b 4 b^2 L_beta (2R_y)^a C_T (4 Lambda_N Lambda_g)^{tau+1-n} alpha_1 mu^{tau-n}/lambda
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p4:dm-y, stepP:p4:dm-Bstruct, bpP:p4:data, bpP:p4:freq, bpP:p4:ext-tonelli, bpP:p4:lattice-tail
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p4:dm-y | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-B@L133-L134 | coordinates y, xi and the function F_k
EDGE: stepP:p4:dm-Bstruct | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-B@L136-L136 | ¦k¦_1 > K_mu and Lambda_N ¦k_1¦_1 <= ¦k_2¦_inf/(2 L_beta)
EDGE: bpP:p4:data | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-B@L133-L136 | (N2) and (N3) give the modulus bound and the covering by the R_{k,j}
EDGE: bpP:p4:freq | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-B@L135-L135 | omega^s_mu affine in xi
EDGE: bpP:p4:ext-tonelli | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-B@L137-L137 | short xi_j-sections plus projection
EDGE: bpP:p4:lattice-tail | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-B@L137-L137 | tail sum (b) over ¦k¦_1 > K_mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: large_modes_measure_le, volume_resonanceSet_large_le (KAM/Planetary/PGMeasure/ResonanceLarge.lean)
LEAN_NOTE: audit P4-RB PASS WITH NOTES
NOTE: -

NODE: stepP:p4:dm-sum
KIND: step
TITLE: Sum
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-sum@L139-L140
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-sum@L139-L140
CONTRACT_ID: stepP:p4:dm-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the three bounds of the cases k_1 = 0, K_A, K_B and R = R^{(0)} union R^{(A)} union R^{(B)}
SOURCE_QUANTIFIERS: as in the proposition
SOURCE_CONCLUSION: adding them, each Lambda_g^n-term is <= c_1 meas D alpha_1 (2 lambda)^b times 1 resp. mu^{tau-n}/lambda, which is the claimed bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p4:dm-slow, stepP:p4:dm-A, stepP:p4:dm-B, K:bp:p1:ext-lebesgue, bpP:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p4:dm-slow | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-sum@L140-L140 | bound for R^{(0)}
EDGE: stepP:p4:dm-A | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-sum@L140-L140 | bound for R^{(A)}
EDGE: stepP:p4:dm-B | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-sum@L140-L140 | bound for R^{(B)}
EDGE: K:bp:p1:ext-lebesgue | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-sum@L140-L140 | subadditivity of meas over the union
EDGE: bpP:p4:data | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-sum@L140-L140 | standing D and Lambda_g in the scalar assembly and normalization by meas D
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4+sol-review-P-f
REVIEWER: sol-delta-P-f
LEAN_STATUS: PROVED
LEAN_REF: two_scale_diophantine_measure, resonanceBad_subset_union (KAM/Planetary/PGMeasure/TwoScale.lean)
LEAN_NOTE: audit P4-RAM PASS WITH NOTES
NOTE: -

NODE: stepP:p4:dc-prod
KIND: step
TITLE: Product structure
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dc-prod@L161-L162
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dc-prod@L161-L162
CONTRACT_ID: stepP:p4:dc-prod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < t < d; 0 < r_K < min{t, lambda_1}; D = D_t x A_sh of bpP:p4:conv#shell; max norm
SOURCE_QUANTIFIERS: t, r_K, lambda_1, lambda_2 fixed
SOURCE_CONCLUSION: Re(D_{r_K}) = N_{r_K}(D_t) x (lambda_1 - r_K, lambda_2 + r_K)^b subset V x (0, infinity)^b (the real neighbourhood of a product is the product of real neighbourhoods; N_{r_K}(D_t) subset V by the collar lemma (c))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:collar, bpP:p4:conv#shell, bpP:p3:conv#data, bpP:p4:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:collar | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dc-prod@L162-L162 | N_{r_K}(D_t) subset V, Lemma collar (c)
EDGE: bpP:p4:conv#shell | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dc-prod@L162-L162 | D = D_t x A_sh
EDGE: bpP:p3:conv#data | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dc-prod@L162-L162 | Re(D_r) is the real neighbourhood of Part 3 conventions
EDGE: bpP:p4:conv#data | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dc-prod@L162-L162 | the definitions of N_s and D_t used in the specialized inclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4+sol-review-P-f
REVIEWER: sol-delta-P-f
LEAN_STATUS: PROVED
LEAN_REF: dc_prod_node (KAM/Planetary/PGAssembly/LowerNodes.lean)
LEAN_NOTE: audit GAP-P5b round 3 PASS WITH NOTES
NOTE: step of Lemma bpP:p4:domain-collar, whose statement and the other step are excluded (outside every root closure: bpP:p5:use5-fix says Part 5 does not use the lemma as a black box); this step alone is cited by bpP:p5:bu-collar.

NODE: bpP:p4:disc-measure
KIND: lemma
TITLE: Cell and polar coordinates
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:disc-measure@L173-L178
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:disc-measure@L179-L186
CONTRACT_ID: bpP:p4:disc-measure
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b >= 1, n = a + b; V subset R^a open bounded (conv#data); r > 0 the frozen radius of bpP:p0:cylinder; F(V,r) the frozen cell; Pi and E of bpP:p4:s-disc#chart; (c) 0 < lambda_1 < lambda_2 = r^2/2
SOURCE_QUANTIFIERS: V, r fixed; (a) X measurable; (c) lambda_1 in (0, lambda_2)
SOURCE_CONCLUSION: (a) Pi is real analytic and injective on R^a x (0,inf)^b x R^a x [0,2pi)^b modulo phi -> phi + 2 pi k with ¦det D Pi¦ = 1; E is injective on R^a x (0,inf)^b x [0,1)^n and meas E(X) = (2pi)^n meas X; (b) F(V,r) minus E(V x (0,r^2/2)^b x [0,1)^n) is null and meas F(V,r) = (2pi)^a meas V (pi r^2)^b = (2pi)^n meas V (r^2/2)^b; (c) the set of z in F(V,r) with xi_j <= lambda_1 for some j has measure <= b (lambda_1/lambda_2) meas F(V,r), and 2 b kappa sqrt(r) meas F for lambda_1 = kappa r^{5/2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:s-disc#chart, bpP:p0:cylinder#cylinderCell, bpP:p4:conv#data, stepP:p4:dm-jac, stepP:p4:dm-cell, stepP:p4:dm-shell
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:s-disc#chart | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:disc-measure@L173-L174 | the maps Pi and E
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:disc-measure@L175-L176 | the frozen cell F(V,r)
EDGE: bpP:p4:conv#data | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:disc-measure@L175-L175 | V bounded open
EDGE: stepP:p4:dm-jac | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:disc-measure@L180-L180 | proof step (a)
EDGE: stepP:p4:dm-cell | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:disc-measure@L182-L182 | proof step (b)
EDGE: stepP:p4:dm-shell | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:disc-measure@L184-L184 | proof step (c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: disc_measure_chart, disc_measure_image, disc_measure, disc_measure_shell (KAM/Planetary/PGMeasure/Polar.lean)
LEAN_NOTE: audit P4-POL PASS WITH NOTES
NOTE: -

NODE: stepP:p4:dm-jac
KIND: step
TITLE: Jacobian
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-jac@L180-L181
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-jac@L180-L181
CONTRACT_ID: stepP:p4:dm-jac
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: one oscillator (xi,psi) -> (q,p) = sqrt(2 xi)(sin psi, cos psi); Pi is the identity on (I, phi) up to permuting coordinates; theta -> 2 pi theta
SOURCE_QUANTIFIERS: xi > 0, psi in [0, 2pi)
SOURCE_CONCLUSION: ¦det D Pi¦ = 1; the oscillator map is a bijection of (0,inf) x [0,2pi) onto R^2 minus 0; Pi is measure preserving on injectivity sets and E multiplies measure by (2pi)^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:s-disc#chart, bpP:p1:typical, bpP:p1:liouville, bpP:p1:ext-area
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:s-disc#chart | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-jac@L181-L181 | Pi and E
EDGE: bpP:p1:typical | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-jac@L181-L181 | dp ^ dq = d xi ^ d psi, Remark typical (1)
EDGE: bpP:p1:liouville | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-jac@L181-L181 | charts scale Lebesgue measure on injectivity sets
EDGE: bpP:p1:ext-area | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-jac@L181-L181 | area formula
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4+sol-review-P-f
REVIEWER: sol-delta-P-f
LEAN_STATUS: PROVED
LEAN_REF: hasFDerivAt_oscillatorPolar, abs_det_fderiv_oscillatorPolar, disc_measure_chart (KAM/Planetary/PGMeasure/Polar.lean)
LEAN_NOTE: audit P4-POL PASS WITH NOTES
NOTE: -

NODE: stepP:p4:dm-cell
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-cell@L182-L183
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-cell@L182-L183
CONTRACT_ID: stepP:p4:dm-cell
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z in F(V,r) with (p_j, q_j) != 0 for all j (the excluded set lies in finitely many codimension-2 subspaces, null); xi_j = (p_j^2 + q_j^2)/2 < r^2/2 on the cylinder; dm-jac
SOURCE_QUANTIFIERS: z in F(V,r)
SOURCE_CONCLUSION: z = E(I,xi,theta) with xi_j in (0, r^2/2), theta in [0,1)^n, I in V, up to a null set (the converse inclusion is the same computation); hence meas F(V,r) = (2pi)^n meas V (r^2/2)^b
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p4:dm-jac, bpP:p0:cylinder#cylinderCell, bpP:p0:cylinder#cylinder, bpP:p0:oscaction#oscillatorAction, bpP:p4:s-disc#chart
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p4:dm-jac | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-cell@L183-L183 | meas E(X) = (2pi)^n meas X
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-cell@L183-L183 | F(V,r) fundamental cell
EDGE: bpP:p0:cylinder#cylinder | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-cell@L183-L183 | the discs (p_j^2 + q_j^2)/2 < r^2/2 of the cylinder
EDGE: bpP:p0:oscaction#oscillatorAction | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-cell@L183-L183 | xi_j = R_j = (p_j^2 + q_j^2)/2
EDGE: bpP:p4:s-disc#chart | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-cell@L183-L183 | z = E(I,xi,theta)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4+sol-review-P-f
REVIEWER: sol-delta-P-f
LEAN_STATUS: PROVED
LEAN_REF: disc_measure (KAM/Planetary/PGMeasure/Polar.lean)
LEAN_NOTE: audit P4-POL PASS WITH NOTES
NOTE: -

NODE: stepP:p4:dm-shell
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-shell@L184-L185
PROOF_SOURCE: blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-shell@L184-L185
CONTRACT_ID: stepP:p4:dm-shell
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: lambda_1 < lambda_2 = r^2/2; F = E(V x (0,lambda_2)^b x [0,1)^n) up to a null set; dm-cell
SOURCE_QUANTIFIERS: 0 < lambda_1 < lambda_2
SOURCE_CONCLUSION: up to the null set of part (b), the set {z in F(V,r): xi_j <= lambda_1 some j} is E(V x {xi: exists j, xi_j <= lambda_1} x [0,1)^n) with the xi-set of measure <= b lambda_1 lambda_2^{b-1}; dividing by (b) gives <= b (lambda_1/lambda_2) meas F
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:s-disc#chart, stepP:p4:dm-cell, stepP:p4:dm-jac
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:s-disc#chart | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-shell@L185-L185 | chart E
EDGE: stepP:p4:dm-cell | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-shell@L185-L185 | meas F(V,r) of part (b)
EDGE: stepP:p4:dm-jac | blueprint-P/parts/p4-pg-measure.tex#stepP:p4:dm-shell@L185-L185 | the chart measure multiplier (2pi)^n converts the action-shell volume to physical measure
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4+sol-review-P-f
REVIEWER: sol-delta-P-f
LEAN_STATUS: PROVED
LEAN_REF: disc_measure_shell (KAM/Planetary/PGMeasure/Polar.lean)
LEAN_NOTE: audit P4-POL PASS WITH NOTES
NOTE: -

NODE: bpP:p4:conv#data
KIND: definition
TITLE: Section data of 4.2: V, A, d of P-G, the collar sets
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:conv#data@L19-L20
PROOF_SOURCE: -
CONTRACT_ID: bpP:p4:conv#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V subset R^a open, connected, bounded; A, d > 0 with meas{I: exists J in boundary V, ¦I-J¦ < t} <= A t for 0 < t < d (the boundary-collar hypothesis hboundary of the data of bpP:p0:pg); max norm on R^a
SOURCE_QUANTIFIERS: V, A, d fixed first (the data of bpP:p0:pg); then t > 0 (for D_t) and s > 0, X subset R^a (for N_s(X))
SOURCE_CONCLUSION: states 0 < meas V < infinity and boundary of V nonempty (V is nonempty, open and not R^a, which is connected); defines D_t := {I in V: dist(I, boundary V) >= t} and N_s(X) := {x in R^a: exists J in X, ¦x-J¦ < s}
CONSTANT_SCOPE: V, A, d are the data of bpP:p0:pg (A, d may depend on V; independent of r and mu)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:ext-conn
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:ext-conn | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:conv#data@L19-L19 | the nonemptiness of the boundary: V nonempty open and not R^a, and R^a is connected, so it meets the boundary of V
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: blockFast, blockSlow, blockFast_real, blockSlow_real, innerCore, realNbhd (KAM/Planetary/PG/Setting.lean)
LEAN_NOTE: audit P45-S PASS WITH NOTES; defining clauses D_t, N_s; consequences 0<meas V<inf and nonempty boundary not separate declarations
NOTE: section data of 4.1 (coverage item p4:prose-L19-L20). The reference to bpP:p0:pg only names the hypotheses (hboundary) of the theorem that Part 4 helps prove: no edge (it would close a cycle through bpP:p5:main); they are recorded in SOURCE_HYPOTHESES. D_t is the barred D with index t of the blueprint.

NODE: bpP:p4:conv#shell
KIND: definition
TITLE: Section data of 4.5: the oscillator shell A_sh and D
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:conv#shell@L153-L154
PROOF_SOURCE: -
CONTRACT_ID: bpP:p4:conv#shell
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < lambda_1 < lambda_2; b >= 1; D_t and V as in bpP:p4:conv#data (lambda_2 = r^2/2 for the frozen radius r when applied)
SOURCE_QUANTIFIERS: lambda_1 < lambda_2 fixed; t > 0
SOURCE_CONCLUSION: defines A_sh := (lambda_1, lambda_2)^b, l := lambda_2 - lambda_1 and D := D_t x A_sh subset R^a x R^b
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:conv#data | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:conv#shell@L153-L153 | D_t as the action factor of D
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: actionShell, joinedActions (KAM/Planetary/PG/Setting.lean)
LEAN_NOTE: audit P45-S PASS WITH NOTES
NOTE: section data of 4.5 (coverage item p4:prose-L153-L154). Consumed only by bpP:p4:dc-prod; bpP:p4:domain-collar, bpP:p4:budget are outside the root closure.

NODE: bpP:p4:s-disc#chart
KIND: definition
TITLE: Section data of 4.6: the oscillator action-angle chart Pi and E
STATEMENT_SOURCE: blueprint-P/parts/p4-pg-measure.tex#bpP:p4:s-disc#chart@L169-L171
PROOF_SOURCE: -
CONTRACT_ID: bpP:p4:s-disc#chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: I in R^a, xi in (0, infinity)^b, phi in R^a, psi in R^b; frozen coordinates z = ((phi, q), (I, p))
SOURCE_QUANTIFIERS: (I, xi, phi, psi) in R^a x (0,infinity)^b x R^a x R^b; theta in [0,1)^n for E
SOURCE_CONCLUSION: defines the oscillator action-angle chart Pi(I,xi;phi,psi) := ((phi, q = sqrt(2 xi) sin psi), (I, p = sqrt(2 xi) cos psi)) and, for a period-one angle theta = (theta_f, theta_s), E(I,xi,theta) := Pi(I,xi;2 pi theta_f, 2 pi theta_s)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:blocks#assemble, bpP:p3:period-dictionary
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:blocks#assemble | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:s-disc#chart@L170-L170 | Pi lands in the assembled coordinates z = ((phi,q),(I,p))
EDGE: bpP:p3:period-dictionary | blueprint-P/parts/p4-pg-measure.tex#bpP:p4:s-disc#chart@L171-L171 | E is the dictionary of the period lemma with Q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p4
REVIEWER: sol-review-P-f
LEAN_STATUS: PROVED
LEAN_REF: oscillatorPolar, polarCellMap, oscillatorPolar_eq_polarMap (KAM/Planetary/PGMeasure/Polar.lean)
LEAN_NOTE: audit P4-POL PASS WITH NOTES
NOTE: section data of 4.6 (coverage item p4:prose-L169-L171); Pol of bpP:p5:phi is this map.
