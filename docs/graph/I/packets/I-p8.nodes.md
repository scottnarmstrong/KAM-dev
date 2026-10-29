NODE: bpI:p8:x-topo
KIND: external
TITLE: Topology of R^k
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:x-topo@L28-L31
PROOF_SOURCE: -
CONTRACT_ID: bpI:p8:x-topo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (external)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Closed bounded sets in R^k are compact; a continuous real function on a nonempty compact set attains its minimum and maximum; for nonempty compact S and x not in S, dist(x,S) = min_{q in S} |q-x| > 0; preimages of open sets under continuous maps are open; a linear isomorphism of R^k is a homeomorphism (maps open sets to open sets and closures to closures); a closed subset of a compact set is compact (Mathlib IsCompact.exists_isMinOn, exists_infDist_eq_dist, Continuous.isOpen_preimage)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p8:x-norm
KIND: external
TITLE: Triangle inequality
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:x-norm@L32-L32
PROOF_SOURCE: -
CONTRACT_ID: bpI:p8:x-norm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (external)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Triangle inequality |u-w| >= |u-v| - |v-w| in a normed space
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p8:x-cont
KIND: external
TITLE: Monotone functions
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:x-cont@L33-L33
PROOF_SOURCE: -
CONTRACT_ID: bpI:p8:x-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (external)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: kappa(e) = sqrt(1-e^2) is continuous and strictly decreasing on [0,1] with kappa(0)=1 and kappa(e) in (0,1) for e in (0,1) (Mathlib Real.sqrt_lt_sqrt)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p8:e-vs-k
KIND: display
TITLE: Elements as inequalities on G/L (display e-vs-k)
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:e-vs-k@L36-L44
PROOF_SOURCE: -
CONTRACT_ID: bpI:p8:e-vs-k
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (L,G) in C_0; 0<=e_prime<e_doubleprime<1; kappa(x)=sqrt(1-x^2), e(L,G)=kappa(G/L)
SOURCE_QUANTIFIERS: for all (L,G) in C_0 and 0 <= e' < e'' < 1
SOURCE_CONCLUSION: e(L,G) in (e',e'') iff G/L in (kappa(e''),kappa(e')); and e(L,G) in [e',e''] iff G/L in [kappa(e''),kappa(e')]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:x-cont, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:x-cont | blueprint-I/parts/p8-r3bp.tex#bpI:p8:e-vs-k@L37-L44 | kappa is continuous and strictly decreasing on [0,1]; the involution identity at L44 is a local square-root calculation, not part of this external input
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#bpI:p8:e-vs-k@L36-L36 | C_0, e(L,G) = sqrt(1-G^2/L^2) of Parts 6-7
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: kappa, kappa_kappa, eccOf_eq_kappa, eccOf_mem_Ioo_iff, eccOf_mem_Icc_iff (KAM/Iso/R3bp/Region.lean)
LEAN_NOTE: audit P8-2 PASS WITH NOTES (helper infrastructure; does not seal I-R3BP)
NOTE: The involution identity kappa(kappa(x))=x on [0,1] is the elementary square-root calculation at L44, combined with strict monotonicity; it is not included in the statement of x-cont as a separate external assumption.

NODE: bpI:p8:sec-safe#data
KIND: definition
TITLE: Fixed data of the safe-region subsection (a_pm, e_pm, rho_*)
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:sec-safe#data@L132-L132
PROOF_SOURCE: -
CONTRACT_ID: bpI:p8:sec-safe#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a_-,a_+,e_-,e_+ as in Theorem I-R3BP (0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1); A, A^cl as in Definition bpI:p8:A
SOURCE_QUANTIFIERS: a_pm, e_pm fixed (hypotheses of I-R3BP)
SOURCE_CONCLUSION: fixes 0<a_-<a_+, 0<e_-<e_+<1/4 and rho_* := a_+(1+e_+) < 1; A, A^cl the action regions of Definition bpI:p8:A for these parameters
CONSTANT_SCOPE: depend on a_pm, e_pm only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:A
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:A | blueprint-I/parts/p8-r3bp.tex#bpI:p8:sec-safe#data@L132-L132 | A, A^cl for the fixed parameters
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: data definition not named in any audited table
NOTE: Section data paragraph L132 (SPEC): rho_* < 1 and e_+ < 1/4 are consumed by sr-radii and the safe definition.

NODE: bpI:p8:A
KIND: definition
TITLE: The action region of N
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:A@L49-L59
PROOF_SOURCE: -
CONTRACT_ID: bpI:p8:A
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1; kappa(e) = sqrt(1-e^2)
SOURCE_QUANTIFIERS: a_pm, e_pm
SOURCE_CONCLUSION: defines A = {(L,G) : sqrt(a_-) < L < sqrt(a_+), kappa(e_+)L < G < kappa(e_-)L} and A^cl (closed inequalities); A open and bounded, A^cl compact, closure(A) subset A^cl, A^cl subset C_0
CONSTANT_SCOPE: depends on a_pm, e_pm only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:x-topo, bpI:p8:x-cont, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:x-topo | blueprint-I/parts/p8-r3bp.tex#bpI:p8:A@L57-L57 | A open bounded, A^cl closed bounded hence compact, closure(A) subset A^cl
EDGE: bpI:p8:x-cont | blueprint-I/parts/p8-r3bp.tex#bpI:p8:A@L52-L52 | kappa(e) = sqrt(1-e^2) with kappa positive and decreasing, giving G >= kappa(e_+)L > 0 and G <= kappa(e_-)L < L
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#bpI:p8:A@L58-L58 | C_0 of Parts 6-7
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: PROVED
LEAN_REF: RegionParams, actionRegion, actionRegionCl, actionRegionCl_subset_cone, isOpen_actionRegion, isCompact_actionRegionCl, closure_actionRegion_subset (KAM/Iso/R3bp/Region.lean)
LEAN_NOTE: audit P8-2 PASS WITH NOTES
NOTE: -

NODE: bpI:p8:topology
KIND: proposition
TITLE: Topology of N
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:topology@L61-L72
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:topology@L73-L81
CONTRACT_ID: bpI:p8:topology
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a_-,a_+,e_-,e_+ as in Theorem I-R3BP (0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1); Definition bpI:p0:nearcircular (N); Delaunay map Q of Part 7
SOURCE_QUANTIFIERS: a_pm, e_pm fixed; then (b) for every z_0 in N
SOURCE_CONCLUSION: (a) A subset C_0 and for (L,G) in C_0: (a_-<L^2<a_+ and e_-<e(L,G)<e_+) iff (L,G) in A; (b) N = Q(R^2 x A) and every z_0 in N equals Q(l_0,g_0,L_0,G_0) with (L_0,G_0) in A; (c) N is open in R^2 x R^2; (d) N is nonempty (explicit point Q(0,0,L_*,G_*) with a_*, e_* the midpoints)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p8:tp-A, stepI:p8:tp-chart, stepI:p8:tp-open, stepI:p8:tp-nonempty, bpI:p8:A, bpI:p0:nearcircular#NearCircular, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p8:tp-A | blueprint-I/parts/p8-r3bp.tex#bpI:p8:topology@L74-L74 | proof step (a)
EDGE: stepI:p8:tp-chart | blueprint-I/parts/p8-r3bp.tex#bpI:p8:topology@L76-L76 | proof step (b)
EDGE: stepI:p8:tp-open | blueprint-I/parts/p8-r3bp.tex#bpI:p8:topology@L78-L78 | proof step (c)
EDGE: stepI:p8:tp-nonempty | blueprint-I/parts/p8-r3bp.tex#bpI:p8:topology@L80-L80 | proof step (d)
EDGE: bpI:p8:A | blueprint-I/parts/p8-r3bp.tex#bpI:p8:topology@L67-L67 | A of the statement
EDGE: bpI:p0:nearcircular#NearCircular | blueprint-I/parts/p8-r3bp.tex#bpI:p8:topology@L66-L66 | the region N
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#bpI:p8:topology@L65-L65 | Delaunay orbit map Q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: PROVED
LEAN_REF: mem_actionRegion_iff, nearCircular_eq_image_region, exists_delaunay_preimage, isOpen_nearCircular_region, nearCircular_nonempty (KAM/Iso/R3bp/Region.lean)
LEAN_NOTE: audit P8-2 PASS WITH NOTES; rows topology (a)-(d)
NOTE: -

NODE: stepI:p8:tp-A
KIND: step
TITLE: Elements as inequalities on G/L
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-A@L74-L74
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-A@L74-L74
CONTRACT_ID: stepI:p8:tp-A
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; (L,G) in C_0
SOURCE_QUANTIFIERS: for (L,G) in C_0
SOURCE_CONCLUSION: A subset A^cl subset C_0; (a): a_-<L^2<a_+ iff sqrt(a_-)<L<sqrt(a_+) and e_-<e<e_+ iff kappa(e_+)L < G < kappa(e_-)L
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:A, bpI:p8:e-vs-k, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:A | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-A@L74-L74 | A subset A^cl subset C_0
EDGE: bpI:p8:e-vs-k | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-A@L74-L74 | e in (e_-,e_+) iff G/L in (kappa(e_+),kappa(e_-))
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-A@L74-L74 | C_0 and/or e(L,G), Q are the orbit-map data used here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: actionRegionCl_subset_cone, mem_actionRegion_iff (KAM/Iso/R3bp/Region.lean)
LEAN_NOTE: audit P8-2 PASS WITH NOTES; row topology(a)
NOTE: -

NODE: stepI:p8:tp-chart
KIND: step
TITLE: Chart description
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-chart@L76-L76
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-chart@L76-L76
CONTRACT_ID: stepI:p8:tp-chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59
SOURCE_QUANTIFIERS: For each fixed a_pm,e_pm as in the topology proposition, every z_0 in N has some ell_0,g_0 in R and (L_0,G_0) in A with Q(ell_0,g_0,L_0,G_0)=z_0
SOURCE_CONCLUSION: N = Q(R^2 x A) and every z_0 in N has a preimage in R^2 x A
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:near-circular, stepI:p8:tp-A, bpI:p7:orbit-maps, bpI:p8:A
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:near-circular | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-chart@L76-L76 | N = Q({(l,g,L,G) in D_R : a_-<L^2<a_+, e_-<e<e_+})
EDGE: stepI:p8:tp-A | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-chart@L76-L76 | (a) converts the conditions to membership in A
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-chart@L76-L76 | Q and D_R
EDGE: bpI:p8:A | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-chart@L76-L76 | A and the fixed parameterization of the initial region
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: nearCircular_eq_image_region, exists_delaunay_preimage (KAM/Iso/R3bp/Region.lean)
LEAN_NOTE: audit P8-2 PASS WITH NOTES; row topology(b)
NOTE: -

NODE: stepI:p8:tp-open
KIND: step
TITLE: Openness
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-open@L78-L78
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-open@L78-L78
CONTRACT_ID: stepI:p8:tp-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the frozen physical set N and the Kepler region C with the elements a(q,p), e(q,p)
SOURCE_QUANTIFIERS: For each a_pm,e_pm satisfying the enclosing topology proposition; no new point or witness is selected
SOURCE_CONCLUSION: N is open in R^2 x R^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:near-circular, bpI:p7:elements, bpI:p8:x-topo
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:near-circular | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-open@L78-L78 | N = {(q,p) in C : a_-<a<a_+, e_-<e<e_+}
EDGE: bpI:p7:elements | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-open@L78-L78 | C open, a and e continuous on C
EDGE: bpI:p8:x-topo | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-open@L78-L78 | finite intersection of preimages of open intervals is open
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: isOpen_nearCircular_region (KAM/Iso/R3bp/Region.lean)
LEAN_NOTE: audit P8-2 PASS WITH NOTES; row topology(c)
NOTE: -

NODE: stepI:p8:tp-nonempty
KIND: step
TITLE: Nonemptiness
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-nonempty@L80-L80
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-nonempty@L80-L80
CONTRACT_ID: stepI:p8:tp-nonempty
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; a_*=(a_-+a_+)/2, e_*=(e_-+e_+)/2, L_*=sqrt(a_*), G_*=L_* kappa(e_*)
SOURCE_QUANTIFIERS: After a_pm,e_pm, define a_*,e_*,L_*,G_* in that order; the displayed point Q(0,0,L_*,G_*) witnesses nonemptiness
SOURCE_CONCLUSION: (L_*,G_*) in A and Q(0,0,L_*,G_*) = ((a_*(1-e_*),0),(0,kappa(e_*)/(L_*(1-e_*)))) in N; hence N nonempty
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:x-cont, bpI:p8:A, stepI:p8:tp-chart, bpI:p7:kepler-eq, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:x-cont | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-nonempty@L80-L80 | strict monotonicity of kappa gives G_* in (kappa(e_+)L_*, kappa(e_-)L_*)
EDGE: bpI:p8:A | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-nonempty@L80-L80 | (L_*,G_*) in A
EDGE: stepI:p8:tp-chart | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-nonempty@L80-L80 | Q(0,0,L_*,G_*) in N by (b)
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-nonempty@L80-L80 | u(0,e) = 0 (Proposition kepler-eq (c))
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#stepI:p8:tp-nonempty@L80-L80 | evaluation of Q at l=g=0: c=1, s=0, D=1-e_*, R(0)=id
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: nearCircular_nonempty (KAM/Iso/R3bp/Region.lean)
LEAN_NOTE: audit P8-2 PASS WITH NOTES; row topology(d)
NOTE: -

NODE: bpI:p8:collision-exclusion
KIND: lemma
TITLE: Collision exclusion from a compact safe set
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:collision-exclusion@L86-L98
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:collision-exclusion@L99-L103
CONTRACT_ID: bpI:p8:collision-exclusion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (X,|.|) normed space over R; m in N; x_1,...,x_m in X; c >= 0, mu_1 > 0; for each j and each real mu with |mu| <= mu_1 a point y_j(mu) in X (no continuity) with |y_j(mu) - x_j| <= c|mu|
SOURCE_QUANTIFIERS: X, m, x_j, c, mu_1, y_j fixed; (a) for all S subset X, delta > 0 with |q-x_j| >= delta on S; then for all mu, q, j; (b) S compact
SOURCE_CONCLUSION: (a) with mu_* = mu_1 (c=0) or min{mu_1, delta/(2c)} (c>0): for |mu| <= mu_*, q in S, j: |q - y_j(mu)| >= delta/2; (b) if X finite dimensional, S compact and x_j not in S: delta_S := min_j min_{q in S}|q-x_j| > 0 (vacuous if S empty or m=0) and there are mu_* > 0, d = delta_S/2 > 0 with |q - y_j(mu)| >= d for all q in S, |mu| <= mu_*, j; in particular q != y_j(mu)
CONSTANT_SCOPE: mu_*, delta/2 depend only on (delta, c, mu_1), not on mu, q or the family y_j
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p8:ce-quant, stepI:p8:ce-compact
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p8:ce-quant | blueprint-I/parts/p8-r3bp.tex#bpI:p8:collision-exclusion@L100-L100 | proof step (a)
EDGE: stepI:p8:ce-compact | blueprint-I/parts/p8-r3bp.tex#bpI:p8:collision-exclusion@L102-L102 | proof step (b)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: PROVED
LEAN_REF: exclusionMu, exclusionMu_pos, collision_exclusion_quant, collision_exclusion_compact_attained (KAM/Iso/Collision.lean)
LEAN_NOTE: audit P8-1 audit-1 + audit-2 PASS (P81-01 closed by attained-minimum theorem); generalized length carrier
NOTE: Used by shell-exclusion (hence by pf-dist); also cited by track P (not a reason for inclusion here).

NODE: stepI:p8:ce-quant
KIND: step
TITLE: Quantitative form
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:ce-quant@L100-L100
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:ce-quant@L100-L100
CONTRACT_ID: stepI:p8:ce-quant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X is a real normed space; m in N; x_j in X; c>=0, mu_1>0; y_j(mu) defined for |mu|<=mu_1 with |y_j(mu)-x_j|<=c|mu|; S subset X, delta>0 with |q-x_j|>=delta for q in S and j; mu_* as in L93
SOURCE_QUANTIFIERS: For fixed X,m,x_j,c,mu_1,y_j, then S,delta as in (a), define mu_*; for every real mu with |mu|<=mu_*, every q in S and every j<=m
SOURCE_CONCLUSION: |q - y_j(mu)| >= |q-x_j| - |x_j - y_j(mu)| >= delta - c|mu| >= delta/2
CONSTANT_SCOPE: depends on (delta,c,mu_1) only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:x-norm
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:x-norm | blueprint-I/parts/p8-r3bp.tex#stepI:p8:ce-quant@L100-L100 | reverse triangle inequality
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: collision_exclusion_quant (KAM/Iso/Collision.lean)
LEAN_NOTE: audit P8-1 audit-1 PASS WITH NOTES; named ce-quant
NOTE: -

NODE: stepI:p8:ce-compact
KIND: step
TITLE: Compact sets
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:ce-compact@L102-L102
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:ce-compact@L102-L102
CONTRACT_ID: stepI:p8:ce-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X is a real normed space; m in N; x_j in X; c>=0, mu_1>0; y_j(mu) defined for |mu|<=mu_1 with |y_j(mu)-x_j|<=c|mu|; X finite dimensional; S compact, x_j not in S; the nondegenerate branch has S nonempty and m>=1 (the other branches are vacuous as stated at L95)
SOURCE_QUANTIFIERS: For fixed X,m,x_j,c,mu_1,y_j and compact S with x_j not in S, handle S empty or m=0 vacuously; otherwise choose a minimizing q_j in S for each j, then delta_S>0 and mu_*,d, before mu,q,j
SOURCE_CONCLUSION: if S is empty or m=0, choose any delta_S>0 (for example 1), and the separation assertion is vacuous; if S is nonempty and m>=1, each continuous distance attains its minimum at q_j in S with q_j != x_j, and delta_S := min_j min_{q in S} norm(q-x_j) > 0; part (a) applies with this delta_S, giving mu_*>0 and d=delta_S/2 with norm(q-y_j(mu))>=d for every q in S, abs(mu)<=mu_* and every j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:x-topo, stepI:p8:ce-quant
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:x-topo | blueprint-I/parts/p8-r3bp.tex#stepI:p8:ce-compact@L102-L102 | continuous function attains its minimum on a nonempty compact set
EDGE: stepI:p8:ce-quant | blueprint-I/parts/p8-r3bp.tex#stepI:p8:ce-compact@L102-L102 | apply (a) with delta = delta_S
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: collision_exclusion_compact_attained, collision_exclusion_compact (KAM/Iso/Collision.lean)
LEAN_NOTE: audit P8-1 audit-2 PASS closes audit-1 P81-01; named ce-compact
NOTE: -

NODE: bpI:p8:shell-exclusion
KIND: corollary
TITLE: The restricted problem: shell around the primary
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:shell-exclusion@L105-L112
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:shell-exclusion@L113-L115
CONTRACT_ID: bpI:p8:shell-exclusion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < r_min <= rho_max < 1; nu_0 = min{r_min, 1-rho_max}; mu real with |mu| <= nu_0/2; a_1(mu) = (-mu,0), a_2(mu) = (1-mu,0) (Definition bpI:p0:primaries)
SOURCE_QUANTIFIERS: r_min, rho_max, mu fixed; then for all q with r_min <= rad(q) <= rho_max
SOURCE_CONCLUSION: rad(q - a_1(mu)) >= nu_0/2 and rad(q - a_2(mu)) >= nu_0/2, and every (q,p) with such q is collision free for this mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p8:se-inst, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2, bpI:p0:primaries#radius, bpI:p0:primaries#CollisionFree
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p8:se-inst | blueprint-I/parts/p8-r3bp.tex#bpI:p8:shell-exclusion@L114-L114 | proof step
EDGE: bpI:p0:primaries#primary1 | blueprint-I/parts/p8-r3bp.tex#bpI:p8:shell-exclusion@L111-L111 | a_1(mu)
EDGE: bpI:p0:primaries#primary2 | blueprint-I/parts/p8-r3bp.tex#bpI:p8:shell-exclusion@L111-L111 | a_2(mu)
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p8-r3bp.tex#bpI:p8:shell-exclusion@L106-L106 | rad
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p8-r3bp.tex#bpI:p8:shell-exclusion@L110-L110 | collision free
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: PROVED
LEAN_REF: shell_exclusion, shell_collisionFree (KAM/Iso/Collision.lean)
LEAN_NOTE: audit P8-1 audit-1 PASS WITH NOTES
NOTE: -

NODE: stepI:p8:se-inst
KIND: step
TITLE: Instance of the lemma
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:se-inst@L114-L114
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:se-inst@L114-L114
CONTRACT_ID: stepI:p8:se-inst
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<r_min<=rho_max<1; nu_0=min{r_min,1-rho_max}; |mu|<=nu_0/2; X=R^2 with Euclidean length, m=2, x_1=(0,0), x_2=(1,0), y_j(mu)=primary_j(mu), c=1 and S the radial shell
SOURCE_QUANTIFIERS: For fixed r_min,rho_max, let nu_0=min{r_min,1-rho_max}; instantiate the mass family and shell, choosing any mu_1>=nu_0/2; for all mu with |mu|<=nu_0/2, all q in the shell and all p in R^2
SOURCE_CONCLUSION: rad(q-a_j(mu)) >= nu_0/2 for q in S, and positive radii mean collision freedom
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:collision-exclusion, bpI:p8:x-norm, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2, bpI:p0:primaries#radius, bpI:p0:primaries#CollisionFree
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:collision-exclusion | blueprint-I/parts/p8-r3bp.tex#stepI:p8:se-inst@L114-L114 | part (a) with delta = nu_0 and c = 1
EDGE: bpI:p8:x-norm | blueprint-I/parts/p8-r3bp.tex#stepI:p8:se-inst@L114-L114 | ¦q - x_2¦_2 >= ¦x_2¦_2 - ¦q¦_2
EDGE: bpI:p0:primaries#primary1 | blueprint-I/parts/p8-r3bp.tex#stepI:p8:se-inst@L114-L114 | y_1(mu) = a_1(mu)
EDGE: bpI:p0:primaries#primary2 | blueprint-I/parts/p8-r3bp.tex#stepI:p8:se-inst@L114-L114 | y_2(mu) = a_2(mu)
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p8-r3bp.tex#stepI:p8:se-inst@L114-L114 | rad is the Euclidean norm
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p8-r3bp.tex#stepI:p8:se-inst@L114-L114 | rad > 0 is collision freedom
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: shell_exclusion (KAM/Iso/Collision.lean)
LEAN_NOTE: audit P8-1 audit-1 PASS WITH NOTES; named se-inst
NOTE: -

NODE: bpI:p8:safe
KIND: definition
TITLE: Enlargement and safe region
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe@L134-L147
PROOF_SOURCE: -
CONTRACT_ID: bpI:p8:safe
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a_-,a_+,e_-,e_+ as in Theorem I-R3BP (0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1); Definition bpI:p8:A; r_min, rho_max of Part 7 Section sec-complex for the compact set calK
SOURCE_QUANTIFIERS: a_pm, e_pm fixed; then t, a'_pm, e'_pm, U, calK, B, B', eta
SOURCE_CONCLUSION: defines t = min{1/8,(1-rho_*)/(6a_+)} > 0, a'_- = a_-/2, a'_+ = a_+(1+t), e'_- = e_-/2, e'_+ = e_++t; U and calK = A, A^cl for (a'_pm,e'_pm) with 0<e'_-<e'_+<3/8<1; B = 2 pi U, B' = 2 pi A, eta = 1; r_min, rho_max those of Part 7 for calK
CONSTANT_SCOPE: depends on a_pm, e_pm only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:A, bpI:p8:sec-safe#data, bpI:p8:x-cont, bpI:p7:sec-complex#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:A | blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe@L142-L142 | U and calK are A, A^cl for (a_pm_pr, e_pm_pr)
EDGE: bpI:p8:sec-safe#data | blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe@L136-L136 | rho_*, e_+ and the fixed parameters
EDGE: bpI:p8:x-cont | blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe@L139-L139 | kappa(e_pr) for the primed parameters
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe@L146-L146 | r_min and rho_max are precisely the min/max definitions of Part 7 L325-335 specialized to K
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: safeT, safeAminus, safeAplus, safeEminus, safeEplus, safeU, safeK, safeB, safeB' (KAM/Iso/R3bp/Safe.lean)
LEAN_NOTE: audit P8-3 PASS WITH NOTES (helper infrastructure; does not seal I-R3BP)
NOTE: The radius symbols specialize the section-data definitions to K; their nonempty compact carrier and positivity are verified by sr-incl and sr-radii, before head-data applies exact-ham. No exact-ham application occurs in the definition.

NODE: bpI:p8:safe-region
KIND: lemma
TITLE: Safe region
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe-region@L149-L159
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe-region@L160-L168
CONTRACT_ID: bpI:p8:safe-region
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition bpI:p8:safe; a_-,a_+,e_-,e_+ as in Theorem I-R3BP (0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1)
SOURCE_QUANTIFIERS: a_pm, e_pm fixed
SOURCE_CONCLUSION: (a) calK subset C_0 compact nonempty, U subset calK open bounded, closure(A) subset A^cl subset U subset calK; (b) for (L,G) in calK: a'_- <= L^2 <= a'_+ and e'_- <= e(L,G) <= e'_+; (c) rho_max = max_calK L^2(1+e) <= a'_+(1+e'_+) <= (1+rho_*)/2 < 1, r_min = min_calK L^2(1-e) >= a'_-(1-e'_+) > 0, r_min <= rho_max; (d) B subset 2 pi calK open bounded nonempty, B' open, closure(B') = 2 pi closure(A) compact, closure(B') subset B; (e) every quantity depends on (a_pm,e_pm) only
CONSTANT_SCOPE: depends on a_pm, e_pm only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p8:sr-incl, stepI:p8:sr-elements, stepI:p8:sr-radii, stepI:p8:sr-B, bpI:p8:safe, bpI:p8:sec-safe#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p8:sr-incl | blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe-region@L161-L161 | proof step (a)
EDGE: stepI:p8:sr-elements | blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe-region@L163-L163 | proof step (b)
EDGE: stepI:p8:sr-radii | blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe-region@L165-L165 | proof step (c)
EDGE: stepI:p8:sr-B | blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe-region@L167-L167 | proof step (d),(e)
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe-region@L151-L151 | t, U, calK, B, B_pr, r_min, rho_max
EDGE: bpI:p8:sec-safe#data | blueprint-I/parts/p8-r3bp.tex#bpI:p8:safe-region@L152-L152 | standing parameters a_pm, e_pm, rho_*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: PROVED
LEAN_REF: safeT_pos, safeT_le_eighth, safe_regionParams, safe_inclusions, safe_elements, safe_radii, safe_domain (KAM/Iso/R3bp/Safe.lean)
LEAN_NOTE: audit P8-3 PASS WITH NOTES; rows safe-region and sr-*
NOTE: -

NODE: stepI:p8:sr-incl
KIND: step
TITLE: Inclusions
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-incl@L161-L161
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-incl@L161-L161
CONTRACT_ID: stepI:p8:sr-incl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147
SOURCE_QUANTIFIERS: For fixed a_pm,e_pm, form the primed parameters,U,K; for every (L,G) in A^cl prove (L,G) in U, yielding the set inclusions
SOURCE_CONCLUSION: calK subset C_0 compact, U open bounded, calK nonempty, and closure(A) subset A^cl subset U subset calK
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:A, bpI:p8:topology, bpI:p8:x-cont, bpI:p8:safe, bpI:p8:sec-safe#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:A | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-incl@L161-L161 | Definition A applied to (a_pm_pr, e_pm_pr)
EDGE: bpI:p8:topology | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-incl@L161-L161 | (d): A nonempty
EDGE: bpI:p8:x-cont | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-incl@L161-L161 | kappa strictly decreasing: kappa(e_+_pr)L < kappa(e_+)L and kappa(e_-)L < kappa(e_-_pr)L
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-incl@L161-L161 | U, calK, primed parameters
EDGE: bpI:p8:sec-safe#data | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-incl@L161-L161 | sqrt(a_-_pr) < sqrt(a_-), e_+_pr > e_+, e_-_pr < e_-
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: safe_inclusions (KAM/Iso/R3bp/Safe.lean)
LEAN_NOTE: audit P8-3 PASS WITH NOTES; row sr-incl
NOTE: -

NODE: stepI:p8:sr-elements
KIND: step
TITLE: Elements on calK
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-elements@L163-L163
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-elements@L163-L163
CONTRACT_ID: stepI:p8:sr-elements
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; (L,G) in K
SOURCE_QUANTIFIERS: for (L,G) in calK
SOURCE_CONCLUSION: L^2 in [a'_-,a'_+] and e(L,G) in [e'_-,e'_+]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:e-vs-k, stepI:p8:sr-incl, bpI:p8:safe, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:e-vs-k | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-elements@L163-L163 | closed-interval form of the equivalence
EDGE: stepI:p8:sr-incl | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-elements@L163-L163 | calK subset C_0
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-elements@L163-L163 | definition of calK
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-elements@L163-L163 | C_0 and/or e(L,G), Q are the orbit-map data used here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: safe_elements (KAM/Iso/R3bp/Safe.lean)
LEAN_NOTE: audit P8-3 PASS WITH NOTES; row sr-elements
NOTE: -

NODE: stepI:p8:sr-radii
KIND: step
TITLE: The radii
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-radii@L165-L165
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-radii@L165-L165
CONTRACT_ID: stepI:p8:sr-radii
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147
SOURCE_QUANTIFIERS: For fixed a_pm,e_pm and the resulting K, bound L^2(1+e) and L^2(1-e) for every (L,G) in K; take the maximum and minimum on the nonempty compact K
SOURCE_CONCLUSION: rho_max <= a'_+(1+e'_+) <= (1+rho_*)/2 < 1; r_min >= a'_-(1-e'_+) > 0; max and min exist; r_min <= rho_max
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p8:sr-elements, bpI:p8:safe, bpI:p8:sec-safe#data, bpI:p8:x-topo, stepI:p8:sr-incl, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p8:sr-elements | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-radii@L165-L165 | (b) bounds on L^2 and e
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-radii@L165-L165 | t, a_pr_+, e_pr_+, r_min, rho_max
EDGE: bpI:p8:sec-safe#data | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-radii@L165-L165 | rho_*, e_+ < 1/4
EDGE: bpI:p8:x-topo | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-radii@L165-L165 | max and min exist by compactness
EDGE: stepI:p8:sr-incl | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-radii@L165-L165 | calK compact nonempty
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-radii@L165-L165 | C_0 and/or e(L,G), Q are the orbit-map data used here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: safeT_mul_le, safe_rho_arith, safe_radii, kRmin_le, le_kRhoMax (KAM/Iso/R3bp/Safe.lean)
LEAN_NOTE: audit P8-3 PASS WITH NOTES; row sr-radii
NOTE: -

NODE: stepI:p8:sr-B
KIND: step
TITLE: The action domain
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-B@L167-L167
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-B@L167-L167
CONTRACT_ID: stepI:p8:sr-B
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147
SOURCE_QUANTIFIERS: For fixed a_pm,e_pm and U,A,K, define B=2 pi U and B_prime=2 pi A; no additional binder
SOURCE_CONCLUSION: B = 2 pi U open bounded nonempty with B subset 2 pi calK; B' open, closure(B') = 2 pi closure(A) compact inside B; (e) explicit dependence on (a_pm,e_pm)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:x-topo, stepI:p8:sr-incl, bpI:p8:safe, bpI:p8:A
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:x-topo | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-B@L167-L167 | linear isomorphism is a homeomorphism; closures
EDGE: stepI:p8:sr-incl | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-B@L167-L167 | (a): closure(A) subset U subset calK
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-B@L167-L167 | B = 2 pi U, B_pr = 2 pi A
EDGE: bpI:p8:A | blueprint-I/parts/p8-r3bp.tex#stepI:p8:sr-B@L167-L167 | A is open and closure(A) is contained in compact A^cl; scaling gives openness of B_prime and compactness of its closure
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: safe_domain (KAM/Iso/R3bp/Safe.lean)
LEAN_NOTE: audit P8-3 PASS WITH NOTES; row sr-B
NOTE: -

NODE: bpI:p8:head-data
KIND: proposition
TITLE: The period-one data of I-HEAD for the restricted problem
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L170-L178
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L179-L185
CONTRACT_ID: bpI:p8:head-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: calK, B, B', eta as in Definition bpI:p8:safe; delta_2, mu_2, C_F, F from Proposition bpI:p7:exact-ham for calK (calK nonempty compact in C_0, rho_max < 1 by Lemma safe-region (c)); s_0 = delta_2/(2 pi), r_0 = 2 pi delta_2, h~ = h_{(2 pi)^2,1/(2 pi)}, f~_mu as in Corollary bpI:p7:period-one extended by 0 outside T_{s_0} x B_{r_0}
SOURCE_QUANTIFIERS: a_pm, e_pm fixed; then for every real mu with 0 <= mu < mu_2
SOURCE_CONCLUSION: (a) hypotheses of Theorem I-HEAD on (B,s_0,r_0,h~,B',eta) hold (B open bounded nonempty; s_0,r_0 > 0; h~ holomorphic on B_{r_0}, real at real I, det B_h~(I) = 3/I_1^4 != 0 on real I in B_{r_0}; B' open with compact closure inside B; eta > 0); (b) f = f~_mu and epsilon = C_F mu >= 0 satisfy the hypotheses of I-HEAD on (f,epsilon) except epsilon < epsilon_0 (holomorphy and Z^2-periodicity on T_{s_0} x B_{r_0}, Im f = 0 at real points, |f| <= epsilon); (c) s_0, r_0, mu_2, C_F depend only on (a_pm,e_pm)
CONSTANT_SCOPE: s_0, r_0, mu_2, C_F depend only on (a_pm, e_pm)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p8:hd-h, stepI:p8:hd-f, stepI:p8:hd-sets, bpI:p8:safe, bpI:p8:safe-region, bpI:p7:exact-ham, bpI:p7:period-one, bpI:p0:bordered#borderedHessian, bpI:p0:domains#complexStrip, bpI:p0:domains#actionNbhd, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p8:hd-h | blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L180-L180 | proof step (a)
EDGE: stepI:p8:hd-f | blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L182-L182 | proof step (b)
EDGE: stepI:p8:hd-sets | blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L184-L184 | proof step (a),(c)
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L171-L171 | calK, B, B_pr, eta
EDGE: bpI:p8:safe-region | blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L171-L171 | rho_max < 1 for admissibility of exact-ham
EDGE: bpI:p7:exact-ham | blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L171-L171 | delta_2, mu_2, C_F, F
EDGE: bpI:p7:period-one | blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L171-L171 | h~ and f~_mu
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L173-L173 | det B_h~
EDGE: bpI:p0:domains#complexStrip | blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L174-L174 | T_{s_0}
EDGE: bpI:p0:domains#actionNbhd | blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L173-L173 | B_{r_0}
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p8-r3bp.tex#bpI:p8:head-data@L170-L178 | the converted h_tilde is the h_{kappa,Omega} defined in Part 6
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: r3bp_headData, r3bp_perturbData, r3bpH (KAM/Iso/R3bp/HeadData.lean)
LEAN_NOTE: audit P8-4 PASS WITH NOTES; (a) r3bp_headData, (b) r3bp_perturbData, (c) constants depend only on (a_pm,e_pm)
NOTE: The statement reproduces the hypotheses of Theorem I-HEAD (a check, not a use of its conclusion): no edge to bpI:p0:head here; the application is stepI:p8:pf-head.

NODE: stepI:p8:hd-h
KIND: step
TITLE: The Hamiltonian
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-h@L180-L180
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-h@L180-L180
CONTRACT_ID: stepI:p8:hd-h
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; delta_2,mu_2,C_F,F are selected for K as at L171, s_0=delta_2/(2 pi), r_0=2 pi delta_2, h_tilde=h_{(2 pi)^2,1/(2 pi)}, f_tilde_mu the period-one perturbation extended by zero outside the analytic domain
SOURCE_QUANTIFIERS: After fixing a_pm,e_pm and the common analytic data of L171, for every real I in B_{r_0}
SOURCE_CONCLUSION: h~ holomorphic on B_{r_0}, real at real I, and det B_h~(I) = 3/I_1^4 > 0 for every real I in B_{r_0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:period-one, bpI:p7:nondeg, bpI:p0:bordered#borderedHessian, bpI:p6:kep-ham, bpI:p8:safe
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:period-one | blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-h@L180-L180 | (b) holomorphy, reality, I_1 > 0
EDGE: bpI:p7:nondeg | blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-h@L180-L180 | det B_h~(I) = 3/I_1^4
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-h@L180-L180 | the bordered Hessian
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-h@L180-L180 | the converted h_tilde is the h_{kappa,Omega} defined in Part 6
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-h@L180-L180 | K, B, B_prime and/or the safe radii fixed by this package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: r3bp_headData (KAM/Iso/R3bp/HeadData.lean)
LEAN_NOTE: audit P8-4 PASS WITH NOTES; named hd-h/hd-sets row
NOTE: -

NODE: stepI:p8:hd-f
KIND: step
TITLE: The perturbation
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-f@L182-L182
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-f@L182-L182
CONTRACT_ID: stepI:p8:hd-f
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; delta_2,mu_2,C_F,F are selected for K as at L171, s_0=delta_2/(2 pi), r_0=2 pi delta_2, h_tilde=h_{(2 pi)^2,1/(2 pi)}, f_tilde_mu the period-one perturbation extended by zero outside the analytic domain; real mu with 0<=mu<mu_2, epsilon=C_F mu
SOURCE_QUANTIFIERS: For each real mu with 0<=mu<mu_2, put epsilon=C_F mu; for all (theta,I) in T_{s_0} x B_{r_0}, with reality at its real points
SOURCE_CONCLUSION: f_tilde_mu is holomorphic on T_{s_0} x B_{r_0}, 1-periodic, real at its real points and bounded by |mu| C_F = C_F mu = epsilon since 0<=mu<mu_2; extension by zero does not change these on-domain facts
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:period-one, bpI:p8:safe
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:period-one | blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-f@L182-L182 | (c)
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-f@L182-L182 | K, B, B_prime and/or the safe radii fixed by this package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: r3bp_perturbData (KAM/Iso/R3bp/HeadData.lean)
LEAN_NOTE: audit P8-4 PASS WITH NOTES; named hd-f row
NOTE: -

NODE: stepI:p8:hd-sets
KIND: step
TITLE: Sets
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-sets@L184-L184
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-sets@L184-L184
CONTRACT_ID: stepI:p8:hd-sets
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; delta_2,mu_2,C_F,F are selected for K as at L171, s_0=delta_2/(2 pi), r_0=2 pi delta_2, h_tilde=h_{(2 pi)^2,1/(2 pi)}, f_tilde_mu the period-one perturbation extended by zero outside the analytic domain
SOURCE_QUANTIFIERS: For fixed a_pm,e_pm and the analytic constants selected for K at L171; no new solution, point or parameter is chosen
SOURCE_CONCLUSION: B open bounded nonempty, B' open with compact closure in B, s_0, r_0 > 0; (c) dependence on (a_pm,e_pm) only
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:safe-region, bpI:p7:period-one, bpI:p7:exact-ham, bpI:p8:safe
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:safe-region | blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-sets@L184-L184 | (d) and (e)
EDGE: bpI:p7:period-one | blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-sets@L184-L184 | (e) dependence of s_0, r_0, mu_2, C_F
EDGE: bpI:p7:exact-ham | blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-sets@L184-L184 | delta_2 in (0,delta_1]
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:hd-sets@L184-L184 | K, B, B_prime and/or the safe radii fixed by this package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: r3bp_headData (KAM/Iso/R3bp/HeadData.lean)
LEAN_NOTE: audit P8-4 PASS WITH NOTES; named hd-h/hd-sets row
NOTE: -

NODE: bpI:p8:constants
KIND: definition
TITLE: Choice of mu_0, d, R
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:constants@L190-L202
PROOF_SOURCE: -
CONTRACT_ID: bpI:p8:constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition bpI:p8:safe, Lemma safe-region, Proposition head-data; eps_0 of Theorem I-HEAD for (B,s_0,r_0,h~,B',eta); C_F = 6/(eps_0^sh sqrt(c_*)) > 0 of Lemma bpI:p7:shift
SOURCE_QUANTIFIERS: in this order depending only on (a_pm,e_pm): (1) t, a'_pm, e'_pm, U, calK, B, B', eta=1, r_min, rho_max; (2) delta_2, mu_2, C_F, s_0, r_0, h~; (3) eps_H; (4) nu_0, mu_0, d, R
SOURCE_CONCLUSION: defines eps_H := the constant epsilon_0 of I-HEAD for (B,s_0,r_0,h~,B',eta); nu_0 = min{r_min,1-rho_max} > 0; mu_0 = min{1/2, mu_2, eps_H/C_F, nu_0/2} in (0,1/2]; d = nu_0/2; R = sqrt(2/r_min); R > 1 > rho_max
CONSTANT_SCOPE: mu_0, d, R depend on nothing but (a_pm,e_pm); fixed before mu and z_0
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:safe, bpI:p8:safe-region, bpI:p8:head-data, bpI:p7:shift, bpI:p0:head, bpI:p8:sec-safe#data, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#bpI:p8:constants@L193-L193 | step (1) data
EDGE: bpI:p8:safe-region | blueprint-I/parts/p8-r3bp.tex#bpI:p8:constants@L193-L193 | r_min, rho_max and rho_max < 1
EDGE: bpI:p8:head-data | blueprint-I/parts/p8-r3bp.tex#bpI:p8:constants@L194-L194 | delta_2, mu_2, C_F, s_0, r_0, h~
EDGE: bpI:p7:shift | blueprint-I/parts/p8-r3bp.tex#bpI:p8:constants@L194-L194 | C_F = 6/(eps_0^sh sqrt(c_*)) > 0
EDGE: bpI:p0:head | blueprint-I/parts/p8-r3bp.tex#bpI:p8:constants@L195-L195 | eps_H is the constant epsilon_0 of I-HEAD
EDGE: bpI:p8:sec-safe#data | blueprint-I/parts/p8-r3bp.tex#bpI:p8:constants@L193-L193 | rho_* and the parameters a_pm, e_pm
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p8-r3bp.tex#bpI:p8:constants@L190-L202 | the converted h_tilde is the h_{kappa,Omega} defined in Part 6
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: shellNu, r3bpMu0, r3bpD, r3bpR, r3bp_constants_pos (KAM/Iso/R3bp/Constants.lean)
LEAN_NOTE: audit P8-5 PASS WITH NOTES + I-R3BP PASS; eps_H is a parameter, instantiated by I-HEAD in the sealed provider; documented D2 (abs(C_F)+1)
NOTE: -

NODE: bpI:p8:bounds
KIND: lemma
TITLE: Bounds along a Delaunay orbit
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:bounds@L204-L207
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p8:bounds@L208-L212
CONTRACT_ID: bpI:p8:bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (L,G) in calK; l, g real; (q,p) = Q(l,g,L,G); r_min, rho_max, R as in Definitions safe and constants
SOURCE_QUANTIFIERS: (L,G) in calK, l, g in R
SOURCE_CONCLUSION: r_min <= rad(q) <= rho_max and rad(p) <= R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p8:bd-r, stepI:p8:bd-p, bpI:p8:safe, bpI:p8:constants, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p8:bd-r | blueprint-I/parts/p8-r3bp.tex#bpI:p8:bounds@L209-L209 | proof step
EDGE: stepI:p8:bd-p | blueprint-I/parts/p8-r3bp.tex#bpI:p8:bounds@L211-L211 | proof step
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#bpI:p8:bounds@L205-L205 | calK, r_min, rho_max
EDGE: bpI:p8:constants | blueprint-I/parts/p8-r3bp.tex#bpI:p8:bounds@L205-L205 | R
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#bpI:p8:bounds@L205-L205 | Q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: PROVED
LEAN_REF: delaunay_orbit_bounds (KAM/Iso/R3bp/Constants.lean)
LEAN_NOTE: audit P8-5 PASS WITH NOTES + I-R3BP PASS
NOTE: -

NODE: stepI:p8:bd-r
KIND: step
TITLE: Radius
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-r@L209-L209
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-r@L209-L209
CONTRACT_ID: stepI:p8:bd-r
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; R from L198; (L,G) in K, ell,g real, (q,p)=Q(ell,g,L,G)
SOURCE_QUANTIFIERS: For every (L,G) in K and real ell,g, with (q,p)=Q(ell,g,L,G), as in the enclosing lemma
SOURCE_CONCLUSION: r_min <= rad(q) <= rho_max
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-identities, bpI:p8:safe, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-r@L209-L209 | (a) bounds on ¦q¦_2
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-r@L209-L209 | definition of r_min, rho_max
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-r@L209-L209 | Q and e(L,G) of the Delaunay orbit data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: delaunay_radius_bounds, delaunay_orbit_bounds (KAM/Iso/R3bp/Constants.lean)
LEAN_NOTE: audit P8-5 PASS WITH NOTES (named adapter row)
NOTE: -

NODE: stepI:p8:bd-p
KIND: step
TITLE: Momentum
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-p@L211-L211
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-p@L211-L211
CONTRACT_ID: stepI:p8:bd-p
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; R from L198; (L,G) in K, ell,g real, (q,p)=Q(ell,g,L,G)
SOURCE_QUANTIFIERS: For every (L,G) in K and real ell,g, with (q,p)=Q(ell,g,L,G), as in the enclosing lemma
SOURCE_CONCLUSION: |p|_2^2 = 2/|q|_2 - 1/L^2 <= 2/r_min = R^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-identities, stepI:p8:bd-r, bpI:p8:constants, bpI:p8:safe, bpI:p7:orbit-maps, bpI:p7:elements
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-p@L211-L211 | (c) energy -1/(2L^2)
EDGE: stepI:p8:bd-r | blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-p@L211-L211 | ¦q¦_2 >= r_min
EDGE: bpI:p8:constants | blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-p@L211-L211 | R = sqrt(2/r_min)
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-p@L211-L211 | K, B, B_prime and/or the safe radii fixed by this package
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-p@L211-L211 | Q and e(L,G) of the Delaunay orbit data
EDGE: bpI:p7:elements | blueprint-I/parts/p8-r3bp.tex#stepI:p8:bd-p@L211-L211 | E(q,p)=¦p¦_2^2/2-1/¦q¦_2 is the energy definition used in rearranging the identity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: delaunay_energy, delaunay_orbit_bounds (KAM/Iso/R3bp/Constants.lean)
LEAN_NOTE: audit P8-5 PASS WITH NOTES (named adapter row)
NOTE: -

NODE: stepI:p8:pf-coord
KIND: step
TITLE: Delaunay coordinates of z_0
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-coord@L217-L217
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-coord@L217-L217
CONTRACT_ID: stepI:p8:pf-coord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; delta_2,mu_2,C_F,F are selected for K as at L171, s_0=delta_2/(2 pi), r_0=2 pi delta_2, h_tilde=h_{(2 pi)^2,1/(2 pi)}, f_tilde_mu the period-one perturbation extended by zero outside the analytic domain; constants mu_0,d,R chosen at L190-202; 0<=mu<mu_0; z_0 in N
SOURCE_QUANTIFIERS: After a_pm,e_pm and mu_0,d,R, for each mu in [0,mu_0) and z_0 in N choose ell_0,g_0,L_0,G_0, then define z_tilde_0 with I_0 in B_prime
SOURCE_CONCLUSION: z_0 = Q(l_0,g_0,L_0,G_0) with (L_0,G_0) in A; z~_0 = (theta_0,I_0) := S^{-1}(l_0,g_0,L_0,G_0) = ((l_0,g_0)/(2 pi), 2 pi (L_0,G_0)), Q(S(z~_0)) = z_0 and I_0 in 2 pi A = B'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:topology, bpI:p6:conversion-map, bpI:p8:safe, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:topology | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-coord@L217-L217 | (b) Delaunay preimage in R^2 x A
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-coord@L217-L217 | S and its inverse (period-one conversion)
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-coord@L217-L217 | B_pr = 2 pi A
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-coord@L217-L217 | Q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: r3bp_core (KAM/Iso/R3bp/Constants.lean); restricted_near_circular (KAM/Provider/Iso/RestrictedNearCircular.lean)
LEAN_NOTE: audit P8-5 PASS WITH NOTES + I-R3BP PASS (row names r3bp_core); step of PROVED parent bpI:p0:r3bp (ruling b)
NOTE: -

NODE: stepI:p8:pf-small
KIND: step
TITLE: Smallness for I-HEAD
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-small@L219-L219
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-small@L219-L219
CONTRACT_ID: stepI:p8:pf-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; delta_2,mu_2,C_F,F are selected for K as at L171, s_0=delta_2/(2 pi), r_0=2 pi delta_2, h_tilde=h_{(2 pi)^2,1/(2 pi)}, f_tilde_mu the period-one perturbation extended by zero outside the analytic domain; constants mu_0,d,R chosen at L190-202; 0<=mu<mu_0; z_0 in N
SOURCE_QUANTIFIERS: After a_pm,e_pm and mu_0,d,R, for each mu in [0,mu_0) and z_0 in N put f=f_tilde_mu and epsilon=C_F mu; no new witness
SOURCE_CONCLUSION: f = f~_mu and epsilon = C_F mu satisfy the hypotheses of I-HEAD on (f,epsilon) and epsilon < eps_H = epsilon_0; the remaining hypotheses of I-HEAD hold by head-data (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:head-data, bpI:p8:constants, bpI:p8:safe, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:head-data | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-small@L219-L219 | (a) and (b) discharge the premises of I-HEAD
EDGE: bpI:p8:constants | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-small@L219-L219 | mu_0 <= mu_2 and C_F mu_0 <= eps_H
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-small@L219-L219 | B, B_pr, eta data of I-HEAD
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-small@L219-L219 | the converted h_tilde is the h_{kappa,Omega} defined in Part 6
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: r3bp_small, r3bp_core (KAM/Iso/R3bp/Constants.lean)
LEAN_NOTE: audit P8-5 PASS WITH NOTES + I-R3BP PASS; step of PROVED parent bpI:p0:r3bp (ruling b)
NOTE: -

NODE: stepI:p8:pf-head
KIND: step
TITLE: Apply I-HEAD
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-head@L221-L221
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-head@L221-L221
CONTRACT_ID: stepI:p8:pf-head
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; delta_2,mu_2,C_F,F are selected for K as at L171, s_0=delta_2/(2 pi), r_0=2 pi delta_2, h_tilde=h_{(2 pi)^2,1/(2 pi)}, f_tilde_mu the period-one perturbation extended by zero outside the analytic domain; constants mu_0,d,R chosen at L190-202; 0<=mu<mu_0; z_0 in N; z_tilde_0 and I_0 are the coordinates chosen at L217
SOURCE_QUANTIFIERS: After the fixed geometric data, their common epsilon_H, mu in [0,mu_0), z_0 and the chosen z_tilde_0, there exists z_tilde:R->R^2 x R^2; then for every t in R
SOURCE_CONCLUSION: z~ : R -> R^2 x R^2 with z~(0) = z~_0 and Sol(Ham_{h~,f~_mu},B,R,z~): z~(t)_2 in B, Ham differentiable at z~(t), z~'(t) = X(z~(t)); confinement and uniqueness clauses not needed
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:head, stepI:p8:pf-small, stepI:p8:pf-coord, bpI:p8:head-data, bpI:p0:hamsol#IsHamiltonianSolutionOn, bpI:p0:realham#realHamiltonian, bpI:p8:safe, bpI:p6:kep-ham, bpI:p8:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:head | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-head@L221-L221 | frozen theorem I-HEAD applied (not re-proved)
EDGE: stepI:p8:pf-small | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-head@L221-L221 | hypotheses and epsilon < epsilon_0 discharged
EDGE: stepI:p8:pf-coord | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-head@L221-L221 | initial point z~_0 with I_0 in B_pr
EDGE: bpI:p8:head-data | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-head@L221-L221 | hypotheses (a) on (B,s_0,r_0,h~,B_pr,eta)
EDGE: bpI:p0:hamsol#IsHamiltonianSolutionOn | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-head@L221-L221 | Sol
EDGE: bpI:p0:realham#realHamiltonian | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-head@L221-L221 | Ham_{h~,f~_mu}
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-head@L221-L221 | B, B_pr, eta
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-head@L221-L221 | the converted h_tilde is the h_{kappa,Omega} defined in Part 6
EDGE: bpI:p8:constants | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-head@L221-L221 | epsilon_H is the same I-HEAD threshold selected before mu and z_0; retain this witness
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: restricted_near_circular (KAM/Provider/Iso/RestrictedNearCircular.lean)
LEAN_NOTE: audit I-R3BP PASS (row names pf-head -> provider); step of PROVED parent bpI:p0:r3bp (ruling b)
NOTE: -

NODE: stepI:p8:pf-sol
KIND: step
TITLE: The physical solution
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-sol@L223-L223
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-sol@L223-L223
CONTRACT_ID: stepI:p8:pf-sol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; delta_2,mu_2,C_F,F are selected for K as at L171, s_0=delta_2/(2 pi), r_0=2 pi delta_2, h_tilde=h_{(2 pi)^2,1/(2 pi)}, f_tilde_mu the period-one perturbation extended by zero outside the analytic domain; constants mu_0,d,R chosen at L190-202; 0<=mu<mu_0; z_0 in N; z_tilde is the same trajectory obtained at L221; define z=Q o S o z_tilde
SOURCE_QUANTIFIERS: After choosing the same z_tilde at L221, define z=Q o S o z_tilde:R->R^2 x R^2; then for every t in R
SOURCE_CONCLUSION: z(0) = z_0 and RSol_mu(R,z)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p8:pf-head, stepI:p8:pf-coord, bpI:p7:transfer, bpI:p8:constants, bpI:p8:safe-region, bpI:p6:conversion-map, bpI:p0:restricted#IsRestrictedSolutionOn, bpI:p8:safe, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p8:pf-head | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-sol@L223-L223 | the Delaunay solution z~
EDGE: stepI:p8:pf-coord | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-sol@L223-L223 | z(0) = z_0
EDGE: bpI:p7:transfer | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-sol@L223-L223 | transfer of Delaunay solutions to the physical problem
EDGE: bpI:p8:constants | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-sol@L223-L223 | mu < mu_0 <= mu_2
EDGE: bpI:p8:safe-region | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-sol@L223-L223 | (d): B subset 2 pi calK
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-sol@L223-L223 | S
EDGE: bpI:p0:restricted#IsRestrictedSolutionOn | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-sol@L223-L223 | RSol_mu
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-sol@L223-L223 | K, B, B_prime and/or the safe radii fixed by this package
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-sol@L223-L223 | Q and e(L,G) of the Delaunay orbit data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: r3bp_core (KAM/Iso/R3bp/Constants.lean); restricted_near_circular (KAM/Provider/Iso/RestrictedNearCircular.lean)
LEAN_NOTE: audit P8-5 PASS WITH NOTES + I-R3BP PASS (row names r3bp_core); step of PROVED parent bpI:p0:r3bp (ruling b)
NOTE: -

NODE: stepI:p8:pf-bounds
KIND: step
TITLE: Radius bounds
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-bounds@L225-L225
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-bounds@L225-L225
CONTRACT_ID: stepI:p8:pf-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; delta_2,mu_2,C_F,F are selected for K as at L171, s_0=delta_2/(2 pi), r_0=2 pi delta_2, h_tilde=h_{(2 pi)^2,1/(2 pi)}, f_tilde_mu the period-one perturbation extended by zero outside the analytic domain; constants mu_0,d,R chosen at L190-202; 0<=mu<mu_0; z_0 in N; z_tilde is the trajectory from L221, z=Q o S o z_tilde as at L223; t in R
SOURCE_QUANTIFIERS: for t in R
SOURCE_CONCLUSION: r_min <= rad(q(t)) <= rho_max < 1 < R and rad(p(t)) <= R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p8:pf-sol, stepI:p8:pf-head, bpI:p8:bounds, bpI:p8:safe, bpI:p8:safe-region, bpI:p8:constants, bpI:p6:conversion-map, bpI:p0:primaries#radius, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p8:pf-sol | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-bounds@L225-L225 | z = Q o S o z~
EDGE: stepI:p8:pf-head | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-bounds@L225-L225 | z~(t)_2 in B
EDGE: bpI:p8:bounds | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-bounds@L225-L225 | bounds along a Delaunay orbit for (L,G) in calK
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-bounds@L225-L225 | B = 2 pi U and U subset calK
EDGE: bpI:p8:safe-region | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-bounds@L225-L225 | U subset calK and rho_max < 1
EDGE: bpI:p8:constants | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-bounds@L225-L225 | R > 1 > rho_max
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-bounds@L225-L225 | S z~(t) = (l,g,L,G) with (L,G) = z~(t)_2/(2 pi)
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-bounds@L225-L225 | rad
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-bounds@L225-L225 | Q(ell,g,L,G) gives the position and momentum of the same physical trajectory
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: r3bp_core (KAM/Iso/R3bp/Constants.lean); restricted_near_circular (KAM/Provider/Iso/RestrictedNearCircular.lean)
LEAN_NOTE: audit P8-5 PASS WITH NOTES + I-R3BP PASS (row names r3bp_core); step of PROVED parent bpI:p0:r3bp (ruling b)
NOTE: -

NODE: stepI:p8:pf-dist
KIND: step
TITLE: Distance to the primaries
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-dist@L227-L227
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-dist@L227-L227
CONTRACT_ID: stepI:p8:pf-dist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; delta_2,mu_2,C_F,F are selected for K as at L171, s_0=delta_2/(2 pi), r_0=2 pi delta_2, h_tilde=h_{(2 pi)^2,1/(2 pi)}, f_tilde_mu the period-one perturbation extended by zero outside the analytic domain; constants mu_0,d,R chosen at L190-202; 0<=mu<mu_0; z_0 in N; z is the physical trajectory defined at L223; t in R
SOURCE_QUANTIFIERS: for t in R
SOURCE_CONCLUSION: rad(q(t) - a_j(mu)) >= nu_0/2 = d for j = 1,2 and all t in R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:shell-exclusion, stepI:p8:pf-bounds, bpI:p8:constants, bpI:p8:safe-region, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2, bpI:p0:primaries#radius, bpI:p8:safe
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:shell-exclusion | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-dist@L227-L227 | shell around the primary (instance of the collision-exclusion lemma)
EDGE: stepI:p8:pf-bounds | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-dist@L227-L227 | q(t) lies in the shell r_min <= rad <= rho_max
EDGE: bpI:p8:constants | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-dist@L227-L227 | nu_0, d = nu_0/2, mu_0 <= nu_0/2
EDGE: bpI:p8:safe-region | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-dist@L227-L227 | r_min, rho_max with 0 < r_min <= rho_max < 1
EDGE: bpI:p0:primaries#primary1 | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-dist@L227-L227 | a_1(mu)
EDGE: bpI:p0:primaries#primary2 | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-dist@L227-L227 | a_2(mu)
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-dist@L227-L227 | rad
EDGE: bpI:p8:safe | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-dist@L227-L227 | r_min and rho_max are the fixed safe-region radii; with their safe-region bounds they specify the shell used here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: r3bp_core (KAM/Iso/R3bp/Constants.lean); restricted_near_circular (KAM/Provider/Iso/RestrictedNearCircular.lean)
LEAN_NOTE: audit P8-5 PASS WITH NOTES + I-R3BP PASS (row names r3bp_core); step of PROVED parent bpI:p0:r3bp (ruling b)
NOTE: -

NODE: stepI:p8:pf-uniq
KIND: step
TITLE: Uniqueness
STATEMENT_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-uniq@L229-L229
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-uniq@L229-L229
CONTRACT_ID: stepI:p8:pf-uniq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<a_-<a_+, 0<e_-<e_+<1/4, a_+(1+e_+)<1; the action region A and Delaunay notation of L36-59; t,a_pm_prime,e_pm_prime,U,K,B,B_prime,eta defined at L134-147; delta_2,mu_2,C_F,F are selected for K as at L171, s_0=delta_2/(2 pi), r_0=2 pi delta_2, h_tilde=h_{(2 pi)^2,1/(2 pi)}, f_tilde_mu the period-one perturbation extended by zero outside the analytic domain; constants mu_0,d,R chosen at L190-202; 0<=mu<mu_0; z_0 in N; z is the physical trajectory from L223; a<0<b, y:R->R^2 x R^2 with y(0)=z_0 and RSol_mu((a,b),y)
SOURCE_QUANTIFIERS: for all a<0<b and y
SOURCE_CONCLUSION: IsSolIn F_mu W_mu (a,b) y and IsSolIn F_mu W_mu (a,b) z; for every t in (a,b), y(t)=z(t)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:ham-eq, bpN:p3:newton-reduction, N:bpN:p3:gen-sol, N:bpN:p3:gen-uniqueness, stepI:p8:pf-sol, stepI:p8:pf-coord, bpI:p0:restricted#IsRestrictedSolutionOn, bpI:p0:restricted#restrictedVectorField, bpI:p0:primaries#CollisionFree, bpI:p7:sec-ham#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:ham-eq | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-uniq@L229-L229 | RSol iff z(t) in W_mu and z_pr = X_Ham; shared ODE layer
EDGE: bpN:p3:newton-reduction | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-uniq@L229-L229 | IsRestrictedSolutionOn iff IsSolIn for V_mu on W_mu
EDGE: N:bpN:p3:gen-sol | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-uniq@L229-L229 | restriction of a solution to a subinterval
EDGE: N:bpN:p3:gen-uniqueness | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-uniq@L229-L229 | uniqueness on arbitrary interval (a,b)
EDGE: stepI:p8:pf-sol | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-uniq@L229-L229 | RSol_mu(R,z) for z
EDGE: stepI:p8:pf-coord | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-uniq@L229-L229 | common initial value z_0
EDGE: bpI:p0:restricted#IsRestrictedSolutionOn | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-uniq@L229-L229 | RSol_mu
EDGE: bpI:p0:restricted#restrictedVectorField | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-uniq@L229-L229 | V_mu
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-uniq@L229-L229 | W_mu = collision-free points
EDGE: bpI:p7:sec-ham#data | blueprint-I/parts/p8-r3bp.tex#stepI:p8:pf-uniq@L229-L229 | W_mu is the open collision-free domain and F_mu is the same total formula extension
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p8+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.R3bp.restricted_unique (KAM/Iso/R3bp/Uniqueness.lean)
LEAN_NOTE: audit P8-6 PASS; exact design signature
NOTE: -
