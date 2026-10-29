NODE: bpP:p5:order
KIND: claim
TITLE: Order in which every constant is chosen
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:order@L13-L23
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:order@L13-L23
CONTRACT_ID: bpP:p5:order
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of bpP:p0:pg fixed first: a, b, V, W, A, d, r_0, mu_0, B, H_0, P, P_0, Omega, beta
SOURCE_QUANTIFIERS: order of choice: (1) data; (2) analytic constants delta_c, s_*, eps_an, r_1, Lambda_P, C_Q, rho_c, M_beta, L_beta, Lambda_N, c_0, M0bar, R_y, L_g, mu_*; (3) tau := n+1, C_1, widths s, sbar; (4) kappa_0, then kappa_1, then G, then C_*; (5) r_*, C := max{C_*+1, C_w}, c := 2 tau + 2 = 2n + 4; (6) only then r in (0,r_*) and mu in (0, min{mu_0, r^6/(log 1/r)^c}); K, Kbar, gamma, rhobar, rho, rhohat, Ehat, r_K, t, lambda_i are explicit functions of (r, mu); finally S
SOURCE_CONCLUSION: each constant of the list depends only on the earlier ones (the analytic constants on the data only, not on mu or r)
CONSTANT_SCOPE: bookkeeping of the order of quantification: the frozen statement requires r_*, C, c to depend on the data only, S on (r, mu)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: main_of_data (KAM/Planetary/PGAssembly/Main.lean)
LEAN_NOTE: audit P5-MAIN PASS WITH NOTES; order of choice realised inside main_of_data (constants chosen before r, mu)
NOTE: remark kept as a node: cited by params, rstar and mn-const as the place where the constants are chosen. The pre-extracted outgoing candidates (to ext, birkhoff-ext, freq-data, kam-hyp, kam-cond, params, lower, rstar, main) are pointers naming which lemma supplies a constant and would close cycles; deleted.

NODE: bpP:p5:ext
KIND: lemma
TITLE: Uniform holomorphic extension of the family
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:ext@L29-L31
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:ext@L32-L37
CONTRACT_ID: bpP:p5:ext
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (H1) and (H2) of bpP:p0:pg (P real analytic at every point of [0,mu_0] x closure of C(V,r_0); P(mu, z+shift(k)) = P(mu,z)); HasFastDiffeo(H_0,W); closure of V subset W; eps_box := r_0/2 (a real box radius only); X_delta the set of complex (I,phi,p,q) within delta of closure(V) x R^a x {¦(p,q)¦ <= eps_box} in the real part with ¦Im¦ < delta
SOURCE_QUANTIFIERS: the data of bpP:p0:pg fixed; delta > 0 in the definition of X_delta; then delta_c in (0,1), M_P, M_0 and the map P~
SOURCE_CONCLUSION: there are delta_c in (0,1), M_P < infinity and P~: [0,mu_0] x X_{delta_c} -> C with P~(mu,.) holomorphic, P~ = P at real points, P~ periodic under 2 pi k e_f (fast angles), ¦P~¦ <= M_P, P~ jointly continuous in mu; and H~_0 holomorphic on {I: dist(I, closure V) < delta_c} with ¦H~_0¦, ¦dH~_0¦, ¦d^2 H~_0¦ <= M_0
CONSTANT_SCOPE: delta_c, M_P, M_0 depend on the data only (not on mu, r)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:fastdiffeo#HasFastDiffeomorphism, stepP:p5:ext-loc, stepP:p5:ext-glue, stepP:p5:ext-per, stepP:p5:ext-H0
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:fastdiffeo#HasFastDiffeomorphism | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:ext@L30-L30 | hypothesis HasFastDiffeo(H_0,W): H_0 analytic on W
EDGE: stepP:p5:ext-loc | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:ext@L33-L33 | proof step
EDGE: stepP:p5:ext-glue | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:ext@L34-L34 | proof step
EDGE: stepP:p5:ext-per | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:ext@L35-L35 | proof step
EDGE: stepP:p5:ext-H0 | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:ext@L36-L36 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: ext, pgExtension (KAM/Planetary/PGAssembly/Extension.lean); PGExtension (KAM/Planetary/PGAssembly/ExtensionDefs.lean)
LEAN_NOTE: audit P5-EX PASS WITH NOTES; conclusion amended (AMEND P-A001, erratum ruling 01:20): agreement on cl C(V, r0)
NOTE: [pre-extract: dropped reference to bpP:p0:pg, which part p5 proves or sets up]

NODE: stepP:p5:ext-loc
KIND: step
TITLE: Local extensions
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-loc@L33-L33
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-loc@L33-L33
CONTRACT_ID: stepP:p5:ext-loc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (H1); X_0 := [0,mu_0] x closure(V) x [0,2pi]^a x {¦(p,q)¦ <= eps_box} compact; 2 eps_box^2 < r_0^2
SOURCE_QUANTIFIERS: x in X_0; delta_1 from a Lebesgue number of the cover by convergence polydiscs
SOURCE_CONCLUSION: X_0 lies in [0,mu_0] x closure of C(V,r_0); P is analytic at each point of X_0, so its power series gives a holomorphic extension P_x on a polydisc B(x,delta_1) with ¦P_x¦ <= M uniformly
CONSTANT_SCOPE: delta_1, M depend on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:cylinder#cylinder
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:cylinder#cylinder | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-loc@L33-L33 | X_0 subset [0,mu_0] x closure of the cylinder C(V,r_0) where (H1) holds
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: ext (KAM/Planetary/PGAssembly/Extension.lean)
LEAN_NOTE: local to PROVED parent ext (ruling 01:20 (b)); audit P5-CL confirms (docs/tracks/P/audits/P5-CL-audit-1.md:23)
NOTE: SOURCE_GAP: L33 uses finite-dimensional compactness, complexification of a real convergent power series, and a Lebesgue number with a uniform bound; no approved node supplies these classical inputs. L336 lists compactness and the Lebesgue number lemma but is not an external declaration under SPEC. The local-extension argument is present; the gap here is its unregistered classical inputs.

NODE: stepP:p5:ext-glue
KIND: step
TITLE: Gluing
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-glue@L34-L34
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-glue@L34-L34
CONTRACT_ID: stepP:p5:ext-glue
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P_x, P_y holomorphic extensions on polydiscs B(x,delta_1), B(y,delta_1) with B(x,delta_1) intersect B(y,delta_1) nonempty; both equal P at real points
SOURCE_QUANTIFIERS: x, y in X_0
SOURCE_CONCLUSION: P_x = P_y on the intersection (convex, hence connected; identity theorem), so the P_x define one holomorphic P~ on the union of the B(x,delta_1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p5:ext-loc
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p5:ext-loc | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-glue@L34-L34 | the local extensions P_x and delta_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: ext (KAM/Planetary/PGAssembly/Extension.lean)
LEAN_NOTE: local to PROVED parent ext (ruling 01:20 (b)); audit P5-CG confirms (docs/tracks/P/audits/P5-CG-audit-1.md:41)
NOTE: SOURCE_GAP: L34 invokes the identity theorem for a holomorphic function of several variables vanishing on a real open subset of a connected overlap. No approved input node supplies this version. The one-variable identity theorem is not silently strengthened.

NODE: stepP:p5:ext-per
KIND: step
TITLE: Periodicity
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-per@L35-L35
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-per@L35-L35
CONTRACT_ID: stepP:p5:ext-per
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (H2); P analytic hence continuous on closure of C(V,r_0); P~ on the fundamental box from ext-glue
SOURCE_QUANTIFIERS: k in Z^a
SOURCE_CONCLUSION: periodicity of P on the closure; P~ extended to phi outside [0,2pi]^a by translation by 2 pi k_f, consistently on overlaps; this gives X_{delta_c} for delta_c = delta_1
CONSTANT_SCOPE: delta_c = delta_1 depends on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p5:ext-glue, bpP:p0:fastshift#fastShift
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p5:ext-glue | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-per@L35-L35 | P~ on the fundamental box and the overlap argument
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-per@L35-L35 | translation by shift(k) = 2 pi k in the fast angles in (H2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: ext (KAM/Planetary/PGAssembly/Extension.lean)
LEAN_NOTE: local to PROVED parent ext (ruling 01:20 (b)); audit P5-EX confirms (docs/tracks/P/audits/P5-EX-audit-1.md:68)
NOTE: -

NODE: stepP:p5:ext-H0
KIND: step
TITLE: $H_0$
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-H0@L36-L36
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-H0@L36-L36
CONTRACT_ID: stepP:p5:ext-H0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H_0 analytic on W containing the compact closure of V
SOURCE_QUANTIFIERS: delta_c decreased as needed
SOURCE_CONCLUSION: H~_0 holomorphic on a complex delta_c-neighbourhood of closure of V, with derivatives bounded by M_0 (shrinking, Cauchy)
CONSTANT_SCOPE: M_0 depends on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p5:ext-loc, stepP:p5:ext-glue, bpP:p0:fastdiffeo#HasFastDiffeomorphism, K:bp:p1:cauchy-open
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p5:ext-loc | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-H0@L36-L36 | same local-extension argument without periodicity
EDGE: stepP:p5:ext-glue | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-H0@L36-L36 | gluing by the identity theorem
EDGE: bpP:p0:fastdiffeo#HasFastDiffeomorphism | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-H0@L36-L36 | H_0 analytic on W (clause (i))
EDGE: K:bp:p1:cauchy-open | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ext-H0@L36-L36 | Cauchy estimates for the derivatives
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: ext (KAM/Planetary/PGAssembly/Extension.lean)
LEAN_NOTE: local to PROVED parent ext (ruling 01:20 (b)); audit P5-EX confirms (docs/tracks/P/audits/P5-EX-audit-1.md:52)
NOTE: -

NODE: bpP:p5:consts
KIND: definition
TITLE: Strip, averaged function, constants
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:consts@L39-L44
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:consts@L45-L47
CONTRACT_ID: bpP:p5:consts
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: delta_c, M_P, P~ of bpP:p5:ext; eps_box := r_0/2; the N-norm of N:bpN:p4:norm in the angles phi with coefficient radius s_*
SOURCE_QUANTIFIERS: delta_c fixed first; then s_*, eps_an, D_c; Lambda_P := sup over mu in [0,mu_0]
SOURCE_CONCLUSION: defines s_* := min{delta_c,1}/2, eps_an := min{eps_box, delta_c/4} (the complex oscillator radius), D_c := {I in C^a: dist(I, closure V) < delta_c/2}, P~_av(mu,I;p,q) := (2pi)^{-a} integral of P~ over real phi in [0,2pi]^a (= P_av at real points of the cylinder) and Lambda_P := sup_mu of the N-norm of P~(mu,.) at coefficient radius s_* <= M_P coth(delta_c/4)^a < infinity (>= 1 after enlarging)
CONSTANT_SCOPE: s_*, eps_an, Lambda_P depend on the data only (through delta_c, M_P)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:ext, bpP:p0:secavg#secularAverage, N:bpN:p4:norm, N:bpN:p4:sup-weighted, K:bp:p1:decay
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:ext | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:consts@L40-L40 | delta_c, eps_box, P~ and M_P
EDGE: bpP:p0:secavg#secularAverage | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:consts@L42-L42 | P~_av = P_av at real points of the cylinder
EDGE: N:bpN:p4:norm | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:consts@L42-L42 | the weighted norm with coefficient radius s_* (Fourier in phi)
EDGE: N:bpN:p4:sup-weighted | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:consts@L46-L46 | sup-to-weighted conversion in the finiteness justification
EDGE: K:bp:p1:decay | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:consts@L46-L46 | decay of Fourier coefficients on a strip
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: pgWidth, pgOscRadius, complexAverage, complexAverage_real, consts (KAM/Planetary/PGAssembly/Extension.lean)
LEAN_NOTE: audit P5-EX PASS WITH NOTES (revision-4 design)
NOTE: -

NODE: bpP:p5:birkhoff-ext
KIND: lemma
TITLE: Birkhoff coefficients as derivatives; analytic extension to $\overline V$
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:birkhoff-ext@L49-L56
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:birkhoff-ext@L57-L62
CONTRACT_ID: bpP:p5:birkhoff-ext
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (H1), (H2), (H4), (H5), (H6) of bpP:p0:pg ((H5) only for (c)); mu in [0,mu_0], I in D_c; P~_av of bpP:p5:consts; R_j = (p_j^2+q_j^2)/2
SOURCE_QUANTIFIERS: data fixed; (mu,I) in [0,mu_0] x D_c
SOURCE_CONCLUSION: with P~_0 = P~_av at x=0, Omega~_j = d^2_{p_j} P~_av at 0, beta~_ij = d^2_{p_i} d^2_{p_j} P~_av at 0 (i != j), beta~_jj = (1/3) d^4_{p_j} P~_av at 0, N~ = P~_0 + Omega~.R + (1/2) R.beta~ R, Q := P~_av - N~: (a) P~_0, Omega~, beta~ holomorphic in I on D_c, continuous in mu, beta~ symmetric, equal to P_0, Omega, beta on [0,mu_0] x V; (b) the jet of Q(mu,I;.) at x = 0 vanishes to order 4; (c) ¦det beta~(mu,I)¦ >= B on [0,mu_0] x closure(V)
CONSTANT_SCOPE: no constants (B from (H5))
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:consts, bpP:p5:ext, bpP:p0:birkhoff#HasSecularBirkhoffForm, bpP:p0:oscaction#oscillatorAction, stepP:p5:be-coef, stepP:p5:be-an, stepP:p5:be-jet, stepP:p5:be-det
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:birkhoff-ext@L50-L50 | P~_av and D_c
EDGE: bpP:p5:ext | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:birkhoff-ext@L50-L50 | holomorphic extension P~
EDGE: bpP:p0:birkhoff#HasSecularBirkhoffForm | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:birkhoff-ext@L50-L50 | hypothesis (H4) HasBirkhoff
EDGE: bpP:p0:oscaction#oscillatorAction | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:birkhoff-ext@L50-L50 | R_j = (p_j^2+q_j^2)/2
EDGE: stepP:p5:be-coef | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:birkhoff-ext@L58-L58 | proof step
EDGE: stepP:p5:be-an | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:birkhoff-ext@L59-L59 | proof step
EDGE: stepP:p5:be-jet | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:birkhoff-ext@L60-L60 | proof step
EDGE: stepP:p5:be-det | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:birkhoff-ext@L61-L61 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: birkhoff_ext, birkhoff_ext_parameter_regularity, jetBeta_det_closure (KAM/Planetary/PGAssembly/Jets.lean); fourth_jet_unique (KAM/Planetary/PGAssembly/JetsFourth.lean)
LEAN_NOTE: audit P5-JET PASS WITH NOTES
NOTE: [pre-extract: dropped reference to bpP:p0:pg, which part p5 proves or sets up]

NODE: stepP:p5:be-coef
KIND: step
TITLE: Coefficients on $V$
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-coef@L58-L58
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-coef@L58-L58
CONTRACT_ID: stepP:p5:be-coef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu in [0,mu_0], I in V; (H4) clause (ii) P_av - N = o(¦x¦^4); (H6) beta symmetric; P_av real analytic near x=0 by differentiation under the integral
SOURCE_QUANTIFIERS: (mu,I) in [0,mu_0] x V
SOURCE_CONCLUSION: the degree <= 4 Taylor polynomial of P_av(mu,I;.) equals N, whence d^2_{p_j} N(0) = Omega_j, d^2_{p_i} d^2_{p_j} N(0) = beta_ij (i != j, using (H6)), d^4_{p_j} N(0) = 3 beta_jj, P_0 = P_av at x=0: part (a) on V
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:birkhoff#HasSecularBirkhoffForm, bpP:p0:secavg#secularAverage, bpP:p5:ext, bpP:p0:oscaction#oscillatorAction
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:birkhoff#HasSecularBirkhoffForm | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-coef@L58-L58 | (H4)(ii): P_av - N is o(¦x¦^4)
EDGE: bpP:p0:secavg#secularAverage | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-coef@L58-L58 | P_av and its analyticity
EDGE: bpP:p5:ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-coef@L58-L58 | P_av analytic by the holomorphic extension
EDGE: bpP:p0:oscaction#oscillatorAction | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-coef@L58-L58 | R_j = (p_j^2+q_j^2)/2 in the Taylor coefficients
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: fourth_jet_unique (KAM/Planetary/PGAssembly/JetsFourth.lean)
LEAN_NOTE: audit P5-JET PASS WITH NOTES; named by handoff
NOTE: SOURCE_GAP: L58 uses differentiation under the integral and uniqueness of the analytic fourth Taylor jet from an o(norm(x)^4) remainder. The polynomial coefficient computation is explicit; the analytic integration and jet facts have no supplying edge in this packet.

NODE: stepP:p5:be-an
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-an@L59-L59
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-an@L59-L59
CONTRACT_ID: stepP:p5:be-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P~_av holomorphic extension; uniform bounds from bpP:p5:ext
SOURCE_QUANTIFIERS: (mu,I) in [0,mu_0] x D_c
SOURCE_CONCLUSION: the listed derivatives of P~_av at x = 0 are holomorphic in I, continuous in mu; symmetry of beta~ is symmetry of mixed derivatives
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:ext, bpP:p5:consts
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-an@L59-L59 | holomorphy and uniform bounds of P~
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-an@L59-L59 | P~_av and D_c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: be_an (KAM/Planetary/PGAssembly/ExtensionNodes.lean)
LEAN_NOTE: audit GAP-P5a round 2 PASS WITH NOTES
NOTE: SOURCE_GAP: L59 invokes holomorphic parameter integration, continuity in the parameter, and commutation of mixed derivatives. These classical inputs are not supplied by ext or consts and have no approved input node here.

NODE: stepP:p5:be-jet
KIND: step
TITLE: (b) on $V$, then everywhere
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-jet@L60-L60
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-jet@L60-L60
CONTRACT_ID: stepP:p5:be-jet
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D_c connected (closure of V is connected, hVc; D_c a union of balls centred on it); the vanishing jet on V from be-coef
SOURCE_QUANTIFIERS: mu in [0,mu_0], multi-index alpha with ¦alpha¦ <= 4
SOURCE_CONCLUSION: each derivative d_x^alpha Q(mu,.;0) is holomorphic on D_c and vanishes on the real open set V, hence on D_c: part (b)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p5:be-coef, stepP:p5:be-an, bpP:p5:consts
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p5:be-coef | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-jet@L60-L60 | vanishing jet and equality N~ = N on V
EDGE: stepP:p5:be-an | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-jet@L60-L60 | holomorphy of the derivatives on D_c
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-jet@L60-L60 | uses the complex strip, oscillator radius or averaged function of this package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: be_jet (KAM/Planetary/PGAssembly/ExtensionNodes.lean)
LEAN_NOTE: audit GAP-P5a round 2 PASS WITH NOTES
NOTE: SOURCE_GAP: L60 invokes the several-variable identity theorem from a real open set, and connectedness of the complex tube about closure(V). Neither is proved here or supplied by an approved external/import. The on-V jet is supplied by be-coef.

NODE: stepP:p5:be-det
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-det@L61-L61
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-det@L61-L61
CONTRACT_ID: stepP:p5:be-det
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (H5) ¦det beta¦ >= B on V; part (a); continuity of det beta~
SOURCE_QUANTIFIERS: (mu,I) in [0,mu_0] x closure(V)
SOURCE_CONCLUSION: ¦det beta~¦ >= B on [0,mu_0] x V by (H5) and (a), and on closure(V) by continuity and density of V
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p5:be-coef, stepP:p5:be-an
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p5:be-coef | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-det@L61-L61 | beta~ = beta on V
EDGE: stepP:p5:be-an | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:be-det@L61-L61 | continuity of beta~ in I
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: jetBeta_det_real, jetBeta_det_closure (KAM/Planetary/PGAssembly/Jets.lean)
LEAN_NOTE: audit P5-JET PASS WITH NOTES; named by audit
NOTE: -

NODE: bpP:p5:uniform-remainder
KIND: proposition
TITLE: Uniform remainder: CP10 (60) from the frozen hypotheses
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:uniform-remainder@L64-L70
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:uniform-remainder@L71-L74
CONTRACT_ID: bpP:p5:uniform-remainder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the hypotheses of bpP:p5:birkhoff-ext, i.e. (H1), (H2), (H4)-(H6) of bpP:p0:pg
SOURCE_QUANTIFIERS: data fixed; then r_1 and C_Q; then for all mu in [0,mu_0], I in D_c' (dist(I,closure V) < delta_c/4) and complex x=(p,q) with ¦x¦ <= r_1
SOURCE_CONCLUSION: there are r_1 in (0, eps_an] and C_Q < infinity with ¦Q(mu,I;x)¦ <= C_Q ¦x¦^5; in particular ¦P_av - N~¦ <= C_Q ¦(p,q)¦^5 on [0,mu_0] x closure(V) x {¦x¦ <= r_1} (real), where N~ equals the original N on V only
CONSTANT_SCOPE: r_1, C_Q depend on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:birkhoff-ext, bpP:p5:consts, bpP:p0:secavg#secularAverage, stepP:p5:ur-bound, stepP:p5:ur-schwarz
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:birkhoff-ext | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:uniform-remainder@L65-L67 | Q, N~, Omega~, beta~ and the vanishing jet (b)
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:uniform-remainder@L65-L65 | D_c' and eps_an
EDGE: bpP:p0:secavg#secularAverage | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:uniform-remainder@L67-L67 | P_av at real points
EDGE: stepP:p5:ur-bound | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:uniform-remainder@L72-L72 | proof step
EDGE: stepP:p5:ur-schwarz | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:uniform-remainder@L73-L73 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: uniform_remainder, schwarz_order_five (KAM/Planetary/PGAssembly/Remainder.lean)
LEAN_NOTE: audit P5-REM PASS WITH NOTES
NOTE: -

NODE: stepP:p5:ur-bound
KIND: step
TITLE: Bound
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ur-bound@L72-L72
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ur-bound@L72-L72
CONTRACT_ID: stepP:p5:ur-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q holomorphic in x on {¦x¦ < eps_an}; r_1 := eps_an/2; bounds M_P of P~ and Cauchy estimates for Omega~, beta~
SOURCE_QUANTIFIERS: (mu,I) in [0,mu_0] x D_c'
SOURCE_CONCLUSION: ¦Q¦ <= M_P + ¦N~¦ <= M_1 on D_c' x {¦x¦ <= r_1}, with M_1 from the bounds of bpP:p5:ext
CONSTANT_SCOPE: M_1 depends on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:ext, bpP:p5:birkhoff-ext, bpP:p5:consts, K:bp:p1:cauchy-open
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ur-bound@L72-L72 | bound M_P of P~
EDGE: bpP:p5:birkhoff-ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ur-bound@L72-L72 | Q = P~_av - N~ holomorphic, N~ with coefficients Omega~, beta~
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ur-bound@L72-L72 | eps_an
EDGE: K:bp:p1:cauchy-open | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ur-bound@L72-L72 | Cauchy estimates for the derivatives at 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: remainder_bound, uniform_remainder (KAM/Planetary/PGAssembly/Remainder.lean)
LEAN_NOTE: audit P5-REM PASS WITH NOTES
NOTE: -

NODE: stepP:p5:ur-schwarz
KIND: step
TITLE: Schwarz
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ur-schwarz@L73-L73
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ur-schwarz@L73-L73
CONTRACT_ID: stepP:p5:ur-schwarz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g(t) = Q(mu,I;t x^) holomorphic on ¦t¦ < r_1, ¦g¦ <= M_1, vanishing to order >= 5 at 0 by birkhoff-ext (b)
SOURCE_QUANTIFIERS: (mu,I) fixed, x^ with ¦x^¦ = 1
SOURCE_CONCLUSION: ¦g(t)¦ <= M_1 ¦t¦^5 / r_1^5, so C_Q := M_1 r_1^{-5}
CONSTANT_SCOPE: C_Q depends on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:birkhoff-ext, stepP:p5:ur-bound
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:birkhoff-ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ur-schwarz@L73-L73 | vanishing jet of Q to order 4
EDGE: stepP:p5:ur-bound | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ur-schwarz@L73-L73 | bound ¦g¦ <= M_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: schwarz_order_five (KAM/Planetary/PGAssembly/Remainder.lean)
LEAN_NOTE: audit P5-REM PASS WITH NOTES
NOTE: SOURCE_GAP: L73 invokes the one-variable maximum principle (equivalently the higher-order Schwarz estimate). L336 names Schwarz but creates no approved external node. The jet and uniform bound have the existing supplying edges.

NODE: bpP:p5:lip-complex
KIND: lemma
TITLE: Lipschitz bound on a complex neighbourhood
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lip-complex@L80-L82
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lip-complex@L83-L86
CONTRACT_ID: bpP:p5:lip-complex
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X subset R^N; rho > 0; Delta: X_{2 rho} -> C^m holomorphic with sup ¦Delta¦ <= A, where X_rho := {z in C^N: dist_inf(z,X) < rho}
SOURCE_QUANTIFIERS: N, X, rho, A, Delta given; then all z, z' in X_rho
SOURCE_CONCLUSION: ¦Delta(z) - Delta(z')¦ <= (2 N A/rho) ¦z - z'¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:cauchy-open, K:bp:p1:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:cauchy-open | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lip-complex@L84-L84 | Cauchy estimate ¦D Delta(w)¦ <= 2NA/rho on polydiscs of radius rho/2
EDGE: K:bp:p1:ext-mvt | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lip-complex@L84-L84 | mean value inequality along the segment
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: lip_complex (KAM/Planetary/PGAssembly/FastComplex.lean)
LEAN_NOTE: audit P5-BL PASS WITH NOTES
NOTE: prose L78 (notation X_rho) is mapped here. The candidate edge to bpP:p3:lip-sup is deleted: it sits in \source (the complex version of ...), provenance.

NODE: bpP:p5:bilip
KIND: lemma
TITLE: Complex bi-Lipschitz bound for $\bar\omega_0$
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:bilip@L88-L90
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:bilip@L91-L94
CONTRACT_ID: bpP:p5:bilip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: HasFastDiffeo(H_0,W) (so omega-bar_0 = omega_{H_0} is injective on W); delta_c, H~_0 of bpP:p5:ext; closure of V compact in W
SOURCE_QUANTIFIERS: data fixed; then rho_c in (0, delta_c/16) and c_0 > 0; for all z, z' in (closure V)_{rho_c}
SOURCE_CONCLUSION: there are rho_c in (0,delta_c/16) and c_0 > 0 with ¦omega~_0(z) - omega~_0(z')¦ >= c_0 ¦z - z'¦ for all z, z' in (closure V)_{rho_c}, omega~_0 = d H~_0; hence ¦(d omega~_0(z))^{-1}¦ <= c_0^{-1} there; and M0bar := sup over (closure V)_{2 rho_c} of ¦d omega~_0¦ < infinity
CONSTANT_SCOPE: rho_c, c_0, M0bar depend on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:fastdiffeo#HasFastDiffeomorphism, bpP:p5:ext, stepP:p5:bl-real, stepP:p5:bl-comp
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:fastdiffeo#HasFastDiffeomorphism | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:bilip@L89-L89 | hypothesis HasFastDiffeo(H_0,W)
EDGE: bpP:p5:ext | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:bilip@L89-L89 | H~_0, delta_c and the bounds M_0
EDGE: stepP:p5:bl-real | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:bilip@L92-L92 | proof step
EDGE: stepP:p5:bl-comp | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:bilip@L93-L93 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: bilip, complexFast (KAM/Planetary/PGAssembly/FastComplex.lean)
LEAN_NOTE: audit P5-BL PASS WITH NOTES
NOTE: -

NODE: stepP:p5:bl-real
KIND: step
TITLE: Real facts
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bl-real@L92-L92
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bl-real@L92-L92
CONTRACT_ID: stepP:p5:bl-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: HasFastDiffeo(H_0,W): g(omega-bar_0(I)) = I on W, g in C^1, omega-bar_0 analytic
SOURCE_QUANTIFIERS: I in W
SOURCE_CONCLUSION: omega-bar_0 is injective on W (contains closure V) and, differentiating g o omega-bar_0 = id (chain rule), d^2 H_0 = D omega-bar_0 is invertible on W
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:fastdiffeo#HasFastDiffeomorphism, bpP:p0:fastfreq#fastFrequency
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:fastdiffeo#HasFastDiffeomorphism | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bl-real@L92-L92 | clause (iii): g o omega_{H_0} = id on W, g C^1
EDGE: bpP:p0:fastfreq#fastFrequency | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bl-real@L92-L92 | omega-bar_0 = omega_{H_0} = dH_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: real_relation, omega_hasFDerivAt, omega_deriv_injective, fderiv_complexFast_lower (KAM/Planetary/PGAssembly/FastComplex.lean)
LEAN_NOTE: audit P5-BL PASS WITH NOTES; named by audit
NOTE: SOURCE_GAP: L92 uses the chain rule for g composed with the fast frequency map and the finite-dimensional inference that a square linear map with a left inverse is invertible. The frozen fast-diffeomorphism definition supplies the premises but does not itself prove these classical facts; no supplying input node is present.

NODE: stepP:p5:bl-comp
KIND: step
TITLE: Compactness
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bl-comp@L93-L93
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bl-comp@L93-L93
CONTRACT_ID: stepP:p5:bl-comp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z_m != z_m' in (closure V)_{1/m} with ¦omega~_0(z_m) - omega~_0(z_m')¦ < ¦z_m - z_m'¦/m (negation of the claim); closure of V compact; bl-real injectivity and invertibility
SOURCE_QUANTIFIERS: m large; limit points x, x' in closure V
SOURCE_CONCLUSION: contradiction in both cases x != x' (injectivity) and x = x' (continuity of d omega~_0 near x); the operator bound follows by differentiating along z' -> z; M0bar < infinity by the bounds of bpP:p5:ext
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p5:bl-real, bpP:p5:ext
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p5:bl-real | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bl-comp@L93-L93 | injectivity of omega-bar_0 on closure V and invertibility of d omega-bar_0
EDGE: bpP:p5:ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bl-comp@L93-L93 | omega~_0 = dH~_0, its continuity and the bound M_0 for M0bar
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: complexFast_local_lower, lower_lip_of_local (KAM/Planetary/PGAssembly/FastComplex.lean)
LEAN_NOTE: audit P5-BL PASS WITH NOTES; named by audit
NOTE: SOURCE_GAP: L93 uses compact sequential extraction in finite-dimensional complex space (listed as compactness at L336). No approved node supplies this classical input. The two-case contradiction is explicitly given in the source.

NODE: bpP:p5:dio-one
KIND: lemma
TITLE: One-scale Diophantine measure on $V$ (CP10 (38))
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:dio-one@L96-L98
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:dio-one@L99-L102
CONTRACT_ID: bpP:p5:dio-one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: L_g, R_y, Lambda_g as in bpP:p4:lip-inverse; S_1 as in bpP:p4:lattice-tail (with n = a+b, tau > n); gamma-bar > 0; D^1_gamma := {y in R^a: ¦k.y¦ >= gamma ¦k¦_1^{-tau} for all k in Z^a minus 0} (closed); omega-bar_0 = omega_{H_0}
SOURCE_QUANTIFIERS: data and tau > n fixed; then gamma-bar > 0
SOURCE_CONCLUSION: meas(V minus omega-bar_0^{-1}(D^1_gamma)) <= c_dio gamma-bar with c_dio := 2 Lambda_g^a S_1 (2 R_y)^{a-1}
CONSTANT_SCOPE: c_dio depends on (a, b, tau, H_0, V, W) only (through Lambda_g, R_y, S_1), not on gamma-bar, mu, r
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:lip-inverse, bpP:p4:lattice-tail, bpP:p4:affine-slab, K:bp:p1:lip-image, K:bp:p1:mcshane, bpP:p0:fastfreq#fastFrequency, K:bp:p1:ext-lebesgue
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:lip-inverse | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:dio-one@L97-L97 | constants L_g, R_y, Lambda_g, Y_0 and g(omega-bar_0(I)) = I
EDGE: bpP:p4:lattice-tail | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:dio-one@L97-L97 | S_1 bounds the sum of ¦k¦_1^{-tau} over Z^a minus 0
EDGE: bpP:p4:affine-slab | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:dio-one@L100-L100 | measure of Y_k with c = 0, N = a, ell = k
EDGE: K:bp:p1:lip-image | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:dio-one@L100-L100 | meas g(Y_k) <= Lambda_g^a meas Y_k
EDGE: K:bp:p1:mcshane | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:dio-one@L100-L100 | McShane extension of g before the Lipschitz-image estimate
EDGE: bpP:p0:fastfreq#fastFrequency | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:dio-one@L97-L97 | omega-bar_0 = fastFrequency H_0
EDGE: K:bp:p1:ext-lebesgue | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:dio-one@L100-L100 | countable subadditivity over k
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: dio_one, dioConstant (KAM/Planetary/PGMeasure/OneScale.lean)
LEAN_NOTE: audit P4-ONE PASS WITH NOTES
NOTE: -

NODE: bpP:p5:freq-data
KIND: lemma
TITLE: Constants of the averaged frequency map
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-data@L104-L108
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-data@L109-L113
CONTRACT_ID: bpP:p5:freq-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: N~ as in bpP:p5:birkhoff-ext; rho_c of bpP:p5:bilip; E := (closure V)_{rho_c} x {¦J_2¦ < 2}; G := d_{J_1} N~, Theta(J_1,xi) := Omega~(J_1) + beta~(J_1) xi
SOURCE_QUANTIFIERS: data fixed; then A_N, Lambda_N, M_beta, L_beta >= 1; for J_1, J_1' in (closure V)_{rho_c}, ¦xi¦, ¦xi'¦ <= 1; all mu in (0, mu_0]
SOURCE_CONCLUSION: there are A_N, Lambda_N, M_beta, L_beta >= 1 with N~, d_J N~, d^2_J N~ bounded by A_N on E; ¦G(J_1,xi) - G(J_1',xi)¦, ¦Theta(J_1,xi) - Theta(J_1',xi)¦ <= Lambda_N ¦J_1 - J_1'¦; ¦G(J_1,xi) - G(J_1,xi')¦ <= Lambda_N ¦xi - xi'¦; ¦nu¦ <= L_beta ¦beta~(J_1) nu¦ for nu in C^b (after decreasing rho_c); the real-variable constants of bpP:p4:data ((N1) to (N3) with D = D_t, lambda_0 = 1) hold with the same Lambda_N, L_beta for all mu in (0,mu_0]
CONSTANT_SCOPE: A_N, Lambda_N, M_beta, L_beta depend on the data only (not on mu, r)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:birkhoff-ext, bpP:p5:bilip, bpP:p4:data, bpP:p4:freq, stepP:p5:fd-bd, stepP:p5:fd-lip, stepP:p5:fd-beta
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:birkhoff-ext | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-data@L105-L105 | N~, Omega~, beta~ and their equality with the frozen P_0, Omega, beta on V
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-data@L105-L105 | rho_c of the complex neighbourhood
EDGE: bpP:p4:data | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-data@L107-L107 | the standing data (S4) that the constants must satisfy
EDGE: bpP:p4:freq | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-data@L105-L107 | G, Theta are the objects G_mu, omega^s_mu of the averaged frequency map
EDGE: stepP:p5:fd-bd | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-data@L110-L110 | proof step
EDGE: stepP:p5:fd-lip | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-data@L111-L111 | proof step
EDGE: stepP:p5:fd-beta | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-data@L112-L112 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: freq_data, pgAnalytic, pgAnalytic_spec, pgCU (KAM/Planetary/PGAssembly/FrequencyBounds.lean); PGAnalytic, PGAnalyticSpec (KAM/Planetary/PGAssembly/FrequencyDefs.lean)
LEAN_NOTE: audit P5-FD PASS WITH NOTES
NOTE: -

NODE: stepP:p5:fd-bd
KIND: step
TITLE: Bounds
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-bd@L110-L110
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-bd@L110-L110
CONTRACT_ID: stepP:p5:fd-bd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: N~ is a polynomial in J_2 with coefficients P~_0, Omega~, beta~ holomorphic and bounded on D_c; rho_c <= delta_c/16
SOURCE_QUANTIFIERS: J in E
SOURCE_CONCLUSION: N~, d_J N~, d^2_J N~ are bounded by A_N on E; J_1-derivatives up to order 3 bounded on (closure V)_{2 rho_c}
CONSTANT_SCOPE: A_N depends on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:birkhoff-ext, bpP:p5:ext, K:bp:p1:cauchy-open, bpP:p5:consts, bpP:p5:bilip
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:birkhoff-ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-bd@L110-L110 | coefficients holomorphic and bounded on D_c
EDGE: bpP:p5:ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-bd@L110-L110 | bound M_P and Cauchy
EDGE: K:bp:p1:cauchy-open | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-bd@L110-L110 | Cauchy estimates for derivatives in J_1
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-bd@L110-L110 | uses the complex strip, oscillator radius or averaged function of this package
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-bd@L110-L110 | uses rho_c, delta_c or M0bar in the domain or bound directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: jetPolynomial_norm_le, jetPolynomial_ball_bound, jetPolynomial_derivs_bound (KAM/Planetary/PGAssembly/FrequencyJets.lean)
LEAN_NOTE: audit P5-FD PASS WITH NOTES
NOTE: -

NODE: stepP:p5:fd-lip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-lip@L111-L111
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-lip@L111-L111
CONTRACT_ID: stepP:p5:fd-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lemma lip-complex; ¦xi¦ <= 1 makes the sup bound uniform; polynomial of degree <= 2 in J_2 on a convex set
SOURCE_QUANTIFIERS: J_1, J_1' in (closure V)_{rho_c}; ¦xi¦, ¦xi'¦ <= 1
SOURCE_CONCLUSION: Lipschitz bounds of G and Theta in J_1 and of G in xi with constant Lambda_N
CONSTANT_SCOPE: Lambda_N depends on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:lip-complex, stepP:p5:fd-bd
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:lip-complex | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-lip@L111-L111 | applied to d_{J_1} N~(.,xi) and Theta(.,xi)
EDGE: stepP:p5:fd-bd | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-lip@L111-L111 | sup bounds A_N
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: jpGrad_lip, jpTheta_lip, jpGrad_lip_slow (KAM/Planetary/PGAssembly/FrequencyLip.lean)
LEAN_NOTE: audit P5-FD PASS WITH NOTES
NOTE: -

NODE: stepP:p5:fd-beta
KIND: step
TITLE: Inverse of $\tilde\beta$
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-beta@L112-L112
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-beta@L112-L112
CONTRACT_ID: stepP:p5:fd-beta
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M_beta := sup ¦beta~_ij¦ on (closure V)_{rho_c}; ¦det beta~¦ >= B on closure V; det Lipschitz; beta~^T = beta~
SOURCE_QUANTIFIERS: J_1 in (closure V)_{rho_c}, nu in C^b
SOURCE_CONCLUSION: ¦det beta~¦ >= B/2 on (closure V)_{rho_c} after decreasing rho_c; ¦nu¦ <= L_beta ¦beta~ nu¦ with L_beta := 2 b! M_beta^{b-1}/B (Cramer; the adjugate bound holds for complex matrices)
CONSTANT_SCOPE: L_beta depends on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:birkhoff-ext, K:bp:p1:ext-cramer, bpP:p5:bilip
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:birkhoff-ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-beta@L112-L112 | (c): ¦det beta~¦ >= B on closure V; beta~ symmetric
EDGE: K:bp:p1:ext-cramer | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-beta@L112-L112 | Cramer inverse for complex matrices
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fd-beta@L112-L112 | rho_c decreased
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: jetBeta_lower, jetBeta_lip_mulVec, jetBeta_lower_nbhd (KAM/Planetary/PGAssembly/FrequencyBeta.lean)
LEAN_NOTE: audit P5-FD PASS WITH NOTES; compactness replaces Cramer
NOTE: The phrase "Cramer as in bpP:p4:beta-inverse" compares the repeated adjugate computation. The actual input is K:bp:p1:ext-cramer for complex matrices, not the real-vector conclusion of bpP:p4:beta-inverse.

NODE: bpP:p5:freq-inj
KIND: lemma
TITLE: Nondegeneracy and injectivity of the frequency map on the complex neighbourhood
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-inj@L115-L125
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-inj@L126-L130
CONTRACT_ID: bpP:p5:freq-inj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu in (0,mu_*] with mu_* <= 1 defined by mu_* A_N <= c_0/2, 4 mu_* A_N^2 L_beta <= c_0, 2 mu_* Lambda_N^2 L_beta < c_0; h~_mu := H~_0(J_1) + mu N~(J) on E_1 := (closure V)_{rho_c} x {¦J_2¦ < 1}; F_mu := d h~_mu = (omega~_0(J_1) + mu G(J), mu Theta(J_1,J_2)); U := d^2 h~_mu; constants of bpP:p5:freq-data and bpP:p5:bilip
SOURCE_QUANTIFIERS: data constants fixed; then mu_*; then mu in (0,mu_*], J, J' in E_1
SOURCE_CONCLUSION: (a) F_mu is injective on E_1; (b) U is invertible on E_1 and, with U = (U_11 U_12; U_21 U_22), U^{-1} = (T_1; T_2): ¦U¦ <= C_U, ¦hat U¦ <= C_U mu, ¦U^{-1}¦ <= C_U/mu, ¦T_1¦ <= C_U, ¦T_2¦ <= C_U/mu with C_U := max{M0bar + A_N + 1, 4(A_N+1)^2 L_beta c_0^{-1} + 4, 8 L_beta + 4}
CONSTANT_SCOPE: mu_*, C_U depend on the data only (not on mu, r)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:freq-data, bpP:p5:bilip, bpP:p5:birkhoff-ext, bpP:p5:ext, bpP:p4:freq, stepP:p5:fi-inj, stepP:p5:fi-blk, stepP:p5:fi-inv
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:freq-data | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-inj@L118-L118 | A_N, Lambda_N, L_beta, G, Theta
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-inj@L118-L118 | c_0, omega~_0, M0bar, rho_c
EDGE: bpP:p5:birkhoff-ext | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-inj@L118-L118 | N~
EDGE: bpP:p5:ext | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-inj@L118-L118 | H~_0
EDGE: bpP:p4:freq | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-inj@L118-L118 | F_mu is the complex-neighbourhood extension of the frequency map omega_mu
EDGE: stepP:p5:fi-inj | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-inj@L127-L127 | proof step (a)
EDGE: stepP:p5:fi-blk | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-inj@L128-L128 | proof step (b) blocks
EDGE: stepP:p5:fi-inv | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:freq-inj@L129-L129 | proof step: inverse
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: freq_inj (KAM/Planetary/PGAssembly/FrequencyInverse.lean)
LEAN_NOTE: audit P5-FI PASS WITH NOTES
NOTE: -

NODE: stepP:p5:fi-inj
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-inj@L127-L127
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-inj@L127-L127
CONTRACT_ID: stepP:p5:fi-inj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F_mu(J) = F_mu(J'); J, J' in E_1; mu_* conditions
SOURCE_QUANTIFIERS: J, J' in E_1
SOURCE_CONCLUSION: ¦J_1 - J_1'¦ <= (2 mu Lambda_N/c_0) ¦J_2 - J_2'¦ and ¦J_2 - J_2'¦ <= (2 mu Lambda_N^2 L_beta/c_0) ¦J_2 - J_2'¦, so J_2 = J_2' and J_1 = J_1'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:bilip, bpP:p5:freq-data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-inj@L127-L127 | c_0 ¦J_1 - J_1'¦ <= ¦omega~_0(J_1) - omega~_0(J_1')¦
EDGE: bpP:p5:freq-data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-inj@L127-L127 | Lipschitz bounds of G and Theta, L_beta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: freq_injOn (KAM/Planetary/PGAssembly/FrequencyInverse.lean)
LEAN_NOTE: audit P5-FI PASS WITH NOTES; named fi-inj
NOTE: -

NODE: stepP:p5:fi-blk
KIND: step
TITLE: (b) Blocks
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-blk@L128-L128
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-blk@L128-L128
CONTRACT_ID: stepP:p5:fi-blk
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U_11 = d omega~_0 + mu N~_11 =: A, U_12 = mu N~_12, U_21 = U_12^T, U_22 = mu beta~; mu A_N <= c_0/2 and 4 mu A_N^2 L_beta <= c_0
SOURCE_QUANTIFIERS: J in E_1
SOURCE_CONCLUSION: ¦A^{-1}¦ <= 2/c_0; the Schur complement S = mu(beta~ - mu N~_21 A^{-1} N~_12) satisfies ¦S^{-1}¦ <= 2 L_beta/mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:bilip, bpP:p5:freq-data, bpP:p3:ext-neumann
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-blk@L128-L128 | ¦(d omega~_0)^{-1}¦ <= c_0^{-1}
EDGE: bpP:p5:freq-data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-blk@L128-L128 | A_N bounds on N~ derivatives and ¦beta~^{-1}¦ <= L_beta
EDGE: bpP:p3:ext-neumann | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-blk@L128-L128 | Neumann inversion of A and of the normalized Schur complement
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27, ruling OVERNIGHT 01:20): the Lean proof of the PROVED parent freq_inj avoids this step
NOTE: SOURCE_GAP: L128 uses Schur-complement algebra without a supplying approved node; L336 names it but is not an external declaration. Neumann inversion is supplied separately by bpP:p3:ext-neumann.

NODE: stepP:p5:fi-inv
KIND: step
TITLE: Inverse
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-inv@L129-L129
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-inv@L129-L129
CONTRACT_ID: stepP:p5:fi-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: block inversion of U with the bounds of fi-blk
SOURCE_QUANTIFIERS: J in E_1
SOURCE_CONCLUSION: the blocks T_11, T_12, T_21, T_22 of U^{-1} have norms <= 2/c_0 + 8 mu A_N^2 L_beta c_0^{-2}, 4 A_N L_beta/c_0, 4 A_N L_beta/c_0, 2 L_beta/mu; hence the row-sum bounds with C_U
CONSTANT_SCOPE: C_U depends on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p5:fi-blk, bpP:p5:bilip, bpP:p5:freq-data
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p5:fi-blk | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-inv@L129-L129 | A^{-1} and S^{-1} bounds
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-inv@L129-L129 | c_0 in the block norms and M0bar in C_U
EDGE: bpP:p5:freq-data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:fi-inv@L129-L129 | A_N, L_beta in the block norms and C_U
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27, gap survey 2 item 4): freq_inj takes its bounds from inv_apriori inside jacobian_bounds and never forms a Schur block (as fi-blk); its row-sum clause is literal in freq_inj
NOTE: SOURCE_GAP: L129 invokes the block inverse identity, listed at L336 but without an approved external or proof of that identity. The displayed blocks and their bounds are preserved verbatim; fi-blk supplies the invertible diagonal blocks.

NODE: bpP:p5:params
KIND: definition
TITLE: Parameters as functions of $(r,\mu)$
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:params@L137-L145
PROOF_SOURCE: -
CONTRACT_ID: bpP:p5:params
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n = a+b; the data constants of Remark order (2); s_* of bpP:p5:consts; C_1, kappa_0, kappa_1, G (chosen in Remark order items 3 and 4); r in (0,1), mu in (0,mu_0), mu_2 := Lambda_P mu
SOURCE_QUANTIFIERS: the constants fixed first in the order of bpP:p5:order; then (r,mu); the listed quantities are explicit functions of (r,mu)
SOURCE_CONCLUSION: defines tau := n+1, c := 2 tau + 2, sigma_av := s_*/6, sigma_tot := s_*/12, s := sigma_tot/5, sbar := 4 sigma_tot/5, Kbar := (30/s_*) log(1/r), t := sqrt r, lambda_2 := r^2/2, lambda_1 := kappa_1 r^{5/2}, lambda_2' := lambda_2 - 2 lambda_1, l := lambda_2' - lambda_1, rho := lambda_1/2, gamma-bar := G max{sqrt(mu_2) Kbar^{tau+1/2} r^{-5/2}, r^{5/2} Kbar^{tau+1}}, alpha_av := gamma-bar/(2 Kbar^tau), rhobar := gamma-bar/(2 M0bar Kbar^{tau+1}), gamma_1 := kappa_0 r^{5/2}, gamma_2 := mu kappa_0 r^{5/2}, K := K_0 := (6/s) log_+(kappa_0^2/C_1^4); rho-hat, E-hat, r_K as in bpP:p3:constants; the sets D_t, Dcheck := D_t intersect omega-bar_0^{-1}(D^1_gamma) (compact), A_sh := (lambda_1, lambda_2')^b, D := Dcheck x A_sh; alpha_i := 2 pi gamma_i
CONSTANT_SCOPE: all quantities are functions of (r,mu) and of constants chosen before r, mu (K = K_0 does not depend on (r,mu)); C_1, kappa_0, kappa_1, G depend on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:order, bpP:p5:consts, bpP:p5:bilip, bpP:p3:constants, bpP:p4:conv#data, bpP:p5:dio-one, bpP:p0:fastfreq#fastFrequency, bpP:p5:kam-hyp#C1, bpP:p5:kam-cond#scales
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:order | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:params@L138-L138 | the constants fixed first and their order
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:params@L138-L138 | s_*, Lambda_P (mu_2), eps_an
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:params@L141-L141 | M0bar in rhobar
EDGE: bpP:p3:constants | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:params@L144-L144 | rho-hat, E-hat, r_K of Definition constants
EDGE: bpP:p4:conv#data | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:params@L144-L144 | D_t of the collar section
EDGE: bpP:p5:dio-one | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:params@L144-L144 | D^1_gamma and Dcheck := D_t intersect omega-bar_0^{-1}(D^1_gamma)
EDGE: bpP:p0:fastfreq#fastFrequency | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:params@L144-L144 | omega-bar_0 = omega_{H_0}
EDGE: bpP:p5:kam-hyp#C1 | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:params@L138-L138 | uses the numerical constant choice separately from the later estimate
EDGE: bpP:p5:kam-cond#scales | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:params@L138-L138 | uses the numerical constant choice separately from the later estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: PGParameters, params, checkedCore, pgActionDomain, admissible (KAM/Planetary/PGAssembly/Parameters.lean)
LEAN_NOTE: audit P5-PAR PASS WITH NOTES; definitions only
NOTE: C_1 and kappa_0,kappa_1,G come from the numerical-choice projections. No edge to the compound kam-hyp or kam-cond result is needed: their later estimates consume params. Remark order records the order, not the defining formulas or inequalities.

NODE: bpP:p5:rstar
KIND: definition
TITLE: Smallness thresholds
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L147-L156
PROOF_SOURCE: -
CONTRACT_ID: bpP:p5:rstar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the constants of Remark order items 2-4 (analytic constants, tau, C_1, widths, kappa_0, kappa_1, G) and C_* of Proposition lower; mu_1 := min{mu_*, (2(1+M) a Lambda_N Lambda_g)^{-1}}, M = 2 b Lambda_N L_beta (bpP:p4:data); c_dio of bpP:p5:dio-one; C_gamma := G (30/s_*)^{tau+1}
SOURCE_QUANTIFIERS: all constants fixed before r_*; then 0 < r < r_*
SOURCE_CONCLUSION: defines r_* in (0, min{r_0, e^{-1/5}, 1}) so small that for 0 < r < r_*: (r1) log(1/r_*) >= Lambda_P, r_*^2 (log 1/r_*)^{tau+1} <= 1 (so mu < r^6/(log 1/r)^c implies mu_2 <= r^6 (log 1/r)^{-(2 tau+1)}) and r_*^6 <= mu_1; (r2) sqrt(r_*) < d, A sqrt(r_*) <= (1/2) meas V, r_* <= r_1/2, r_* <= eps_an/4; (r3) C_gamma sqrt(r_*) <= 2 M0bar rho_c and c_dio C_gamma sqrt(r_*) <= (1/4) meas V; (r4) 6 kappa_1 sqrt(r_*) <= 1/2; (r5) the displacement margin sqrt(2) Delta_max <= kappa_1 r^{3/2} and (C_*+1) sqrt(r_*) <= 1/2
CONSTANT_SCOPE: r_* depends on the data and the constants of Remark order items 2-4 and C_* only; not on r or mu
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:order, bpP:p5:consts, bpP:p5:uniform-remainder, bpP:p5:freq-inj, bpP:p5:freq-data, bpP:p4:data, bpP:p4:lip-inverse, bpP:p5:dio-one, bpP:p5:bilip, bpP:p4:conv#data, bpP:p5:lower#constant, bpP:p5:kam-cond#scales, bpP:p5:rstar#Cgamma
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:order | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L148-L148 | the constants of items 2 to 4 fixed before r_*
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L150-L151 | Lambda_P, eps_an, s_*
EDGE: bpP:p5:uniform-remainder | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L151-L151 | r_1
EDGE: bpP:p5:freq-inj | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L150-L150 | mu_*
EDGE: bpP:p5:freq-data | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L150-L150 | Lambda_N, L_beta
EDGE: bpP:p4:data | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L150-L150 | mu_1 and M of the standing data
EDGE: bpP:p4:lip-inverse | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L150-L150 | Lambda_g in mu_1
EDGE: bpP:p5:dio-one | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L152-L152 | c_dio
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L152-L152 | M0bar, rho_c
EDGE: bpP:p4:conv#data | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L151-L151 | A, d, meas V in (r2)
EDGE: bpP:p5:lower#constant | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L148-L148 | uses the numerical constant choice separately from the later estimate
EDGE: bpP:p5:kam-cond#scales | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L150-L150 | uses the numerical constant choice separately from the later estimate
EDGE: bpP:p5:rstar#Cgamma | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L152-L152 | uses the numerical constant choice separately from the later estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: rstar, pgRstar (KAM/Planetary/PGAssembly/Threshold.lean)
LEAN_NOTE: audit P5-TH PASS WITH NOTES
NOTE: C_* is supplied by lower#constant and the numerical C_b witness, independently of their later estimates. The admissible-radius estimates use (r1)-(r4) and the displacement half of (r5); after those constants are chosen shrink the preliminary radius to impose (C_*+1)sqrt(r_*)<=1/2. Delta_max is bounded by the explicit numerical expression 18 r^(11/2)/(G eps_an) from L171-L179; the sufficient displacement condition involves no averaging-map construction. No edge to the compound lower, budget, avg or location result is justified.

NODE: bpP:p5:param-facts
KIND: lemma
TITLE: Consequences of the parameter choice
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:param-facts@L158-L163
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:param-facts@L164-L166
CONTRACT_ID: bpP:p5:param-facts
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < r < r_* (bpP:p5:rstar); 0 < mu < min{mu_0, r^6/(log 1/r)^c}; objects of bpP:p5:params
SOURCE_QUANTIFIERS: the constants fixed first; then r, mu in the stated ranges
SOURCE_CONCLUSION: (a) mu_2 <= r^6 (log 1/r)^{-(2 tau+1)}, mu < mu_1, Kbar s_* = 30 log(1/r) >= 6, gamma-bar <= C_gamma sqrt r; (b) rhobar <= rho_c, rhobar >= lambda_1 if G >= 2 M0bar kappa_1 (so rho = lambda_1/2 <= rhobar/2), l >= lambda_2/2 >= r^2/4; (c) meas D_t >= (1/2) meas V, meas Dcheck >= (1/4) meas V, meas D_t <= 4 meas Dcheck
CONSTANT_SCOPE: C_gamma depends on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:rstar, bpP:p5:params, bpP:p4:collar, bpP:p5:dio-one, bpP:p5:bilip, bpP:p4:conv#data, bpP:p5:consts
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:param-facts@L159-L165 | conditions (r1) to (r4)
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:param-facts@L160-L160 | Kbar, gamma-bar, rhobar, lambda_i, l, Dcheck
EDGE: bpP:p4:collar | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:param-facts@L165-L165 | (b): meas D_t >= meas V - A t
EDGE: bpP:p5:dio-one | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:param-facts@L165-L165 | meas(D_t minus Dcheck) <= c_dio gamma-bar
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:param-facts@L165-L165 | M0bar in rhobar <= rho_c
EDGE: bpP:p4:conv#data | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:param-facts@L165-L165 | D_t, A, meas V
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:param-facts@L158-L163 | uses the complex strip, oscillator radius or averaged function of this package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: param_facts (KAM/Planetary/PGAssembly/Threshold.lean)
LEAN_NOTE: audit P5-TH PASS WITH NOTES
NOTE: -

NODE: bpP:p5:avg
KIND: proposition
TITLE: Averaged system in CP variables
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L170-L174
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L175-L180
CONTRACT_ID: bpP:p5:avg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < r < r_*, admissible mu; objects of bpP:p5:params; P~ of bpP:p5:ext; P~_av, eps_an, sigma_av of bpP:p5:consts; N~, Q of bpP:p5:birkhoff-ext; W := {(I,phi,p,q) in C^{2n}: I in Dcheck_{rhobar/2}, ¦Im phi¦ < sigma_av, ¦(p,q)¦ < eps_an/2}
SOURCE_QUANTIFIERS: constants fixed first; then (r,mu)
SOURCE_CONCLUSION: there is a holomorphic, injective map Psi-bar on W, real at real points, with Psi-bar - id 2pi-periodic in phi, mapping W into the domain of P~, with D Psi-bar^T M_0 D Psi-bar = M_0 (symplectic), H_mu o Psi-bar = H~_0(I) + mu N~(I,R) + mu Q(mu,I;p,q) + P~_rem with N-norm of P~_rem <= 2 Lambda_P mu r^5 on W, and ¦I - I-bar¦ <= Delta_I := 12 mu_2 Kbar^tau/(s_* gamma-bar), ¦p - p-bar¦, ¦q - q-bar¦ <= Delta_max := 18 mu_2 Kbar^tau/(eps_an gamma-bar); with Delta_max <= 18 r^{11/2}/(G eps_an), Delta_I <= 12 r^{11/2}/(G s_*)
CONSTANT_SCOPE: constants depend on the data only; Psi-bar depends on (r,mu)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:ext, bpP:p5:params, bpP:p5:consts, bpP:p5:birkhoff-ext, bpP:p5:param-facts, bpP:p2:osc-averaging, bpP:p0:degham#degenerateHamiltonian, stepP:p5:av-dict, stepP:p5:av-R1, stepP:p5:av-R2, stepP:p5:av-id
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:ext | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L171-L171 | domain of P~ into which Psi-bar maps W
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L171-L171 | Dcheck, rhobar, sigma_av, eps_an and the parameters
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L171-L171 | sigma_av, eps_an, Lambda_P
EDGE: bpP:p5:birkhoff-ext | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L172-L172 | N~ and Q
EDGE: bpP:p5:param-facts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L171-L171 | admissible (r,mu), rhobar <= rho_c
EDGE: bpP:p2:osc-averaging | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L171-L171 | symplectic conclusion of the oscillator averaging
EDGE: bpP:p0:degham#degenerateHamiltonian | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L172-L172 | H_mu = H_0 + mu P
EDGE: stepP:p5:av-dict | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L176-L176 | proof step
EDGE: stepP:p5:av-R1 | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L177-L177 | proof step
EDGE: stepP:p5:av-R2 | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L178-L178 | proof step
EDGE: stepP:p5:av-id | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:avg@L179-L179 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: pg_avg, pgAvg (KAM/Planetary/PGAssembly/Averaging.lean); PGAveraging, AveragingSpec (KAM/Planetary/PGAssembly/AveragingDefs.lean)
LEAN_NOTE: audit P5-AV PASS WITH NOTES; signed theorem pg_avg (renamed from avg)
NOTE: -

NODE: stepP:p5:av-dict
KIND: step
TITLE: Dictionary
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-dict@L176-L176
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-dict@L176-L176
CONTRACT_ID: stepP:p5:av-dict
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Prop averaged-remainder with n = a, m = b, D = Dcheck, epsilon = r, mu -> mu_2, P -> P~/Lambda_P (N-norm <= 1); canonical chart (theta,I,p,q) = (phi/2pi, 2pi I_CP, p, q); s_0 = s_*/2pi, alpha = alpha_av, d = rhobar s_*, kappa = Kbar s_* = 30 log(1/r), e^{-kappa/6} = r^5
SOURCE_QUANTIFIERS: (r,mu) admissible
SOURCE_CONCLUSION: the setting of bpP:p2:averaged-remainder is matched to the CP variables: parameter dictionary s_0, alpha, d, kappa, mu_2, P~/Lambda_P
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:averaged-remainder, bpP:p5:consts, bpP:p2:use5, bpP:p5:params, bpP:p5:param-facts, bpP:p5:bilip
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:averaged-remainder | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-dict@L176-L176 | the averaged-remainder proposition applied
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-dict@L176-L176 | normalisation of P~ by Lambda_P
EDGE: bpP:p2:use5 | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-dict@L176-L176 | canonical chart (3) and the period dictionary
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-dict@L176-L176 | Kbar, alpha_av, rhobar, mu_2, Dcheck
EDGE: bpP:p5:param-facts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-dict@L176-L176 | rhobar <= rho_c < eps_an^2/s_*
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-dict@L176-L176 | rho_c decreased
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: pg_osc_normalization (KAM/Planetary/PGAssembly/AveragingNorm.lean); pg_osc_domain (KAM/Planetary/PGAssembly/AveragingDom.lean); avg_diff, avg_sympl, avg_real_mem (KAM/Planetary/PGAssembly/AveragingConj.lean); avg_chart (KAM/Planetary/PGAssembly/AveragingDisp.lean)
LEAN_NOTE: audit P5-AV PASS WITH NOTES
NOTE: -

NODE: stepP:p5:av-R1
KIND: step
TITLE: (R1)
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R1@L177-L177
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R1@L177-L177
CONTRACT_ID: stepP:p5:av-R1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I' in Dcheck_{rhobar}, I in Dcheck with ¦I' - I¦ < rhobar, 0 < ¦k¦_1 <= Kbar; omega-bar_0(I) in D^1_gamma-bar; mean value inequality on [I,I'] subset (closure V)_{rho_c}
SOURCE_QUANTIFIERS: I', I, k as stated
SOURCE_CONCLUSION: ¦k . omega~_0(I')¦ >= gamma-bar/(2 Kbar^tau) = alpha_av (CP10 (39))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:params, bpP:p5:bilip, K:bp:p1:ext-mvt, bpP:p5:param-facts, bpP:p5:ext
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R1@L177-L177 | Dcheck, gamma-bar, rhobar, alpha_av, Kbar
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R1@L177-L177 | ¦d omega~_0¦ <= M0bar on (closure V)_{2 rho_c}
EDGE: K:bp:p1:ext-mvt | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R1@L177-L177 | mean value inequality on the segment
EDGE: bpP:p5:param-facts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R1@L177-L177 | rhobar <= rho_c so the segment lies in (closure V)_{rho_c}
EDGE: bpP:p5:ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R1@L177-L177 | omega~_0 = d H~_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: core_divisor, pg_osc_divisor (KAM/Planetary/PGAssembly/AveragingDiv.lean)
LEAN_NOTE: audit P5-AV PASS WITH NOTES
NOTE: -

NODE: stepP:p5:av-R2
KIND: step
TITLE: (R2) and the remainder
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R2@L178-L178
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R2@L178-L178
CONTRACT_ID: stepP:p5:av-R2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: alpha_av d = gamma-bar^2 s_*/(4 M0bar Kbar^{2 tau+1}) >= G^2 s_* mu_2 r^{-5}/(4 M0bar) (first branch of gamma-bar); G^2 >= 2^14 (1+b) M0bar and G^2 >= 1600 (1+b) M0bar/s_*
SOURCE_QUANTIFIERS: (r,mu) admissible
SOURCE_CONCLUSION: (R2): 2^12 (1+b) Kbar s_* mu_2 <= alpha_av d and 400 (1+b) mu_2/(alpha_av d) <= r^5; hence the N-norm of P~_rem <= mu_2 r^5 + mu_2 r^5 = 2 Lambda_P mu r^5
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:params, bpP:p5:order, bpP:p2:averaged-remainder, stepP:p5:av-dict, bpP:p5:consts, bpP:p5:bilip, bpP:p5:rstar, bpP:p5:kam-cond#scales
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R2@L178-L178 | gamma-bar, alpha_av, d
EDGE: bpP:p5:order | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R2@L178-L178 | the conditions on G are met by the choice of G in Remark order item 4
EDGE: bpP:p2:averaged-remainder | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R2@L178-L178 | remainder bound of the proposition
EDGE: stepP:p5:av-dict | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R2@L178-L178 | the matched setting
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R2@L178-L178 | uses the complex strip, oscillator radius or averaged function of this package
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R2@L178-L178 | uses rho_c, delta_c or M0bar in the domain or bound directly
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R2@L178-L178 | uses the threshold or C_gamma and its smallness conditions directly
EDGE: bpP:p5:kam-cond#scales | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-R2@L178-L178 | uses the numerical constant choice separately from the later estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: gammaBar_sq, pg_osc_small (KAM/Planetary/PGAssembly/AveragingSmall.lean); two_pi_avgB_le (KAM/Planetary/PGAssembly/AveragingRem.lean); avg_rem_fourier, avg_rem_pointwise (KAM/Planetary/PGAssembly/AveragingFourier.lean)
LEAN_NOTE: audit P5-AV PASS WITH NOTES
NOTE: The G inequalities are supplied by the scale-choice projection of kam-cond item (3), not by the order remark alone. The threshold edge supplies the small-r regime; Kbar r^5<=1 follows from (r2), r<=eps_an/4<=s_*/8 and r log(1/r)<=1.

NODE: stepP:p5:av-id
KIND: step
TITLE: Identification
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-id@L179-L179
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-id@L179-L179
CONTRACT_ID: stepP:p5:av-id
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu_2 <P_2> = mu P~_av = mu N~ + mu Q (birkhoff-ext); displacement bounds of averaged-remainder converted by use5 (3): alpha_av s_* ¦Delta I¦ <= 6 mu_2, alpha_av eps_an ¦Delta p¦, ¦Delta q¦ <= 9 mu_2; gamma-bar >= G sqrt(mu_2) Kbar^{tau+1/2} r^{-5/2}
SOURCE_QUANTIFIERS: (r,mu) admissible
SOURCE_CONCLUSION: the displayed identity H_mu o Psi-bar = H~_0 + mu N~ + mu Q + P~_rem and the displacements Delta_I, Delta_max with mu_2 Kbar^tau/gamma-bar <= r^{11/2}/G
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p2:averaged-remainder, bpP:p5:birkhoff-ext, bpP:p2:use5, bpP:p5:params, stepP:p5:av-dict, stepP:p5:av-R2, bpP:p5:consts
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p2:averaged-remainder | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-id@L179-L179 | average and displacement bounds
EDGE: bpP:p5:birkhoff-ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-id@L179-L179 | P~_av = N~ + Q
EDGE: bpP:p2:use5 | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-id@L179-L179 | conversion of the displacement bounds to CP variables
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-id@L179-L179 | alpha_av, gamma-bar
EDGE: stepP:p5:av-dict | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-id@L179-L179 | the matched setting
EDGE: stepP:p5:av-R2 | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-id@L179-L179 | remainder bound of the N-norm
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:av-id@L179-L179 | uses the complex strip, oscillator radius or averaged function of this package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: pg_osc_zero (KAM/Planetary/PGAssembly/AveragingBound.lean); avg_hamil (KAM/Planetary/PGAssembly/AveragingHamil.lean); avg_disp (KAM/Planetary/PGAssembly/AveragingDisp.lean)
LEAN_NOTE: audit P5-AV PASS WITH NOTES
NOTE: -

NODE: bpP:p5:phi
KIND: definition
TITLE: Polar chart, composite chart $\Phi$
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi@L184-L186
PROOF_SOURCE: -
CONTRACT_ID: bpP:p5:phi
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: psi = (psi_f, psi_s) in R^n, J = (J_1,J_2) with J_2 in (0,infinity)^b; Psi-bar of bpP:p5:avg; Dcheck, rhobar, lambda_1, lambda_2 of bpP:p5:params
SOURCE_QUANTIFIERS: (psi,J) in R^n x R^n; O_0 defined from (r,mu)
SOURCE_CONCLUSION: defines Pol(psi,J) = ((phi,q),(I,p)) with phi = psi_f, I = J_1, (q_j,p_j) = sqrt(2 J_{2,j}) (sin psi_{s,j}, cos psi_{s,j}) (the map Pi of bpP:p4:s-disc#chart in the frozen order; holomorphic on Re J_2 > 0 by the principal square root), O_0 := {(psi,J): J_1 in Re(Dcheck_{rhobar/2}), J_2 in (lambda_1/2, 2 lambda_2)^b} (open, invariant under psi -> psi + 2 pi k) and Phi := Psi-bar o Pol on O_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:s-disc#chart, bpP:p5:avg, bpP:p5:params, bpP:p0:blocks#assemble
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:s-disc#chart | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi@L185-L185 | Pol is the map Pi (action-angle chart of the oscillators)
EDGE: bpP:p5:avg | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi@L185-L185 | Psi-bar
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi@L185-L185 | Dcheck, rhobar, lambda_1, lambda_2
EDGE: bpP:p0:blocks#assemble | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi@L185-L185 | frozen order ((phi,q),(I,p))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: phi, phiDomain, oscillatorPolarComplex, oscillatorPolarComplex_real (KAM/Planetary/PGAssembly/ChartDefs.lean)
LEAN_NOTE: audit P5-CH round 2 PASS WITH NOTES; definitions exact source objects
NOTE: -

NODE: bpP:p5:phi-chart
KIND: lemma
TITLE: $\Phi$ is a $1$-chart with the lattice properties of \Pref{bpP:p1:cyl-pipeline}
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi-chart@L188-L191
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi-chart@L192-L196
CONTRACT_ID: bpP:p5:phi-chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < r < r_*, admissible mu; Phi, Pol, O_0 of bpP:p5:phi; Psi-bar of bpP:p5:avg; H_mu = H_0 + mu P
SOURCE_QUANTIFIERS: (r,mu) admissible; k in Z^n, z, z' in O_0
SOURCE_CONCLUSION: Phi is a symplectic chart on O_0 (Definition chart, c = 1), O_0 + (2 pi k,0) = O_0, Phi(z + (2 pi k,0)) = Phi(z) + shift(k_f), and Phi(z') = Phi(z) + shift(k_f) implies z' = z + (2 pi m, 0) for some m in Z^n; H_mu o Phi = h_mu + f_mu on O_0 with h_mu(J) = H~_0(J_1) + mu N~(J) and f_mu = (mu Q + P~_rem) o Pol
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:phi, bpP:p5:avg, bpP:p1:chart, bpP:p0:degham#degenerateHamiltonian, bpP:p0:fastshift#fastShift, stepP:p5:pc-img, stepP:p5:pc-lat, stepP:p5:pc-ham, bpP:p5:params, bpP:p5:birkhoff-ext
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi-chart@L189-L189 | Phi, Pol, O_0
EDGE: bpP:p5:avg | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi-chart@L189-L190 | Psi-bar and the identity for H_mu o Psi-bar
EDGE: bpP:p1:chart | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi-chart@L189-L189 | Definition of a (conformally) symplectic chart with c = 1
EDGE: bpP:p0:degham#degenerateHamiltonian | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi-chart@L189-L189 | H_mu
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi-chart@L189-L189 | shift(k_f)
EDGE: stepP:p5:pc-img | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi-chart@L193-L193 | proof step
EDGE: stepP:p5:pc-lat | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi-chart@L194-L194 | proof step
EDGE: stepP:p5:pc-ham | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi-chart@L195-L195 | proof step
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi-chart@L188-L191 | uses the parameter definitions (widths, scales, domain or shell) directly
EDGE: bpP:p5:birkhoff-ext | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:phi-chart@L188-L191 | uses N-tilde and Q in the displayed Hamiltonian directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: phi_chart, phi_comp_hamiltonian (KAM/Planetary/PGAssembly/Chart.lean)
LEAN_NOTE: audit P5-CH round 2 PASS WITH NOTES; geometry plus literal Hamiltonian identity cover full lemma
NOTE: -

NODE: stepP:p5:pc-img
KIND: step
TITLE: Image
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-img@L193-L193
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-img@L193-L193
CONTRACT_ID: stepP:p5:pc-img
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z in O_0; abs bounds sqrt(2 J_2) < 2 sqrt(lambda_2) <= 2 r < eps_an/2; Psi-bar real analytic and symplectic (Prop avg); Pol a 1-chart on {J_2>0}
SOURCE_QUANTIFIERS: z in O_0
SOURCE_CONCLUSION: Pol(O_0) is contained in W intersect R^{2n}, so Psi-bar is defined and holomorphic there; Phi = Psi-bar o Pol is a symplectic chart (composition of charts)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:avg, bpP:p1:hol-chart, bpP:p1:typical, bpP:p5:phi, bpP:p5:rstar, bpP:p5:params, bpP:p5:consts
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:avg | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-img@L193-L193 | Psi-bar real analytic and symplectic on W
EDGE: bpP:p1:hol-chart | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-img@L193-L193 | a real-analytic restriction of a holomorphic symplectic map is a chart
EDGE: bpP:p1:typical | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-img@L193-L193 | Remark typical (1) for each oscillator and (3) for compositions
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-img@L193-L193 | Pol, O_0
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-img@L193-L193 | r_* <= eps_an/4 gives 2r < eps_an/2
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-img@L193-L193 | lambda_2 = r^2/2
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-img@L193-L193 | uses the complex strip, oscillator radius or averaged function of this package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: polar_mem_averagingDomain (KAM/Planetary/PGAssembly/ChartMem.lean); phi_chart (KAM/Planetary/PGAssembly/Chart.lean)
LEAN_NOTE: audit P5-CH round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p5:pc-lat
KIND: step
TITLE: Lattice
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-lat@L194-L194
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-lat@L194-L194
CONTRACT_ID: stepP:p5:pc-lat
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Pol(psi + 2 pi k, J) = Pol(psi,J) + shift(k_f); Psi-bar - id periodic; Psi-bar injective; Pol injective modulo psi -> psi + 2 pi k on {J_2 > 0}
SOURCE_QUANTIFIERS: k in Z^n, z, z' in O_0
SOURCE_CONCLUSION: Phi(z + (2 pi k,0)) = Phi(z) + shift(k_f) and Phi(z') = Phi(z) + shift(k_f) implies z' = z + (2 pi m,0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:avg, bpP:p4:disc-measure, bpP:p0:fastshift#fastShift, bpP:p5:phi
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:avg | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-lat@L194-L194 | Psi-bar - id periodic and Psi-bar injective
EDGE: bpP:p4:disc-measure | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-lat@L194-L194 | (a): Pol injective modulo 2 pi on {J_2 > 0}
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-lat@L194-L194 | shift(k_f) moves only the fast angles
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-lat@L194-L194 | Pol, Phi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: oscillatorPolar_fullShift (KAM/Planetary/PGAssembly/ChartMem.lean); phi_chart (KAM/Planetary/PGAssembly/Chart.lean)
LEAN_NOTE: audit P5-CH round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p5:pc-ham
KIND: step
TITLE: Hamiltonian
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-ham@L195-L195
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-ham@L195-L195
CONTRACT_ID: stepP:p5:pc-ham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H_mu o Psi-bar from Prop avg; R_j o Pol = J_{2,j}
SOURCE_QUANTIFIERS: z in O_0
SOURCE_CONCLUSION: H_mu o Phi = h_mu + f_mu with f_mu = (mu Q + P~_rem) o Pol
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:avg, bpP:p0:oscaction#oscillatorAction, bpP:p5:phi
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:avg | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-ham@L195-L195 | H_mu o Psi-bar = H~_0 + mu N~(I,R) + mu Q + P~_rem
EDGE: bpP:p0:oscaction#oscillatorAction | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-ham@L195-L195 | R_j o Pol = J_{2,j}
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:pc-ham@L195-L195 | Phi = Psi-bar o Pol
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: phi_comp_hamiltonian (KAM/Planetary/PGAssembly/Chart.lean)
LEAN_NOTE: audit P5-CH round 2 PASS WITH NOTES; closes audit-1 F1
NOTE: -

NODE: bpP:p5:kam-hyp
KIND: lemma
TITLE: Hypotheses of the two-scale KAM theorem
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L198-L202
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L203-L208
CONTRACT_ID: bpP:p5:kam-hyp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < r < r_*, 0 < mu < min{mu_0, r^6/(log 1/r)^c}; h_mu, f_mu of bpP:p5:phi-chart; H_3(J,theta) := H~(J,2 pi theta)/2pi with H~ = h_mu + f_mu in (J,psi); objects of bpP:p5:params
SOURCE_QUANTIFIERS: constants chosen before (r,mu) in the order of Remark order; C_1 >= 1 depends on the data only; then (r,mu)
SOURCE_CONCLUSION: there is C_1 >= 1 (data only) such that the hypotheses of bpP:p3:two-scale-kam hold with n_1 = a, n_2 = b, tau = n+1, D = Dcheck x A_sh, rho = lambda_1/2, A = D_rho, s, sbar of bpP:p5:params, and M = C_1, hat M = C_1 mu, bar M = bar M_2 = C_1/mu, bar M_1 = C_1, E = C_1 mu r^5; explicitly C_1 := max{1, 2 pi C_U, C_R coth(sigma_av/4)^n/2 pi} with C_R := 2^5 C_Q + 2 Lambda_P
CONSTANT_SCOPE: C_1 depends on the data only (Remark order items 2-3), not on r, mu
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p3:two-scale-kam, bpP:p5:params, bpP:p5:rstar, bpP:p5:phi-chart, bpP:p3:period-dictionary, bpP:p5:freq-inj, bpP:p5:uniform-remainder, bpP:p5:consts, stepP:p5:kh-dom, stepP:p5:kh-h, stepP:p5:kh-f, stepP:p5:kh-norm, bpP:p5:kam-hyp#C1
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L199-L199 | the hypotheses of the two-scale KAM theorem to be verified
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L199-L200 | D = Dcheck x A_sh, rho, s, sbar, tau, c
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L199-L199 | 0 < r < r_*
EDGE: bpP:p5:phi-chart | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L199-L199 | h_mu, f_mu in the variables (J,psi)
EDGE: bpP:p3:period-dictionary | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L199-L199 | H_3 = H~(J,2 pi theta)/2 pi
EDGE: bpP:p5:freq-inj | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L201-L201 | C_U
EDGE: bpP:p5:uniform-remainder | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L201-L201 | C_Q in C_R
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L201-L201 | Lambda_P, sigma_av
EDGE: stepP:p5:kh-dom | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L204-L204 | proof step
EDGE: stepP:p5:kh-h | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L205-L205 | proof step
EDGE: stepP:p5:kh-f | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L206-L206 | proof step
EDGE: stepP:p5:kh-norm | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L207-L207 | proof step
EDGE: bpP:p5:kam-hyp#C1 | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L201-L201 | uses the numerical constant choice separately from the later estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: kam_hyp, pg_kam_hyp (KAM/Planetary/PGAssembly/KAMInputs.lean); kamH, pgKamScale (KAM/Planetary/PGAssembly/KAMInputsBase.lean); kamF (KAM/Planetary/PGAssembly/KAMInputsF.lean)
LEAN_NOTE: audit P5-KH PASS WITH NOTES; signed exports kamH, kamF, kam_hyp, pgKamScale, pg_kam_hyp (+ pg_kam_dictionary)
NOTE: -

NODE: stepP:p5:kh-dom
KIND: step
TITLE: Domain
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-dom@L204-L204
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-dom@L204-L204
CONTRACT_ID: stepP:p5:kh-dom
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D_rho = Dcheck_rho x (A_sh)_rho (max norm) with rho <= rhobar/2 <= rho_c; ¦J_2¦ < lambda_2' + rho < 1; polar image within W
SOURCE_QUANTIFIERS: (r,mu) admissible
SOURCE_CONCLUSION: D_rho subset E_1; the polar image of D_rho x {¦Im psi¦ < sigma_av} lies in W (¦(p-bar,q-bar)¦ < 2r <= eps_an/2); so f_mu is holomorphic on D_rho x {¦Im psi¦ < sigma_av}, 2 pi-periodic and real at real points, and h_mu is holomorphic on D_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:params, bpP:p5:param-facts, bpP:p5:freq-inj, bpP:p5:avg, bpP:p5:phi, bpP:p5:consts, bpP:p5:phi-chart, bpP:p5:rstar
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-dom@L204-L204 | D, rho, Dcheck, A_sh, rhobar
EDGE: bpP:p5:param-facts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-dom@L204-L204 | rho <= rhobar/2 <= rho_c, lambda_2' + rho < 1
EDGE: bpP:p5:freq-inj | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-dom@L204-L204 | E_1 = (closure V)_{rho_c} x {¦J_2¦ < 1}
EDGE: bpP:p5:avg | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-dom@L204-L204 | W and holomorphy of Psi-bar
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-dom@L204-L204 | polar image under Pol
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-dom@L204-L204 | sigma_av, eps_an
EDGE: bpP:p5:phi-chart | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-dom@L204-L204 | f_mu = (mu Q + P~_rem) o Pol
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-dom@L204-L204 | uses the threshold or C_gamma and its smallness conditions directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: actionNbhd_sub_analytic, kamH_differentiableOn (KAM/Planetary/PGAssembly/KAMInputsKamH.lean); kamPolar_mem, kamF_differentiableOn (KAM/Planetary/PGAssembly/KAMInputsF.lean); kamF_periodic, kamH_real, kamF_real (KAM/Planetary/PGAssembly/KAMInputsPer.lean); complexFrequency_realSlice (KAM/Planetary/PGAssembly/KAMInputsFreq.lean)
LEAN_NOTE: audit P5-KH PASS WITH NOTES; audit table kh-dom PASS
NOTE: -

NODE: stepP:p5:kh-h
KIND: step
TITLE: $h$
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-h@L205-L205
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-h@L205-L205
CONTRACT_ID: stepP:p5:kh-h
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lemma freq-inj bounds for U; h_3 = h_mu/2pi so U_3 = U/2pi, U_3^{-1} = 2 pi U^{-1}; mu < mu_* by param-facts (a)
SOURCE_QUANTIFIERS: (r,mu) admissible
SOURCE_CONCLUSION: d h_3 = F_mu/2pi is injective on A, U_3 nonsingular, ¦U_3¦ <= C_U, ¦hat U_3¦ <= C_U mu, ¦U_3^{-1}¦ <= 2 pi C_U/mu, ¦T_1¦ <= 2 pi C_U, ¦T_2¦ <= 2 pi C_U/mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:freq-inj, bpP:p5:param-facts, stepP:p5:kh-dom
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:freq-inj | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-h@L205-L205 | bounds of U, U^{-1}, T_1, T_2 and injectivity of F_mu
EDGE: bpP:p5:param-facts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-h@L205-L205 | mu < mu_* since mu < mu_1
EDGE: stepP:p5:kh-dom | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-h@L205-L205 | A = D_rho subset E_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: freq_kamH, kamH_injOn, kamH_hessian (KAM/Planetary/PGAssembly/KAMInputsKamH.lean)
LEAN_NOTE: audit P5-KH PASS WITH NOTES; audit table kh-h PASS
NOTE: -

NODE: stepP:p5:kh-f
KIND: step
TITLE: $f$
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-f@L206-L206
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-f@L206-L206
CONTRACT_ID: stepP:p5:kh-f
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: on the polar image ¦x¦ < 2r <= r_1; sup bounds of mu Q (uniform remainder) and P~_rem (N-norm bound of avg); sup-to-weighted conversion with loss sigma_av/2
SOURCE_QUANTIFIERS: (r,mu) admissible
SOURCE_CONCLUSION: sup of ¦f_mu¦ <= C_R mu r^5 on the strip sigma_av, hence the N-norm of f_3 at (rho, sigma_tot) is <= C_R coth(sigma_av/4)^n mu r^5/2 pi <= C_1 mu r^5 = E
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:uniform-remainder, bpP:p5:avg, bpP:p5:consts, N:bpN:p4:sup-weighted, stepP:p5:kh-dom, bpP:p5:phi-chart, bpP:p5:rstar, bpP:p5:params, bpP:p5:kam-hyp#C1
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:uniform-remainder | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-f@L206-L206 | ¦Q¦ <= C_Q ¦x¦^5
EDGE: bpP:p5:avg | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-f@L206-L206 | N-norm of P~_rem <= 2 Lambda_P mu r^5
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-f@L206-L206 | sup-to-weighted conversion and Lambda_P
EDGE: N:bpN:p4:sup-weighted | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-f@L206-L206 | sup <= weighted norm and weighted <= coth . sup
EDGE: stepP:p5:kh-dom | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-f@L206-L206 | polar image inside W
EDGE: bpP:p5:phi-chart | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-f@L206-L206 | f_mu = (mu Q + P~_rem) o Pol
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-f@L206-L206 | 2r <= r_1 from r_* <= r_1/2
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-f@L206-L206 | uses the parameter definitions (widths, scales, domain or shell) directly
EDGE: bpP:p5:kam-hyp#C1 | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-f@L206-L206 | C_R := 2^5 C_Q + 2 Lambda_P and the defining maximum give C_R coth(sigma_av/4)^n/(2 pi) <= C_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-delta-P-g
REVIEWER: sol-delta2-P-b
LEAN_STATUS: PROVED
LEAN_REF: kamF_eq, kamF_sup (KAM/Planetary/PGAssembly/KAMInputsF.lean); kam_hyp (KAM/Planetary/PGAssembly/KAMInputs.lean)
LEAN_NOTE: audit P5-KH PASS WITH NOTES; audit table kh-f PASS
NOTE: -

NODE: stepP:p5:kh-norm
KIND: step
TITLE: Normalizations
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-norm@L207-L207
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-norm@L207-L207
CONTRACT_ID: stepP:p5:kh-norm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M = C_1, hat M = C_1 mu, bar M_i; mu <= 1
SOURCE_QUANTIFIERS: (r,mu) admissible
SOURCE_CONCLUSION: hat M <= M and bar M_i <= bar M, the normalisations required by Proposition two-scale-kam; all numerical constants are upper bounds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p3:rem-norm, stepP:p5:kh-h, bpP:p3:two-scale-kam, bpP:p5:rstar
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p3:rem-norm | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-norm@L207-L207 | normalisation hat M <= M, bar M_i <= bar M and the order of computing the constants
EDGE: stepP:p5:kh-h | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-norm@L207-L207 | values M, hat M, bar M
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-norm@L207-L207 | the normalisation required by its data
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kh-norm@L207-L207 | uses the threshold or C_gamma and its smallness conditions directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: mu_lt_one_of_admissible (KAM/Planetary/PGAssembly/KAMInputsBase.lean); pg_kam_hyp (KAM/Planetary/PGAssembly/KAMInputs.lean)
LEAN_NOTE: audit P5-KH PASS WITH NOTES; audit table kh-norm PASS
NOTE: -

NODE: bpP:p5:kam-cond
KIND: lemma
TITLE: Scale constants and the KAM condition
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L212-L222
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L223-L226
CONTRACT_ID: bpP:p5:kam-cond
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hat c = hat c(n,tau) = max{2^13 n, 24^{tau+1}/3} (bpP:p3:constants); C_1, s of bpP:p5:kam-hyp and bpP:p5:params; r in (0,1) small enough that rho = lambda_1/2 makes sense; mu in (0,1]
SOURCE_QUANTIFIERS: constants chosen in this order: kappa_0 >= C_1^2 with kappa_0^2 > 9 hat c C_1^4 K_0^{2 tau+2}; kappa_1 with kappa_1^2 > 4 hat c C_1^2; G >= max{2 M0bar kappa_1, (2^14 (1+b) M0bar)^{1/2}, (1600 (1+b) M0bar/s_*)^{1/2}}; then (r,mu)
SOURCE_CONCLUSION: with them, L = C_1/mu, x = C_1^4/kappa_0^2, K = K_0 independent of (r,mu), rho-hat = min{kappa_0 r^{5/2}/(3 C_1 K_0^{tau+1}), kappa_1 r^{5/2}/2}, E-hat = C_1^2 r^5/rho-hat^2 = max{9 C_1^4 K_0^{2 tau+2}/kappa_0^2, 4 C_1^2/kappa_1^2} < 1/hat c, i.e. the KAM condition hat c E-hat < 1 holds, gamma_1 >= gamma_2 and tau > n
CONSTANT_SCOPE: kappa_0, kappa_1, G depend on the data only (chosen in this order), not on (r,mu)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p3:constants, bpP:p5:kam-hyp, bpP:p5:params, bpP:p5:bilip, bpP:p5:consts, stepP:p5:kc-eval, stepP:p5:kc-small, bpP:p5:kam-cond#scales
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p3:constants | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L213-L213 | hat c, L, K, rho-hat, E-hat of Definition constants
EDGE: bpP:p5:kam-hyp | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L213-L219 | C_1 and the values M, hat M, bar M, E
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L213-L219 | s, gamma_i, K_0 of the parameter definition
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L217-L217 | M0bar in the condition on G
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L217-L217 | s_* in the condition on G
EDGE: stepP:p5:kc-eval | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L224-L224 | proof step
EDGE: stepP:p5:kc-small | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L225-L225 | proof step
EDGE: bpP:p5:kam-cond#scales | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L215-L215 | uses the numerical constant choice separately from the later estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: kam_cond_node (KAM/Planetary/PGAssembly/ScaleNodes.lean)
LEAN_NOTE: audit GAP-P5a round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p5:kc-eval
KIND: step
TITLE: Evaluation
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kc-eval@L224-L224
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kc-eval@L224-L224
CONTRACT_ID: stepP:p5:kc-eval
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: L = max{bar M, M^{-1}, hat M^{-1}} with M = C_1, hat M = C_1 mu, bar M = C_1/mu; C_1 >= 1, mu <= 1; E M^2 L = C_1^4 r^5; x = C_1^4 r^5/gamma_1^2
SOURCE_QUANTIFIERS: (r,mu) with mu <= 1
SOURCE_CONCLUSION: L = C_1/mu, x = C_1^4/kappa_0^2 <= 1, K = (6/s) log_+(1/x) = K_0 exactly, rho-hat as displayed, E-hat = E L/rho-hat^2 = C_1^2 r^5/rho-hat^2 and the displayed max
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:kam-hyp, bpP:p3:constants, bpP:p5:params
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:kam-hyp | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kc-eval@L224-L224 | the values M, hat M, bar M, E
EDGE: bpP:p3:constants | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kc-eval@L224-L224 | the formulas for L, K, x, rho-hat, E-hat
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kc-eval@L224-L224 | gamma_1, gamma_2, K_0, s
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: kc_eval (KAM/Planetary/PGAssembly/ScaleNodes.lean)
LEAN_NOTE: audit GAP-P5a round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p5:kc-small
KIND: step
TITLE: Smallness
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kc-small@L225-L225
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kc-small@L225-L225
CONTRACT_ID: stepP:p5:kc-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the choice of kappa_0, kappa_1 (items 1, 2 of the lemma); gamma_2 = mu gamma_1
SOURCE_QUANTIFIERS: (r,mu) as above
SOURCE_CONCLUSION: hat c E-hat < 1 (KAM condition), gamma_2 = mu gamma_1 <= gamma_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p5:kc-eval, bpP:p3:constants, bpP:p5:params, bpP:p5:kam-cond#scales
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p5:kc-eval | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kc-small@L225-L225 | the displayed value of E-hat
EDGE: bpP:p3:constants | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kc-small@L225-L225 | hat c and the KAM condition hat c E-hat < 1
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kc-small@L225-L225 | uses the parameter definitions (widths, scales, domain or shell) directly
EDGE: bpP:p5:kam-cond#scales | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:kc-small@L225-L225 | uses the numerical constant choice separately from the later estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: kc_small (KAM/Planetary/PGAssembly/ScaleNodes.lean)
LEAN_NOTE: audit GAP-P5a round 2 PASS WITH NOTES
NOTE: -

NODE: bpP:p5:rK
KIND: lemma
TITLE: The radius $r_K$ (what Part~4 should state instead of $r_K\le C\hat\rho\le C\gamma_2$)
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rK@L228-L231
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rK@L232-L234
CONTRACT_ID: bpP:p5:rK
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the situation of bpP:p5:kam-cond; r_K := 32 E-hat rho-hat (the enlargement radius of bpP:p3:two-scale-kam)
SOURCE_QUANTIFIERS: all admissible (r,mu)
SOURCE_CONCLUSION: r_K < rho-hat/(256 n) <= lambda_1/(512 n); r_K < min{t, lambda_1}; r_K < rhobar/2; 2 r_K/l <= kappa_1 sqrt(r)/(64 n); (1 + 2 r_K/l)^b < 2
CONSTANT_SCOPE: none (functions of (r,mu))
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:kam-cond, bpP:p3:two-scale-kam, bpP:p5:params, stepP:p5:rk-dir, bpP:p5:rstar
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:kam-cond | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rK@L229-L229 | hat c E-hat < 1, E-hat and rho-hat
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rK@L229-L229 | r_K = 32 E-hat rho-hat is its enlargement radius
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rK@L230-L230 | t, lambda_1, l, rhobar
EDGE: stepP:p5:rk-dir | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rK@L233-L233 | proof step
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rK@L228-L231 | uses the threshold or C_gamma and its smallness conditions directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: r_k (KAM/Planetary/PGAssembly/Threshold.lean); rk_dir (KAM/Planetary/PGAssembly/ScaleNodes.lean)
LEAN_NOTE: audit P5-TH PASS WITH NOTES + GAP-P5a round 2 (rk_dir supplies the bounds)
NOTE: -

NODE: stepP:p5:rk-dir
KIND: step
TITLE: Direct
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:rk-dir@L233-L233
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:rk-dir@L233-L233
CONTRACT_ID: stepP:p5:rk-dir
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hat c >= 2^13 n and hat c E-hat < 1; rho-hat <= rho = lambda_1/2; lambda_1 = kappa_1 r^{5/2} < sqrt r = t (r4); lambda_1 <= rhobar and l >= r^2/4 (param-facts (b)); (1+x)^b <= e^{bx}
SOURCE_QUANTIFIERS: admissible (r,mu)
SOURCE_CONCLUSION: E-hat < 2^{-13}/n so r_K < rho-hat/(256 n) <= lambda_1/(512 n), r_K < min{t, lambda_1}, r_K < rhobar/2, 2 r_K/l <= kappa_1 sqrt r/(64 n), (1+2 r_K/l)^b < 2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:kam-cond, bpP:p3:constants, bpP:p5:param-facts, bpP:p5:params, bpP:p5:rstar
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:kam-cond | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:rk-dir@L233-L233 | KAM condition hat c E-hat < 1
EDGE: bpP:p3:constants | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:rk-dir@L233-L233 | hat c >= 2^13 n
EDGE: bpP:p5:param-facts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:rk-dir@L233-L233 | (b): lambda_1 <= rhobar, l >= lambda_2/2 >= r^2/4
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:rk-dir@L233-L233 | lambda_1, t, rho
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:rk-dir@L233-L233 | (r4): kappa_1 r^2 < 1 and kappa_1 sqrt r <= 1/12
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: rk_dir (KAM/Planetary/PGAssembly/ScaleNodes.lean)
LEAN_NOTE: audit GAP-P5a round 2 PASS WITH NOTES
NOTE: -

NODE: bpP:p5:location
KIND: lemma
TITLE: Location of the tori in the cylinder
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:location@L241-L243
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:location@L244-L248
CONTRACT_ID: bpP:p5:location
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi_omega = (v, theta + u) a torus of bpP:p3:two-scale-kam (so v in Re(D_{r_K})); z := Phi(2 pi (theta + u), v) in Ph_n; Delta_max of bpP:p5:avg; (r5): sqrt 2 Delta_max <= kappa_1 r^{3/2}; 0 < r < r_*
SOURCE_QUANTIFIERS: (r,mu) admissible; omega in Omega_*, theta in R^n
SOURCE_CONCLUSION: v lies in the O_0-range (v_1 in Re(Dcheck_{rhobar/2}), v_2 in (lambda_1/2, 2 lambda_2)^b), I(z) in V and p_j^2 + q_j^2 < r^2 for all j; hence z in C(V,r)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p3:two-scale-kam, bpP:p5:phi, bpP:p5:avg, bpP:p0:cylinder#cylinder, bpP:p5:rstar, stepP:p5:lo-range, stepP:p5:lo-act, stepP:p5:lo-disc, bpP:p5:params
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:location@L242-L242 | the torus phi_omega and v in Re(D_{r_K})
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:location@L242-L242 | Phi, O_0
EDGE: bpP:p5:avg | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:location@L242-L242 | Delta_max, Delta_I
EDGE: bpP:p0:cylinder#cylinder | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:location@L242-L242 | z in C(V,r)
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:location@L242-L242 | (r5), r < r_*
EDGE: stepP:p5:lo-range | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:location@L245-L245 | proof step
EDGE: stepP:p5:lo-act | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:location@L246-L246 | proof step
EDGE: stepP:p5:lo-disc | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:location@L247-L247 | proof step
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:location@L241-L243 | uses the parameter definitions (widths, scales, domain or shell) directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: location (KAM/Planetary/PGAssembly/Chart.lean)
LEAN_NOTE: audit P5-CH round 2 PASS WITH NOTES
NOTE: -

NODE: stepP:p5:lo-range
KIND: step
TITLE: Range
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-range@L245-L245
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-range@L245-L245
CONTRACT_ID: stepP:p5:lo-range
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v in Re(D_{r_K}): dist(v_1, Dcheck) < r_K < rhobar/2 and v_2 in (lambda_1 - r_K, lambda_2' + r_K)^b
SOURCE_QUANTIFIERS: torus point v
SOURCE_CONCLUSION: v_1 in Re(Dcheck_{rhobar/2}) and v_2 in (lambda_1/2, 2 lambda_2)^b
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:rK, bpP:p5:params, bpP:p5:phi
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:rK | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-range@L245-L245 | r_K < rhobar/2 and r_K < lambda_1/2
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-range@L245-L245 | Dcheck, A_sh, lambda_i
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-range@L245-L245 | the O_0-range
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: location (KAM/Planetary/PGAssembly/Chart.lean)
LEAN_NOTE: local to PROVED parent location (ruling 01:20 (b)); audit P5-CH confirms (docs/tracks/P/audits/P5-CH-audit-2.md:64)
NOTE: -

NODE: stepP:p5:lo-act
KIND: step
TITLE: Actions
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-act@L246-L246
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-act@L246-L246
CONTRACT_ID: stepP:p5:lo-act
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I = I-bar + (I - I-bar), I-bar = v_1, dist(I-bar, D_t) < r_K, ¦I - I-bar¦ <= Delta_I; r_K + Delta_I < t
SOURCE_QUANTIFIERS: torus point
SOURCE_CONCLUSION: I in N_{r_K+Delta_I}(D_t) subset V by the collar lemma (c)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:avg, bpP:p4:collar, bpP:p5:rK, bpP:p5:params, bpP:p4:conv#data, bpP:p5:rstar
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:avg | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-act@L246-L246 | ¦I - I-bar¦ <= Delta_I
EDGE: bpP:p4:collar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-act@L246-L246 | (c): N_s(D_t) subset V for s < t
EDGE: bpP:p5:rK | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-act@L246-L246 | r_K < t
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-act@L246-L246 | t = sqrt r and Delta_I < t via the bound r^{11/2}/G
EDGE: bpP:p4:conv#data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-act@L246-L246 | N_s and D_t
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-act@L246-L246 | uses the threshold or C_gamma and its smallness conditions directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: location (KAM/Planetary/PGAssembly/Chart.lean)
LEAN_NOTE: local to PROVED parent location (ruling 01:20 (b)); audit P5-CH confirms (docs/tracks/P/audits/P5-CH-audit-2.md:65)
NOTE: -

NODE: stepP:p5:lo-disc
KIND: step
TITLE: Discs
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-disc@L247-L247
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-disc@L247-L247
CONTRACT_ID: stepP:p5:lo-disc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: polar point (p-bar,q-bar): p-bar_j^2 + q-bar_j^2 = 2 v_{2,j} < 2 (lambda_2' + r_K) <= r^2 - 3 lambda_1; ¦p - p-bar¦, ¦q - q-bar¦ <= Delta_max; (r5)
SOURCE_QUANTIFIERS: torus point, j <= b
SOURCE_CONCLUSION: sqrt(p_j^2 + q_j^2) < r - (3/2) kappa_1 r^{3/2} + kappa_1 r^{3/2} < r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:rK, bpP:p5:avg, bpP:p5:rstar, bpP:p5:params, bpP:p5:phi
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:rK | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-disc@L247-L247 | 2 r_K <= lambda_1 so p-bar_j^2 + q-bar_j^2 <= r^2 - 3 lambda_1
EDGE: bpP:p5:avg | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-disc@L247-L247 | ¦p - p-bar¦, ¦q - q-bar¦ <= Delta_max
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-disc@L247-L247 | (r5): sqrt 2 Delta_max <= kappa_1 r^{3/2}
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-disc@L247-L247 | lambda_2', lambda_1
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-disc@L247-L247 | polar point of v
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: location (KAM/Planetary/PGAssembly/Chart.lean)
LEAN_NOTE: local to PROVED parent location (ruling 01:20 (b)); audit P5-CH confirms (docs/tracks/P/audits/P5-CH-audit-2.md:66)
NOTE: -

NODE: bpP:p5:kset
KIND: definition
TITLE: Torus family and Kolmogorov set
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kset@L250-L254
PROOF_SOURCE: -
CONTRACT_ID: bpP:p5:kset
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: bpP:p5:params (D = Dcheck x A_sh, gamma_i, tau); omega_0 = d h_3 = F_mu/2 pi (bpP:p5:kam-hyp); phi_omega the tori of bpP:p3:two-scale-kam; Phi of bpP:p5:phi; B subset D_0 Borel
SOURCE_QUANTIFIERS: (r,mu) admissible; omega in Omega_*; B subset D_0 Borel
SOURCE_CONCLUSION: defines Omega_* := omega_0(D) intersect D_{gamma_1,gamma_2,tau}, D_0 := D^dio = omega_0^{-1}(Omega_*) intersect D, Omega_B := omega_0(B), K_omega(theta) := Phi(S_{2 pi} pi phi_omega(theta)), S_B := union over omega in Omega_B of K_omega(R^n), K_B := union over omega in Omega_B of phi_omega(R^n) subset R^n x R^n (coordinates (J,vartheta)); D_0 is relatively closed in D and sigma-compact
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p3:two-scale-kam, bpP:p1:two-scale, bpP:p5:params, bpP:p5:kam-hyp, bpP:p5:phi, bpP:p1:period-convert, bpP:p1:order
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kset@L251-L251 | Omega_*, D^dio and the tori phi_omega
EDGE: bpP:p1:two-scale | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kset@L251-L251 | the set D_{gamma_1,gamma_2,tau}
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kset@L251-L251 | D, gamma_i, tau
EDGE: bpP:p5:kam-hyp | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kset@L251-L251 | h_3 and omega_0 = d h_3 = F_mu/2pi
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kset@L252-L252 | Phi
EDGE: bpP:p1:period-convert | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kset@L253-L253 | S_{2 pi}
EDGE: bpP:p1:order | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kset@L253-L253 | the relabelling pi(J,vartheta) = (vartheta,J)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: pgD0_relClosed (KAM/Planetary/PGAssembly/LocationNodes.lean)
LEAN_NOTE: audit GAP-P5b round 3 PASS WITH NOTES
NOTE: -

NODE: bpP:p5:torus-conv
KIND: proposition
TITLE: Each torus is a frozen cylinder torus with frozen frequencies
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L256-L258
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L259-L264
CONTRACT_ID: bpP:p5:torus-conv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < r < r_*, admissible mu; omega in Omega_*; w := omega; K_omega of bpP:p5:kset; C_w := (M_omega + A_N)/2 pi + 1, M_omega := sup over closure V of ¦omega-bar_0¦
SOURCE_QUANTIFIERS: r_*, mu admissible fixed; omega in Omega_*
SOURCE_CONCLUSION: IsCylTorus(H_mu, C(V,r), w, K_omega); w is (min{gamma_1,gamma_2}, tau)-Diophantine with tau = n+1 > a+b; ¦w^f¦ <= C_w, ¦w^s¦ <= C_w mu; K_omega(R^n) subset C(V,r)
CONSTANT_SCOPE: C_w depends on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:kset, bpP:p0:cyltorus#IsCylinderTorus, bpP:p0:cylinder#cylinder, bpP:p0:diophantine#IsDiophantine, bpP:p1:dio-sources, bpP:p5:rstar, stepP:p5:tc-chart, stepP:p5:tc-LT, stepP:p5:tc-pipe, stepP:p5:tc-freq, bpP:p5:params, bpP:p5:freq-data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L257-L257 | Omega_*, K_omega
EDGE: bpP:p0:cyltorus#IsCylinderTorus | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L257-L257 | the predicate IsCylTorus
EDGE: bpP:p0:cylinder#cylinder | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L257-L257 | C(V,r)
EDGE: bpP:p0:diophantine#IsDiophantine | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L257-L257 | (gamma,tau)-Diophantine
EDGE: bpP:p1:dio-sources | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L257-L257 | Diophantine clause for the frozen predicate
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L257-L257 | r < r_*
EDGE: stepP:p5:tc-chart | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L260-L260 | proof step
EDGE: stepP:p5:tc-LT | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L261-L261 | proof step
EDGE: stepP:p5:tc-pipe | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L262-L262 | proof step
EDGE: stepP:p5:tc-freq | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L263-L263 | proof step
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L256-L258 | uses the parameter definitions (widths, scales, domain or shell) directly
EDGE: bpP:p5:freq-data | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:torus-conv@L256-L258 | uses A_N in the displayed C_w directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: torus_conv_node (KAM/Planetary/PGAssembly/LocationNodes.lean)
LEAN_NOTE: audit GAP-P5b round 3 PASS WITH NOTES (constant A_N from freq-data)
NOTE: -

NODE: stepP:p5:tc-chart
KIND: step
TITLE: Chart data
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-chart@L260-L260
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-chart@L260-L260
CONTRACT_ID: stepP:p5:tc-chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lemma phi-chart supplies O_0, Phi with the hypotheses of the pipeline lemma (d = n); G_3 = (2 pi)^{-1} (H_mu o Phi)(2 pi z_1, z_2)
SOURCE_QUANTIFIERS: (r,mu) admissible
SOURCE_CONCLUSION: G_3 equals H_3 in the frozen order pi on O = S_{2 pi}^{-1}(O_0), so the pipeline hypotheses hold
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:phi-chart, bpP:p1:cyl-pipeline, bpP:p5:kam-hyp, bpP:p5:phi, bpP:p1:period-convert
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:phi-chart | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-chart@L260-L260 | O_0, Phi and H_mu o Phi = h_mu + f_mu
EDGE: bpP:p1:cyl-pipeline | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-chart@L260-L260 | hypotheses of the pipeline lemma
EDGE: bpP:p5:kam-hyp | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-chart@L260-L260 | H_3 = (h_mu + f_mu)(.,2 pi theta)/2 pi
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-chart@L260-L260 | uses Phi, Pol or O_0 directly
EDGE: bpP:p1:period-convert | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-chart@L260-L260 | uses S_{2pi} directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: fam_ham_eq (KAM/Planetary/PGAssembly/FamilyAux.lean)
LEAN_NOTE: audit P5-FAM PASS WITH NOTES; pulled-back H equals Re(kamH+kamF) on the real strip (Revision-4 attachment)
NOTE: -

NODE: stepP:p5:tc-LT
KIND: step
TITLE: $\operatorname{LT}(G_3,O,w,K_3)$, $K_3=\pi\circ\varphi_\omega$
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261
CONTRACT_ID: stepP:p5:tc-LT
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi_omega real analytic (Prop two-scale-kam (a)); K_3 = pi o phi_omega; K_3(R^n) subset O by location; H_mu analytic near Phi(.) in C(V,r) since r < r_0, (H1), H_0 analytic on W; G_3 = H_3 on Re(D_rho) x R^n
SOURCE_QUANTIFIERS: omega in Omega_*
SOURCE_CONCLUSION: LT(G_3, O, w, K_3) holds: (L1) analyticity, K_3(R^n) subset O, G_3 differentiable at K_3(theta); (L2) periodicity; (L3) injectivity modulo translations; (L4), (L5) isotropy and injectivity of the derivative; (L6) invariance under the Hamiltonian flow in the order pi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p3:two-scale-kam, bpP:p5:location, stepP:p5:lo-range, bpP:p1:chart-field, bpP:p1:order, bpP:p1:lattice-torus, bpP:p5:rK, bpP:p5:phi-chart, bpP:p0:fastdiffeo#HasFastDiffeomorphism, bpP:p0:degham#degenerateHamiltonian, stepP:p5:tc-chart, bpP:p5:params, bpP:p5:phi, bpP:p5:kset, bpP:p1:period-convert
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | conclusions (a), (b), (c) and injectivity modulo translations
EDGE: bpP:p5:location | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | K_3(R^n) subset O and the range v
EDGE: stepP:p5:lo-range | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | range of v
EDGE: bpP:p1:chart-field | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | chart-field lemma: H_mu is analytic near the chart image
EDGE: bpP:p1:order | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | relabelling pi of the frozen order
EDGE: bpP:p1:lattice-torus | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | the lattice-torus predicate LT
EDGE: bpP:p5:rK | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | r_K < rho
EDGE: bpP:p5:phi-chart | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | G_3 = H_3
EDGE: bpP:p0:fastdiffeo#HasFastDiffeomorphism | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | H_0 analytic on W
EDGE: bpP:p0:degham#degenerateHamiltonian | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | H_mu = H_0 + mu P near the image
EDGE: stepP:p5:tc-chart | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L260-L261 | O and G_3
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | uses the parameter definitions (widths, scales, domain or shell) directly
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | uses Phi, Pol or O_0 directly
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | uses D_0, K_omega, S_B or the action-angle torus union directly
EDGE: bpP:p1:period-convert | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-LT@L261-L261 | uses S_{2pi} directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: fam_lattice (KAM/Planetary/PGAssembly/FamilyAux.lean); torus_conv (KAM/Planetary/PGAssembly/Family.lean)
LEAN_NOTE: audit P5-FAM PASS WITH NOTES; lattice-torus transfer, hypothesis is the P3 two-scale-kam torus output
NOTE: -

NODE: stepP:p5:tc-pipe
KIND: step
TITLE: Pipeline
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-pipe@L262-L262
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-pipe@L262-L262
CONTRACT_ID: stepP:p5:tc-pipe
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the pipeline lemma with U = C(V,r) containing Psi(K_3(R^n)) = K_omega(R^n) (location)
SOURCE_QUANTIFIERS: omega in Omega_*
SOURCE_CONCLUSION: IsCylTorus(H_mu, C(V,r), w, K_omega) with the same w = omega
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p1:cyl-pipeline, bpP:p5:location, stepP:p5:tc-LT, stepP:p5:tc-chart, bpP:p0:cyltorus#IsCylinderTorus, bpP:p0:cylinder#cylinder, bpP:p5:kset
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p1:cyl-pipeline | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-pipe@L262-L262 | lattice torus to IsCylTorus
EDGE: bpP:p5:location | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-pipe@L262-L262 | K_omega(R^n) subset C(V,r)
EDGE: stepP:p5:tc-LT | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-pipe@L262-L262 | LT(G_3,O,w,K_3)
EDGE: stepP:p5:tc-chart | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-pipe@L262-L262 | pipeline hypotheses
EDGE: bpP:p0:cyltorus#IsCylinderTorus | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-pipe@L262-L262 | conclusion predicate
EDGE: bpP:p0:cylinder#cylinder | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-pipe@L262-L262 | U = C(V,r)
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-pipe@L262-L262 | K_omega
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: torus_conv, PGFamilySpec (KAM/Planetary/PGAssembly/Family.lean)
LEAN_NOTE: audit P5-FAM PASS WITH NOTES; final IsCylinderTorus clause of PGFamilySpec, same frequency
NOTE: -

NODE: stepP:p5:tc-freq
KIND: step
TITLE: Frequencies
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-freq@L263-L263
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-freq@L263-L263
CONTRACT_ID: stepP:p5:tc-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega = omega_0(I_0), I_0 = (J_1,J_2) in D real, ¦J_2¦ <= lambda_2 <= 1; ¦G¦, ¦Theta¦ <= A_N; gamma_1, gamma_2 > 0, tau > n
SOURCE_QUANTIFIERS: omega in Omega_*
SOURCE_CONCLUSION: w^f = (omega-bar_0(J_1) + mu G)/2 pi and w^s = mu Theta/2 pi are bounded by C_w and C_w mu; w is (min{gamma_1,gamma_2}, tau)-Diophantine
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:kset, bpP:p5:freq-data, bpP:p0:fastfreq#fastFrequency, bpP:p1:dio-sources, bpP:p0:diophantine#IsDiophantine, bpP:p5:kam-hyp, bpP:p5:params
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-freq@L263-L263 | omega = omega_0(I_0) with I_0 in D
EDGE: bpP:p5:freq-data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-freq@L263-L263 | ¦G¦, ¦Theta¦ <= A_N
EDGE: bpP:p0:fastfreq#fastFrequency | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-freq@L263-L263 | omega-bar_0 and M_omega
EDGE: bpP:p1:dio-sources | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-freq@L263-L263 | (a): Diophantine clause
EDGE: bpP:p0:diophantine#IsDiophantine | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-freq@L263-L263 | IsDiophantine
EDGE: bpP:p5:kam-hyp | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-freq@L263-L263 | omega_0 = F_mu/2 pi
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:tc-freq@L263-L263 | uses the parameter definitions (widths, scales, domain or shell) directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: tc_freq_node (KAM/Planetary/PGAssembly/LocationNodes.lean)
LEAN_NOTE: audit GAP-P5b round 3 PASS WITH NOTES
NOTE: -

NODE: bpP:p5:cell-transfer
KIND: lemma
TITLE: Borelness, whole tori, cell measure
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:cell-transfer@L266-L268
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:cell-transfer@L269-L275
CONTRACT_ID: bpP:p5:cell-transfer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B subset D_0 sigma-compact; A_B := K_B intersect (R^n x [0,1)^n) (the measured representative: an output-angle cell); 0 < r < r_*, admissible mu
SOURCE_QUANTIFIERS: (r,mu) admissible; B subset D_0 sigma-compact
SOURCE_CONCLUSION: (a) A_B is sigma-compact; S_B is Borel, S_B subset C(V,r), and every point of S_B lies on some K_omega(R^n) subset S_B; (b) meas(S_B intersect F(V,r)) = (2 pi)^n meas A_B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:kset, bpP:p0:cylinder#cylinderCell, bpP:p0:cylinder#cylinder, stepP:p5:ct-cell, stepP:p5:ct-dec, stepP:p5:ct-disj, stepP:p5:ct-count, stepP:p5:ct-liou, bpP:p5:rstar
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:cell-transfer@L267-L267 | K_B, S_B, K_omega
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:cell-transfer@L267-L267 | F(V,r)
EDGE: bpP:p0:cylinder#cylinder | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:cell-transfer@L267-L267 | S_B subset C(V,r)
EDGE: stepP:p5:ct-cell | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:cell-transfer@L270-L270 | proof step
EDGE: stepP:p5:ct-dec | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:cell-transfer@L271-L271 | proof step
EDGE: stepP:p5:ct-disj | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:cell-transfer@L272-L272 | proof step
EDGE: stepP:p5:ct-count | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:cell-transfer@L273-L273 | proof step
EDGE: stepP:p5:ct-liou | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:cell-transfer@L274-L274 | proof step
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:cell-transfer@L266-L268 | uses the threshold or C_gamma and its smallness conditions directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: outputRepresentative, cell_transfer (KAM/Planetary/PGAssembly/CellTransfer.lean)
LEAN_NOTE: audit P5-CT round 2 PASS WITH NOTES (F1 closed)
NOTE: -

NODE: stepP:p5:ct-cell
KIND: step
TITLE: $\sigma$-compactness
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-cell@L270-L270
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-cell@L270-L270
CONTRACT_ID: stepP:p5:ct-cell
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: check-iota and Phi_3 continuous (Part 3); B x [0,1)^n sigma-compact; phi_omega(vartheta + k) = phi_omega(vartheta) + (0,k)
SOURCE_QUANTIFIERS: B subset D_0 sigma-compact
SOURCE_CONCLUSION: K^c_B := Phi_3(check-iota(B) x [0,1)^n) is sigma-compact; K_B = union over k of (K^c_B + (0,k)) is sigma-compact and invariant under (0,k); A_B is sigma-compact
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p3:limit-actions, bpP:p3:limit-phi, bpP:p5:kset, bpP:p3:two-scale-kam
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p3:limit-actions | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-cell@L270-L270 | check-iota continuous
EDGE: bpP:p3:limit-phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-cell@L270-L270 | Phi_3 continuous
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-cell@L270-L270 | K_B, D_0
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-cell@L270-L270 | periodicity of v, u: phi_omega(vartheta + k) = phi_omega(vartheta) + (0,k)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: ct_rawUnion_period, ct_rawUnion_eq, ct_rawUnion_sigmaCompact, ct_sigmaCompact_inter_cell (KAM/Planetary/PGAssembly/CellTransfer.lean)
LEAN_NOTE: audit P5-CT round 2 PASS WITH NOTES (F1 closed)
NOTE: -

NODE: stepP:p5:ct-dec
KIND: step
TITLE: Decomposition
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-dec@L271-L271
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-dec@L271-L271
CONTRACT_ID: stepP:p5:ct-dec
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T := Phi(S_{2 pi} pi A_B); S_{2 pi} pi A_B subset Q'' := [0,2pi)^n intersect O_0 (location); Phi continuous on O_0; Phi(z + (2 pi k,0)) = Phi(z) + shift(k_f)
SOURCE_QUANTIFIERS: B sigma-compact
SOURCE_CONCLUSION: T is sigma-compact; S_B = union over k in Z^a of (T + shift(k)), hence Borel; every point of T is some K_omega(theta); part (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:location, bpP:p5:phi-chart, bpP:p5:phi, bpP:p5:kset, bpP:p0:fastshift#fastShift, stepP:p5:ct-cell, bpP:p1:period-convert, bpP:p1:order
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:location | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-dec@L271-L271 | S_{2 pi} pi A_B subset O_0 and S_B subset C(V,r)
EDGE: bpP:p5:phi-chart | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-dec@L271-L271 | lattice property of Phi
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-dec@L271-L271 | Phi continuous on O_0
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-dec@L271-L271 | K_omega, S_B, K_B
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-dec@L271-L271 | shift(m_f)
EDGE: stepP:p5:ct-cell | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-dec@L271-L271 | sigma-compactness of A_B
EDGE: bpP:p1:period-convert | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-dec@L271-L271 | uses S_{2pi} directly
EDGE: bpP:p1:order | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-dec@L271-L271 | uses the coordinate permutation pi directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: ct_chartImage_sigmaCompact, ct_kset_eq, ct_phi_shift, ct_kset_cover, ct_kset_measurable, ct_kset_subset_cylinder (KAM/Planetary/PGAssembly/CellTransfer.lean)
LEAN_NOTE: audit P5-CT round 2 PASS WITH NOTES (F1 closed); ct_chartImage_sigmaCompact closes sigma-compactness of T
NOTE: -

NODE: stepP:p5:ct-disj
KIND: step
TITLE: Disjointness and injectivity
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-disj@L272-L272
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-disj@L272-L272
CONTRACT_ID: stepP:p5:ct-disj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z, z' in Q'' with Phi(z) + shift(k) = Phi(z') + shift(k'); (Q2) of the chart lemma
SOURCE_QUANTIFIERS: k, k' in Z^a
SOURCE_CONCLUSION: Phi is injective on S_{2 pi} pi A_B and the translates T + shift(k), k in Z^a, are pairwise disjoint
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:phi-chart, bpP:p5:location, bpP:p0:fastshift#fastShift, stepP:p5:ct-dec, bpP:p5:phi, bpP:p5:kset
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:phi-chart | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-disj@L272-L272 | (Q2): Phi(z') = Phi(z) + shift(k - k') implies z' = z + (2 pi m,0)
EDGE: bpP:p5:location | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-disj@L272-L272 | both points in [0,2pi)^n intersect O_0
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-disj@L272-L272 | shift(k)
EDGE: stepP:p5:ct-dec | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-disj@L272-L272 | T and Q''
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-disj@L272-L272 | uses Phi, Pol or O_0 directly
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-disj@L272-L272 | uses D_0, K_omega, S_B or the action-angle torus union directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: ct_cell_shift_unique, ct_translate_inj (KAM/Planetary/PGAssembly/CellTransfer.lean)
LEAN_NOTE: audit P5-CT round 2 PASS WITH NOTES (F1 closed)
NOTE: -

NODE: stepP:p5:ct-count
KIND: step
TITLE: Counting
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-count@L273-L273
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-count@L273-L273
CONTRACT_ID: stepP:p5:ct-count
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S_B subset C(V,r) so S_B intersect F = S_B intersect {phi in [0,2pi)^a}; translation invariance of meas; ct-dec, ct-disj
SOURCE_QUANTIFIERS: B sigma-compact
SOURCE_CONCLUSION: meas(S_B intersect F(V,r)) = sum over k of meas(T intersect {phi in [-2 pi k, 2 pi (1-k))}) = meas T (the slabs partition R^a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p5:ct-dec, stepP:p5:ct-disj, bpP:p0:cylinder#cylinderCell, bpP:p0:cylinder#cylinder, bpP:p0:fastshift#fastShift, bpP:p5:kset
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p5:ct-dec | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-count@L273-L273 | S_B = union of the translates T + shift(k)
EDGE: stepP:p5:ct-disj | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-count@L273-L273 | disjointness of the translates
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-count@L273-L273 | F(V,r) = C(V,r) intersect {phi in [0,2pi)^a}
EDGE: bpP:p0:cylinder#cylinder | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-count@L273-L273 | S_B subset C(V,r)
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-count@L273-L273 | shift(k)
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-count@L273-L273 | uses D_0, K_omega, S_B or the action-angle torus union directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: volume_fastTranslates_inter_fastCell (KAM/Planetary/PGAssembly/CellTransferTile.lean)
LEAN_NOTE: audit P5-CT round 2 PASS WITH NOTES (F1 closed)
NOTE: -

NODE: stepP:p5:ct-liou
KIND: step
TITLE: Liouville
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-liou@L274-L274
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-liou@L274-L274
CONTRACT_ID: stepP:p5:ct-liou
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Phi a 1-chart injective on the measurable set S_{2 pi} pi A_B; S_{2 pi} multiplies volume by (2 pi)^n; pi permutes coordinates
SOURCE_QUANTIFIERS: B sigma-compact
SOURCE_CONCLUSION: meas T = meas(S_{2 pi} pi A_B) = (2 pi)^n meas A_B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p5:ct-disj, bpP:p1:liouville, bpP:p1:period-convert, bpP:p5:phi-chart, stepP:p5:ct-dec, bpP:p5:phi, bpP:p5:kset, bpP:p1:order
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p5:ct-disj | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-liou@L274-L274 | injectivity of Phi on S_{2 pi} pi A_B
EDGE: bpP:p1:liouville | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-liou@L274-L274 | charts scale Lebesgue measure on injectivity sets
EDGE: bpP:p1:period-convert | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-liou@L274-L274 | (a): S_{2 pi} multiplies volume by (2 pi)^n
EDGE: bpP:p5:phi-chart | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-liou@L274-L274 | Phi is a 1-chart
EDGE: stepP:p5:ct-dec | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-liou@L274-L274 | T = Phi(S_{2 pi} pi A_B)
EDGE: bpP:p5:phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-liou@L274-L274 | uses Phi, Pol or O_0 directly
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-liou@L274-L274 | uses D_0, K_omega, S_B or the action-angle torus union directly
EDGE: bpP:p1:order | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:ct-liou@L274-L274 | uses the coordinate permutation pi directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: cell_transfer (KAM/Planetary/PGAssembly/CellTransfer.lean)
LEAN_NOTE: audit P5-CT round 2 PASS WITH NOTES (F1 closed); final step of cell_transfer
NOTE: -

NODE: bpP:p5:budget
KIND: lemma
TITLE: Budget on the action side
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:budget@L280-L283
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:budget@L284-L288
CONTRACT_ID: bpP:p5:budget
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < r < r_*, admissible mu; K := K_{D_0} of bpP:p5:kset; c_n = 1 + (1 + 2^n)(1 + (4/3)^n) of bpP:p3:two-scale-kam
SOURCE_QUANTIFIERS: data and kappa_0, kappa_1, G fixed; then C_b; then admissible (r,mu)
SOURCE_CONCLUSION: there is C_b < infinity (data and kappa_0, kappa_1, G only) with meas((D x T^n) minus K) <= c_n C_b sqrt r meas D and meas D = meas Dcheck l^b > 0
CONSTANT_SCOPE: C_b depends on the data and kappa_0, kappa_1, G only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:kset, bpP:p3:two-scale-kam, bpP:p5:rstar, bpP:p5:params, bpP:p5:param-facts, stepP:p5:bu-read, stepP:p5:bu-dio, stepP:p5:bu-collar, bpP:p5:budget#constant
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:budget@L281-L281 | K = K_{D_0}
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:budget@L281-L281 | c_n and inequality (3.1)
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:budget@L281-L282 | admissible (r,mu)
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:budget@L282-L282 | D = Dcheck x A_sh, l
EDGE: bpP:p5:param-facts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:budget@L282-L282 | meas Dcheck > 0
EDGE: stepP:p5:bu-read | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:budget@L285-L285 | proof step
EDGE: stepP:p5:bu-dio | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:budget@L286-L286 | proof step
EDGE: stepP:p5:bu-collar | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:budget@L287-L287 | proof step
EDGE: bpP:p5:budget#constant | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:budget@L281-L281 | uses the numerical constant choice separately from the later estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: budget (KAM/Planetary/PGAssembly/ActionBudget.lean); pgBudget (KAM/Planetary/PGAssembly/ActionBudgetDefs.lean)
LEAN_NOTE: audit P5-BU PASS WITH NOTES
NOTE: -

NODE: stepP:p5:bu-read
KIND: step
TITLE: Reading (3.1)
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-read@L285-L285
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-read@L285-L285
CONTRACT_ID: stepP:p5:bu-read
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K = K_Omega of bpP:p3:two-scale-kam for (Omega_*, r_K); D subset Re(D_{r_K}); (3.1)
SOURCE_QUANTIFIERS: admissible (r,mu)
SOURCE_CONCLUSION: meas((D x T^n) minus K) <= meas((Re(D_{r_K}) x T^n) minus K) <= c_n (meas(D minus D_0) + meas(Re(D_{r_K}) minus D))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p3:two-scale-kam, bpP:p5:kset, bpP:p5:params, K:bp:p1:ext-lebesgue
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-read@L285-L285 | inequality (3.1)
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-read@L285-L285 | K = K_Omega
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-read@L285-L285 | D and r_K
EDGE: K:bp:p1:ext-lebesgue | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-read@L285-L285 | monotonicity of meas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: budget (KAM/Planetary/PGAssembly/ActionBudget.lean)
LEAN_NOTE: audit P5-BU PASS WITH NOTES; inside proof of budget
NOTE: -

NODE: stepP:p5:bu-dio
KIND: step
TITLE: Diophantine part
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L286
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L286
CONTRACT_ID: stepP:p5:bu-dio
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D minus D_0 subset R := {(I,xi) in D_t x A_sh: F_mu(I,xi) not in D_{alpha_1,alpha_2,tau}}, alpha_i = 2 pi gamma_i; (S4) of bpP:p4:data holds with D = D_t, lambda_0 = 1, mu_1 of (r1) and the constants of freq-data; lambda = lambda_2' in [lambda_2/2, 1], Q = A_sh, gamma-bar_P4 = alpha_2/mu = 2 pi kappa_0 r^{5/2}; meas D_t >= (1/2) meas V
SOURCE_QUANTIFIERS: admissible (r,mu)
SOURCE_CONCLUSION: meas(D minus D_0) <= 4^{b+1} 2 pi kappa_0 (5 c-bar_1 + 4 c-bar_2) sqrt r meas D
CONSTANT_SCOPE: c-bar_1, c-bar_2 data-dependent bounds on c_1, c_2
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:freq, bpP:p4:data, bpP:p5:param-facts, bpP:p5:freq-data, bpP:p4:two-scale-diophantine-measure, bpP:p1:two-scale, bpP:p5:rstar, bpP:p5:params, bpP:p5:kset, bpP:p4:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:freq | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L286 | the dictionary D minus D^dio = {omega_mu not in D_{alpha_1,alpha_2,tau}}
EDGE: bpP:p4:data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L286 | (S4) with D = D_t, lambda_0 = 1
EDGE: bpP:p5:param-facts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L286 | meas D_t >= (1/2) meas V, meas D_t <= 4 meas Dcheck, mu < mu_1
EDGE: bpP:p5:freq-data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L286 | the constants Lambda_N, L_beta for (S4)
EDGE: bpP:p4:two-scale-diophantine-measure | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L286 | measure of the non-Diophantine set R
EDGE: bpP:p1:two-scale | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L286 | D_{alpha_1,alpha_2,tau}
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L286 | mu_1 of (r1)
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L286 | alpha_i, A_sh, lambda_2', gamma_i
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L286 | D_0
EDGE: bpP:p4:conv#data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L286 | uses the inner core D_t and the volume of V directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: budget_dio (KAM/Planetary/PGAssembly/ActionBudgetDio.lean)
LEAN_NOTE: audit P5-BU PASS WITH NOTES
NOTE: -

NODE: stepP:p5:bu-collar
KIND: step
TITLE: Collar part
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-collar@L287-L287
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-collar@L287-L287
CONTRACT_ID: stepP:p5:bu-collar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Re(D_{r_K}) = N_{r_K}(Dcheck) x (lambda_1 - r_K, lambda_2' + r_K)^b; N_{r_K}(Dcheck) minus Dcheck subset (N_{r_K}(D_t) minus D_t) union (D_t minus Dcheck); meas Dcheck >= (1/4) meas V; (1 + 2 r_K/l)^b < 2
SOURCE_QUANTIFIERS: admissible (r,mu)
SOURCE_CONCLUSION: meas(Re(D_{r_K}) minus D) <= meas D [8 (A + c_dio C_gamma)/meas V + b kappa_1/16] sqrt r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p4:dc-prod, bpP:p4:collar, bpP:p5:dio-one, bpP:p5:rK, bpP:p5:param-facts, bpP:p5:params, K:bp:p1:ext-lebesgue, bpP:p4:conv#data, bpP:p5:rstar
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p4:dc-prod | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-collar@L287-L287 | product structure of Re(D_{r_K}) (max norm)
EDGE: bpP:p4:collar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-collar@L287-L287 | (c): meas(N_{r_K}(D_t) minus D_t) <= A t
EDGE: bpP:p5:dio-one | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-collar@L287-L287 | meas(D_t minus Dcheck) <= c_dio gamma-bar
EDGE: bpP:p5:rK | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-collar@L287-L287 | (1 + 2 r_K/l)^b < 2 and r_K < t < d
EDGE: bpP:p5:param-facts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-collar@L287-L287 | meas Dcheck >= (1/4) meas V, gamma-bar <= C_gamma sqrt r
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-collar@L287-L287 | D, Dcheck, A_sh, t
EDGE: K:bp:p1:ext-lebesgue | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-collar@L287-L287 | monotonicity and subadditivity of meas
EDGE: bpP:p4:conv#data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-collar@L287-L287 | A, N_s, D_t
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-collar@L287-L287 | uses the threshold or C_gamma and its smallness conditions directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: budget_collar, budget_collar_fast (KAM/Planetary/PGAssembly/ActionBudgetCollar.lean)
LEAN_NOTE: audit P5-BU PASS WITH NOTES
NOTE: the pre-extracted edges to bpP:p4:domain-collar and stepP:p4:dc-diff are deleted: the text says it re-derives their steps ("as in") and Part 4 is not used as a black box (bpP:p5:use5-fix); only the product structure stepP:p4:dc-prod is cited.

NODE: bpP:p5:lower
KIND: proposition
TITLE: Lower bound for $\meas(S\cap\mathcal F)$
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L290-L293
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L294-L298
CONTRACT_ID: bpP:p5:lower
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: C_* := (A + c_dio C_gamma)/meas V + 6 b kappa_1 + c_n C_b; 0 < r < r_*, admissible mu; S := S_{D_0}; F(V,r) the frozen cell
SOURCE_QUANTIFIERS: constants fixed; then (r,mu) admissible
SOURCE_CONCLUSION: meas(F(V,r) minus S) <= C_* sqrt r meas F(V,r), i.e. meas(S intersect F) >= (1 - C_* sqrt r) meas F
CONSTANT_SCOPE: C_* depends on the data and kappa_0, kappa_1, G only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:kset, bpP:p0:cylinder#cylinderCell, bpP:p5:rstar, bpP:p5:budget, bpP:p5:dio-one, bpP:p3:two-scale-kam, bpP:p4:conv#data, stepP:p5:lo-setup, stepP:p5:lo-bad, stepP:p5:lo-lost, bpP:p5:params, bpP:p5:lower#constant
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | S := S_{D_0}
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | F(V,r)
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | r < r_*, C_gamma
EDGE: bpP:p5:budget | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | C_b
EDGE: bpP:p5:dio-one | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | c_dio
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | c_n
EDGE: bpP:p4:conv#data | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | A, meas V
EDGE: stepP:p5:lo-setup | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L295-L295 | proof step
EDGE: stepP:p5:lo-bad | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L296-L296 | proof step
EDGE: stepP:p5:lo-lost | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L297-L297 | proof step
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L290-L293 | uses the parameter definitions (widths, scales, domain or shell) directly
EDGE: bpP:p5:lower#constant | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | uses the numerical constant choice separately from the later estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: lower (KAM/Planetary/PGAssembly/Lower.lean)
LEAN_NOTE: audit P5-LO PASS WITH NOTES; signed conclusion incl. positivity of pgLoss
NOTE: -

NODE: stepP:p5:lo-setup
KIND: step
TITLE: Set up
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-setup@L295-L295
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-setup@L295-L295
CONTRACT_ID: stepP:p5:lo-setup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: cell-transfer (b); L := K intersect (R^n x [0,1)^n); location gives L subset V x (0,lambda_2)^b x [0,1)^n =: F'; disc-measure (b)
SOURCE_QUANTIFIERS: admissible (r,mu)
SOURCE_CONCLUSION: meas(S intersect F) = (2 pi)^n meas L, meas F = (2 pi)^n meas F' = (2 pi)^n meas V lambda_2^b, hence meas(F minus S) = (2 pi)^n meas(F' minus L)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:cell-transfer, bpP:p5:location, bpP:p4:disc-measure, bpP:p0:cylinder#cylinderCell, bpP:p5:kset, bpP:p5:params
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:cell-transfer | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-setup@L295-L295 | (b): meas(S_B intersect F) = (2 pi)^n meas A_B
EDGE: bpP:p5:location | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-setup@L295-L295 | L subset V x (0,lambda_2)^b x [0,1)^n
EDGE: bpP:p4:disc-measure | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-setup@L295-L295 | (b): meas F(V,r) = (2 pi)^n meas V (r^2/2)^b
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-setup@L295-L295 | F(V,r)
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-setup@L295-L295 | K = K_{D_0}, S
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-setup@L295-L295 | uses the parameter definitions (widths, scales, domain or shell) directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27, ruling OVERNIGHT 01:20): the Lean proof of the PROVED parent lower avoids this step
NOTE: -

NODE: stepP:p5:lo-bad
KIND: step
TITLE: Bad actions
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-bad@L296-L296
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-bad@L296-L296
CONTRACT_ID: stepP:p5:lo-bad
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D x [0,1)^n subset F'; meas V lambda_2^b - meas Dcheck l^b <= lambda_2^b (meas V - meas Dcheck) + meas V b lambda_2^{b-1} 3 lambda_1; meas V - meas Dcheck <= A t + c_dio gamma-bar; 3 lambda_1/lambda_2 = 6 kappa_1 sqrt r
SOURCE_QUANTIFIERS: admissible (r,mu)
SOURCE_CONCLUSION: (meas V lambda_2^b - meas D)/(meas V lambda_2^b) <= [(A + c_dio C_gamma)/meas V + 6 b kappa_1] sqrt r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:collar, bpP:p5:dio-one, bpP:p5:param-facts, bpP:p5:params, bpP:p5:rstar, bpP:p4:conv#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:collar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-bad@L296-L296 | (b): meas(V minus D_t) <= A t
EDGE: bpP:p5:dio-one | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-bad@L296-L296 | meas(D_t minus Dcheck) <= c_dio gamma-bar
EDGE: bpP:p5:param-facts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-bad@L296-L296 | gamma-bar <= C_gamma sqrt r
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-bad@L296-L296 | D, l, lambda_1, lambda_2, t
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-bad@L296-L296 | C_gamma
EDGE: bpP:p4:conv#data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-bad@L296-L296 | A, meas V
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: lo_bad_ratio (KAM/Planetary/PGAssembly/LowerNodes.lean)
LEAN_NOTE: audit GAP-P5b round 3 PASS WITH NOTES
NOTE: -

NODE: stepP:p5:lo-lost
KIND: step
TITLE: Lost tori
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-lost@L297-L297
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-lost@L297-L297
CONTRACT_ID: stepP:p5:lo-lost
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: meas((D x [0,1)^n) minus L) = meas((D x T^n) minus K) since K is Z^n-invariant in vartheta; budget
SOURCE_QUANTIFIERS: admissible (r,mu)
SOURCE_CONCLUSION: meas((D x [0,1)^n) minus L) <= c_n C_b sqrt r meas D <= c_n C_b sqrt r meas F'; adding the bad-action part gives the claim
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:budget, stepP:p5:lo-setup, stepP:p5:lo-bad, bpP:p5:kset, bpP:p5:params
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:budget | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-lost@L297-L297 | meas((D x T^n) minus K) <= c_n C_b sqrt r meas D
EDGE: stepP:p5:lo-setup | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-lost@L297-L297 | F', L
EDGE: stepP:p5:lo-bad | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-lost@L297-L297 | the bad-action part
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-lost@L297-L297 | K is Z^n-invariant in vartheta
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:lo-lost@L297-L297 | uses the parameter definitions (widths, scales, domain or shell) directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: lo_lost_complement, lo_lost_budget (KAM/Planetary/PGAssembly/LowerNodes.lean)
LEAN_NOTE: audit GAP-P5b round 3 PASS WITH NOTES
NOTE: -

NODE: bpP:p5:strictness
KIND: proposition
TITLE: Deleting a small positive-measure family of tori
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:strictness@L302-L307
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:strictness@L308-L313
CONTRACT_ID: bpP:p5:strictness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < r < r_*, admissible mu; S := S_{D_0}; the family S_B of bpP:p5:kset
SOURCE_QUANTIFIERS: (r,mu) admissible; then a sigma-compact B subset D_0
SOURCE_CONCLUSION: there is a sigma-compact B subset D_0 such that S' := S_{D_0 minus B} satisfies 0 < meas(S' intersect F) and (1 - (C_* + 1/2) sqrt r) meas F <= meas(S' intersect F) < meas F
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:kset, bpP:p5:rstar, bpP:p0:cylinder#cylinderCell, stepP:p5:st-add, stepP:p5:st-null, stepP:p5:st-ivt, stepP:p5:st-conc
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:strictness@L303-L303 | S_B, D_0
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:strictness@L303-L303 | r < r_*, (r5)
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:strictness@L304-L304 | F(V,r)
EDGE: stepP:p5:st-add | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:strictness@L309-L309 | proof step
EDGE: stepP:p5:st-null | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:strictness@L310-L310 | proof step
EDGE: stepP:p5:st-ivt | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:strictness@L311-L311 | proof step
EDGE: stepP:p5:st-conc | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:strictness@L312-L312 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: strictness (KAM/Planetary/PGAssembly/Strictness.lean)
LEAN_NOTE: audit P5-ST PASS WITH NOTES; signed KAM.Planetary.strictness
NOTE: sourcegap L306 (strictness from the slack and the bi-Lipschitz parametrisation of Part 3) is supplied by these steps.

NODE: stepP:p5:st-add
KIND: step
TITLE: Additivity
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-add@L309-L309
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-add@L309-L309
CONTRACT_ID: stepP:p5:st-add
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m(B) := meas(S_B intersect F) = (2 pi)^n meas A_B for sigma-compact B subset D_0 (cell-transfer); the tori phi_omega(R^n) are pairwise disjoint (injectivity modulo translations)
SOURCE_QUANTIFIERS: B sigma-compact subset of D_0
SOURCE_CONCLUSION: m is countably additive on sigma-compact subsets of D_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:cell-transfer, bpP:p3:two-scale-kam, bpP:p5:kset, bpP:p0:cylinder#cylinderCell
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:cell-transfer | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-add@L309-L309 | m(B) = (2 pi)^n meas A_B
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-add@L309-L309 | injectivity modulo translations: disjoint tori
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-add@L309-L309 | K_B, A_B, Omega_B
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-add@L309-L309 | the source statement directly uses this frozen predicate or cell definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: stParam, stMeasure, st_mass, st_add (KAM/Planetary/PGAssembly/Strictness.lean)
LEAN_NOTE: audit P5-ST PASS WITH NOTES
NOTE: -

NODE: stepP:p5:st-null
KIND: step
TITLE: Slices are null
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-null@L310-L310
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-null@L310-L310
CONTRACT_ID: stepP:p5:st-null
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: x_1(I) = I_1; H_s := D_0 intersect {x_1 = s} null; K^c_{H_s} = Phi_3(check-iota(H_s) x [0,1)^n) a Lipschitz image (check-iota Lipschitz, Phi_3 Lipschitz in the rescaled norm)
SOURCE_QUANTIFIERS: s in R
SOURCE_CONCLUSION: meas K^c_{H_s} <= Lambda^{2n} meas check-iota(H_s) = 0; K_{H_s} and A_{H_s} are null, i.e. m(H_s) = 0
CONSTANT_SCOPE: Lambda a Lipschitz constant (Part 3)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p3:limit-actions, bpP:p3:limit-phi, bpP:p1:torus-union, bpP:p5:kset, stepP:p5:st-add
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p3:limit-actions | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-null@L310-L310 | check-iota Lipschitz
EDGE: bpP:p3:limit-phi | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-null@L310-L310 | Phi_3 Lipschitz in the rescaled norm
EDGE: bpP:p1:torus-union | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-null@L310-L310 | measure of a Lipschitz image of a null set
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-null@L310-L310 | K^c, K_B, A_B
EDGE: stepP:p5:st-add | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-null@L310-L310 | the function m
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: st_slice_rep_null, st_null, stMeasure_slice_null (KAM/Planetary/PGAssembly/Strictness.lean)
LEAN_NOTE: audit P5-ST PASS WITH NOTES
NOTE: -

NODE: stepP:p5:st-ivt
KIND: step
TITLE: Intermediate value
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-ivt@L311-L311
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-ivt@L311-L311
CONTRACT_ID: stepP:p5:st-ivt
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f(s) := m(D_0 intersect {x_1 <= s}) nondecreasing; f(+inf) = m(D_0) >= (1 - C_* sqrt r) meas F > 0 (lower bound, (r5)); additivity; slices null
SOURCE_QUANTIFIERS: s in R
SOURCE_CONCLUSION: f is continuous (right: decreasing intersections and additivity; left: slices null), so there is s with f(s) = theta_0 := min{m(D_0)/2, (1/2) sqrt r meas F} > 0; B := D_0 intersect {x_1 <= s} is closed in D_0, hence sigma-compact, and so is D_0 minus B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:lower, stepP:p5:st-null, stepP:p5:st-add, bpP:p5:rstar, bpP:p5:kset, bpP:p0:cylinder#cylinderCell
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:lower | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-ivt@L311-L311 | m(D_0) = meas(S intersect F) >= (1 - C_* sqrt r) meas F
EDGE: stepP:p5:st-null | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-ivt@L311-L311 | left-continuity: m(H_s) = 0
EDGE: stepP:p5:st-add | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-ivt@L311-L311 | additivity and continuity from above of m
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-ivt@L311-L311 | (r5): (C_* + 1/2) sqrt r <= 1/2 so the lower bound is positive
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-ivt@L311-L311 | D_0 sigma-compact
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-ivt@L311-L311 | the source statement directly uses this frozen predicate or cell definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: st_cut_value, st_ivt, strictness_aux (KAM/Planetary/PGAssembly/Strictness.lean)
LEAN_NOTE: audit P5-ST PASS WITH NOTES; IVT via finite_measure_coordinate_cut (P5-CUT)
NOTE: SOURCE_GAP: L311 invokes continuity of finite measure along monotone sequences and the intermediate value theorem. L336 lists the former but creates no approved external; neither classical input is supplied by the existing edges. Additivity, null slices and the lower bound retain their stated contracts.

NODE: stepP:p5:st-conc
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-conc@L312-L312
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-conc@L312-L312
CONTRACT_ID: stepP:p5:st-conc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: meas(S' intersect F) = m(D_0) - theta_0; S intersect F subset F; (r5): (C_* + 1/2) sqrt r <= 1/2; meas F > 0
SOURCE_QUANTIFIERS: the B of st-ivt
SOURCE_CONCLUSION: meas(S' intersect F) < meas F and meas(S' intersect F) >= (1 - (C_* + 1/2) sqrt r) meas F > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepP:p5:st-ivt, bpP:p5:lower, bpP:p5:rstar, bpP:p0:cylinder#cylinderCell, bpP:p5:kset
ROUTES: -
ROUTE_FOR: -
EDGE: stepP:p5:st-ivt | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-conc@L312-L312 | theta_0 and B
EDGE: bpP:p5:lower | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-conc@L312-L312 | m(D_0) >= (1 - C_* sqrt r) meas F
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-conc@L312-L312 | (r5)
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-conc@L312-L312 | F(V,r), meas F > 0
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:st-conc@L312-L312 | uses D_0, K_omega, S_B or the action-angle torus union directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: strictness (KAM/Planetary/PGAssembly/Strictness.lean)
LEAN_NOTE: audit P5-ST PASS WITH NOTES
NOTE: -

NODE: bpP:p5:main
KIND: theorem
TITLE: P-G; \Pref{bpP:p0:pg}
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L317-L320
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L321-L326
CONTRACT_ID: bpP:p5:main
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the hypotheses and data of bpP:p0:pg: a, b >= 1; V open connected bounded; W open with closure V subset W; A, d > 0 with the collar bound; r_0, mu_0, B > 0; H_0, P, P_0, Omega, beta; (H1) joint analyticity of P on [0,mu_0] x closure of C(V,r_0); (H2) periodicity; (H3) HasFastDiffeo(H_0,W); (H4) HasBirkhoff(P,V,r_0,mu_0,P_0,Omega,beta); (H5) ¦det beta¦ >= B; (H6) beta symmetric
SOURCE_QUANTIFIERS: data fixed first; then exists r_*, C, c; then for all r, mu with 0 < r < r_*, 0 < mu < mu_0, mu < r^6/(log 1/r)^c; then exists S (the printed quantifier order of bpP:p0:pg); witnesses are c := 2n+4, C := max{C_*+1,C_w}, r_* of bpP:p5:rstar (L319)
SOURCE_CONCLUSION: there exist r_*, C, c with 0 < r_* < r_0, r_* < 1, C > 0, c > 0 such that for all r, mu with 0 < r < r_*, 0 < mu < mu_0, mu < r^6/(log 1/r)^c there is S subset Ph_{a+b} with IsCylKol(H_mu, V, r, mu, C, S) (H_mu = H_0 + mu P(mu,.)), 0 < meas(S intersect F(V,r)), ofReal(1 - C sqrt r) meas F(V,r) < meas(S intersect F(V,r)) < meas F(V,r)
CONSTANT_SCOPE: r_*, C, c depend on all the data and hypotheses (a, b, V, W, A, d, r_0, mu_0, B, H_0, P, P_0, Omega, beta) and not on r or mu; C is both the frequency bound of IsCylKol and the measure constant; S depends on (r, mu)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:rstar, stepP:p5:mn-const, stepP:p5:mn-given, stepP:p5:mn-set, stepP:p5:mn-meas, bpP:p0:fastdiffeo#HasFastDiffeomorphism, bpP:p0:birkhoff#HasSecularBirkhoffForm, bpP:p0:degham#degenerateHamiltonian, bpP:p0:cylkol#IsCylinderKolmogorovSet, bpP:p0:cylinder#cylinderCell, bpP:p5:lower#constant, bpP:p5:torus-conv
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L319-L319 | r_* of the definition
EDGE: stepP:p5:mn-const | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L322-L322 | proof step
EDGE: stepP:p5:mn-given | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L323-L323 | proof step
EDGE: stepP:p5:mn-set | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L324-L324 | proof step
EDGE: stepP:p5:mn-meas | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L325-L325 | proof step
EDGE: bpP:p0:fastdiffeo#HasFastDiffeomorphism | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L317-L320 | the source statement directly uses this frozen predicate or cell definition
EDGE: bpP:p0:birkhoff#HasSecularBirkhoffForm | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L317-L320 | the source statement directly uses this frozen predicate or cell definition
EDGE: bpP:p0:degham#degenerateHamiltonian | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L317-L320 | the source statement directly uses this frozen predicate or cell definition
EDGE: bpP:p0:cylkol#IsCylinderKolmogorovSet | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L317-L320 | the source statement directly uses this frozen predicate or cell definition
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L317-L320 | the source statement directly uses this frozen predicate or cell definition
EDGE: bpP:p5:lower#constant | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L319-L319 | C_* in the specified witness C
EDGE: bpP:p5:torus-conv | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L319-L319 | C_w in the specified witness C
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: main, main_of_data (KAM/Planetary/PGAssembly/Main.lean)
LEAN_NOTE: audit P5-MAIN PASS WITH NOTES; main is the verbatim frozen telescope, same conclusion
NOTE: Proving result of frozen root bpP:p0:pg; the root depends on this node, with no edge back. Direct statement edges to the frozen definitions are retained independently of their uses by mn-set and mn-meas.

NODE: stepP:p5:mn-const
KIND: step
TITLE: Constants first
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322
CONTRACT_ID: stepP:p5:mn-const
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the order of Remark order; data constants of the lemmas ext to freq-inj; C_U, C_1; kappa_0, kappa_1, G; C_gamma, C_b, C_*; C_w; r_* a finite list of conditions
SOURCE_QUANTIFIERS: constants chosen before (r,mu): r_*, C := max{C_* + 1, C_w}, c := 2n + 4
SOURCE_CONCLUSION: r_*, C, c are defined from the data alone, with 0 < r_* < r_0, r_* < 1, C > 0, c > 0, none depending on r or mu
CONSTANT_SCOPE: r_*, C, c depend on the data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:order, bpP:p5:ext, bpP:p5:birkhoff-ext, bpP:p5:uniform-remainder, bpP:p5:bilip, bpP:p5:dio-one, bpP:p5:freq-data, bpP:p5:freq-inj, bpP:p5:kam-hyp, bpP:p5:kam-cond, bpP:p5:budget, bpP:p5:lower, bpP:p5:torus-conv, bpP:p5:rstar, bpP:p5:consts
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:order | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | the order of choice of the constants
EDGE: bpP:p5:ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | delta_c, M_P, M_0
EDGE: bpP:p5:birkhoff-ext | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | data constants
EDGE: bpP:p5:uniform-remainder | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | r_1, C_Q
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | rho_c, c_0, M0bar
EDGE: bpP:p5:dio-one | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | c_dio
EDGE: bpP:p5:freq-data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | A_N, Lambda_N, M_beta, L_beta
EDGE: bpP:p5:freq-inj | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | mu_*, C_U
EDGE: bpP:p5:kam-hyp | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | C_1
EDGE: bpP:p5:kam-cond | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | kappa_0, kappa_1, G
EDGE: bpP:p5:budget | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | C_b
EDGE: bpP:p5:lower | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | C_*
EDGE: bpP:p5:torus-conv | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | C_w
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | r_*
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-const@L322-L322 | s_*, Lambda_P
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: main_of_data (KAM/Planetary/PGAssembly/Main.lean)
LEAN_NOTE: audit P5-MAIN PASS WITH NOTES; local step of main_of_data, credited in audit table
NOTE: -

NODE: stepP:p5:mn-given
KIND: step
TITLE: Given $(r,\mu)$
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-given@L323-L323
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-given@L323-L323
CONTRACT_ID: stepP:p5:mn-given
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < r < r_*, 0 < mu < mu_0, mu < r^6/(log 1/r)^c (r < 1 so the base is positive)
SOURCE_QUANTIFIERS: (r,mu) in the stated range
SOURCE_CONCLUSION: all objects of bpP:p5:params are defined and bpP:p5:param-facts holds; bpP:p5:avg, bpP:p5:kam-hyp, bpP:p5:kam-cond verify the hypotheses of bpP:p3:two-scale-kam, including the complex injectivity (bpP:p5:freq-inj)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:params, bpP:p5:param-facts, bpP:p5:avg, bpP:p5:kam-hyp, bpP:p5:kam-cond, bpP:p5:freq-inj, bpP:p3:two-scale-kam, bpP:p5:rstar
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:params | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-given@L323-L323 | objects of Definition params
EDGE: bpP:p5:param-facts | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-given@L323-L323 | consequences of the parameter choice
EDGE: bpP:p5:avg | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-given@L323-L323 | averaged system
EDGE: bpP:p5:kam-hyp | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-given@L323-L323 | hypotheses of Proposition two-scale-kam
EDGE: bpP:p5:kam-cond | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-given@L323-L323 | KAM condition
EDGE: bpP:p5:freq-inj | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-given@L323-L323 | complex injectivity and nondegeneracy
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-given@L323-L323 | the proposition whose hypotheses are verified
EDGE: bpP:p5:rstar | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-given@L323-L323 | 0 < r < r_*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: main_of_data (KAM/Planetary/PGAssembly/Main.lean)
LEAN_NOTE: audit P5-MAIN PASS WITH NOTES; local step of main_of_data, credited in audit table
NOTE: -

NODE: stepP:p5:mn-set
KIND: step
TITLE: The set
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-set@L324-L324
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-set@L324-L324
CONTRACT_ID: stepP:p5:mn-set
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S := S' of bpP:p5:strictness; cell-transfer (a); torus-conv; C_w <= C
SOURCE_QUANTIFIERS: (r,mu) admissible
SOURCE_CONCLUSION: S is Borel (so Lebesgue measurable), S subset C(V,r), every z in S is K_omega(theta) with K_omega(R^n) subset S, IsCylTorus(H_mu, C(V,r), w, K_omega), gamma > 0, tau > a+b, ¦w^f¦ <= C_w <= C, ¦w^s¦ <= C_w mu <= C mu; hence IsCylKol(H_mu, V, r, mu, C, S)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:strictness, bpP:p5:cell-transfer, bpP:p5:torus-conv, bpP:p0:cylkol#IsCylinderKolmogorovSet, bpP:p5:kset, stepP:p5:mn-const, stepP:p5:mn-given, bpP:p0:degham#degenerateHamiltonian
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:strictness | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-set@L324-L324 | S := S'
EDGE: bpP:p5:cell-transfer | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-set@L324-L324 | (a): Borel, S subset C(V,r), every point lies on a torus K_omega(R^n) subset S
EDGE: bpP:p5:torus-conv | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-set@L324-L324 | IsCylTorus, Diophantine and frequency bounds
EDGE: bpP:p0:cylkol#IsCylinderKolmogorovSet | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-set@L324-L324 | the predicate IsCylKol
EDGE: bpP:p5:kset | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-set@L324-L324 | Omega_*, K_omega
EDGE: stepP:p5:mn-const | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-set@L324-L324 | C_w <= C
EDGE: stepP:p5:mn-given | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-set@L324-L324 | the objects of the construction
EDGE: bpP:p0:degham#degenerateHamiltonian | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-set@L324-L324 | H_mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: main_of_data (KAM/Planetary/PGAssembly/Main.lean)
LEAN_NOTE: audit P5-MAIN PASS WITH NOTES; local step of main_of_data, credited in audit table
NOTE: -

NODE: stepP:p5:mn-meas
KIND: step
TITLE: Measures
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-meas@L325-L325
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-meas@L325-L325
CONTRACT_ID: stepP:p5:mn-meas
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: strictness; C >= C_* + 1; meas F > 0; V bounded; ofReal truncation of 1 - C sqrt r
SOURCE_QUANTIFIERS: (r,mu) admissible
SOURCE_CONCLUSION: 0 < meas(S intersect F) < meas F and meas(S intersect F) >= (1 - (C_* + 1/2) sqrt r) meas F > (1 - C sqrt r) meas F, hence ofReal(1 - C sqrt r) meas F < meas(S intersect F) (both cases 1 - C sqrt r <= 0 and > 0); meas F < infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:strictness, bpP:p0:totality, bpP:p0:cylinder#cylinderCell, stepP:p5:mn-set, stepP:p5:mn-const
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:strictness | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-meas@L325-L325 | the two-sided bound for S'
EDGE: bpP:p0:totality | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-meas@L325-L325 | ofReal truncation and meas F < infinity (Lean totality)
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-meas@L325-L325 | F(V,r)
EDGE: stepP:p5:mn-set | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-meas@L324-L325 | S := S'
EDGE: stepP:p5:mn-const | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:mn-meas@L325-L325 | C >= C_* + 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p5
REVIEWER: sol-review-P-g
LEAN_STATUS: PROVED
LEAN_REF: main_of_data, ofReal_mul_lt_of_slack (KAM/Planetary/PGAssembly/Main.lean)
LEAN_NOTE: audit P5-MAIN PASS WITH NOTES; local step of main_of_data, credited in audit table
NOTE: -

NODE: bpP:p5:kam-hyp#C1
KIND: definition
TITLE: The numerical constant C_1, before the estimates
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L200-L201
PROOF_SOURCE: -
CONTRACT_ID: bpP:p5:kam-hyp#C1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data constants C_U, C_Q, Lambda_P and s_*; n=a+b
SOURCE_QUANTIFIERS: data fixed; then C_R, sigma_av and C_1, before r or mu
SOURCE_CONCLUSION: C_R := 2^5 C_Q + 2 Lambda_P, sigma_av := s_*/6, C_1 := max{1, 2 pi C_U, C_R coth(sigma_av/4)^n/(2 pi)}
CONSTANT_SCOPE: data only; does not depend on the KAM-hypothesis verification or averaging map
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:freq-inj, bpP:p5:uniform-remainder, bpP:p5:consts
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:freq-inj | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L200-L201 | numerical data used in this constant choice
EDGE: bpP:p5:uniform-remainder | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L200-L201 | numerical data used in this constant choice
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-hyp@L200-L201 | numerical data used in this constant choice
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: kam_c1 (KAM/Planetary/PGAssembly/Scales.lean)
LEAN_NOTE: audit P5-SCALE PASS WITH NOTES
NOTE: -

NODE: bpP:p5:kam-cond#scales
KIND: definition
TITLE: Scale-constant selection before r and mu
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L213-L217
PROOF_SOURCE: -
CONTRACT_ID: bpP:p5:kam-cond#scales
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=a+b, tau=n+1; C_1 and s_*>0, M0bar fixed data constants; s=s_*/60
SOURCE_QUANTIFIERS: choose kappa_0, then kappa_1, then G; all before r, mu
SOURCE_CONCLUSION: choose kappa_0>=C_1^2 with kappa_0^2>9 chat C_1^4 K_0^(2 tau+2), K_0=(6/s)log_+(kappa_0^2/C_1^4); kappa_1^2>4 chat C_1^2; G>=max{2 M0bar kappa_1, sqrt(2^14(1+b)M0bar), sqrt(1600(1+b)M0bar/s_*)}
CONSTANT_SCOPE: data only, in the displayed order
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:kam-hyp#C1, bpP:p5:consts, bpP:p5:bilip, bpP:p3:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:kam-hyp#C1 | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L213-L217 | numerical data used in this constant choice
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L213-L217 | numerical data used in this constant choice
EDGE: bpP:p5:bilip | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L213-L217 | numerical data used in this constant choice
EDGE: bpP:p3:constants | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:kam-cond@L213-L217 | numerical data used in this constant choice
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: PGScales, pgTau, pgK0, pgChat, PGScaleSpec, kam_cond, pgScales (KAM/Planetary/PGAssembly/Scales.lean)
LEAN_NOTE: audit P5-SCALE PASS WITH NOTES
NOTE: SOURCE_GAP: Numerical witness selection from items 1-3, not the later KAM-condition verification. L215 invokes the elementary limit kappa_0^2/(log kappa_0)^(2 tau+2) -> infinity; that standard growth fact is an unregistered input, so its existence justification remains SOURCE_GAP unless an approved supplier is added. The numerical contract is unchanged.

NODE: bpP:p5:rstar#Cgamma
KIND: definition
TITLE: C_gamma independently of the threshold
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L152-L152
PROOF_SOURCE: -
CONTRACT_ID: bpP:p5:rstar#Cgamma
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: s_*>0 and G chosen in the data-dependent scale selection; tau=n+1
SOURCE_QUANTIFIERS: data fixed; define C_gamma before r_*
SOURCE_CONCLUSION: C_gamma := G(30/s_*)^(tau+1)
CONSTANT_SCOPE: data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p5:consts, bpP:p5:kam-cond#scales
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p5:consts | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L152-L152 | numerical data used in this constant choice
EDGE: bpP:p5:kam-cond#scales | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:rstar@L152-L152 | numerical data used in this constant choice
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.pgCgamma (KAM/Planetary/PGAssembly/ThresholdAlg.lean)
LEAN_NOTE: DEFS-P3-audit-1 CLOSABLE: pgCgamma = G*(30/s_*)^(tau+1) on every PGData, no fallback
NOTE: -

NODE: bpP:p5:budget#constant
KIND: definition
TITLE: Numerical budget constant before the small-radius restriction
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L287
PROOF_SOURCE: -
CONTRACT_ID: bpP:p5:budget#constant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data constants of the Part 4 measure estimate; kappa_0,kappa_1,G chosen; C_gamma fixed; meas V>0
SOURCE_QUANTIFIERS: data fixed; choose bar c_1,bar c_2 and C_b before r_*, r, mu
SOURCE_CONCLUSION: take bar c_1 from the explicit Part 4 c_1 formula with its denominator meas(Dbar) replaced by meas(V)/2 and bar c_2=c_2; choose C_b as the sum 4^(b+1) 2 pi kappa_0 (5 bar c_1+4 bar c_2) + 8(A+c_dio C_gamma)/meas(V) + b kappa_1/16
CONSTANT_SCOPE: data and kappa_0,kappa_1,G only; this is the numerical witness, not the later estimate for a torus union
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:two-scale-diophantine-measure, bpP:p4:conv#data, bpP:p5:freq-data, bpP:p5:dio-one, bpP:p5:rstar#Cgamma, bpP:p5:kam-cond#scales, bpP:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:two-scale-diophantine-measure | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L287 | numerical data used in this constant choice
EDGE: bpP:p4:conv#data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L287 | numerical data used in this constant choice
EDGE: bpP:p5:freq-data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L287 | numerical data used in this constant choice
EDGE: bpP:p5:dio-one | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L287 | numerical data used in this constant choice
EDGE: bpP:p5:rstar#Cgamma | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L287 | numerical data used in this constant choice
EDGE: bpP:p5:kam-cond#scales | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L287 | numerical data used in this constant choice
EDGE: bpP:p4:data | blueprint-P/parts/p5-pg-assembly.tex#stepP:p5:bu-dio@L286-L287 | standing numerical constants in the Part 4 measure coefficient
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: kamMeasureConstant, pgMeasureUpper1, pgMeasureUpper2, pgBudget (KAM/Planetary/PGAssembly/ActionBudgetDefs.lean); budget (KAM/Planetary/PGAssembly/ActionBudget.lean)
LEAN_NOTE: audit P5-BU PASS WITH NOTES
NOTE: Extracts the displayed coefficients from L286-L287; their validity as estimates is proved by bu-dio and bu-collar under the preliminary margins. This definition itself does not assert those estimates or assume r<r_*.

NODE: bpP:p5:lower#constant
KIND: definition
TITLE: The lower-measure coefficient before the threshold
STATEMENT_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291
PROOF_SOURCE: -
CONTRACT_ID: bpP:p5:lower#constant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A, meas V>0, c_dio, C_gamma, kappa_1 and C_b fixed; n=a+b
SOURCE_QUANTIFIERS: data fixed; then C_* before r_*
SOURCE_CONCLUSION: C_* := (A+c_dio C_gamma)/meas V + 6 b kappa_1 + c_n C_b, c_n=1+(1+2^n)(1+(4/3)^n)
CONSTANT_SCOPE: data and scale constants only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p4:conv#data, bpP:p5:dio-one, bpP:p5:rstar#Cgamma, bpP:p5:kam-cond#scales, bpP:p5:budget#constant, bpP:p3:two-scale-kam
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p4:conv#data | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | numerical data used in this constant choice
EDGE: bpP:p5:dio-one | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | numerical data used in this constant choice
EDGE: bpP:p5:rstar#Cgamma | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | numerical data used in this constant choice
EDGE: bpP:p5:kam-cond#scales | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | numerical data used in this constant choice
EDGE: bpP:p5:budget#constant | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | numerical data used in this constant choice
EDGE: bpP:p3:two-scale-kam | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:lower@L291-L291 | numerical data used in this constant choice
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-P-g
REVIEWER: sol-delta-P-g
LEAN_STATUS: PROVED
LEAN_REF: pgLoss (KAM/Planetary/PGAssembly/Lower.lean)
LEAN_NOTE: audit P5-LO PASS WITH NOTES; exact C_* formula
NOTE: -
