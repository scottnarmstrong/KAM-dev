NODE: bpI:p5:real-ham
KIND: lemma
TITLE: Regularity and ODE reduction
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:real-ham@L33-L44
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:real-ham@L45-L50
CONTRACT_ID: bpI:p5:real-ham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting (n=2, tau=2, B' nonempty); constants of Definition bpI:p3:constants; f, epsilon as in Theorem I-HEAD (f holomorphic on T_{s_0} x B_{r_0}, Z^2-periodic in theta, real at real theta and real I in B_{r_0}, epsilon >= 0, |f| <= epsilon there); H_R := Ham_{h,f}, U = iota^{-1}(B_{r_0}), W_B = R^2 x B, P = R^2 x R^2 with max norm, X_R := X_{H_R}; in (d) epsilon <= 1
SOURCE_QUANTIFIERS: f, epsilon fixed (hypotheses of I-HEAD); then the assertions (a)-(e); in (c) for all J subset R and z : R -> P
SOURCE_CONCLUSION: (a) H_R(theta,I)=h(iota I)+f(iota theta,iota I) on R^2 x U, H_R is C^infty on the open set R^2 x U containing W_B and Z^2-periodic in theta; (b) X_R(z)=X_H(z) at every real z in R^2 x U; (c) X_R is C^1 and Z^2-periodic in theta on W_B and IsHamiltonianSolutionOn H_R B J z iff IsSolIn X_R W_B J z; (d) for real (phi,I) in R^2 x B and v: |d/dt f(phi,I+tv)|_{t=0}| <= F_1 epsilon |v| (epsilon<=1); (e) |H_R - h(iota I)| <= epsilon on R^2 x U
CONSTANT_SCOPE: F_1 is the already fixed constant of bpI:p3:constants; no new constant is selected
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p5:rh-values, stepI:p5:rh-smooth, stepI:p5:rh-field, stepI:p5:rh-deriv, bpI:p3:setting, bpI:p3:constants, bpI:p0:realham#realHamiltonian, bpI:p0:hamiltonian#hamiltonianVectorFieldC, bpI:p0:hamsol#IsHamiltonianSolutionOn, N:bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p5:rh-values | blueprint-I/parts/p5-confinement.tex#bpI:p5:real-ham@L46-L46 | proof step (a),(e)
EDGE: stepI:p5:rh-smooth | blueprint-I/parts/p5-confinement.tex#bpI:p5:real-ham@L47-L47 | proof step: smoothness and periodicity
EDGE: stepI:p5:rh-field | blueprint-I/parts/p5-confinement.tex#bpI:p5:real-ham@L48-L48 | proof step (b),(c)
EDGE: stepI:p5:rh-deriv | blueprint-I/parts/p5-confinement.tex#bpI:p5:real-ham@L49-L49 | proof step (d)
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#bpI:p5:real-ham@L29-L29 | standing data: Assumption of Part 3 (statement L29-31)
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#bpI:p5:real-ham@L29-L29 | constants of Part 3 (F_1, s_0 r_0 domains) used in the statement
EDGE: bpI:p0:realham#realHamiltonian | blueprint-I/parts/p5-confinement.tex#bpI:p5:real-ham@L30-L30 | H_R := Ham_{h,f}
EDGE: bpI:p0:hamiltonian#hamiltonianVectorFieldC | blueprint-I/parts/p5-confinement.tex#bpI:p5:real-ham@L37-L37 | X_H the complex Hamiltonian field in (b)
EDGE: bpI:p0:hamsol#IsHamiltonianSolutionOn | blueprint-I/parts/p5-confinement.tex#bpI:p5:real-ham@L39-L39 | predicate in (c)
EDGE: N:bpN:p3:gen-sol | blueprint-I/parts/p5-confinement.tex#bpI:p5:real-ham@L39-L39 | IsSolIn in (c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.realHam_eq, realHam_contDiffOn, realHam_periodic, realHam_field_eq, realHam_field_contDiffOn, realHam_field_periodic, realHam_solution_iff, realHam_fderiv_bound, realHam_sub_le (KAM/Iso/Confinement/RealHam.lean)
LEAN_NOTE: (a)-(e) covered; (d) takes Part-3 derivative estimate hD as input; audit P5-2 PASS WITH NOTES
NOTE: Section prose L29-31 (standing data) is mapped here and to rh-deriv; no separate #data node.

NODE: stepI:p5:rh-values
KIND: step
TITLE: Values
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-values@L46-L46
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-values@L46-L46
CONTRACT_ID: stepI:p5:rh-values
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting and the local notation of L29-31; (theta,I) in R^2 x U
SOURCE_QUANTIFIERS: for all (theta,I) in R^2 x U
SOURCE_CONCLUSION: H_R = h o iota + f o (iota,iota) on R^2 x U, and |H_R - h o iota| <= epsilon (gives (e))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p0:realham#realHamiltonian
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-values@L46-L46 | iota, U, T_{s_0}, B_{r_0} and the reality hypotheses of f and h
EDGE: bpI:p0:realham#realHamiltonian | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-values@L46-L46 | H_R is the real part of H, which equals the real value
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.realHam_eq, realHam_contDiffOn, realHam_periodic, realHam_field_eq, realHam_field_contDiffOn, realHam_field_periodic, realHam_solution_iff, realHam_fderiv_bound, realHam_sub_le (KAM/Iso/Confinement/RealHam.lean)
LEAN_NOTE: realHam_eq, realHam_sub_le; audit P5-2 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:rh-smooth
KIND: step
TITLE: Smoothness and periodicity
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-smooth@L47-L47
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-smooth@L47-L47
CONTRACT_ID: stepI:p5:rh-smooth
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting and the local notation of L29-31
SOURCE_QUANTIFIERS: on R^2 x U
SOURCE_CONCLUSION: H_R is C^infty on R^2 x U (R-linear inclusion composed with holomorphic H) and Z^2-periodic as f is
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, stepI:p5:rh-values, K:bp:p1:holomorphic-regularity
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-smooth@L47-L47 | H=h+f holomorphic on the open set T_{s_0} x B_{r_0}
EDGE: stepI:p5:rh-values | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-smooth@L47-L47 | H_R is the composition of H with the inclusion (values step)
EDGE: K:bp:p1:holomorphic-regularity | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-smooth@L47-L47 | holomorphic implies C^infty
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.realHam_eq, realHam_contDiffOn, realHam_periodic, realHam_field_eq, realHam_field_contDiffOn, realHam_field_periodic, realHam_solution_iff, realHam_fderiv_bound, realHam_sub_le (KAM/Iso/Confinement/RealHam.lean)
LEAN_NOTE: realHam_contDiffOn, realHam_periodic; audit P5-2 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:rh-field
KIND: step
TITLE: The fields
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-field@L48-L48
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-field@L48-L48
CONTRACT_ID: stepI:p5:rh-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting and the local notation of L29-31
SOURCE_QUANTIFIERS: For every real z in R^2 x U for (b); for every J subset R and z:R->P for (c), with X_R C^1 and periodic on W_B
SOURCE_CONCLUSION: (b) X_R = X_H at real points (H real there, H_R = Re H); (c) the predicate equivalence and X_R C^1 on W_B via the ODE reduction, periodicity of X_R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, stepI:p5:rh-smooth, bpI:p0:realham#realHamiltonian, bpI:p0:hamsol#IsHamiltonianSolutionOn, K:bp:p1:hamiltonian-real, N:bpN:p3:ham-reduction, N:bpN:p3:ham-periodic, stepI:p5:rh-values
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-field@L48-L48 | H real at real points of its domain
EDGE: stepI:p5:rh-smooth | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-field@L48-L48 | H_R is C^2 on W
EDGE: bpI:p0:realham#realHamiltonian | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-field@L48-L48 | H_R = Re H
EDGE: bpI:p0:hamsol#IsHamiltonianSolutionOn | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-field@L48-L48 | predicate whose equivalence with IsSolIn is shown
EDGE: K:bp:p1:hamiltonian-real | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-field@L48-L48 | (b) is this lemma
EDGE: N:bpN:p3:ham-reduction | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-field@L48-L48 | (c) with U:=B, W=R^2 x U
EDGE: N:bpN:p3:ham-periodic | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-field@L48-L48 | periodicity of X_R
EDGE: stepI:p5:rh-values | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-field@L48-L48 | H_R agrees with Re H on the real open neighbourhood for the K field lemma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.realHam_eq, realHam_contDiffOn, realHam_periodic, realHam_field_eq, realHam_field_contDiffOn, realHam_field_periodic, realHam_solution_iff, realHam_fderiv_bound, realHam_sub_le (KAM/Iso/Confinement/RealHam.lean)
LEAN_NOTE: realHam_field_*, realHam_solution_iff; audit P5-2 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:rh-deriv
KIND: step
TITLE: Derivative bound
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-deriv@L49-L49
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-deriv@L49-L49
CONTRACT_ID: stepI:p5:rh-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting and the local notation of L29-31; epsilon <= 1; (phi,I) in R^2 x B and v in R^2
SOURCE_QUANTIFIERS: for real (phi,I) in R^2 x B, v in R^2
SOURCE_CONCLUSION: |d/dt f(phi,I+tv)|_{t=0}| <= F_1 epsilon |v| (real directional derivative = Df(phi,I)(0,v))
CONSTANT_SCOPE: F_1 from bpI:p3:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:hypothesis-d, bpI:p3:setting, bpI:p3:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:hypothesis-d | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-deriv@L49-L49 | norm{Df(z)} <= F_1 epsilon on frak D
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-deriv@L49-L49 | B subset B_{r_0/2}, r_0 > 0, f and epsilon as in I-HEAD
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#stepI:p5:rh-deriv@L49-L49 | frak D = T_{s/2} x B_{r_0/2} and F_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.realHam_eq, realHam_contDiffOn, realHam_periodic, realHam_field_eq, realHam_field_contDiffOn, realHam_field_periodic, realHam_solution_iff, realHam_fderiv_bound, realHam_sub_le (KAM/Iso/Confinement/RealHam.lean)
LEAN_NOTE: realHam_fderiv_bound, from Part-3 hD (hypothesis-d dependency); audit P5-2 PASS WITH NOTES
NOTE: -

NODE: bpI:p5:ext-top
KIND: external
TITLE: Topology
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:ext-top@L55-L56
PROOF_SOURCE: -
CONTRACT_ID: bpI:p5:ext-top
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (external)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: A continuous image of a compact set is compact, hence closed; a nonempty compact set and a disjoint nonempty closed set have positive distance (guards checked at each application); a continuous real function on a nonempty compact set attains max and min (nonemptiness verified at each use); the closure of a subset of a closed set lies in it; for A open, boundary(A) = closure(A) minus A (Mathlib IsCompact.exists_isMaxOn, exists_isMinOn, isClosed, exists_infDist_eq_dist, closure_minimal)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p5:sec-patch#data
KIND: definition
TITLE: Patch data of Part 5 (Phi, V, Q, Omega, calK, slopes m_pm)
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-patch#data@L64-L66
PROOF_SOURCE: -
CONTRACT_ID: bpI:p5:sec-patch#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Patch p=(c,W,delta_E,delta_m,rho_c) of Lemma bpI:p3:cover (Definition bpI:p3:patch (P1)-(P3), W as in Lemma bpI:p3:chart); slopes m_pm = m_{p,pm} of Definition bpI:p3:patch-rays
SOURCE_QUANTIFIERS: p fixed; c in closure B'
SOURCE_CONCLUSION: defines Phi=Phi_c, V=Phi(W), Q=[E_c-delta_E,E_c+delta_E] x [-delta_m,delta_m] subset V (P2), E_c=h(c), O (open box), Omega=Phi^{-1}(O) subset W open, calK=Phi^{-1}(Q) subset W; m_pm slopes of the rays
CONSTANT_SCOPE: depends only on the patch p and its rays
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:cover, bpI:p3:patch, bpI:p3:chart, bpI:p3:coordinates, bpI:p3:patch-rays
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-patch#data@L64-L64 | h, B, B_{r_0}
EDGE: bpI:p3:cover | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-patch#data@L64-L64 | patch of Lemma bpI:p3:cover
EDGE: bpI:p3:patch | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-patch#data@L64-L64 | (P2) Q subset V; W subset B
EDGE: bpI:p3:chart | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-patch#data@L64-L64 | Phi=Phi_c on W is a homeomorphism onto open V with C^1 inverse
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-patch#data@L64-L64 | Phi_c=(h,m_c) and m_c
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-patch#data@L65-L65 | slopes m_pm of the rays
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.EnergyPatch, EnergyPatch.Q, EnergyPatch.O, EnergyPatch.Omega, EnergyPatch.K (KAM/Iso/Confinement/Setting.lean)
LEAN_NOTE: definitions; audit P5-0 PASS WITH NOTES; compactness/openness by P5-1
NOTE: Section data paragraph L64-66 (SPEC section-data rule): states openness of Omega and the inclusions consumed by patch-const, ec-*, sp-*.

NODE: bpI:p5:patch-const
KIND: definition
TITLE: Patch constants
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:patch-const@L68-L77
PROOF_SOURCE: -
CONTRACT_ID: bpI:p5:patch-const
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Patch p and its data of bpI:p5:sec-patch#data; W bounded by (P1) of bpI:p3:patch; m_pm in (delta_m/2,delta_m), (-delta_m,-delta_m/2) by Definition bpI:p3:patch-rays
SOURCE_QUANTIFIERS: for each patch p of Lemma bpI:p3:cover
SOURCE_CONCLUSION: defines: calK compact; r_p = min{1, dist(calK, R^2 minus W)/2} > 0; calN = {dist(I,calK) <= r_p} compact subset of W; L_m = max{1, max_{calN} norm Dm_c}; L_Phi = max{1, max_Q norm D(Phi^{-1})}; kappa_p = min{delta_m/4, delta_m - m_+, delta_m + m_-} > 0
CONSTANT_SCOPE: depend only on p and its rays, hence only on (B, s_0, r_0, h, B', eta)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:sec-patch#data, bpI:p3:patch, bpI:p3:patch-rays, bpI:p3:chart, bpI:p3:coordinates, bpI:p5:ext-top, bpI:p3:setting, bpI:p3:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#bpI:p5:patch-const@L70-L70 | calK, Q, Phi, W of the patch
EDGE: bpI:p3:patch | blueprint-I/parts/p5-confinement.tex#bpI:p5:patch-const@L70-L70 | (P1): W bounded; W subset B
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p5-confinement.tex#bpI:p5:patch-const@L74-L74 | m_pm in (delta_m/2,delta_m), (-delta_m,-delta_m/2) for kappa_p
EDGE: bpI:p3:chart | blueprint-I/parts/p5-confinement.tex#bpI:p5:patch-const@L70-L70 | Phi^{-1} continuous and C^1 on V (instance of the inverse function theorem; alias bpI:p5:ext-ift)
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#bpI:p5:patch-const@L72-L72 | m_c is C^1 on U_c containing W
EDGE: bpI:p5:ext-top | blueprint-I/parts/p5-confinement.tex#bpI:p5:patch-const@L70-L70 | compact image, positive distance of compact and closed sets, attained maxima
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#bpI:p5:patch-const@L68-L77 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#bpI:p5:patch-const@L68-L77 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.PatchConst (KAM/Iso/Confinement/Setting.lean); KAM.Iso.Confinement.patchConst_exists, EnergyPatch.isCompact_K (KAM/Iso/Confinement/PatchConst.lean)
LEAN_NOTE: sufficient-bound certificate + existence, not literal extremum formulas (documented departure); audits P5-0, P5-1 PASS WITH NOTES
NOTE: -

NODE: bpI:p5:eps0
KIND: definition
TITLE: The constant epsilon_0
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:eps0@L79-L85
PROOF_SOURCE: -
CONTRACT_ID: bpI:p5:eps0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3: epsilon_1, C_K (Definition bpI:p3:uniform), F_1, rho_infty (Definition bpI:p3:constants); finite family of patches P with constants delta_{E,j}, r_j, kappa_j, L_{m,j}, L_{Phi,j}
SOURCE_QUANTIFIERS: chosen after all data of Part 3 and the patch constants; independent of f, epsilon, z_0
SOURCE_CONCLUSION: defines epsilon_0 := min{epsilon_1, min_{j in P} min{delta_{E,j}/4, rho_infty/(8 C_K), r_j/C_K, kappa_j/(L_{m,j} C_K), 1/(2 F_1 L_{Phi,j})}} > 0
CONSTANT_SCOPE: epsilon_0 depends on (B, s_0, r_0, h, B', eta) only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:constants, bpI:p3:uniform, bpI:p3:cover, bpI:p5:patch-const
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#bpI:p5:eps0@L80-L80 | data of Part 3
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#bpI:p5:eps0@L80-L80 | F_1, rho_infty
EDGE: bpI:p3:uniform | blueprint-I/parts/p5-confinement.tex#bpI:p5:eps0@L80-L80 | epsilon_1 and C_K
EDGE: bpI:p3:cover | blueprint-I/parts/p5-confinement.tex#bpI:p5:eps0@L82-L82 | finite family P of patches
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#bpI:p5:eps0@L82-L82 | delta_E, r_j, kappa_j, L_m, L_Phi per patch
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.Smallness (KAM/Iso/Confinement/Setting.lean); KAM.Iso.Confinement.exists_eps0 (KAM/Iso/Confinement/PatchConst.lean)
LEAN_NOTE: Smallness clauses + existence of threshold, not literal min; audits P5-0 PASS WITH NOTES, P5-1 PASS WITH NOTES
NOTE: -

NODE: bpI:p5:sec-graph#data
KIND: definition
TITLE: Fixed data of the torus-graph subsection (f, epsilon, I_0, E, k_pm, u_pm, v_pm, T_pm)
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-graph#data@L90-L90
PROOF_SOURCE: -
CONTRACT_ID: bpI:p5:sec-graph#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f, epsilon as in Theorem I-HEAD with epsilon < epsilon_0; I_0 in closure B'; E with |E - h(I_0)| <= epsilon; the output of Proposition bpI:p3:tori (j, K_pm, I_pm, omega_pm)
SOURCE_QUANTIFIERS: f, epsilon, I_0, E fixed; then the output of bpI:p3:tori
SOURCE_CONCLUSION: defines k_pm : R^2 -> R^2 x R^2 as the real restriction of K_pm, k_pm(theta) = (theta+u_pm(theta), I_pm+v_pm(theta)) with u_pm, v_pm real-analytic R^2 -> R^2 (T1, real restriction), and T_pm := k_pm(R^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:tori, bpI:p5:eps0, bpI:p3:setting, K:bp:p1:real-restriction, bpI:p3:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:tori | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-graph#data@L90-L90 | output of the proposition (T1)
EDGE: bpI:p5:eps0 | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-graph#data@L90-L90 | epsilon < epsilon_0
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-graph#data@L90-L90 | f, epsilon, h as in I-HEAD
EDGE: K:bp:p1:real-restriction | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-graph#data@L90-L90 | real restriction of holomorphic K_pm is real-analytic
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-graph#data@L90-L90 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.TorusOutput, GraphData, graphSet, P2 (KAM/Iso/Confinement/Setting.lean)
LEAN_NOTE: definitions; audit P5-0 PASS WITH NOTES
NOTE: Section data paragraph L90 (SPEC): fixes the objects used by graph, invariance, mu, separation.

NODE: bpI:p5:graph
KIND: lemma
TITLE: Graph property
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L92-L99
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L100-L105
CONTRACT_ID: bpI:p5:graph
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: bpI:p5:sec-graph#data (f, epsilon < epsilon_0, I_0, E, K_pm, k_pm, u_pm, v_pm); max norm; Psi := theta -> theta + u_pm(theta)
SOURCE_QUANTIFIERS: for each sign; Psi, Y_pm defined from the fixed data
SOURCE_CONCLUSION: (a) Psi : R^2 -> R^2 is a bijection with |Psi theta - Psi theta'| >= |theta-theta'|/2 and Psi^{-1} 2-Lipschitz; (b) Y_pm := I_pm + v_pm o Psi^{-1} continuous, |Y_pm - I_pm| <= C_K epsilon and T_pm = graph of Y_pm over R^2; (c) H_R(phi,Y_pm(phi)) = E, Y_pm(phi) in calN, |h(Y_pm(phi)) - E| <= epsilon
CONSTANT_SCOPE: C_K from Part 3 (depends on (B,s_0,r_0,h,B',eta) only)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p5:gr-contr, stepI:p5:gr-bij, stepI:p5:gr-graph, stepI:p5:gr-energy, bpI:p5:sec-graph#data, bpI:p5:patch-const, bpI:p3:setting, bpI:p3:uniform, bpI:p3:constants, bpI:p3:coordinates, bpI:p5:sec-patch#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p5:gr-contr | blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L101-L101 | proof step
EDGE: stepI:p5:gr-bij | blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L102-L102 | proof step
EDGE: stepI:p5:gr-graph | blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L103-L103 | proof step
EDGE: stepI:p5:gr-energy | blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L104-L104 | proof step
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L90-L90 | T_pm, k_pm, u_pm, v_pm of the statement
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L97-L97 | calN of (c)
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L93-L93 | standing data of Parts 3 and 5
EDGE: bpI:p3:uniform | blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L92-L99 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L92-L99 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L92-L99 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#bpI:p5:graph@L92-L99 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.torus_phase_sub_lipschitz, torus_phase_bijective, torus_phase_inv, torus_graph, torus_graph_mem, torus_graph_energy_close (KAM/Iso/Confinement/Graph.lean)
LEAN_NOTE: (a)-(c) covered; audit P5-3 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:gr-contr
KIND: step
TITLE: Contraction
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-contr@L101-L101
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-contr@L101-L101
CONTRACT_ID: stepI:p5:gr-contr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; a sign is fixed
SOURCE_QUANTIFIERS: for each sign
SOURCE_CONCLUSION: u_pm is 1/2-Lipschitz on R^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:tori, bpI:p5:eps0, bpI:p5:sec-graph#data, K:bp:p1:real-restriction, K:bp:p1:ext-mvt, bpI:p3:constants, bpI:p3:setting, bpI:p3:uniform
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:tori | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-contr@L101-L101 | (T4) bound on Du_pm
EDGE: bpI:p5:eps0 | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-contr@L101-L101 | epsilon < rho_infty/(8 C_K)
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-contr@L101-L101 | u_pm real restriction
EDGE: K:bp:p1:real-restriction | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-contr@L101-L101 | real derivative norm at most the complex one
EDGE: K:bp:p1:ext-mvt | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-contr@L101-L101 | mean value inequality on convex R^2
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-contr@L101-L101 | rho_infty
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-contr@L101-L101 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p3:uniform | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-contr@L101-L101 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.torus_phase_sub_lipschitz, torus_phase_bijective, torus_phase_inv, torus_graph, torus_graph_mem, torus_graph_energy_close (KAM/Iso/Confinement/Graph.lean)
LEAN_NOTE: torus_phase_sub_lipschitz; audit P5-3 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:gr-bij
KIND: step
TITLE: Bijectivity
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-bij@L102-L102
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-bij@L102-L102
CONTRACT_ID: stepI:p5:gr-bij
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; a sign and phi in R^2 are fixed
SOURCE_QUANTIFIERS: for each phi in R^2
SOURCE_CONCLUSION: Psi bijective, |Psi theta - Psi theta'| >= |theta-theta'|/2, Psi^{-1} 2-Lipschitz
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p5:gr-contr, K:bp:p1:ext-banach, bpI:p3:setting, bpI:p5:sec-graph#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p5:gr-contr | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-bij@L102-L102 | theta -> phi - u(theta) is a 1/2-contraction
EDGE: K:bp:p1:ext-banach | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-bij@L102-L102 | Banach fixed point theorem (alias of bpI:p5:ext-banach)
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-bij@L102-L102 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-bij@L102-L102 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.torus_phase_sub_lipschitz, torus_phase_bijective, torus_phase_inv, torus_graph, torus_graph_mem, torus_graph_energy_close (KAM/Iso/Confinement/Graph.lean)
LEAN_NOTE: torus_phase_bijective, torus_phase_inv; audit P5-3 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:gr-graph
KIND: step
TITLE: Graph
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-graph@L103-L103
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-graph@L103-L103
CONTRACT_ID: stepI:p5:gr-graph
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; a sign is fixed
SOURCE_QUANTIFIERS: for each sign
SOURCE_CONCLUSION: (b): Y_pm continuous, |Y_pm - I_pm| <= C_K epsilon, T_pm = {(phi,Y_pm(phi))}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p5:gr-bij, bpI:p3:tori, bpI:p5:sec-graph#data, bpI:p3:setting, bpI:p3:uniform
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p5:gr-bij | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-graph@L103-L103 | substitute theta = Psi^{-1} phi; Psi^{-1} continuous
EDGE: bpI:p3:tori | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-graph@L103-L103 | (T4) ¦v_pm¦ <= C_K epsilon
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-graph@L103-L103 | k_pm, T_pm
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-graph@L103-L103 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p3:uniform | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-graph@L103-L103 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.torus_phase_sub_lipschitz, torus_phase_bijective, torus_phase_inv, torus_graph, torus_graph_mem, torus_graph_energy_close (KAM/Iso/Confinement/Graph.lean)
LEAN_NOTE: torus_graph; audit P5-3 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:gr-energy
KIND: step
TITLE: Energy and position
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104
CONTRACT_ID: stepI:p5:gr-energy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; a sign and phi in R^2 are fixed
SOURCE_QUANTIFIERS: for each sign, all phi
SOURCE_CONCLUSION: (c): H_R(phi,Y_pm(phi)) = E, Y_pm(phi) in calN, |h(Y_pm(phi)) - E| <= epsilon
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:tori, bpI:p3:points, bpI:p5:patch-const, bpI:p5:sec-patch#data, bpI:p5:eps0, bpI:p5:real-ham, stepI:p5:gr-graph, bpI:p3:setting, bpI:p3:uniform, bpI:p3:patch-rays, bpI:p5:sec-graph#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:tori | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104 | (T3) energy identity H_R = E on the torus
EDGE: bpI:p3:points | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104 | I_pm = Phi^{-1}(E,m_pm) in calK as (E,m_pm) in Q
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104 | calN, r_p definition
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104 | calK = Phi^{-1}(Q)
EDGE: bpI:p5:eps0 | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104 | C_K epsilon < r_j
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104 | (e): ¦f¦ <= epsilon, H_R = Re H
EDGE: stepI:p5:gr-graph | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104 | Y_pm and the graph description
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p3:uniform | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:gr-energy@L104-L104 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.torus_phase_sub_lipschitz, torus_phase_bijective, torus_phase_inv, torus_graph, torus_graph_mem, torus_graph_energy_close (KAM/Iso/Confinement/Graph.lean)
LEAN_NOTE: torus_graph, torus_graph_mem, torus_graph_energy_close; audit P5-3 PASS WITH NOTES
NOTE: -

NODE: bpI:p5:invariance
KIND: lemma
TITLE: Invariance
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:invariance@L107-L109
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:invariance@L110-L114
CONTRACT_ID: bpI:p5:invariance
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0
SOURCE_QUANTIFIERS: J' interval; y with IsSolIn X_R W_B J' y; t_1 in J'
SOURCE_CONCLUSION: T_pm subset W_B and T_+ union T_- is invariant for (X_R, W_B) in the sense of N:gen-invariant: if y(t_1) in T_pm for one t_1 in J' then y(t) in T_pm for all t in J'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p5:inv-incl, stepI:p5:inv-sol, stepI:p5:inv-uniq, bpN:p3:gen-invariant, N:bpN:p3:gen-sol, bpI:p5:sec-graph#data, bpI:p5:real-ham, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p5:inv-incl | blueprint-I/parts/p5-confinement.tex#bpI:p5:invariance@L111-L111 | proof step
EDGE: stepI:p5:inv-sol | blueprint-I/parts/p5-confinement.tex#bpI:p5:invariance@L112-L112 | proof step
EDGE: stepI:p5:inv-uniq | blueprint-I/parts/p5-confinement.tex#bpI:p5:invariance@L113-L113 | proof step
EDGE: bpN:p3:gen-invariant | blueprint-I/parts/p5-confinement.tex#bpI:p5:invariance@L108-L108 | definition of invariant set
EDGE: N:bpN:p3:gen-sol | blueprint-I/parts/p5-confinement.tex#bpI:p5:invariance@L108-L108 | IsSolIn
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#bpI:p5:invariance@L108-L108 | T_pm
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#bpI:p5:invariance@L108-L108 | X_R and W_B
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#bpI:p5:invariance@L107-L109 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.torus_flow, torus_invariant (KAM/Iso/Confinement/Invariance.lean)
LEAN_NOTE: per-torus invariance and inclusion; union via KAM.ODE.isInvariantSet_union; audit P5-4 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:inv-incl
KIND: step
TITLE: Inclusion
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-incl@L111-L111
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-incl@L111-L111
CONTRACT_ID: stepI:p5:inv-incl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0
SOURCE_QUANTIFIERS: for each sign, theta in R^2
SOURCE_CONCLUSION: T_pm subset W_B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:graph, bpI:p3:patch, bpI:p5:patch-const, bpI:p5:eps0, bpI:p5:sec-graph#data, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:graph | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-incl@L111-L111 | Y_pm(Psi theta) in calN (c)
EDGE: bpI:p3:patch | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-incl@L111-L111 | (P1): W subset B
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-incl@L111-L111 | calN subset W
EDGE: bpI:p5:eps0 | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-incl@L111-L111 | smallness in epsilon_0 used
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-incl@L111-L111 | k_pm
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-incl@L111-L111 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.torus_flow, torus_invariant (KAM/Iso/Confinement/Invariance.lean)
LEAN_NOTE: torus_invariant; audit P5-4 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:inv-sol
KIND: step
TITLE: The torus solution
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-sol@L112-L112
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-sol@L112-L112
CONTRACT_ID: stepI:p5:inv-sol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; J' is an interval, y is a solution in W_B on J', t_1 in J', and y(t_1)=k_pm(theta_1)
SOURCE_QUANTIFIERS: t_1, theta_1
SOURCE_CONCLUSION: w(t) := k_pm(theta_1 + (t-t_1) omega_pm) satisfies IsSolIn X_R W_B R w
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:tori, K:bp:p1:real-restriction, bpI:p5:real-ham, stepI:p5:inv-incl, N:bpN:p3:gen-sol, bpI:p5:sec-graph#data, bpI:p3:setting, bpI:p3:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:tori | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-sol@L112-L112 | (T2) invariance equation and omega_pm
EDGE: K:bp:p1:real-restriction | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-sol@L112-L112 | w differentiable with derivative DK omega
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-sol@L112-L112 | (b): X_H = X_R at real points
EDGE: stepI:p5:inv-incl | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-sol@L112-L112 | w stays in W_B
EDGE: N:bpN:p3:gen-sol | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-sol@L112-L112 | IsSolIn
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-sol@L112-L112 | k_pm
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-sol@L112-L112 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-sol@L112-L112 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.torus_flow, torus_invariant (KAM/Iso/Confinement/Invariance.lean)
LEAN_NOTE: torus_flow; audit P5-4 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:inv-uniq
KIND: step
TITLE: Uniqueness
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-uniq@L113-L113
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-uniq@L113-L113
CONTRACT_ID: stepI:p5:inv-uniq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; J' is an interval, y is a solution in W_B on J', t_1 in J', and y(t_1)=k_pm(theta_1); w is the map defined at L112
SOURCE_QUANTIFIERS: For each sign, every interval J', solution y on J', t_1 in J' and theta_1 with y(t_1)=k_pm(theta_1); for all t in J'
SOURCE_CONCLUSION: y = w on J', hence y(J') subset T_pm; union of two invariant sets is invariant
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:real-ham, stepI:p5:inv-sol, N:bpN:p3:gen-uniqueness, bpN:p3:gen-invariant, bpI:p3:setting, bpI:p5:sec-graph#data, N:bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-uniq@L113-L113 | (c): X_R C^1 on W_B
EDGE: stepI:p5:inv-sol | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-uniq@L113-L113 | comparison solution w
EDGE: N:bpN:p3:gen-uniqueness | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-uniq@L113-L113 | uniqueness on J
EDGE: bpN:p3:gen-invariant | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-uniq@L113-L113 | invariance of a union
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-uniq@L113-L113 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-uniq@L113-L113 | objects or constants of this package occur in the local claim or its proof
EDGE: N:bpN:p3:gen-sol | blueprint-I/parts/p5-confinement.tex#stepI:p5:inv-uniq@L113-L113 | restrict w from R to J' before applying arbitrary-interval uniqueness
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.torus_flow, torus_invariant (KAM/Iso/Confinement/Invariance.lean)
LEAN_NOTE: torus_invariant; audit P5-4 PASS WITH NOTES
NOTE: -

NODE: bpI:p5:energy-coordinate
KIND: lemma
TITLE: Energy equation is uniquely solvable in e=h(I)
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:energy-coordinate@L119-L122
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:energy-coordinate@L123-L126
CONTRACT_ID: bpI:p5:energy-coordinate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: patch data of bpI:p5:sec-patch#data and constants of bpI:p5:patch-const; epsilon <= min{1, 1/(2 F_1 L_Phi)}
SOURCE_QUANTIFIERS: patch p fixed; epsilon; phi in R^2; (e_1,m),(e_2,m) in Q; I_i = Phi^{-1}(e_i,m)
SOURCE_CONCLUSION: H_R(phi,I_1) = H_R(phi,I_2) implies I_1 = I_2
CONSTANT_SCOPE: F_1 from bpI:p3:constants; L_Phi from bpI:p5:patch-const
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p5:ec-reduce, stepI:p5:ec-lip, bpI:p5:sec-patch#data, bpI:p5:patch-const, bpI:p3:constants, bpI:p5:real-ham, bpI:p3:setting, bpI:p3:coordinates
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p5:ec-reduce | blueprint-I/parts/p5-confinement.tex#bpI:p5:energy-coordinate@L124-L124 | proof step
EDGE: stepI:p5:ec-lip | blueprint-I/parts/p5-confinement.tex#bpI:p5:energy-coordinate@L125-L125 | proof step
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#bpI:p5:energy-coordinate@L120-L120 | Q, Phi
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#bpI:p5:energy-coordinate@L120-L120 | L_Phi
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#bpI:p5:energy-coordinate@L120-L120 | F_1
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#bpI:p5:energy-coordinate@L120-L120 | H_R and f of the setting
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#bpI:p5:energy-coordinate@L119-L122 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#bpI:p5:energy-coordinate@L119-L122 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.energy_coordinate (KAM/Iso/Confinement/EnergyCoordinate.lean)
LEAN_NOTE: audit P5-5 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:ec-reduce
KIND: step
TITLE: Reduction to one variable
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-reduce@L124-L124
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-reduce@L124-L124
CONTRACT_ID: stepI:p5:ec-reduce
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting and the local notation of L29-31; a patch and its constants are fixed; epsilon <= min{1,1/(2 F_1 L_Phi)}, phi in R^2, (e_1,m),(e_2,m) in Q, I_i=Phi^{-1}(e_i,m), H_R(phi,I_1)=H_R(phi,I_2)
SOURCE_QUANTIFIERS: fixed phi, m
SOURCE_CONCLUSION: H_R(phi,Phi^{-1}(e,m)) = g(e) on [E_c-delta_E,E_c+delta_E]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:real-ham, bpI:p3:coordinates, bpI:p5:sec-patch#data, bpI:p3:patch, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-reduce@L124-L124 | (a): H_R = h + f on R^2 x U
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-reduce@L124-L124 | first component of Phi is h
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-reduce@L124-L124 | calK = Phi^{-1}(Q) subset W
EDGE: bpI:p3:patch | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-reduce@L124-L124 | (P1): W subset B
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-reduce@L124-L124 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.energy_coordinate (KAM/Iso/Confinement/EnergyCoordinate.lean)
LEAN_NOTE: inside energy_coordinate; audit P5-5 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:ec-lip
KIND: step
TITLE: Contraction
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-lip@L125-L125
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-lip@L125-L125
CONTRACT_ID: stepI:p5:ec-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting and the local notation of L29-31; a patch and its constants are fixed; epsilon <= min{1,1/(2 F_1 L_Phi)}, phi in R^2, (e_1,m),(e_2,m) in Q, I_i=Phi^{-1}(e_i,m), H_R(phi,I_1)=H_R(phi,I_2)
SOURCE_QUANTIFIERS: fixed phi, m; e_1, e_2
SOURCE_CONCLUSION: |e_1 - e_2| <= |e_1-e_2|/2, hence e_1=e_2 and I_1=I_2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:real-ham, K:bp:p1:ext-mvt, bpI:p5:patch-const, bpI:p3:chart, stepI:p5:ec-reduce, bpI:p3:constants, bpI:p3:setting, bpI:p3:coordinates, bpI:p5:sec-patch#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-lip@L125-L125 | (d): directional derivative bound F_1 epsilon
EDGE: K:bp:p1:ext-mvt | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-lip@L125-L125 | mean value inequality
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-lip@L125-L125 | L_Phi
EDGE: bpI:p3:chart | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-lip@L125-L125 | Phi^{-1} is C^1 on V (alias bpI:p5:ext-ift)
EDGE: stepI:p5:ec-reduce | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-lip@L125-L125 | g(e_1)=g(e_2) from equal energies
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-lip@L125-L125 | F_1
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-lip@L125-L125 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-lip@L125-L125 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:ec-lip@L125-L125 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.energy_coordinate (KAM/Iso/Confinement/EnergyCoordinate.lean)
LEAN_NOTE: inside energy_coordinate; audit P5-5 PASS WITH NOTES
NOTE: -

NODE: bpI:p5:sec-sep#data
KIND: definition
TITLE: Separation data (mu_pm, G, calV)
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-sep#data@L131-L135
PROOF_SOURCE: -
CONTRACT_ID: bpI:p5:sec-sep#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Notation of the torus-graph subsection (bpI:p5:sec-graph#data, Lemma bpI:p5:graph for Y_pm); patch j with |I_0 - c_j| < rho_j and its data (bpI:p5:sec-patch#data)
SOURCE_QUANTIFIERS: fixed data of the previous subsection
SOURCE_CONCLUSION: defines mu_pm(phi) := m_c(Y_pm(phi)), G := {z in P : H_R(z) = E}, calV := {(phi,I) in R^2 x Omega : mu_-(phi) < m_c(I) < mu_+(phi)}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:sec-graph#data, bpI:p5:sec-patch#data, bpI:p5:graph, bpI:p5:real-ham, bpI:p3:coordinates, bpI:p3:setting, bpI:p5:patch-const
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-sep#data@L131-L131 | f, epsilon, E, tori of the previous subsection
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-sep#data@L131-L131 | c, Phi, Q, Omega, calK, calN, delta_E, delta_m, kappa of the patch j
EDGE: bpI:p5:graph | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-sep#data@L133-L133 | Y_pm
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-sep#data@L133-L133 | H_R
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-sep#data@L133-L133 | m_c
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-sep#data@L131-L135 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#bpI:p5:sec-sep#data@L131-L135 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.SepSetting, levelSet, sepRegion (KAM/Iso/Confinement/Setting.lean)
LEAN_NOTE: definitions; audit P5-0 PASS WITH NOTES
NOTE: Section data paragraph L131-135 (SPEC): defines the objects of the separation proposition.

NODE: bpI:p5:mu
KIND: lemma
TITLE: Position of the graphs in the chart
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L137-L139
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L140-L144
CONTRACT_ID: bpI:p5:mu
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; notation of L131-135
SOURCE_QUANTIFIERS: for each sign, all phi in R^2
SOURCE_CONCLUSION: mu_pm is continuous on R^2, |mu_pm(phi) - m_pm| <= L_m C_K epsilon < kappa <= delta_m/4; hence mu_-(phi) < -delta_m/4, mu_+(phi) > delta_m/4 and mu_pm(phi) in (-delta_m, delta_m)
CONSTANT_SCOPE: L_m, kappa from bpI:p5:patch-const; C_K from Part 3
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p5:mu-cont, stepI:p5:mu-lip, stepI:p5:mu-order, bpI:p5:sec-sep#data, bpI:p5:patch-const, bpI:p5:eps0, bpI:p3:setting, bpI:p3:uniform, bpI:p3:constants, bpI:p3:coordinates, bpI:p3:patch-rays
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p5:mu-cont | blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L141-L141 | proof step
EDGE: stepI:p5:mu-lip | blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L142-L142 | proof step
EDGE: stepI:p5:mu-order | blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L143-L143 | proof step
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L138-L138 | mu_pm
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L138-L138 | L_m, kappa
EDGE: bpI:p5:eps0 | blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L138-L138 | epsilon < epsilon_0 gives L_m C_K epsilon < kappa
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L137-L139 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p3:uniform | blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L137-L139 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L137-L139 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L137-L139 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p5-confinement.tex#bpI:p5:mu@L137-L139 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.slope_close, slope_window_plus, slope_window_minus, slope_continuous (KAM/Iso/Confinement/Position.lean)
LEAN_NOTE: audit P5-6 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:mu-cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-cont@L141-L141
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-cont@L141-L141
CONTRACT_ID: stepI:p5:mu-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; patch and notation of L131-135
SOURCE_QUANTIFIERS: for each sign
SOURCE_CONCLUSION: mu_pm = m_c o Y_pm is continuous
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:graph, bpI:p3:coordinates, bpI:p3:chart, bpI:p5:patch-const, bpI:p5:sec-sep#data, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:graph | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-cont@L141-L141 | Y_pm continuous with values in calN
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-cont@L141-L141 | m_c continuous on U_c
EDGE: bpI:p3:chart | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-cont@L141-L141 | W subset U_c
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-cont@L141-L141 | calN subset W
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-cont@L141-L141 | definition of mu_pm
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-cont@L141-L141 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.slope_close, slope_window_plus, slope_window_minus, slope_continuous (KAM/Iso/Confinement/Position.lean)
LEAN_NOTE: slope_continuous; audit P5-6 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:mu-lip
KIND: step
TITLE: Lipschitz comparison
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142
CONTRACT_ID: stepI:p5:mu-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; patch and notation of L131-135; a sign and phi in R^2
SOURCE_QUANTIFIERS: for each sign, all phi
SOURCE_CONCLUSION: |mu_pm(phi) - m_pm| <= L_m C_K epsilon < kappa
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:graph, bpI:p3:points, bpI:p5:patch-const, K:bp:p1:ext-mvt, bpI:p5:eps0, bpI:p5:sec-patch#data, bpI:p3:setting, bpI:p3:uniform, bpI:p3:constants, bpI:p3:coordinates, bpI:p3:patch-rays, bpI:p5:sec-graph#data, bpI:p5:sec-sep#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:graph | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | (b): ¦Y_pm - I_pm¦ <= C_K epsilon
EDGE: bpI:p3:points | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | I_pm in calK and m_c(I_pm) = m_pm
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | calN, r_p, L_m
EDGE: K:bp:p1:ext-mvt | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | mean value inequality for m_c along the segment
EDGE: bpI:p5:eps0 | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | L_m C_K epsilon < kappa
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | calK
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p3:uniform | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-lip@L142-L142 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.slope_close, slope_window_plus, slope_window_minus, slope_continuous (KAM/Iso/Confinement/Position.lean)
LEAN_NOTE: slope_close; audit P5-6 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:mu-order
KIND: step
TITLE: Ordering
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-order@L143-L143
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-order@L143-L143
CONTRACT_ID: stepI:p5:mu-order
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; patch and notation of L131-135; a sign and phi in R^2
SOURCE_QUANTIFIERS: for each sign, all phi
SOURCE_CONCLUSION: mu_+ > delta_m/4, mu_- < -delta_m/4, mu_pm in (-delta_m,delta_m)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:patch-rays, bpI:p5:patch-const, stepI:p5:mu-lip, bpI:p3:setting, bpI:p3:coordinates, bpI:p5:sec-graph#data, bpI:p5:sec-sep#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-order@L143-L143 | m_+ in (delta_m/2,delta_m), m_- in (-delta_m,-delta_m/2)
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-order@L143-L143 | kappa = min{delta_m/4, delta_m - m_+, delta_m + m_-}
EDGE: stepI:p5:mu-lip | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-order@L143-L143 | ¦mu_pm - m_pm¦ < kappa
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-order@L143-L143 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-order@L143-L143 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-order@L143-L143 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:mu-order@L143-L143 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.slope_close, slope_window_plus, slope_window_minus, slope_continuous (KAM/Iso/Confinement/Position.lean)
LEAN_NOTE: slope_window_plus/minus; audit P5-6 PASS WITH NOTES
NOTE: -

NODE: bpI:p5:separation
KIND: proposition
TITLE: Separation by two invariant tori
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L146-L153
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L154-L161
CONTRACT_ID: bpI:p5:separation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z_0 = (theta_0, I_0) with I_0 in B'; E := H_R(z_0); epsilon < epsilon_0 (so bpI:p3:tori applies with this E); bpI:p5:sec-graph#data, bpI:p5:sec-sep#data
SOURCE_QUANTIFIERS: z_0, E, epsilon fixed; (c) for all intervals J containing 0 and z with IsSolIn X_R W_B J z, z(0) = z_0
SOURCE_CONCLUSION: (a) calV is open in P, z_0 in calV, z_0 not in T_+ union T_-; (b) closure(calV) subset R^2 x calK and boundary(calV) cap G subset T_+ union T_-; (c) z(t) in calV for all t in J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p5:sp-open, stepI:p5:sp-init, stepI:p5:sp-closure, stepI:p5:sp-window, stepI:p5:sp-bdry, stepI:p5:sp-barrier, bpI:p5:sec-sep#data, bpI:p5:sec-graph#data, bpI:p3:tori, bpI:p5:eps0, bpI:p5:real-ham, N:bpN:p3:gen-sol, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p5:sp-open | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L155-L155 | proof step
EDGE: stepI:p5:sp-init | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L156-L156 | proof step
EDGE: stepI:p5:sp-closure | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L157-L157 | proof step
EDGE: stepI:p5:sp-window | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L158-L158 | proof step
EDGE: stepI:p5:sp-bdry | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L159-L159 | proof step
EDGE: stepI:p5:sp-barrier | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L160-L160 | proof step
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L150-L150 | calV, G
EDGE: bpI:p5:sec-graph#data | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L147-L147 | T_pm and the tori output
EDGE: bpI:p3:tori | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L147-L147 | tori proposition applies with this E
EDGE: bpI:p5:eps0 | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L147-L147 | epsilon < epsilon_0
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L147-L147 | H_R, X_R, W_B
EDGE: N:bpN:p3:gen-sol | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L151-L151 | IsSolIn
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#bpI:p5:separation@L146-L153 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.separation_isOpen, separation_init, separation_closure, separation_window, separation_boundary, separation_confined (KAM/Iso/Confinement/Separation.lean)
LEAN_NOTE: (a)-(c) covered; audit P5-7 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:sp-open
KIND: step
TITLE: Openness
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-open@L155-L155
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-open@L155-L155
CONTRACT_ID: stepI:p5:sp-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; z_0=(theta_0,I_0), I_0 in B', E=H_R(z_0), and the sets of L131-135
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of the enclosing proof; no new binders
SOURCE_CONCLUSION: calV open in P
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:mu, bpI:p3:coordinates, bpI:p5:sec-patch#data, bpI:p5:sec-sep#data, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:mu | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-open@L155-L155 | mu_pm continuous
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-open@L155-L155 | m_c continuous on U_c
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-open@L155-L155 | Omega open subset of W subset U_c
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-open@L155-L155 | definition of calV
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-open@L155-L155 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.separation_isOpen, separation_init, separation_closure, separation_window, separation_boundary, separation_confined (KAM/Iso/Confinement/Separation.lean)
LEAN_NOTE: separation_isOpen; audit P5-7 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:sp-init
KIND: step
TITLE: The initial point
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-init@L156-L156
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-init@L156-L156
CONTRACT_ID: stepI:p5:sp-init
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; z_0=(theta_0,I_0), I_0 in B', E=H_R(z_0), and the sets of L131-135
SOURCE_QUANTIFIERS: z_0 = (theta_0,I_0)
SOURCE_CONCLUSION: z_0 in calV; z_0 not in T_+ union T_-
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:tori, bpI:p3:patch, bpI:p5:mu, bpI:p5:graph, bpI:p5:sec-patch#data, bpI:p5:sec-sep#data, bpI:p3:setting, bpI:p3:coordinates
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:tori | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-init@L156-L156 | patch j with ¦I_0 - c_j¦ < rho_j
EDGE: bpI:p3:patch | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-init@L156-L156 | (P3): bounds on h and m_c near c
EDGE: bpI:p5:mu | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-init@L156-L156 | mu_- < -delta_m/4 < m_c(I_0) < delta_m/4 < mu_+
EDGE: bpI:p5:graph | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-init@L156-L156 | (b): T_pm is the graph of Y_pm
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-init@L156-L156 | Phi, O, Omega
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-init@L156-L156 | calV
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-init@L156-L156 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-init@L156-L156 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.separation_isOpen, separation_init, separation_closure, separation_window, separation_boundary, separation_confined (KAM/Iso/Confinement/Separation.lean)
LEAN_NOTE: separation_init; audit P5-7 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:sp-closure
KIND: step
TITLE: Closure
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-closure@L157-L157
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-closure@L157-L157
CONTRACT_ID: stepI:p5:sp-closure
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; z_0=(theta_0,I_0), I_0 in B', E=H_R(z_0), and the sets of L131-135
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of the enclosing proof; no new binders
SOURCE_CONCLUSION: closure(Omega) subset calK and closure(calV) subset R^2 x calK
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:ext-top, bpI:p5:patch-const, bpI:p5:sec-patch#data, bpI:p3:setting, bpI:p5:sec-sep#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:ext-top | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-closure@L157-L157 | compact sets are closed; closure of subset of closed set
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-closure@L157-L157 | calK compact
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-closure@L157-L157 | Omega subset calK
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-closure@L157-L157 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-closure@L157-L157 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.separation_isOpen, separation_init, separation_closure, separation_window, separation_boundary, separation_confined (KAM/Iso/Confinement/Separation.lean)
LEAN_NOTE: separation_closure; audit P5-7 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:sp-window
KIND: step
TITLE: Energy window
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-window@L158-L158
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-window@L158-L158
CONTRACT_ID: stepI:p5:sp-window
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; z_0=(theta_0,I_0), I_0 in B', E=H_R(z_0), and the sets of L131-135; (phi,I) in G with I in K
SOURCE_QUANTIFIERS: (phi,I) in G, I in calK
SOURCE_CONCLUSION: |h(I) - E_c| < delta_E
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:real-ham, bpI:p3:patch, bpI:p5:eps0, bpI:p5:sec-sep#data, bpI:p3:setting, bpI:p5:sec-patch#data, bpI:p5:patch-const
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-window@L158-L158 | (e): ¦E - h(I_0)¦ <= epsilon and h(I) = E - f(phi,I) with ¦f¦ <= epsilon
EDGE: bpI:p3:patch | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-window@L158-L158 | (P3): ¦h(I_0) - h(c)¦ < delta_E/2
EDGE: bpI:p5:eps0 | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-window@L158-L158 | epsilon < delta_E/4
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-window@L158-L158 | G
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-window@L158-L158 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-window@L158-L158 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-window@L158-L158 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.separation_isOpen, separation_init, separation_closure, separation_window, separation_boundary, separation_confined (KAM/Iso/Confinement/Separation.lean)
LEAN_NOTE: separation_window; audit P5-7 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:sp-bdry
KIND: step
TITLE: Boundary on the level
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159
CONTRACT_ID: stepI:p5:sp-bdry
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; z_0=(theta_0,I_0), I_0 in B', E=H_R(z_0), and the sets of L131-135; p=(phi,I) in boundary(V) intersect G
SOURCE_QUANTIFIERS: p in boundary(calV) cap G
SOURCE_CONCLUSION: p in T_+ union T_- (this is (b))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p5:sp-closure, bpI:p5:mu, stepI:p5:sp-window, bpI:p5:graph, bpI:p5:energy-coordinate, bpI:p3:chart, bpI:p5:patch-const, bpI:p5:ext-top, bpI:p5:sec-sep#data, bpI:p5:sec-patch#data, bpI:p3:setting, bpI:p3:coordinates, stepI:p5:sp-open, bpI:p5:eps0
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p5:sp-closure | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | I in calK subset W
EDGE: bpI:p5:mu | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | ¦m_c¦ < delta_m and (mu_pm in (-delta_m,delta_m)) and (h(Y),mu_s) in Q
EDGE: stepI:p5:sp-window | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | ¦h(I) - E_c¦ < delta_E
EDGE: bpI:p5:graph | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | (b),(c): H_R(phi,Y) = E and T_s = graph
EDGE: bpI:p5:energy-coordinate | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | I = Y_s(phi)
EDGE: bpI:p3:chart | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | Phi injective on W
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | calN subset W
EDGE: bpI:p5:ext-top | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | boundary(A) = closure(A) minus A for A open
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | calV, G, mu_pm
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | Q, O, Omega
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p3:coordinates | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | objects or constants of this package occur in the local claim or its proof
EDGE: stepI:p5:sp-open | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | boundary V = closure V minus V requires the openness proved at L155
EDGE: bpI:p5:eps0 | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-bdry@L159-L159 | epsilon < epsilon_0 <= epsilon_1 <= 1 and epsilon_0 <= 1/(2 F_1 L_Phi) discharge the conditional energy-coordinate application
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.separation_isOpen, separation_init, separation_closure, separation_window, separation_boundary, separation_confined (KAM/Iso/Confinement/Separation.lean)
LEAN_NOTE: separation_boundary; audit P5-7 PASS WITH NOTES
NOTE: -

NODE: stepI:p5:sp-barrier
KIND: step
TITLE: Barrier
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-barrier@L160-L160
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-barrier@L160-L160
CONTRACT_ID: stepI:p5:sp-barrier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; z_0=(theta_0,I_0), I_0 in B', E=H_R(z_0), and the sets of L131-135; J an interval containing 0, IsSolIn X_R W_B J z and z(0)=z_0
SOURCE_QUANTIFIERS: J interval containing 0
SOURCE_CONCLUSION: z(t) in calV for all t in J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:real-ham, N:bpN:p3:ham-energy, bpN:p3:gen-barrier, bpI:p5:invariance, stepI:p5:sp-open, stepI:p5:sp-init, stepI:p5:sp-bdry, bpI:p5:sec-sep#data, N:bpN:p3:gen-sol, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-barrier@L160-L160 | (c): H_R differentiable with derivative X_R; X_R C^1 on W_B
EDGE: N:bpN:p3:ham-energy | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-barrier@L160-L160 | z(J) subset G by energy conservation
EDGE: bpN:p3:gen-barrier | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-barrier@L160-L160 | barrier lemma with V=calV, S=T_+ union T_-
EDGE: bpI:p5:invariance | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-barrier@L160-L160 | S invariant
EDGE: stepI:p5:sp-open | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-barrier@L160-L160 | calV open
EDGE: stepI:p5:sp-init | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-barrier@L160-L160 | z(0) in calV and not in S
EDGE: stepI:p5:sp-bdry | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-barrier@L160-L160 | boundary(calV) cap G subset S
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-barrier@L160-L160 | calV, G
EDGE: N:bpN:p3:gen-sol | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-barrier@L160-L160 | IsSolIn
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:sp-barrier@L160-L160 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.separation_isOpen, separation_init, separation_closure, separation_window, separation_boundary, separation_confined (KAM/Iso/Confinement/Separation.lean)
LEAN_NOTE: separation_confined; audit P5-7 PASS WITH NOTES
NOTE: -

NODE: bpI:p5:confinement
KIND: proposition
TITLE: Confinement and global existence
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:confinement@L172-L174
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p5:confinement@L175-L178
CONTRACT_ID: bpI:p5:confinement
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of Proposition bpI:p5:separation; z the maximal solution of z' = X_R(z) in W_B with z(0) = z_0 (N:gen-maximal), maximal interval (T_-,T_+)
SOURCE_QUANTIFIERS: z_0, epsilon as in separation; z maximal solution
SOURCE_CONCLUSION: T_- = -infinity, T_+ = +infinity and for all t in R: z(t) in calV, z(t)_2 in calK subset calS subset B and |z(t)_2 - I_0| < eta/2 < eta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p5:cf-conf, stepI:p5:cf-cont, bpI:p5:separation, N:bpN:p3:gen-maximal, bpI:p5:real-ham, bpI:p3:constants, bpI:p3:setting, bpI:p5:sec-sep#data, bpI:p5:patch-const
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p5:cf-conf | blueprint-I/parts/p5-confinement.tex#bpI:p5:confinement@L176-L176 | proof step
EDGE: stepI:p5:cf-cont | blueprint-I/parts/p5-confinement.tex#bpI:p5:confinement@L177-L177 | proof step
EDGE: bpI:p5:separation | blueprint-I/parts/p5-confinement.tex#bpI:p5:confinement@L173-L173 | setting and the sets calV, calK
EDGE: N:bpN:p3:gen-maximal | blueprint-I/parts/p5-confinement.tex#bpI:p5:confinement@L173-L173 | maximal solution
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#bpI:p5:confinement@L173-L173 | X_R, W_B
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#bpI:p5:confinement@L173-L173 | calS and eta
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#bpI:p5:confinement@L172-L174 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#bpI:p5:confinement@L172-L174 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#bpI:p5:confinement@L172-L174 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.confinement_prop (KAM/Iso/Confinement/Confinement.lean)
LEAN_NOTE: source-facing, derives barrier via separation_confined; audit P5-8 PASS
NOTE: -

NODE: stepI:p5:cf-conf
KIND: step
TITLE: Confinement on the maximal interval
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-conf@L176-L176
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-conf@L176-L176
CONTRACT_ID: stepI:p5:cf-conf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; z_0=(theta_0,I_0), I_0 in B', E=H_R(z_0), and the sets of L131-135; z is the maximal solution through z_0 in W_B, with interval (T_-,T_+)
SOURCE_QUANTIFIERS: t in (T_-,T_+)
SOURCE_CONCLUSION: z(t) in calV, z(t)_2 in Omega subset W, |z(t)_2 - I_0| < eta_1/2 <= eta/2
CONSTANT_SCOPE: eta_1 = min{eta, d_B/2} from bpI:p3:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:separation, bpI:p3:patch, bpI:p3:constants, N:bpN:p3:gen-maximal, bpI:p5:sec-patch#data, bpI:p3:setting, bpI:p5:sec-sep#data, bpI:p5:patch-const
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:separation | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-conf@L176-L176 | (c) with J = (T_-,T_+)
EDGE: bpI:p3:patch | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-conf@L176-L176 | (P1),(P3): W within eta_1/4 of c; rho_c <= eta_1/4
EDGE: bpI:p3:constants | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-conf@L176-L176 | eta_1 <= eta
EDGE: N:bpN:p3:gen-maximal | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-conf@L176-L176 | z is a solution on the maximal interval
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-conf@L176-L176 | Omega subset W
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-conf@L176-L176 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-conf@L176-L176 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-conf@L176-L176 | objects or constants of this package occur in the local claim or its proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.confinement_prop (KAM/Iso/Confinement/Confinement.lean)
LEAN_NOTE: named in audit P5-8 PASS
NOTE: -

NODE: stepI:p5:cf-cont
KIND: step
TITLE: Continuation
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-cont@L177-L177
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-cont@L177-L177
CONTRACT_ID: stepI:p5:cf-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The fixed f, epsilon, I_0, E and selected torus data of L90, with epsilon < epsilon_0; z_0=(theta_0,I_0), I_0 in B', E=H_R(z_0), and the sets of L131-135; z is the maximal solution through z_0 in W_B, with interval (T_-,T_+)
SOURCE_QUANTIFIERS: inherits the fixed data and quantifiers of the enclosing proof; no new binders
SOURCE_CONCLUSION: T_- = -infinity and T_+ = +infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:real-ham, N:bpN:p3:gen-continuation-periodic, stepI:p5:cf-conf, bpI:p5:patch-const, bpI:p3:patch, N:bpN:p3:gen-maximal, bpI:p3:setting, bpI:p5:sec-sep#data, bpI:p5:sec-patch#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-cont@L177-L177 | (c): X_R C^1 and periodic on R^2 x B
EDGE: N:bpN:p3:gen-continuation-periodic | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-cont@L177-L177 | continuation for periodic fields with unbounded angles
EDGE: stepI:p5:cf-conf | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-cont@L177-L177 | on the maximal interval the actions lie in Omega; with Omega subset K from sec-patch#data this supplies the compact carrier required for continuation
EDGE: bpI:p5:patch-const | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-cont@L177-L177 | calK compact
EDGE: bpI:p3:patch | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-cont@L177-L177 | calK subset W subset B (P1)
EDGE: N:bpN:p3:gen-maximal | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-cont@L177-L177 | maximal interval (T_-,T_+)
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-cont@L177-L177 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: bpI:p5:sec-sep#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-cont@L177-L177 | objects or constants of this package occur in the local claim or its proof
EDGE: bpI:p5:sec-patch#data | blueprint-I/parts/p5-confinement.tex#stepI:p5:cf-cont@L177-L177 | Omega = Phi^{-1}(O) subset Phi^{-1}(Q) = K; combine with cf-conf to obtain z(t)_2 in K
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Confinement.confinement_prop (KAM/Iso/Confinement/Confinement.lean)
LEAN_NOTE: named in audit P5-8 PASS
NOTE: -

NODE: stepI:p5:hd-eps
KIND: step
TITLE: The constant
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-eps@L181-L181
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-eps@L181-L181
CONTRACT_ID: stepI:p5:hd-eps
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Theorem I-HEAD data (B, s_0, r_0, h, B', eta) fixed before f, epsilon, z_0
SOURCE_QUANTIFIERS: B, s_0, r_0, h, B', eta fixed; then epsilon_0
SOURCE_CONCLUSION: if B' is empty the conclusion is vacuous and epsilon_0 = 1 works; otherwise epsilon_0 of Definition bpI:p5:eps0 depends on (B, s_0, r_0, h, B', eta) only (not on f, epsilon, z_0)
CONSTANT_SCOPE: epsilon_0 depends on (B, s_0, r_0, h, B', eta) only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:eps0
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:eps0 | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-eps@L181-L181 | the constant epsilon_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: confinement_main, all_time_confinement (KAM/Provider/Iso/AllTimeConfinement.lean)
LEAN_NOTE: audit I-HEAD PASS (row names this step -> confinement_main); step of PROVED parent bpI:p0:head (ruling b)
NOTE: The eps0 dependency is used only in the B' nonempty branch. All geometric data and constants in that branch are chosen before f, epsilon, z_0.

NODE: stepI:p5:hd-fix
KIND: step
TITLE: Fixing f, epsilon, z_0
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-fix@L182-L182
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-fix@L182-L182
CONTRACT_ID: stepI:p5:hd-fix
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f, epsilon with 0 <= epsilon < epsilon_0 (epsilon=0 allowed); z_0 = (theta_0,I_0), I_0 in B'
SOURCE_QUANTIFIERS: epsilon_0 fixed; f, epsilon; z_0
SOURCE_CONCLUSION: E := H_R(z_0) satisfies |E - h(I_0)| <= epsilon, I_0 in closure B', so Proposition bpI:p3:tori applies; all objects of Part 5 exist (epsilon=0: u_pm = v_pm = 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p5:hd-eps, bpI:p5:real-ham, bpI:p3:tori, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p5:hd-eps | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-fix@L182-L182 | epsilon_0
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-fix@L182-L182 | (e): ¦E - h(I_0)¦ <= epsilon
EDGE: bpI:p3:tori | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-fix@L182-L182 | proposition applies
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-fix@L182-L182 | data of I-HEAD
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5
REVIEWER: sol-review-I-p5p8
LEAN_STATUS: PROVED
LEAN_REF: confinement_main, all_time_confinement (KAM/Provider/Iso/AllTimeConfinement.lean)
LEAN_NOTE: audit I-HEAD PASS (row names this step -> confinement_main); step of PROVED parent bpI:p0:head (ruling b)
NOTE: -

NODE: stepI:p5:hd-sol
KIND: step
TITLE: The solution
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-sol@L183-L183
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-sol@L183-L183
CONTRACT_ID: stepI:p5:hd-sol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I-HEAD data; B' nonempty; f, epsilon satisfy I-HEAD with 0 <= epsilon < epsilon_0 chosen at L181; z_0.2 in B'
SOURCE_QUANTIFIERS: After epsilon_0, for every admissible f, epsilon and z_0, there exists z:R->R^2 x R^2; then for all t in R
SOURCE_CONCLUSION: z : R -> R^2 x R^2 with z(0) = z_0, IsSolIn X_R W_B R z, i.e. IsHamiltonianSolutionOn H_R B univ z (Sol(Ham_{h,f},B,R,z)) and |z(t)_2 - I_0| < eta for all t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:confinement, bpI:p5:real-ham, stepI:p5:hd-fix, bpI:p0:hamsol#IsHamiltonianSolutionOn, N:bpN:p3:gen-maximal, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:confinement | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-sol@L183-L183 | defined on R and confined
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-sol@L183-L183 | (c): predicate equivalence
EDGE: stepI:p5:hd-fix | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-sol@L183-L183 | z_0, E, epsilon fixed
EDGE: bpI:p0:hamsol#IsHamiltonianSolutionOn | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-sol@L183-L183 | Sol
EDGE: N:bpN:p3:gen-maximal | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-sol@L183-L183 | maximal solution
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-sol@L183-L183 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: confinement_main, all_time_confinement (KAM/Provider/Iso/AllTimeConfinement.lean)
LEAN_NOTE: audit I-HEAD PASS (row names this step -> confinement_main); step of PROVED parent bpI:p0:head (ruling b)
NOTE: -

NODE: stepI:p5:hd-uniq
KIND: step
TITLE: Uniqueness among all solutions
STATEMENT_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-uniq@L184-L184
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-uniq@L184-L184
CONTRACT_ID: stepI:p5:hd-uniq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I-HEAD data; f, epsilon, z_0 fixed as at L182; z is the global solution constructed at L183; a<0<b, y(0)=z_0, Sol(Ham_{h,f},B,(a,b),y)
SOURCE_QUANTIFIERS: for all a<0<b and y
SOURCE_CONCLUSION: y = z on (a,b); no smallness or confinement of y is assumed
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p5:real-ham, N:bpN:p3:gen-uniqueness, stepI:p5:hd-sol, bpI:p0:hamsol#IsHamiltonianSolutionOn, bpI:p3:setting, N:bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p5:real-ham | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-uniq@L184-L184 | (c): Sol is IsSolIn X_R W_B (a,b)
EDGE: N:bpN:p3:gen-uniqueness | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-uniq@L184-L184 | uniqueness on (a,b)
EDGE: stepI:p5:hd-sol | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-uniq@L184-L184 | the solution z compared with y
EDGE: bpI:p0:hamsol#IsHamiltonianSolutionOn | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-uniq@L184-L184 | Sol
EDGE: bpI:p3:setting | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-uniq@L184-L184 | local I-HEAD data h, f, epsilon and action domains, standing by L29-31
EDGE: N:bpN:p3:gen-sol | blueprint-I/parts/p5-confinement.tex#stepI:p5:hd-uniq@L184-L184 | restrict the global z to (a,b) for uniqueness
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p5+sol-review-I-p5p8
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: confinement_main, all_time_confinement (KAM/Provider/Iso/AllTimeConfinement.lean)
LEAN_NOTE: audit I-HEAD PASS (row names this step -> confinement_main); step of PROVED parent bpI:p0:head (ruling b)
NOTE: -
