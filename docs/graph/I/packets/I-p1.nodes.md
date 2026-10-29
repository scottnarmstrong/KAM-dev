NODE: bpI:p1:setting
KIND: definition
TITLE: Standing setting of Part~\ref{bpI:p1}
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting@L30-L46
PROOF_SOURCE: -
CONTRACT_ID: bpI:p1:setting
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data and standing hypotheses of Part 1)
SOURCE_QUANTIFIERS: n, tau, M, D, H, gamma, omega, r, K fixed by the setting (outermost)
SOURCE_CONCLUSION: defines the standing setting of Part 1: n>=2, tau>=0, M>0; D open and Z^n-invariant; H holomorphic on D, 1-periodic in theta, real at real phase points, with bounds M on DH, X_H, DX_H, D^2 X_H (I1-I4); gamma>0, omega in R^n cap Dio_{gamma,tau}; r>0, K holomorphic, primary and real on reals on T_r with K(T_r) subset D (I5, I6); det G_K != 0 on T_r where the frame is used; also fixes Gamma_delta := c_R gamma^{-1} delta^{-kappa}, kappa = tau+n, as in K
CONSTANT_SCOPE: all constants (M, gamma, r, tau, n) are fixed by the setting; Gamma_delta uses c_R, kappa of K:bp:p2:constants (c_R depends on n, tau only)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:diophantine#IsDiophantine, bpI:p0:domains#complexStrip, bpI:p0:stripdata#IsPrimaryOnStrip, bpI:p0:stripdata#IsRealOnReals, bpI:p0:hamiltonian#hamiltonianVectorFieldC, bpI:p0:stripdata#gramMatrix, K:bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting@L35-L35 | omega in Dio_{gamma,tau}
EDGE: bpI:p0:domains#complexStrip | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting@L35-L35 | strip T_r
EDGE: bpI:p0:stripdata#IsPrimaryOnStrip | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting@L35-L35 | K primary on T_r
EDGE: bpI:p0:stripdata#IsRealOnReals | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting@L35-L35 | K real on reals
EDGE: bpI:p0:hamiltonian#hamiltonianVectorFieldC | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting@L34-L34 | bounds on X_H, DX_H, D^2 X_H
EDGE: bpI:p0:stripdata#gramMatrix | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting@L36-L36 | det G_K != 0 where the frame is used
EDGE: K:bp:p2:constants | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting@L45-L45 | Gamma_delta, kappa, c_R as in K constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.SettingSrc (KAM/Iso/Linear/SettingSrc.lean)
LEAN_NOTE: GAP-I1a (audit 1 PASS; N1 ruling (i), tau>=n-1 via KAM.IsDiophantine.n_sub_one_le_tau)
NOTE: -

NODE: bpI:p1:setting#k-bridge
KIND: step
TITLE: Bridge: common K standing data and frozen objects with h := H, B(frak) := D
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting#k-bridge@L39-L46
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting#k-bridge@L39-L46
CONTRACT_ID: bpI:p1:setting#k-bridge
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p1:setting; det G_K != 0 wherever frame objects are used
SOURCE_QUANTIFIERS: as in the setting; K data h := H, B(frak) := D
SOURCE_CONCLUSION: identifies the common K standing data with h := H and B(frak) := D, with the additional bound on DH; uses the explicitly stated range tau >= 0, n >= 1 of K Part 2; identifies L,G,B,N,P,X_N,T,E,A,Omega_K,E_sym,Q,eta and averages with K objects and the frozen definitions; additional bounds required by particular K lemmas are supplied locally, not asserted by this bridge
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, K:bp:p2:standing, K:bp:p2:objects, K:bp:p2:frozen-agreement, bpI:p0:stripdata#gramMatrix, bpI:p0:stripdata#normalFrame, bpI:p0:stripdata#torsion, bpI:p0:stripdata#invarianceError
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting#k-bridge@L39-L39 | the package of Part 1
EDGE: K:bp:p2:standing | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting#k-bridge@L39-L39 | K standing data with h := H, B(frak) := D
EDGE: K:bp:p2:objects | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting#k-bridge@L41-L41 | objects with h := H
EDGE: K:bp:p2:frozen-agreement | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting#k-bridge@L42-L42 | agreement with the frozen definitions
EDGE: bpI:p0:stripdata#gramMatrix | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting#k-bridge@L43-L43 | frozen gramMatrix
EDGE: bpI:p0:stripdata#normalFrame | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting#k-bridge@L43-L43 | frozen normalFrame
EDGE: bpI:p0:stripdata#torsion | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting#k-bridge@L43-L43 | frozen torsion
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:setting#k-bridge@L43-L43 | frozen invarianceError
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.SettingSrc.k_bridge (KAM/Iso/Linear/SettingSrc.lean)
LEAN_NOTE: GAP-I1a (audit 1 PASS; N1 ruling (i), tau>=n-1 via KAM.IsDiophantine.n_sub_one_le_tau)
NOTE: K:bp:p2:standing prose at blueprint/parts/p2-aposteriori.tex L67-L69 explicitly states that only tau >= 0 and n >= 1 are used below. The positive sigma parameters are free constants, not admissibility bounds in the standing package; each bound used by a consumer is supplied locally. No SOURCE_GAP is established by the different parameter lists. This bridge identifies common data, not the stronger tau >= n-1 proposition literally.

NODE: bpI:p1:ray
KIND: claim
TITLE: Rays: $s\omega^*$ is Diophantine with the constant of $\omega^*$
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:ray@L48-L53
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:ray@L48-L53
CONTRACT_ID: bpI:p1:ray
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega* in R^n with omega* in Dio_{gamma,tau}; s > 1 (the I-G1 data; no Part 1 setting)
SOURCE_QUANTIFIERS: omega*, gamma, tau, s; k in Z^n minus {0}
SOURCE_CONCLUSION: s omega* in Dio_{gamma,tau} with the same gamma: ¦k.s omega*¦ = s¦k.omega*¦ >= gamma/(sum ¦k_i¦)^tau
CONSTANT_SCOPE: gamma, tau as in the hypothesis omega* in Dio_{gamma,tau}; no new constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:diophantine#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:ray@L49-L49 | omega* in Dio_{gamma,tau} and the conclusion s omega* in Dio_{gamma,tau}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.isDiophantine_smul (KAM/Iso/Linear/Tools.lean)
LEAN_NOTE: audit I1-1 PASS WITH NOTES (also I1-5); holds for s>=1, stronger than s>1
NOTE: -

NODE: bpI:p1:ext-chain
KIND: external
TITLE: Chain and product rules
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:ext-chain@L94-L95
PROOF_SOURCE: -
CONTRACT_ID: bpI:p1:ext-chain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (external)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Chain and product rules for Frechet derivatives of holomorphic maps, and linearity of the derivative (Mathlib HasFDerivAt.comp, fderiv_add, fderiv_const)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p1:ext-real-direction
KIND: external
TITLE: Complex derivative in a real direction
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:ext-real-direction@L96-L100
PROOF_SOURCE: -
CONTRACT_ID: bpI:p1:ext-real-direction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (external)
SOURCE_QUANTIFIERS: phi, U, x, v
SOURCE_CONCLUSION: If phi is holomorphic on an open U subset C^n, x in U cap R^n and v in R^n, then phi restricted to U cap R^n has the real directional derivative D phi(x) v at x; if moreover phi is real on U cap R^n then D phi(x) v is in R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: EXTERNAL kept (not an alias): K:step:p1:hr-derivative (of K:bp:p1:hamiltonian-real) states the real clause only (h real at real points, H agrees with Re h near z, DH(z)e = Dh(z)e real), while this item also asserts the directional derivative of a complex-valued phi on U cap R^n

NODE: bpI:p1:ext-neumann
KIND: external
TITLE: Neumann criterion of radius one
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:ext-neumann@L101-L105
PROOF_SOURCE: -
CONTRACT_ID: bpI:p1:ext-neumann
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (external)
SOURCE_QUANTIFIERS: X, m
SOURCE_CONCLUSION: If X in C^{m x m} and the operator norm of X (induced by the max norm of C^m) is < 1, then I - X is invertible; only invertibility is claimed, no bound on the inverse
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-I-p1
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p1:extended-basic
KIND: lemma
TITLE: Regularity, periodicity, realness and size of the extended torsion
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:extended-basic@L111-L127
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:extended-basic@L129-L167
CONTRACT_ID: bpI:p1:extended-basic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p1:setting (n>=2, tau>=0, M>0; D open, Z^n-invariant in theta; H holomorphic on D, 1-periodic in theta, real at real phase points of D, ¦DH¦,¦X_H¦,¦DX_H¦,¦D^2 X_H¦ <= M on D; gamma>0, omega in R^n cap Dio_{gamma,tau}; r>0, K holomorphic, primary, real on reals on T_r with K(T_r) subset D); det G_K != 0 on T_r; Y := DH(K)N on T_r; for (b): ¦DK¦ <= sigma_K' and ¦B¦ <= sigma_B' on T_r; ¦T¦ <= C_T on the set considered
SOURCE_QUANTIFIERS: setting data (outermost); sigma_K', sigma_B', C_T; then claims (a), (b)
SOURCE_CONCLUSION: (a) Y and the entries of T_H (built from (H,K,omega)) are holomorphic, 1-periodic on T_r and real at real theta; T_H is continuous on R^n; avg(T_H) is defined, real, equal to [[avg T, omega],[avg Y, 0]] with avg T the torsion average of K:bp:p2:objects; (b) ¦Y¦ <= M sigma_K' sigma_B' on T_r and, on any set where ¦T¦ <= C_T, ¦T_H¦ <= max{C_T + ¦omega¦, M sigma_K' sigma_B'} (row-sum norm of C^{(n+1)x(n+1)})
CONSTANT_SCOPE: sigma_K', sigma_B', C_T are free bounds (not constants chosen from the data); M from the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p1:setting#k-bridge, K:bp:p2:objects, bpI:p0:extended#extendedTorsion, bpI:p0:extended#extendedTorsionAverage, stepI:p1:eb-holo, stepI:p1:eb-period, stepI:p1:eb-average, stepI:p1:eb-bounds
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:extended-basic@L112-L112 | Assume the setting
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:extended-basic@L120-L120 | K objects (N, T, avg T) with h := H and K standing results applied
EDGE: K:bp:p2:objects | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:extended-basic@L120-L120 | torsion average of K objects
EDGE: bpI:p0:extended#extendedTorsion | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:extended-basic@L125-L125 | T_H
EDGE: bpI:p0:extended#extendedTorsionAverage | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:extended-basic@L116-L116 | avg(T_H)
EDGE: stepI:p1:eb-holo | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:extended-basic@L130-L130 | proof step: holomorphy
EDGE: stepI:p1:eb-period | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:extended-basic@L148-L148 | proof step: periodicity and realness
EDGE: stepI:p1:eb-average | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:extended-basic@L155-L155 | proof step: the average
EDGE: stepI:p1:eb-bounds | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:extended-basic@L162-L162 | proof step: bounds
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.extended_basic_src (KAM/Iso/Linear/FullRange.lean)
LEAN_NOTE: GAP-I1a (audit 1 PASS; N1 ruling (i), tau>=n-1 via KAM.IsDiophantine.n_sub_one_le_tau)
NOTE: -

NODE: stepI:p1:eb-holo
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo@L130-L146
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo@L130-L146
CONTRACT_ID: stepI:p1:eb-holo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0 on T_r
SOURCE_QUANTIFIERS: K, H
SOURCE_CONCLUSION: N, T, Y and every entry of T_H are holomorphic on T_r, in particular continuous on R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, stepI:p1:eb-holo-frame, stepI:p1:eb-holo-inverse, stepI:p1:eb-holo-field, stepI:p1:eb-holo-torsion, stepI:p1:eb-holo-conclude
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo@L131-L131 | uses only holomorphy of K on the open strip, K(T_r) subset D open, det G_K != 0; no ball margin, no bounds, no torsion
EDGE: stepI:p1:eb-holo-frame | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo@L133-L134 | substep: frame and Gram matrix
EDGE: stepI:p1:eb-holo-inverse | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo@L136-L137 | substep: inverse B, N, P
EDGE: stepI:p1:eb-holo-field | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo@L139-L140 | substep: field along K
EDGE: stepI:p1:eb-holo-torsion | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo@L142-L143 | substep: derivative along omega and torsion
EDGE: stepI:p1:eb-holo-conclude | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo@L145-L146 | substep: conclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-global-I+sonnet-amend-I-p1
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_eb_holo (KAM/Iso/Linear/FullRangeStepsExt.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: K:step:p2:fb-holo is only compared with (stated under K (A2)-(A4)), not used; the former SOURCE_GAP is closed by the direct substeps.

NODE: stepI:p1:eb-holo-frame
KIND: step
TITLE: Frame and Gram matrix
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-frame@L133-L134
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-frame@L133-L134
CONTRACT_ID: stepI:p1:eb-holo-frame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; K holomorphic on T_r with K(T_r) subset D open; det G_K != 0 on T_r
SOURCE_QUANTIFIERS: K, H on T_r
SOURCE_CONCLUSION: L = DK and the entries of G = L^T L are holomorphic on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, K:bp:p1:holomorphic-regularity, bpI:p1:ext-chain
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-frame@L134-L134 | K holomorphic on T_r
EDGE: K:bp:p1:holomorphic-regularity | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-frame@L134-L134 | DK holomorphic on T_r
EDGE: bpI:p1:ext-chain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-frame@L134-L134 | entries of G are finite sums of products of holomorphic entries of L
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-I-p1+sol-delta-I-amend
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: KAM.Torus.differentiableOn_tangentMat, KAM.Torus.differentiableOn_gramMatrix (KAM/Torus/FrozenAgreement.lean)
LEAN_NOTE: Setting-free (premise hK only; precedent rd-ql). Same LEAN_REF as PROVED K node step:p3:red-holomorphy.
NOTE: -

NODE: stepI:p1:eb-holo-inverse
KIND: step
TITLE: The inverse
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-inverse@L136-L137
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-inverse@L136-L137
CONTRACT_ID: stepI:p1:eb-holo-inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; K holomorphic on T_r with K(T_r) subset D open; det G_K != 0 on T_r
SOURCE_QUANTIFIERS: K, H on T_r
SOURCE_CONCLUSION: B = G^{-1}, N = Omega_0 L B and P = (L N) are holomorphic on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, stepI:p1:eb-holo-frame, K:bp:p1:holomorphic-inverse, bpI:p1:ext-chain
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-inverse@L137-L137 | det G_K != 0 on T_r
EDGE: stepI:p1:eb-holo-frame | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-inverse@L137-L137 | G holomorphic matrix function
EDGE: K:bp:p1:holomorphic-inverse | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-inverse@L137-L137 | G holomorphic with det != 0 on open T_r gives G^{-1} holomorphic
EDGE: bpI:p1:ext-chain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-inverse@L137-L137 | products of holomorphic matrices with constant Omega_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-I-p1+sol-delta-I-amend
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_eb_holo_inverse (KAM/Iso/Linear/FullRangeStepsExt.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:eb-holo-field
KIND: step
TITLE: Field along K
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-field@L139-L140
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-field@L139-L140
CONTRACT_ID: stepI:p1:eb-holo-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; K holomorphic on T_r with K(T_r) subset D open; det G_K != 0 on T_r; H holomorphic on D
SOURCE_QUANTIFIERS: K, H on T_r
SOURCE_CONCLUSION: A = DX_H o K and DH o K are holomorphic on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p1:setting#k-bridge, K:bp:p2:hamiltonian, K:bp:p1:holomorphic-regularity, bpI:p1:ext-chain
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-field@L140-L140 | K(T_r) subset D, K holomorphic, H holomorphic on D
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-field@L140-L140 | supplies the K standing data of the hamiltonian item
EDGE: K:bp:p2:hamiltonian | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-field@L140-L140 | item (a): X_H and DX_H holomorphic on D
EDGE: K:bp:p1:holomorphic-regularity | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-field@L140-L140 | DH and DX_H holomorphic on D
EDGE: bpI:p1:ext-chain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-field@L140-L140 | chain rule for A = DX_H o K and DH o K
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-I-p1
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_eb_holo_field (KAM/Iso/Linear/FullRangeStepsExt.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:eb-holo-torsion
KIND: step
TITLE: Derivative along omega, torsion
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-torsion@L142-L143
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-torsion@L142-L143
CONTRACT_ID: stepI:p1:eb-holo-torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; K holomorphic on T_r with K(T_r) subset D open; det G_K != 0 on T_r
SOURCE_QUANTIFIERS: K, H on T_r
SOURCE_CONCLUSION: X_N, T, E_sym, Q, eta, Y = DH(K) N are holomorphic on T_r; entries of T_H are T, the constant block omega, entries of Y and 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, stepI:p1:eb-holo-inverse, stepI:p1:eb-holo-field, K:bp:p1:holomorphic-regularity, bpI:p1:ext-chain, bpI:p0:extended#extendedTorsion
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-torsion@L142-L143 | frequency vector omega is constant
EDGE: stepI:p1:eb-holo-inverse | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-torsion@L142-L143 | N holomorphic
EDGE: stepI:p1:eb-holo-field | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-torsion@L142-L143 | A and DH o K holomorphic
EDGE: K:bp:p1:holomorphic-regularity | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-torsion@L142-L142 | DN holomorphic, regularity applied to N
EDGE: bpI:p1:ext-chain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-torsion@L142-L143 | products and sums of holomorphic functions
EDGE: bpI:p0:extended#extendedTorsion | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-torsion@L143-L143 | the stated entries of T_H are the blocks of the frozen extended-torsion definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-I-p1+sol-delta-I-amend
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_eb_holo_torsion (KAM/Iso/Linear/FullRangeStepsExt.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:eb-holo-conclude
KIND: step
TITLE: Conclusion of the step
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-conclude@L145-L146
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-conclude@L145-L146
CONTRACT_ID: stepI:p1:eb-holo-conclude
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; K holomorphic on T_r with K(T_r) subset D open; det G_K != 0 on T_r
SOURCE_QUANTIFIERS: K, H on T_r
SOURCE_CONCLUSION: N, T, Y and every entry of T_H are holomorphic on T_r, hence continuous on R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:eb-holo-frame, stepI:p1:eb-holo-inverse, stepI:p1:eb-holo-torsion, bpI:p0:extended#extendedTorsion, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:eb-holo-frame | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-conclude@L146-L146 | frame holomorphic
EDGE: stepI:p1:eb-holo-inverse | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-conclude@L146-L146 | N holomorphic
EDGE: stepI:p1:eb-holo-torsion | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-conclude@L146-L146 | T, Y holomorphic
EDGE: bpI:p0:extended#extendedTorsion | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-conclude@L146-L146 | entries of the frozen T_H
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-holo-conclude@L146-L146 | local H,K,omega,r and the real slice R^n subset T_r used in the conclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-I-p1+sol-delta-I-amend
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_eb_holo_conclude (KAM/Iso/Linear/FullRangeStepsExt.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:eb-period
KIND: step
TITLE: Periodicity and realness
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-period@L148-L153
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-period@L148-L153
CONTRACT_ID: stepI:p1:eb-period
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0 on T_r; K real on reals
SOURCE_QUANTIFIERS: K, H
SOURCE_CONCLUSION: Y is 1-periodic on T_r and real at real theta (N, T periodic and real; DH real at real phase points)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, K:bp:p2:periodicity, K:step:p2:ham-real, bpI:p1:setting#k-bridge
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-period@L149-L149 | H periodic in theta, K primary, H real at real points (I2, I3)
EDGE: K:bp:p2:periodicity | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-period@L150-L150 | N, T periodic and real
EDGE: K:step:p2:ham-real | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-period@L152-L152 | DH real at real points of D
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-period@L150-L150 | supplies the K standing data of periodicity and ham-real
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_eb_period (KAM/Iso/Linear/FullRangeStepsExt.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS; accepted deviation: carries parent standing hyps (K primary, real on reals, K(T_r) in D)
NOTE: -

NODE: stepI:p1:eb-average
KIND: step
TITLE: The average
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-average@L155-L160
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-average@L155-L160
CONTRACT_ID: stepI:p1:eb-average
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0 on T_r
SOURCE_QUANTIFIERS: K, H
SOURCE_CONCLUSION: each entry of T_H is integrable on [0,1]^n; the frozen avg(T_H) is the entrywise integral, real; the border entries are omega and 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:eb-holo, stepI:p1:eb-period, K:bp:p1:ext-integral, bpI:p0:extended#extendedTorsionAverage, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:eb-holo | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-average@L156-L156 | continuity of the entries
EDGE: stepI:p1:eb-period | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-average@L159-L159 | realness of the integrand
EDGE: K:bp:p1:ext-integral | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-average@L157-L157 | continuous functions on a compact box are integrable
EDGE: bpI:p0:extended#extendedTorsionAverage | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-average@L158-L158 | Bochner integral of the frozen average
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-average@L156-L156 | direct use of the local H, K, omega, domain or standing constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_eb_average (KAM/Iso/Linear/FullRangeStepsExt.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS; accepted deviation: carries parent standing hyps (K primary, real on reals, K(T_r) in D)
NOTE: -

NODE: stepI:p1:eb-bounds
KIND: step
TITLE: Bounds
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-bounds@L162-L166
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-bounds@L162-L166
CONTRACT_ID: stepI:p1:eb-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; ¦DK¦ <= sigma_K', ¦B¦ <= sigma_B' on T_r; ¦T¦ <= C_T
SOURCE_QUANTIFIERS: K, H
SOURCE_CONCLUSION: ¦Y¦ <= ¦DH(K)¦¦N¦ <= M sigma_K' sigma_B'; ¦T_H¦ <= max{C_T + ¦omega¦, ¦Y¦} in the row-sum norm
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, K:bp:p2:matrix, K:bp:p2:objects, bpI:p1:setting#k-bridge
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-bounds@L163-L163 | ¦DH¦ <= M (I4)
EDGE: K:bp:p2:matrix | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-bounds@L163-L163 | ¦MN¦ <= ¦M¦¦N¦, ¦Omega_0 M¦ = ¦M¦, block bounds
EDGE: K:bp:p2:objects | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-bounds@L163-L163 | N = Omega_0 L B
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:eb-bounds@L163-L163 | K objects with h := H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_eb_bounds (KAM/Iso/Linear/FullRangeStepsExt.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS; accepted deviation: |DH(K)| read as row-sum norm
NOTE: -

NODE: bpI:p1:trivial
KIND: lemma
TITLE: $\mathsf T_H=\mathsf B_h$ at the trivial torus
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L169-L183
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L185-L219
CONTRACT_ID: bpI:p1:trivial
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^n open; h holomorphic on U with h(J) in R for every real J in U; D = C^n x U; H(theta,J) := h(J) on D; I in U cap R^n; K(theta) = (theta,I); omega := grad h(I) in R^n (frequencyMap); no Part 1 setting
SOURCE_QUANTIFIERS: U, h, then D, H, I, K, omega; then theta in C^n
SOURCE_CONCLUSION: K is holomorphic, primary and real on reals, K(C^n) subset D, G_K = I_n, E_{H,K,omega} = 0, and for every theta T_H(theta) = B_h(I) (real matrix viewed in C^{(n+1)x(n+1)}), avg(T_H) = B_h(I); det avg(T_H) != 0 iff det B_h(I) != 0, the (total) inverses correspond under the cast and ¦avg(T_H)^{-1}¦ = ¦B_h(I)^{-1}¦ in both cases
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:extended#extendedTorsion, bpI:p0:extended#extendedTorsionAverage, bpI:p0:bordered#borderedHessian, bpI:p0:realham#frequencyMap, bpI:p0:stripdata#IsPrimaryOnStrip, bpI:p0:stripdata#IsRealOnReals, bpI:p0:stripdata#gramMatrix, bpI:p0:stripdata#invarianceError, stepI:p1:tr-torus, stepI:p1:tr-frame, stepI:p1:tr-field, stepI:p1:tr-torsion, stepI:p1:tr-border, stepI:p1:tr-compare
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:extended#extendedTorsion | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L175-L175 | T_H
EDGE: bpI:p0:extended#extendedTorsionAverage | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L176-L176 | avg(T_H)
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L176-L176 | B_h(I)
EDGE: bpI:p0:realham#frequencyMap | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L172-L172 | omega := grad h(I)
EDGE: bpI:p0:stripdata#IsPrimaryOnStrip | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L172-L172 | K primary
EDGE: bpI:p0:stripdata#IsRealOnReals | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L172-L172 | K real on reals
EDGE: bpI:p0:stripdata#gramMatrix | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L173-L173 | G_K = I_n
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L173-L173 | E_{H,K,omega} = 0
EDGE: stepI:p1:tr-torus | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L186-L186 | proof step
EDGE: stepI:p1:tr-frame | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L191-L191 | proof step
EDGE: stepI:p1:tr-field | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L195-L195 | proof step
EDGE: stepI:p1:tr-torsion | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L203-L203 | proof step
EDGE: stepI:p1:tr-border | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L207-L207 | proof step
EDGE: stepI:p1:tr-compare | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:trivial@L211-L211 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.trivial_torus (KAM/Iso/Linear/Trivial.lean)
LEAN_NOTE: audit I1-4 PASS WITH NOTES; exact design type, no Setting/N1 dependence, all conclusions proved
NOTE: -

NODE: stepI:p1:tr-torus
KIND: step
TITLE: The torus
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torus@L186-L189
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torus@L186-L189
CONTRACT_ID: stepI:p1:tr-torus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of trivial (K(theta) = (theta,I))
SOURCE_QUANTIFIERS: theta, k
SOURCE_CONCLUSION: K(theta+k) = K(theta) + (k,0), K affine hence holomorphic, real on reals; DK e_i = (e_i,0); G_K = I_n, det G_K = 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:stripdata#IsPrimaryOnStrip, bpI:p0:stripdata#IsRealOnReals, bpI:p0:stripdata#dotC, bpI:p0:stripdata#gramMatrix
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:stripdata#IsPrimaryOnStrip | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torus@L187-L187 | K primary
EDGE: bpI:p0:stripdata#IsRealOnReals | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torus@L187-L187 | K real on reals
EDGE: bpI:p0:stripdata#dotC | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torus@L188-L188 | bilinear dot gives G_K = (e_i.e_j) = I_n
EDGE: bpI:p0:stripdata#gramMatrix | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torus@L188-L188 | Gram matrix of K
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.trivial_torus (KAM/Iso/Linear/Trivial.lean)
LEAN_NOTE: audit I1-4 PASS WITH NOTES; included in trivial_torus
NOTE: -

NODE: stepI:p1:tr-frame
KIND: step
TITLE: The normal frame
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-frame@L191-L193
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-frame@L191-L193
CONTRACT_ID: stepI:p1:tr-frame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of bpI:p1:trivial (U, h, D, H, I, K and omega defined there); no Part 1 setting assumed
SOURCE_QUANTIFIERS: j
SOURCE_CONCLUSION: N_{.j} = Omega_0(e_j,0) = (0,e_j), constant in theta, so D_theta N_{.j} = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:tr-torus, bpI:p0:stripdata#normalFrame, bpI:p0:stripdata#omegaZero
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:tr-torus | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-frame@L192-L192 | G_K = I_n, B = I_n, DK e_k = (e_k,0)
EDGE: bpI:p0:stripdata#normalFrame | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-frame@L192-L192 | N_{.j} = sum_k (G^{-1})_{kj} Omega_0(DK e_k)
EDGE: bpI:p0:stripdata#omegaZero | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-frame@L192-L192 | Omega_0(e_j,0) = (0,e_j)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.trivial_torus (KAM/Iso/Linear/Trivial.lean)
LEAN_NOTE: audit I1-4 PASS WITH NOTES; included in trivial_torus
NOTE: -

NODE: stepI:p1:tr-field
KIND: step
TITLE: The vector field
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-field@L195-L201
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-field@L195-L201
CONTRACT_ID: stepI:p1:tr-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of bpI:p1:trivial (U, h, D, H, I, K and omega defined there); no Part 1 setting assumed
SOURCE_QUANTIFIERS: a
SOURCE_CONCLUSION: X_H(theta,J) = ((d_a h(J))_a, 0); E_{H,K,omega} = (grad^C h(I) - omega, 0) = 0; d_a h(J) real for real J; omega_a = d_a h(I); grad h(J)_a = d_a h(J) for real J in U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:hamiltonian#hamiltonianVectorFieldC, bpI:p0:stripdata#invarianceError, stepI:p1:tr-torus, bpI:p1:ext-real-direction, bpI:p0:realham#frequencyMap
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:hamiltonian#hamiltonianVectorFieldC | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-field@L196-L196 | X_H of H(theta,J) = h(J)
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-field@L196-L196 | E = X_H(K theta) - DK omega
EDGE: stepI:p1:tr-torus | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-field@L196-L196 | DK omega = (omega,0)
EDGE: bpI:p1:ext-real-direction | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-field@L197-L197 | complex derivative in a real direction for phi = h
EDGE: bpI:p0:realham#frequencyMap | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-field@L200-L200 | definition of the frequency map
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.trivial_torus (KAM/Iso/Linear/Trivial.lean)
LEAN_NOTE: audit I1-4 PASS WITH NOTES; included in trivial_torus; private invarianceError_trivial
NOTE: -

NODE: stepI:p1:tr-torsion
KIND: step
TITLE: The torsion
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torsion@L203-L205
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torsion@L203-L205
CONTRACT_ID: stepI:p1:tr-torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of bpI:p1:trivial (U, h, D, H, I, K and omega defined there); no Part 1 setting assumed
SOURCE_QUANTIFIERS: i, j
SOURCE_CONCLUSION: T(theta)_ij = d_j d_i h(I)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:stripdata#torsion, stepI:p1:tr-frame, stepI:p1:tr-field, bpI:p0:hamiltonian#hamiltonianVectorFieldC, bpI:p0:stripdata#omegaZero, bpI:p0:stripdata#dotC
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:stripdata#torsion | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torsion@L205-L205 | torsion formula
EDGE: stepI:p1:tr-frame | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torsion@L204-L204 | N_{.j} = (0,e_j) constant, D_theta N = 0
EDGE: stepI:p1:tr-field | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torsion@L204-L204 | X_H = ((d_a h),0)
EDGE: bpI:p0:hamiltonian#hamiltonianVectorFieldC | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torsion@L204-L204 | DX_H(theta,I)(0,e_j)
EDGE: bpI:p0:stripdata#omegaZero | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torsion@L204-L204 | Omega_0(w,0) = (0,w)
EDGE: bpI:p0:stripdata#dotC | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-torsion@L205-L205 | N_{.i} . Omega_0(...)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.trivial_torus (KAM/Iso/Linear/Trivial.lean)
LEAN_NOTE: audit I1-4 PASS WITH NOTES; included in trivial_torus; private torsion_trivial
NOTE: -

NODE: stepI:p1:tr-border
KIND: step
TITLE: The border
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-border@L207-L209
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-border@L207-L209
CONTRACT_ID: stepI:p1:tr-border
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of bpI:p1:trivial (U, h, D, H, I, K and omega defined there); no Part 1 setting assumed
SOURCE_QUANTIFIERS: b
SOURCE_CONCLUSION: last column of T_H is omega = grad h(I), last row is DH(K theta) N_{.b} = d_b h(I) = omega_b, corner 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:extended#extendedTorsion, stepI:p1:tr-field, stepI:p1:tr-frame
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:extended#extendedTorsion | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-border@L208-L208 | border of the frozen T_H
EDGE: stepI:p1:tr-field | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-border@L208-L208 | omega_a = d_a h(I)
EDGE: stepI:p1:tr-frame | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-border@L209-L209 | N_{.b} = (0,e_b)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.trivial_torus (KAM/Iso/Linear/Trivial.lean)
LEAN_NOTE: audit I1-4 PASS WITH NOTES; included in trivial_torus; private extendedTorsion_trivial
NOTE: -

NODE: stepI:p1:tr-compare
KIND: step
TITLE: Comparison with the bordered Hessian
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-compare@L211-L218
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-compare@L211-L218
CONTRACT_ID: stepI:p1:tr-compare
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of bpI:p1:trivial (U, h, D, H, I, K and omega defined there); no Part 1 setting assumed
SOURCE_QUANTIFIERS: a, b
SOURCE_CONCLUSION: T_H(theta) = B_h(I) for all theta; avg(T_H) = B_h(I); det and inverse statements by cases (det B_h(I) != 0: same determinant and corresponding inverses; det = 0: both total inverses are 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:bordered#borderedHessian, stepI:p1:tr-field, bpI:p1:ext-real-direction, K:bp:p1:holomorphic-regularity, stepI:p1:tr-torsion, stepI:p1:tr-border, bpI:p0:extended#extendedTorsionAverage, K:bp:p1:real-inverse
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-compare@L212-L212 | entries of the frozen B_h(I)
EDGE: stepI:p1:tr-field | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-compare@L213-L213 | grad h(J)_a = d_a h(J)
EDGE: bpI:p1:ext-real-direction | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-compare@L214-L214 | real derivative equals complex partial
EDGE: K:bp:p1:holomorphic-regularity | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-compare@L215-L215 | symmetry of the Hessian of a holomorphic function
EDGE: stepI:p1:tr-torsion | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-compare@L215-L215 | upper-left blocks T = d_j d_i h
EDGE: stepI:p1:tr-border | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-compare@L215-L215 | border agrees with grad h(I)
EDGE: bpI:p0:extended#extendedTorsionAverage | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-compare@L216-L216 | average of a constant matrix
EDGE: K:bp:p1:real-inverse | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:tr-compare@L217-L217 | real matrix and its cast have corresponding inverses
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.trivial_torus (KAM/Iso/Linear/Trivial.lean)
LEAN_NOTE: audit I1-4 PASS WITH NOTES; included in trivial_torus; private extendedTorsion_trivial
NOTE: -

NODE: bpI:p1:last-row
KIND: lemma
TITLE: The energy row of the extended torsion
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:last-row@L228-L247
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:last-row@L249-L270
CONTRACT_ID: bpI:p1:last-row
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p1:setting (n>=2, tau>=0, M>0; D open, Z^n-invariant in theta; H holomorphic on D, 1-periodic in theta, real at real phase points of D, ¦DH¦,¦X_H¦,¦DX_H¦,¦D^2 X_H¦ <= M on D; gamma>0, omega in R^n cap Dio_{gamma,tau}; r>0, K holomorphic, primary, real on reals on T_r with K(T_r) subset D); det G_K != 0 on T_r; E := E_{H,K,omega}, eta^L := -N^T Omega_0 E as in K:bp:p2:objects; for (c): ¦E¦ <= e, ¦L¦ <= sigma_K', ¦B¦ <= sigma_B' on T_r
SOURCE_QUANTIFIERS: setting data (outermost); e, sigma_K', sigma_B'; then claims (a)-(c) on T_r
SOURCE_CONCLUSION: (a) Y = DH(K)N = omega^T - (eta^L)^T, so ¦Y - omega^T¦ = sum_b ¦eta^L_b¦ <= n¦eta^L¦ and Y_b = omega_b + N_{.b}^T Omega_0 E; (b) if E = 0 on T_r then Y = omega^T and T_H = [[T, omega],[omega^T, 0]], avg(T_H) = [[avg T, omega],[omega^T, 0]]; (c) in general avg(T_H) = T^inv - [[0,0],[avg(eta^L)^T,0]] with T^inv := [[avg T, omega],[omega^T, 0]], and if ¦E¦ <= e, ¦L¦ <= sigma_K', ¦B¦ <= sigma_B' then ¦avg(T_H) - T^inv¦ <= 2 n^2 sigma_K' sigma_B' e
CONSTANT_SCOPE: e, sigma_K', sigma_B' free bounds; n, M from the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p1:setting#k-bridge, K:bp:p2:objects, bpI:p0:stripdata#invarianceError, bpI:p0:extended#extendedTorsion, bpI:p0:extended#extendedTorsionAverage, stepI:p1:lr-gradient, stepI:p1:lr-insert, stepI:p1:lr-average
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:last-row@L229-L229 | Assume the setting
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:last-row@L229-L229 | K objects with h := H, K results applied
EDGE: K:bp:p2:objects | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:last-row@L229-L229 | E, eta^L, N as in K objects
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:last-row@L229-L229 | E = E_{H,K,omega}
EDGE: bpI:p0:extended#extendedTorsion | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:last-row@L244-L244 | T_H and its last row
EDGE: bpI:p0:extended#extendedTorsionAverage | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:last-row@L237-L237 | avg(T_H)
EDGE: stepI:p1:lr-gradient | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:last-row@L250-L250 | proof step
EDGE: stepI:p1:lr-insert | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:last-row@L254-L254 | proof step
EDGE: stepI:p1:lr-average | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:last-row@L263-L263 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.last_row_src (KAM/Iso/Linear/FullRange.lean)
LEAN_NOTE: GAP-I1a (audit 1 PASS; N1 ruling (i), tau>=n-1 via KAM.IsDiophantine.n_sub_one_le_tau)
NOTE: -

NODE: stepI:p1:lr-gradient
KIND: step
TITLE: The gradient identity
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-gradient@L250-L252
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-gradient@L250-L252
CONTRACT_ID: stepI:p1:lr-gradient
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting
SOURCE_QUANTIFIERS: z in D
SOURCE_CONCLUSION: DH(z) = (Omega_0 X_H(z))^T = -X_H(z)^T Omega_0 on D
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:hamiltonian, bpI:p1:setting#k-bridge, bpI:p1:setting, bpI:p0:stripdata#omegaZero
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:hamiltonian | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-gradient@L251-L251 | Omega_0 X_H = (DH)^T (item (d))
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-gradient@L251-L251 | supplies the K standing data of the Hamiltonian lemma
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-gradient@L251-L251 | H holomorphic on D
EDGE: bpI:p0:stripdata#omegaZero | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-gradient@L252-L252 | Omega_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_lr_gradient (KAM/Iso/Linear/FullRangeStepsExt.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:lr-insert
KIND: step
TITLE: Insert the error
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-insert@L254-L261
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-insert@L254-L261
CONTRACT_ID: stepI:p1:lr-insert
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0 on T_r
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: Y = DH(K)N = omega^T - E^T Omega_0 N, entrywise Y_b = omega_b + N_{.b}^T Omega_0 E = omega_b - eta^L_b; ¦Y - omega^T¦ <= n¦eta^L¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:lr-gradient, bpI:p0:stripdata#invarianceError, K:bp:p2:frame-identities, bpI:p1:setting#k-bridge, K:bp:p2:objects, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:lr-gradient | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-insert@L257-L257 | DH = -X_H^T Omega_0
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-insert@L255-L255 | X_H(K) = L omega + E
EDGE: K:bp:p2:frame-identities | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-insert@L259-L259 | L^T Omega_0 N = -I_n
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-insert@L259-L259 | supplies the K standing data of frame-identities
EDGE: K:bp:p2:objects | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-insert@L260-L260 | eta^L = -N^T Omega_0 E
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-insert@L255-L255 | direct use of the local H, K, omega, domain or standing constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.LastRowAux.energyRow_eq_sub_etaL, KAM.Iso.Linear.LastRowAux.sum_norm_energyRow_sub_le (KAM/Iso/Linear/LastRow.lean)
LEAN_NOTE: Premise IsUnit det G only; Y = omega - etaL and sum|Y_b - omega_b| <= n|etaL|; I1-2-audit-1.md:60-61 PASS.
NOTE: -

NODE: stepI:p1:lr-average
KIND: step
TITLE: Invariant torus and average
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-average@L263-L269
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-average@L263-L269
CONTRACT_ID: stepI:p1:lr-average
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0 on T_r; for the quantitative bound, norms of E, L, B as stated in last-row(c)
SOURCE_QUANTIFIERS: theta
SOURCE_CONCLUSION: (b) Y = omega^T when E = 0, with the stated T_H and avg(T_H); (c) avg(T_H) = T^inv - last-row correction with the bound 2 n^2 sigma_K' sigma_B' e
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:extended#extendedTorsion, bpI:p0:extended#extendedTorsionAverage, bpI:p1:extended-basic, stepI:p1:lr-insert, K:bp:p2:averages, K:bp:p2:matrix, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:extended#extendedTorsion | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-average@L264-L264 | definition of T_H
EDGE: bpI:p0:extended#extendedTorsionAverage | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-average@L266-L266 | avg(T_H)
EDGE: bpI:p1:extended-basic | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-average@L265-L265 | block form of avg(T_H) (a)
EDGE: stepI:p1:lr-insert | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-average@L266-L266 | (a) averaged
EDGE: K:bp:p2:averages | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-average@L267-L267 | ¦avg f¦ <= sup ¦f¦, linearity
EDGE: K:bp:p2:matrix | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-average@L268-L268 | norm inequalities for N, Omega_0, transposes
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:lr-average@L264-L264 | direct use of the local H, K, omega, domain or standing constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_lr_average (KAM/Iso/Linear/FullRangeStepsExt.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: bpI:p1:energy-approx
KIND: lemma
TITLE: Approximate energy identities
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L275-L298
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L300-L335
CONTRACT_ID: bpI:p1:energy-approx
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p1:setting (n>=2, tau>=0, M>0; D open, Z^n-invariant in theta; H holomorphic on D, 1-periodic in theta, real at real phase points of D, ¦DH¦,¦X_H¦,¦DX_H¦,¦D^2 X_H¦ <= M on D; gamma>0, omega in R^n cap Dio_{gamma,tau}; r>0, K holomorphic, primary, real on reals on T_r with K(T_r) subset D); E := E_{H,K,omega}, E^en := H o K - avg(H o K) on T_r; (e): ¦E¦ <= eps on T_r, 0 < delta < r, 0 < delta' < r - delta; (f): det G_K != 0 on T_r, xi = (xi^L, xi^N) holomorphic on T_{r'} with 0 < r' <= r, Delta K = P xi, and for the consequence avg(Y xi^N) = eta^omega
SOURCE_QUANTIFIERS: setting data (outermost); eps, delta, delta', r', xi; then claims (a)-(f)
SOURCE_CONCLUSION: (a) H o K holomorphic, 1-periodic on T_r, real on reals, D(H o K) = DH(K) DK, avg(H o K) = Ebar_H(K) (frozen energyAverage), real; (b) d_omega(H o K) = D(H o K)omega = -DH(K)E on T_r; (c) L^T Omega_0 E = (D(H o K))^T - Omega_K omega, and eta^N = L^T Omega_0 E if det G_K != 0; (d) avg(D(H o K)) = 0, avg(Omega_K) = 0, avg(eta^N) = 0; (e) ¦E^en¦ <= M Gamma_delta eps on T_{r-delta} and ¦D(H o K)¦ <= n M Gamma_delta eps/delta' on T_{r-delta-delta'}; (f) DH(K) Delta K = Y xi^N + D(H o K) xi^L = Y xi^N + (eta^N)^T xi^L - omega^T Omega_K xi^L on T_{r'}, hence avg(DH(K)Delta K) = eta^omega + E^omega_lin with E^omega_lin := avg(D(H o K) xi^L) bounded by sup¦D(H o K)¦ sup¦xi^L¦ <= n(sup¦eta^N¦ + ¦omega¦ sup¦Omega_K¦) sup¦xi^L¦
CONSTANT_SCOPE: Gamma_delta = c_R gamma^{-1} delta^{-kappa} (c_R, kappa from K constants, depending on n, tau); M from the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p1:setting#k-bridge, K:bp:p2:objects, bpI:p0:stripdata#invarianceError, bpI:p0:extended#energyAverage, stepI:p1:ea-chain, stepI:p1:ea-omega, stepI:p1:ea-gradient, stepI:p1:ea-avg, stepI:p1:ea-size, stepI:p1:ea-defect
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L276-L276 | Assume the setting
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L276-L276 | K objects (Omega_K, eta^N, P, N) with h := H and K results applied
EDGE: K:bp:p2:objects | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L276-L276 | E, Omega_K, eta, P, N
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L276-L276 | E = E_{H,K,omega}
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L279-L279 | avg(H o K) is the frozen energyAverage
EDGE: stepI:p1:ea-chain | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L301-L301 | proof step
EDGE: stepI:p1:ea-omega | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L307-L307 | proof step
EDGE: stepI:p1:ea-gradient | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L311-L311 | proof step
EDGE: stepI:p1:ea-avg | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L316-L316 | proof step
EDGE: stepI:p1:ea-size | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L321-L321 | proof step
EDGE: stepI:p1:ea-defect | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-approx@L328-L328 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.energy_approx_src, KAM.Iso.Linear.energy_defect_src (KAM/Iso/Linear/FullRange.lean)
LEAN_NOTE: GAP-I1a (audit 1 PASS; N1 ruling (i), tau>=n-1 via KAM.IsDiophantine.n_sub_one_le_tau)
NOTE: -

NODE: stepI:p1:ea-chain
KIND: step
TITLE: Regularity and chain rule
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-chain@L301-L305
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-chain@L301-L305
CONTRACT_ID: stepI:p1:ea-chain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: H o K holomorphic, 1-periodic on T_r, real on reals, D(H o K) = DH(K) DK; avg(H o K) = Ebar_H(K), integrable
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p1:ext-chain, bpI:p0:extended#energyAverage, K:bp:p2:averages
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-chain@L302-L302 | K holomorphic with values in D, H holomorphic on D; periodicity and realness (I2, I3)
EDGE: bpI:p1:ext-chain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-chain@L303-L303 | chain rule
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-chain@L304-L304 | average is the frozen energyAverage
EDGE: K:bp:p2:averages | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-chain@L305-L305 | integrability of a continuous periodic function
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_ea_chain (KAM/Iso/Linear/FullRangeStepsEnergy.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS; accepted deviation: carries parent standing hyps (K primary, real on reals, K(T_r) in D)
NOTE: -

NODE: stepI:p1:ea-omega
KIND: step
TITLE: The derivative along $\omega$
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-omega@L307-L309
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-omega@L307-L309
CONTRACT_ID: stepI:p1:ea-omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: D(H o K)omega = DH(K)L omega = -DH(K)E on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:ea-chain, bpI:p0:stripdata#invarianceError, K:bp:p2:hamiltonian, bpI:p1:setting#k-bridge, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:ea-chain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-omega@L308-L308 | D(H o K) = DH(K) L
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-omega@L308-L308 | L omega = X_H(K) - E
EDGE: K:bp:p2:hamiltonian | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-omega@L308-L308 | DH = (Omega_0 X_H)^T, antisymmetry of Omega_0
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-omega@L308-L308 | supplies the K standing data of the Hamiltonian lemma
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-omega@L308-L308 | H holomorphic on D
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.Energy.fderiv_comp_apply, KAM.Iso.Linear.Energy.fderiv_comp_omega (KAM/Iso/Linear/Energy.lean)
LEAN_NOTE: Pointwise differentiability only; chain rule gives D(H o K)omega = DH(K)L omega, and = -DH(K)E; I1-3-audit-1.md:71-73 PASS.
NOTE: -

NODE: stepI:p1:ea-gradient
KIND: step
TITLE: The gradient identity
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-gradient@L311-L314
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-gradient@L311-L314
CONTRACT_ID: stepI:p1:ea-gradient
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0 for the eta^N identification
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: L^T Omega_0 E = (D(H o K))^T - Omega_K omega; eta^N = L^T Omega_0 E
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:ea-chain, bpI:p1:setting#k-bridge, K:bp:p2:objects, bpI:p1:setting, K:bp:p2:exactness
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:ea-chain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-gradient@L312-L312 | DH(K)L = D(H o K)
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-gradient@L312-L312 | supplies the K standing data of the Hamiltonian lemma
EDGE: K:bp:p2:objects | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-gradient@L313-L313 | definitions of eta^N and Omega_K
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-gradient@L312-L312 | direct use of the local H, K, omega, domain or standing constants
EDGE: K:bp:p2:exactness | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-gradient@L312-L312 | repeats the gradient step of exactness
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_ea_gradient (KAM/Iso/Linear/FullRangeStepsEnergy.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS; accepted deviation: carries parent standing hyps (K primary, real on reals, K(T_r) in D)
NOTE: -

NODE: stepI:p1:ea-avg
KIND: step
TITLE: Averages
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg@L316-L319
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg@L316-L319
CONTRACT_ID: stepI:p1:ea-avg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0 where eta^N is used
SOURCE_QUANTIFIERS: l
SOURCE_CONCLUSION: avg(D(H o K)) = 0, avg(Omega_K) = 0, avg(eta^N) = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting
ROUTES: stepI:p1:ea-avg#exactness-route, stepI:p1:ea-avg#gradient-route
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg@L317-L317 | direct use of the local H, K, omega, domain or standing constants
EDGE: stepI:p1:ea-avg#exactness-route | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg@L317-L319 | first alternative derivation of the vanishing average (exactness)
EDGE: stepI:p1:ea-avg#gradient-route | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg@L317-L319 | second alternative derivation of the vanishing average (gradient identity)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_ea_avg (KAM/Iso/Linear/FullRangeStepsEnergy.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS; accepted deviation: carries parent standing hyps (K primary, real on reals, K(T_r) in D)
NOTE: -

NODE: stepI:p1:ea-size
KIND: step
TITLE: The size of the energy fluctuation
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-size@L321-L326
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-size@L321-L326
CONTRACT_ID: stepI:p1:ea-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; norm E <= eps on T_r; 0 < delta < r; 0 < delta' < r-delta
SOURCE_QUANTIFIERS: delta, delta'
SOURCE_CONCLUSION: ¦E^en¦ <= M Gamma_delta eps on T_{r-delta}; ¦D(H o K)¦ <= n M Gamma_delta eps/delta' on T_{r-delta-delta'}
CONSTANT_SCOPE: Gamma_delta = c_R gamma^{-1} delta^{-kappa}
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:ea-chain, stepI:p1:ea-omega, bpI:p1:setting, K:bp:p2:cohomological, bpI:p1:setting#k-bridge, K:bp:p1:cauchy-strip
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:ea-chain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-size@L322-L322 | E^en holomorphic and periodic with zero average
EDGE: stepI:p1:ea-omega | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-size@L322-L322 | d_omega E^en = -DH(K)E
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-size@L323-L323 | ¦DH¦ <= M on D and K(T_r) subset D (I4)
EDGE: K:bp:p2:cohomological | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-size@L324-L324 | cohomological equation in operator norms, (b)
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-size@L324-L324 | supplies the K standing data (gamma, tau, omega) of the cohomological lemma
EDGE: K:bp:p1:cauchy-strip | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-size@L325-L325 | Cauchy estimate on strips
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_ea_size (KAM/Iso/Linear/FullRangeStepsEnergy.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS; accepted deviation: carries parent standing hyps (K primary, real on reals, K(T_r) in D)
NOTE: -

NODE: stepI:p1:ea-defect
KIND: step
TITLE: The energy defect
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-defect@L328-L334
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-defect@L328-L334
CONTRACT_ID: stepI:p1:ea-defect
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0 on T_r; xi holomorphic on T_{r'}, 0 < r' <= r; Delta K = P xi; for the averaged consequence, avg(Y xi^N) = eta^omega
SOURCE_QUANTIFIERS: xi, r'
SOURCE_CONCLUSION: DH(K)Delta K = Y xi^N + D(H o K) xi^L = Y xi^N + (eta^N)^T xi^L - omega^T Omega_K xi^L; avg splits linearly; bound on E^omega_lin by the suprema of D(H o K), eta^N, Omega_K, xi^L over the cube
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:objects, bpI:p1:setting#k-bridge, stepI:p1:ea-chain, stepI:p1:ea-gradient, K:bp:p1:ext-integral, K:bp:p2:matrix, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:objects | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-defect@L329-L329 | P = (L N), Omega_K = L^T Omega_0 L
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-defect@L329-L329 | K objects with h := H
EDGE: stepI:p1:ea-chain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-defect@L329-L329 | DH(K)L = D(H o K) (a)
EDGE: stepI:p1:ea-gradient | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-defect@L330-L330 | D(H o K) = (eta^N + Omega_K omega)^T (c)
EDGE: K:bp:p1:ext-integral | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-defect@L331-L331 | continuous on the compact cube, integrable; ¦avg f¦ <= sup ¦f¦
EDGE: K:bp:p2:matrix | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-defect@L334-L334 | transpose of a row has norm <= n times the vector norm
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-defect@L329-L329 | direct use of the local H, K, omega, domain or standing constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_ea_defect_node (KAM/Iso/Linear/FullRangeStepsEnergy.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS (replacement step_ea_defect_node, audit 2 F1 PASS); accepted deviation: carries parent standing hyps (K primary, real on reals, K(T_r) in D)
NOTE: -

NODE: bpI:p1:energy-conservation
KIND: lemma
TITLE: Energy conservation of an invariant torus
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-conservation@L337-L348
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-conservation@L350-L363
CONTRACT_ID: bpI:p1:energy-conservation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p1:setting (n>=2, tau>=0, M>0; D open, Z^n-invariant in theta; H holomorphic on D, 1-periodic in theta, real at real phase points of D, ¦DH¦,¦X_H¦,¦DX_H¦,¦D^2 X_H¦ <= M on D; gamma>0, omega in R^n cap Dio_{gamma,tau}; r>0, K holomorphic, primary, real on reals on T_r with K(T_r) subset D); E_{H,K,omega}(theta) = 0 for all theta in T_r; for (b): E_0 in R (or C), Ebar_H(K) = E_0
SOURCE_QUANTIFIERS: setting data (outermost); E_0; then claims (a)-(c)
SOURCE_CONCLUSION: (a) H o K is constant, = Ebar_H(K), on T_r; (b) H(K(theta)) = E_0 for every theta in T_r; (c) sup over T_r of ¦H o K - E_0¦ = ¦Ebar_H(K) - E_0¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p0:stripdata#invarianceError, bpI:p0:extended#energyAverage, stepI:p1:ec-derivative, stepI:p1:ec-unique, stepI:p1:ec-pointwise
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-conservation@L338-L338 | Assume the setting on T_r (omega in Dio_{gamma,tau})
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-conservation@L338-L338 | E_{H,K,omega} = 0
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-conservation@L341-L341 | Ebar_H(K) = frozen energyAverage
EDGE: stepI:p1:ec-derivative | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-conservation@L351-L351 | proof step
EDGE: stepI:p1:ec-unique | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-conservation@L355-L355 | proof step
EDGE: stepI:p1:ec-pointwise | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:energy-conservation@L361-L361 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.energy_conservation_src (KAM/Iso/Linear/FullRange.lean)
LEAN_NOTE: GAP-I1a (audit 1 PASS; N1 ruling (i), tau>=n-1 via KAM.IsDiophantine.n_sub_one_le_tau)
NOTE: -

NODE: stepI:p1:ec-derivative
KIND: step
TITLE: The derivative vanishes along $\omega$
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-derivative@L351-L353
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-derivative@L351-L353
CONTRACT_ID: stepI:p1:ec-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; E = 0 on T_r
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: u := H o K - avg(H o K) is holomorphic, 1-periodic on T_r with avg(u) = 0 and Du omega = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:energy-approx, bpI:p0:stripdata#invarianceError, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:energy-approx | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-derivative@L352-L352 | (a): u holomorphic, periodic, zero average; (b) (line 335): Du omega = -DH(K)E = 0
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-derivative@L353-L353 | E = 0
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-derivative@L352-L352 | direct use of the local H, K, omega, domain or standing constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_ec_derivative (KAM/Iso/Linear/FullRangeStepsEnergy.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS; accepted deviation: carries parent standing hyps (K primary, real on reals, K(T_r) in D)
NOTE: -

NODE: stepI:p1:ec-unique
KIND: step
TITLE: Uniqueness for the cohomological equation
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-unique@L355-L359
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-unique@L355-L359
CONTRACT_ID: stepI:p1:ec-unique
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; E = 0 on T_r
SOURCE_QUANTIFIERS: delta in (0,r)
SOURCE_CONCLUSION: u = 0 on T_{r-delta} for every delta, hence u = 0 on T_r, which is (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:ec-derivative, K:bp:p1:cohomological, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:ec-derivative | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-unique@L356-L356 | u holomorphic periodic with zero average solving Du omega = 0
EDGE: K:bp:p1:cohomological | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-unique@L357-L357 | uniqueness clause of the cohomological equation
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-unique@L357-L357 | omega in Dio_{gamma,tau}, gamma > 0, tau >= 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_ec_unique (KAM/Iso/Linear/FullRangeStepsEnergy.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS; accepted deviation: carries parent standing hyps (K primary, real on reals, K(T_r) in D)
NOTE: -

NODE: stepI:p1:ec-pointwise
KIND: step
TITLE: Pointwise energy
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-pointwise@L361-L362
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-pointwise@L361-L362
CONTRACT_ID: stepI:p1:ec-pointwise
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; E = 0 on T_r; E_0 in R or C arbitrary, with Ebar_H(K) = E_0 additionally for conclusion (b)
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: H o K is identically Ebar_H(K); if Ebar_H(K) = E_0, then H(K(theta)) = E_0 everywhere; for arbitrary E_0, sup_{T_r} norm(H o K - E_0) = norm(Ebar_H(K)-E_0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:ec-unique, bpI:p0:extended#energyAverage, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:ec-unique | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-pointwise@L362-L362 | (a): H o K = Ebar_H(K)
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-pointwise@L362-L362 | Ebar_H(K)
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ec-pointwise@L362-L362 | direct use of the local H, K, omega, domain or standing constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_ec_pointwise (KAM/Iso/Linear/FullRangeStepsEnergy.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS; accepted deviation: carries parent standing hyps (K primary, real on reals, K(T_r) in D)
NOTE: -

NODE: bpI:p1:border-solve
KIND: lemma
TITLE: Bordered triangular equations (HL19 Lemma 6.1)
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L376-L423
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L425-L471
CONTRACT_ID: bpI:p1:border-solve
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: gamma > 0, tau >= 0, omega in R^n cap Dio_{gamma,tau}, r > 0, delta > 0, 2 delta < r; Gamma_delta = c_R gamma^{-1} delta^{-kappa}; eta^L, eta^N : T_r -> C^n holomorphic, 1-periodic, ¦eta^L¦ <= H_L, ¦eta^N¦ <= H_N on T_r, avg(eta^N) = 0; eta^omega in C; T : T_r -> C^{nxn}, Y : T_r -> C^{1xn} holomorphic, 1-periodic with ¦T¦ <= H_T, ¦Y¦ <= H_Y on T_{r-delta}; script-T := [[avg T, omega],[avg Y, 0]] with det script-T != 0 and ¦script-T^{-1}¦ <= sigma (row-sum norm of C^{(n+1)x(n+1)}); xi^L_0 in C^n; R the solution operator of K:bp:p2:cohomological(a)
SOURCE_QUANTIFIERS: gamma, tau, omega, r, delta, Gamma_delta, eta^L, eta^N, H_L, H_N, eta^omega, T, Y, H_T, H_Y, sigma, xi^L_0 (all fixed before the definitions of u^N, xi_0, xi^omega, xi^N, g^L, xi^L); claims (a)-(e)
SOURCE_CONCLUSION: with u^N := R eta^N on T_{r-delta}, (xi_0, xi^omega) := script-T^{-1}(avg eta^L + avg(T u^N), eta^omega + avg(Y u^N)), xi^N := xi_0 - u^N, g^L := T xi^N + omega xi^omega - eta^L on T_{r-delta}, xi^L := xi^L_0 + R g^L on T_{r-2 delta}: (a) u^N, xi^N, g^L holomorphic, 1-periodic on T_{r-delta}, avg g^L = 0, xi^L holomorphic, 1-periodic on T_{r-2delta}, averages exist; (b) on T_{r-2delta}: T xi^N - d_omega xi^L + omega xi^omega = eta^L, -d_omega xi^N = eta^N, avg(Y xi^N) = eta^omega; (c) estimates with S_* := sigma max{H_L + H_T Gamma_delta H_N, ¦eta^omega¦ + H_Y Gamma_delta H_N}: ¦xi_0¦,¦xi^omega¦ <= S_*, sup¦xi^N¦ <= S_* + Gamma_delta H_N, sup¦g^L¦ <= H_T(S_* + Gamma_delta H_N) + ¦omega¦ S_* + H_L, sup¦xi^L - xi^L_0¦ <= Gamma_delta sup¦g^L¦; (d) uniqueness: any holomorphic periodic solution (xi~^L, xi~^N, xi~^omega) of the system of (b) on T_{r-2delta} has xi~^omega = xi^omega, xi~^N = xi^N, xi~^L - xi^L constant; (e) realness if omega real, eta^L, eta^N, T, Y real on reals, eta^omega in R, xi^L_0 in R^n
CONSTANT_SCOPE: Gamma_delta = c_R gamma^{-1} delta^{-kappa} with c_R, kappa of K constants (c_R depends on n, tau); H_L, H_N, H_T, H_Y, sigma free bounds; no other constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:diophantine#IsDiophantine, K:bp:p2:constants, K:bp:p2:cohomological, bpI:p1:setting#k-bridge, stepI:p1:bs-first, stepI:p1:bs-averages, stepI:p1:bs-bordered, stepI:p1:bs-energy, stepI:p1:bs-second, stepI:p1:bs-unique, stepI:p1:bs-real
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L383-L383 | omega in Dio_{gamma,tau}
EDGE: K:bp:p2:constants | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L383-L383 | Gamma_delta, c_R, kappa
EDGE: K:bp:p2:cohomological | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L379-L379 | the solution operator R
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L379-L379 | supplies the K standing data (gamma, tau, omega) of the cohomological lemma
EDGE: stepI:p1:bs-first | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L426-L426 | proof step
EDGE: stepI:p1:bs-averages | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L430-L430 | proof step
EDGE: stepI:p1:bs-bordered | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L436-L436 | proof step
EDGE: stepI:p1:bs-energy | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L445-L445 | proof step
EDGE: stepI:p1:bs-second | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L450-L450 | proof step
EDGE: stepI:p1:bs-unique | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L459-L459 | proof step
EDGE: stepI:p1:bs-real | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:border-solve@L467-L467 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.border_solve (KAM/Iso/Linear/BorderSolve.lean); KAM.Iso.Linear.border_unique (KAM/Iso/Linear/BorderUnique.lean)
LEAN_NOTE: audit I1-5 PASS WITH NOTES; border_solve covers (a)-(e); no Setting/N1 dependence
NOTE: -

NODE: stepI:p1:bs-first
KIND: step
TITLE: First cohomological equation
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-first@L426-L428
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-first@L426-L428
CONTRACT_ID: stepI:p1:bs-first
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of border-solve
SOURCE_QUANTIFIERS: eta^N, delta
SOURCE_CONCLUSION: u^N = R eta^N is holomorphic, 1-periodic on T_{r-delta}, avg u^N = 0, d_omega u^N = eta^N, ¦u^N¦ <= Gamma_delta H_N, real on reals if eta^N is
CONSTANT_SCOPE: Gamma_delta as in border-solve
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:cohomological, bpI:p1:setting#k-bridge
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:cohomological | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-first@L427-L427 | (a): solution of the cohomological equation
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-first@L427-L427 | supplies the K standing data (gamma, tau, omega) of the cohomological lemma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.border_solve (KAM/Iso/Linear/BorderSolve.lean)
LEAN_NOTE: audit I1-5 PASS WITH NOTES; audit names step; included in border_solve
NOTE: -

NODE: stepI:p1:bs-averages
KIND: step
TITLE: Averages of the products
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-averages@L430-L434
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-averages@L430-L434
CONTRACT_ID: stepI:p1:bs-averages
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of border-solve
SOURCE_QUANTIFIERS: T u^N, Y u^N
SOURCE_CONCLUSION: averages of T u^N and Y u^N exist, ¦avg(T u^N)¦ <= H_T Gamma_delta H_N, ¦avg(Y u^N)¦ <= H_Y Gamma_delta H_N, ¦avg eta^L¦ <= H_L; w := (avg eta^L + avg(T u^N), eta^omega + avg(Y u^N)) has ¦w¦ <= max{H_L + H_T Gamma_delta H_N, ¦eta^omega¦ + H_Y Gamma_delta H_N}
CONSTANT_SCOPE: Gamma_delta as in border-solve
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:bs-first, K:bp:p2:averages
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:bs-first | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-averages@L431-L431 | u^N holomorphic, periodic, bounded by Gamma_delta H_N
EDGE: K:bp:p2:averages | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-averages@L432-L432 | existence of averages of continuous periodic functions and the sup bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.border_solve (KAM/Iso/Linear/BorderSolve.lean)
LEAN_NOTE: audit I1-5 PASS WITH NOTES; audit names step; included in border_solve
NOTE: -

NODE: stepI:p1:bs-bordered
KIND: step
TITLE: The bordered average system
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-bordered@L436-L443
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-bordered@L436-L443
CONTRACT_ID: stepI:p1:bs-bordered
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of border-solve, including det script-T != 0
SOURCE_QUANTIFIERS: xi_0, xi^omega
SOURCE_CONCLUSION: (xi_0, xi^omega) = script-T^{-1} w is the unique solution of avg T xi_0 + omega xi^omega = avg eta^L + avg(T u^N), avg Y xi_0 = eta^omega + avg(Y u^N), and ¦(xi_0, xi^omega)¦ <= ¦script-T^{-1}¦¦w¦ <= S_*
CONSTANT_SCOPE: S_* as in border-solve
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:bs-averages, K:bp:p2:matrix
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:bs-averages | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-bordered@L437-L437 | the right-hand side w and its bound
EDGE: K:bp:p2:matrix | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-bordered@L441-L441 | ¦Mv¦ <= ¦M¦¦v¦
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.border_solve (KAM/Iso/Linear/BorderSolve.lean)
LEAN_NOTE: audit I1-5 PASS WITH NOTES; audit names step; included in border_solve
NOTE: -

NODE: stepI:p1:bs-energy
KIND: step
TITLE: The energy equation and $\xi^N$
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-energy@L445-L448
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-energy@L445-L448
CONTRACT_ID: stepI:p1:bs-energy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of border-solve
SOURCE_QUANTIFIERS: xi^N
SOURCE_CONCLUSION: xi^N = xi_0 - u^N is holomorphic, periodic on T_{r-delta}, d_omega xi^N = -eta^N, ¦xi^N¦ <= S_* + Gamma_delta H_N, avg(Y xi^N) = eta^omega
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:bs-first, stepI:p1:bs-bordered
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:bs-first | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-energy@L446-L446 | u^N and d_omega u^N = eta^N
EDGE: stepI:p1:bs-bordered | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-energy@L447-L447 | second equation of the bordered average system, bound on xi_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.border_solve (KAM/Iso/Linear/BorderSolve.lean)
LEAN_NOTE: audit I1-5 PASS WITH NOTES; audit names step; included in border_solve
NOTE: -

NODE: stepI:p1:bs-second
KIND: step
TITLE: The second cohomological equation
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-second@L450-L457
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-second@L450-L457
CONTRACT_ID: stepI:p1:bs-second
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of border-solve
SOURCE_QUANTIFIERS: g^L, xi^L
SOURCE_CONCLUSION: g^L = T xi^N + omega xi^omega - eta^L holomorphic, periodic on T_{r-delta}, ¦g^L¦ <= H_T(S_* + Gamma_delta H_N) + ¦omega¦ S_* + H_L, avg g^L = 0; R g^L holomorphic periodic on T_{r-2delta} with d_omega R g^L = g^L and ¦R g^L¦ <= Gamma_delta sup¦g^L¦; the first equation of (b) holds; this gives (a), (b), (c)
CONSTANT_SCOPE: Gamma_delta as in border-solve
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:bs-bordered, stepI:p1:bs-first, stepI:p1:bs-energy, K:bp:p2:cohomological, bpI:p1:setting#k-bridge
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:bs-bordered | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-second@L453-L453 | first equation of the bordered average system gives avg g^L = 0
EDGE: stepI:p1:bs-first | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-second@L457-L457 | u^N
EDGE: stepI:p1:bs-energy | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-second@L457-L457 | xi^N and its bound
EDGE: K:bp:p2:cohomological | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-second@L455-L455 | (a) on T_{r-delta} with loss delta
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-second@L455-L455 | supplies the K standing data (gamma, tau, omega) of the cohomological lemma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.border_solve (KAM/Iso/Linear/BorderSolve.lean)
LEAN_NOTE: audit I1-5 PASS WITH NOTES; audit names step; included in border_solve
NOTE: -

NODE: stepI:p1:bs-unique
KIND: step
TITLE: Uniqueness
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-unique@L459-L465
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-unique@L459-L465
CONTRACT_ID: stepI:p1:bs-unique
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of border-solve; tilde solution holomorphic and periodic on T_{r-2delta}, satisfying the same system, as in (d)
SOURCE_QUANTIFIERS: xi~
SOURCE_CONCLUSION: xi~^omega = xi^omega, xi~^N = xi^N, xi~^L - xi^L constant
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:bs-first, K:bp:p1:cohomological, K:bp:p2:averages, stepI:p1:bs-bordered
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:bs-first | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-unique@L460-L460 | u^N with d_omega u^N = eta^N
EDGE: K:bp:p1:cohomological | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-unique@L461-L461 | uniqueness clause
EDGE: K:bp:p2:averages | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-unique@L463-L463 | avg(d_omega xi~^L) = 0
EDGE: stepI:p1:bs-bordered | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-unique@L463-L463 | invertibility of script-T and the bordered average system
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.border_solve (KAM/Iso/Linear/BorderSolve.lean)
LEAN_NOTE: audit I1-5 PASS WITH NOTES; audit names step; included in border_solve
NOTE: -

NODE: stepI:p1:bs-real
KIND: step
TITLE: Realness
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-real@L467-L470
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-real@L467-L470
CONTRACT_ID: stepI:p1:bs-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of border-solve; eta^L, eta^N, T, Y real on reals; eta^omega real and xi^L_0 real
SOURCE_QUANTIFIERS: xi_0, xi^omega, u^N, xi^N, g^L, xi^L
SOURCE_CONCLUSION: xi_0, xi^omega, xi^N, xi^L, g^L are real on reals
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:averages, K:bp:p1:real-inverse, K:bp:p2:cohomological, bpI:p1:setting#k-bridge, stepI:p1:bs-bordered
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:averages | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-real@L468-L468 | real averages of real continuous periodic functions
EDGE: K:bp:p1:real-inverse | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-real@L469-L469 | script-T real with real inverse
EDGE: K:bp:p2:cohomological | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-real@L469-L469 | R preserves realness
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-real@L469-L469 | supplies the K standing data (gamma, tau, omega) of the cohomological lemma
EDGE: stepI:p1:bs-bordered | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:bs-real@L469-L469 | xi_0, xi^omega = script-T^{-1} w
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.border_solve (KAM/Iso/Linear/BorderSolve.lean)
LEAN_NOTE: audit I1-5 PASS WITH NOTES; audit names step; included in border_solve
NOTE: -

NODE: bpI:p1:reduced
KIND: lemma
TITLE: The linearized isoenergetic equation in the frame
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:reduced@L483-L503
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:reduced@L505-L522
CONTRACT_ID: bpI:p1:reduced
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p1:setting (n>=2, tau>=0, M>0; D open, Z^n-invariant in theta; H holomorphic on D, 1-periodic in theta, real at real phase points of D, ¦DH¦,¦X_H¦,¦DX_H¦,¦D^2 X_H¦ <= M on D; gamma>0, omega in R^n cap Dio_{gamma,tau}; r>0, K holomorphic, primary, real on reals on T_r with K(T_r) subset D); det G_K != 0 on T_r; omega in R^n (any); xi = (xi^L, xi^N) holomorphic on T_{r'} with 0 < r' <= r; xi^omega in C; Delta K = P xi, Delta omega = -omega xi^omega; for (c): the bordered system of border-solve(b) holds on T_{r'}; for (d): det P != 0 on T_{r'}
SOURCE_QUANTIFIERS: setting data (outermost); omega, r', xi, xi^omega; then claims (a)-(d) on T_{r'}
SOURCE_CONCLUSION: (a) Q L = (I_n; -Omega_K), hence Q L omega xi^omega = (omega; -Omega_K omega) xi^omega; (b) Q(A Delta K - d_omega Delta K - DK Delta omega) + Q E = Lambda xi - d_omega xi + (omega; 0) xi^omega - eta + E_lin with E_lin := E_red xi + Omega_0 E_sym d_omega xi - (0; Omega_K omega) xi^omega; (c) if the bordered system holds then Q Res = E_lin with Res := A Delta K - d_omega Delta K + L omega xi^omega + E, and ¦E_lin¦ <= ¦E_red¦¦xi¦ + ¦E_sym¦¦d_omega xi¦ + ¦Omega_K¦¦omega¦¦xi^omega¦; (d) if moreover det P != 0 then Res = Q^{-1} E_lin, and for any xi, xi^omega: Res = 0 iff Lambda xi - d_omega xi + (omega;0) xi^omega = eta - E_lin
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p1:setting#k-bridge, K:bp:p2:objects, bpI:p0:stripdata#invarianceError, stepI:p1:rd-ql, stepI:p1:rd-expand, stepI:p1:rd-consequence
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:reduced@L484-L484 | Assume the setting
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:reduced@L484-L484 | K objects and K frame results with h := H
EDGE: K:bp:p2:objects | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:reduced@L499-L499 | eta^L, eta^N, T, Y data of K objects
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:reduced@L492-L492 | E = E_{H,K,omega} in Res
EDGE: stepI:p1:rd-ql | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:reduced@L506-L506 | proof step
EDGE: stepI:p1:rd-expand | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:reduced@L510-L510 | proof step
EDGE: stepI:p1:rd-consequence | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:reduced@L516-L516 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.AnyOmega.reduced_anyOmega_src (KAM/Iso/Linear/FullRangeAnyOmega.lean)
LEAN_NOTE: GAP-I1c audit 2 PASS WITH NOTES; literal SettingSrc (tau>=0), arbitrary tested omega with |omega|<=Theta (ruling 05:10, free omega literal)
NOTE: -

NODE: stepI:p1:rd-ql
KIND: step
TITLE: The product $QL$
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-ql@L506-L508
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-ql@L506-L508
CONTRACT_ID: stepI:p1:rd-ql
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0 on T_r
SOURCE_QUANTIFIERS: theta
SOURCE_CONCLUSION: Q L = (I_n; -Omega_K)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:objects, K:bp:p2:frame-identities, bpI:p1:setting#k-bridge, K:bp:p2:matrix, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:objects | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-ql@L507-L507 | Q = -Omega_0 P^T Omega_0, P = (L N), Omega_K
EDGE: K:bp:p2:frame-identities | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-ql@L507-L507 | (a): L^T Omega_0 N = -I_n, N^T Omega_0 L = I_n
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-ql@L507-L507 | supplies the K standing data of frame-identities
EDGE: K:bp:p2:matrix | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-ql@L508-L508 | Omega_0 (U_1; U_2) = (-U_2; U_1)
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-ql@L507-L507 | direct use of the local H, K, omega, domain or standing constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: reducer_mul_tangentMat, omegaZeroMatrix_mul_fromRows (KAM/Iso/Linear/Reduced.lean)
LEAN_NOTE: audit I1-6 PASS WITH NOTES; pointwise statement needing only IsUnit det Gram (no Setting, so no N1 restriction)
NOTE: -

NODE: stepI:p1:rd-expand
KIND: step
TITLE: Expanding the linearized operator
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-expand@L510-L514
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-expand@L510-L514
CONTRACT_ID: stepI:p1:rd-expand
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0 on T_r; xi holomorphic on T_{r'}, 0 < r' <= r; xi^omega scalar; Delta K = P xi and Delta omega = -omega xi^omega
SOURCE_QUANTIFIERS: xi, xi^omega
SOURCE_CONCLUSION: Q(A Delta K - d_omega Delta K - DK Delta omega) + Q E = (Lambda + E_red) xi - d_omega xi + Omega_0 E_sym d_omega xi + (omega;0) xi^omega - (0; Omega_K omega) xi^omega - eta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:frame-identities, bpI:p1:setting#k-bridge, stepI:p1:rd-ql, K:bp:p2:objects, bpI:p1:setting, bpI:p1:ext-chain
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:frame-identities | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-expand@L512-L512 | (e) Q(AP - d_omega P) = Lambda + E_red; (f) QP = I - Omega_0 E_sym
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-expand@L512-L512 | supplies the K standing data of frame-identities
EDGE: stepI:p1:rd-ql | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-expand@L513-L513 | (a): Q L omega xi^omega
EDGE: K:bp:p2:objects | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-expand@L513-L513 | Q E = -eta
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-expand@L511-L511 | direct use of the local H, K, omega, domain or standing constants
EDGE: bpI:p1:ext-chain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-expand@L511-L511 | product rule for the directional derivative of P xi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_rd_expand (KAM/Iso/Linear/FullRangeStepsFrame.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:rd-consequence
KIND: step
TITLE: Consequence
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-consequence@L516-L521
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-consequence@L516-L521
CONTRACT_ID: stepI:p1:rd-consequence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0; xi, xi^omega and strip as in reduced; for (c) the bordered system holds; for (d) det P != 0, sufficient if norm E_sym < 1
SOURCE_QUANTIFIERS: xi, xi^omega
SOURCE_CONCLUSION: Q Res = E_lin when the bordered system holds, with the bound on E_lin; det P != 0 (when ¦E_sym¦ < 1) gives Q invertible, Res = Q^{-1} E_lin and the equivalence in (d)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:rd-expand, K:bp:p2:frame-identities, bpI:p1:setting#k-bridge, bpI:p1:ext-neumann, K:bp:p1:matrix-norms, K:bp:p2:matrix, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:rd-expand | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-consequence@L517-L517 | (b)
EDGE: K:bp:p2:frame-identities | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-consequence@L518-L518 | (b): P^T Omega_0 P = Omega_0 + E_sym
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-consequence@L518-L518 | supplies the K standing data of frame-identities
EDGE: bpI:p1:ext-neumann | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-consequence@L519-L519 | radius-one Neumann criterion: I - Omega_0 E_sym invertible when ¦E_sym¦ < 1 (not K:bp:p1:neumann, threshold 1/2)
EDGE: K:bp:p1:matrix-norms | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-consequence@L519-L519 | ¦Omega_0 E_sym¦ = ¦E_sym¦
EDGE: K:bp:p2:matrix | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-consequence@L521-L521 | norm bounds for E_lin
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:rd-consequence@L517-L517 | direct use of the local H, K, omega, domain or standing constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-global-I+sonnet-amend-I-p1
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_rd_consequence (KAM/Iso/Linear/FullRangeStepsFrame.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS; accepted deviation: keeps det P on T_r'
NOTE: -

NODE: bpI:p1:geometry-noA5
KIND: lemma
TITLE: Geometry of an approximately invariant torus, without \Kref{bp:p2:A5}
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:geometry-noA5@L535-L544
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:geometry-noA5@L545-L563
CONTRACT_ID: bpI:p1:geometry-noA5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega in Dio_{gamma,tau}, 0 < delta <= 1, 2 delta < r, 0 <= eps <= 1; Part 1 setting data D, H, M, n, tau (Assumption bpI:p1:setting; K and r as in this lemma); K holomorphic, primary and real on reals on T_r with B_beta(K(theta)) subset D (some beta > 0), ¦DK¦ <= sigma_K, det G_K != 0, ¦B¦ <= sigma_B, ¦E_{H,K,omega}¦ <= eps on T_r
SOURCE_QUANTIFIERS: setting data, omega, gamma, tau, delta, r, eps, beta, sigma_K, sigma_B, K; then conclusions with the constants m, Theta, C_* of K:bp:p2:constants
SOURCE_CONCLUSION: on T_{r-delta}: ¦DE¦ <= n eps/delta, ¦d_omega Omega_K¦ <= 2n(n+1) m eps/delta, ¦E_red¦ <= C_red eps/delta; on T_{r-2delta}: ¦Omega_K¦ <= C_Omega eps/(gamma delta^{kappa+1}), ¦E_sym¦ <= C_sym eps/(gamma delta^{kappa+1}); on T_r: ¦eta^L¦ <= 2n m^2 eps, ¦eta^N¦ <= 2n m eps, ¦L¦ <= m, ¦B¦ <= m, ¦N¦ <= m^2, ¦P¦ <= 2 m^2; if ¦omega¦ <= Theta then ¦X_N¦ <= C_X/delta, ¦T¦ <= C_T/delta on T_{r-delta}
CONSTANT_SCOPE: m, Theta, C_* are the constants of K:bp:p2:constants, depending on (n, tau, M, sigma_K, sigma_B, sigma_T) only, with sigma_T entering only through m = max{1, M, sigma_K, sigma_B, sigma_T}
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p1:setting#k-bridge, K:bp:p2:constants, K:bp:p2:admissible, K:bp:p2:frame-basic, stepI:p1:geo-de, stepI:p1:geo-red, stepI:p1:geo-sym
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:geometry-noA5@L536-L536 | D, H, M, n, tau from the setting
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:geometry-noA5@L546-L546 | K Part 2 results (frame-basic, frame-identities, exactness, cohomological) applied with h := H
EDGE: K:bp:p2:constants | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:geometry-noA5@L537-L537 | constants m, Theta, C_*
EDGE: K:bp:p2:admissible | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:geometry-noA5@L546-L546 | frame-basic hypotheses (A2)-(A4), (A6) are supplied by the hypotheses of this lemma
EDGE: K:bp:p2:frame-basic | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:geometry-noA5@L546-L546 | last sentence: items (b)-(d) of frame-basic
EDGE: stepI:p1:geo-de | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:geometry-noA5@L547-L547 | proof step
EDGE: stepI:p1:geo-red | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:geometry-noA5@L549-L549 | proof step
EDGE: stepI:p1:geo-sym | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:geometry-noA5@L561-L561 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.geometry_noA5_src (KAM/Iso/Linear/FullRange.lean)
LEAN_NOTE: GAP-I1a (audit 1 PASS; N1 ruling (i), tau>=n-1 via KAM.IsDiophantine.n_sub_one_le_tau)
NOTE: -

NODE: stepI:p1:geo-de
KIND: step
TITLE: Derivatives of the error
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-de@L547-L548
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-de@L547-L548
CONTRACT_ID: stepI:p1:geo-de
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hypotheses of geometry-noA5
SOURCE_QUANTIFIERS: delta
SOURCE_CONCLUSION: E holomorphic with ¦E¦ <= eps on T_r; ¦DE¦ <= n eps/delta and ¦(DE)^T¦ <= 2n eps/delta on T_{r-delta}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:frame-basic, bpI:p1:setting#k-bridge, K:bp:p1:cauchy-strip, K:bp:p1:cauchy-corollaries, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:frame-basic | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-de@L548-L548 | (a): E holomorphic with ¦E¦ <= eps
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-de@L548-L548 | supplies the K standing data of frame-basic
EDGE: K:bp:p1:cauchy-strip | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-de@L548-L548 | Cauchy estimate on strips
EDGE: K:bp:p1:cauchy-corollaries | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-de@L548-L548 | with p = 2n: ¦(DE)^T¦ <= 2n eps/delta
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-de@L548-L548 | direct use of the local H, K, omega, domain or standing constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1+sonnet-amend-I-p1
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_geo_de (KAM/Iso/Linear/FullRangeStepsFrame.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:geo-red
KIND: step
TITLE: $\partial_\omega\Omega_K$ and $E_{\mathrm{red}}$
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red@L549-L559
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red@L549-L559
CONTRACT_ID: stepI:p1:geo-red
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hypotheses of geometry-noA5 (no torsion condition, no A5)
SOURCE_QUANTIFIERS: delta
SOURCE_CONCLUSION: ¦d_omega Omega_K¦ <= (2n m + 2n^2 m) eps/delta and ¦E_red¦ <= C_red eps/delta on T_{r-delta}
CONSTANT_SCOPE: inherited constants m and C_red of K:bp:p2:constants, depending only on (n,tau,M,sigma_K,sigma_B,sigma_T); no new constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:geo-red-domega, stepI:p1:geo-red-ered, bpI:p1:setting, K:bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:geo-red-domega | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red@L552-L556 | substep: bound on d_omega Omega_K
EDGE: stepI:p1:geo-red-ered | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red@L558-L559 | substep: bound on E_red
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red@L550-L550 | the local frame data and geometry-noA5 setting inherited by this result
EDGE: K:bp:p2:constants | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red@L550-L559 | m and C_red are the named constants in the two estimates and their declared scope
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-delta-I-amend
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_geo_red (KAM/Iso/Linear/FullRangeStepsFrame.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: K:step:p2:geo-domegak and K:step:p2:geo-ered are only compared with (stated under A5); the former SOURCE_GAP is closed by the direct substeps.

NODE: stepI:p1:geo-red-domega
KIND: step
TITLE: Bound on $\partial_\omega\Omega_K$
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-domega@L552-L556
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-domega@L552-L556
CONTRACT_ID: stepI:p1:geo-red-domega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hypotheses of geometry-noA5 (no torsion condition, no A5)
SOURCE_QUANTIFIERS: delta
SOURCE_CONCLUSION: ¦d_omega Omega_K¦ <= (2n m + 2n^2 m) eps/delta = 2n(n+1) m eps/delta on T_{r-delta}
CONSTANT_SCOPE: inherited constant m of K:bp:p2:constants; no new constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p1:setting#k-bridge, K:bp:p2:frame-identities, K:bp:p2:matrix, K:bp:p2:frame-basic, stepI:p1:geo-de, K:bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-domega@L553-L553 | local H, K, omega data
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-domega@L553-L553 | supplies the K standing data of frame-identities and frame-basic
EDGE: K:bp:p2:frame-identities | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-domega@L553-L553 | (d): d_omega Omega_K = -(DE)^T Omega_0 L - L^T Omega_0 DE
EDGE: K:bp:p2:matrix | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-domega@L553-L553 | (b), (d): norm of products, ¦Omega_0¦ = 1
EDGE: K:bp:p2:frame-basic | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-domega@L553-L553 | (b): ¦L¦ <= m, ¦L^T¦ <= 2n m
EDGE: stepI:p1:geo-de | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-domega@L553-L553 | ¦DE¦ and ¦(DE)^T¦ bounds
EDGE: K:bp:p2:constants | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-domega@L553-L555 | definition of m
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-I-p1+sol-delta-I-amend
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_geo_red_domega (KAM/Iso/Linear/FullRangeStepsFrame.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:geo-red-ered
KIND: step
TITLE: Bound on $E_{\mathrm{red}}$
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-ered@L558-L559
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-ered@L558-L559
CONTRACT_ID: stepI:p1:geo-red-ered
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hypotheses of geometry-noA5 (no torsion condition, no A5)
SOURCE_QUANTIFIERS: delta
SOURCE_CONCLUSION: ¦E_red¦ <= C_red eps/delta = 2n(n+1) m^2 eps/delta on T_{r-delta}
CONSTANT_SCOPE: inherited constants m and C_red of K:bp:p2:constants; no new constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p1:setting#k-bridge, K:bp:p2:frame-identities, K:bp:p2:matrix, K:bp:p2:frame-basic, stepI:p1:geo-de, K:bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-ered@L559-L559 | local H, K, omega data
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-ered@L559-L559 | supplies the K standing data of frame-identities and frame-basic
EDGE: K:bp:p2:frame-identities | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-ered@L559-L559 | (e): block form of E_red
EDGE: K:bp:p2:matrix | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-ered@L559-L559 | (c): block-row norm bound
EDGE: K:bp:p2:frame-basic | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-ered@L559-L559 | (b): ¦N¦ <= m^2, ¦N^T¦ <= 2n m^2, ¦L^T¦ <= 2n m
EDGE: stepI:p1:geo-de | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-ered@L559-L559 | ¦DE¦ and ¦(DE)^T¦ bounds
EDGE: K:bp:p2:constants | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-red-ered@L559-L559 | definition of C_red and m >= 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-amend-I-p1+sol-delta-I-amend
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_geo_red_ered (KAM/Iso/Linear/FullRangeStepsFrame.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:geo-sym
KIND: step
TITLE: Lagrangian defect and symplecticity defect
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-sym@L561-L562
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-sym@L561-L562
CONTRACT_ID: stepI:p1:geo-sym
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hypotheses of geometry-noA5
SOURCE_QUANTIFIERS: delta
SOURCE_CONCLUSION: Omega_K holomorphic, 1-periodic on T_{r-delta} with avg Omega_K = 0; ¦Omega_K¦ <= C_Omega eps/(gamma delta^{kappa+1}) on T_{r-2delta}; ¦E_sym¦ <= m^2 ¦Omega_K¦
CONSTANT_SCOPE: inherited constants m, C_Omega and kappa of K:bp:p2:constants, depending only on (n,tau,M,sigma_K,sigma_B,sigma_T); no new constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:exactness, K:bp:p2:cohomological, K:bp:p2:frame-identities, bpI:p1:setting#k-bridge, bpI:p1:setting, K:bp:p2:constants, stepI:p1:geo-red
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:exactness | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-sym@L562-L562 | avg Omega_K = 0, K primary
EDGE: K:bp:p2:cohomological | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-sym@L562-L562 | (b) on T_{r-delta} with loss delta
EDGE: K:bp:p2:frame-identities | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-sym@L562-L562 | (b): E_sym = diag(Omega_K, B Omega_K B)
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-sym@L562-L562 | supplies the K standing data of exactness, cohomological, frame-identities
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-sym@L562-L562 | direct use of the local H, K, omega, domain or standing constants
EDGE: K:bp:p2:constants | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-sym@L562-L562 | definitions of m and C_Omega used in the cohomological and symplectic-defect bounds
EDGE: stepI:p1:geo-red | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:geo-sym@L562-L562 | preceding bound on d_omega Omega_K supplies the right-hand side for the cohomological a-priori estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-delta-I-a
REVIEWER: sol-delta-I-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_geo_sym (KAM/Iso/Linear/FullRangeStepsFrame.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: bpI:p1:perturbation-noA5
KIND: lemma
TITLE: Perturbation of the frame, without \Kref{bp:p2:A5}
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:perturbation-noA5@L566-L577
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#bpI:p1:perturbation-noA5@L578-L590
CONTRACT_ID: bpI:p1:perturbation-noA5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r > 0, 0 < delta <= 1, 2 delta < r, ¦omega¦ <= Theta, omega in R^n; Part 1 setting data D, H, M, n, tau (Assumption bpI:p1:setting; K, r as in this lemma); K holomorphic on T_r with B_beta(K(theta)) subset D, ¦DK¦ <= sigma_K, det G != 0, ¦B¦ <= sigma_B on T_r; K~ holomorphic on T_r with ¦K~ - K¦ <= d on T_r, d < beta, 2 m C_{DeltaT} d/delta^2 <= 1
SOURCE_QUANTIFIERS: setting data, r, delta, omega, K, beta, sigma_K, sigma_B, K~, d; then claims (a)-(e)
SOURCE_CONCLUSION: (a) B_{beta-d}(K~(theta)) subset D on T_r and ¦A~ - A¦ <= m d; (b) ¦DK~ - DK¦ <= n d/delta on T_{r-delta}; (c) det G~ != 0, ¦B~¦ <= 2m, ¦B~ - B¦ <= C_B d/delta on T_{r-delta}; (d) ¦N~ - N¦ <= C_{DeltaN} d/delta, ¦N~¦ <= 2 m^2, ¦N~^T¦ <= 4n m^2 on T_{r-delta}; (e) ¦T~ - T¦ <= C_{DeltaT} d/delta^2 on T_{r-2delta} (T~ the torsion of K~ for the same omega)
CONSTANT_SCOPE: m, Theta, C_B, C_{DeltaN}, C_{DeltaT} are the constants of K:bp:p2:constants (dependence on n, tau, M, sigma_K, sigma_B, sigma_T as there); no new constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p1:setting#k-bridge, K:bp:p2:constants, stepI:p1:pt-small, stepI:p1:pt-domain, stepI:p1:pt-frame, stepI:p1:pt-torsion
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:perturbation-noA5@L567-L567 | D, H, M, n, tau from the setting
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:perturbation-noA5@L567-L567 | K Part 2 results applied with h := H
EDGE: K:bp:p2:constants | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:perturbation-noA5@L568-L568 | m, Theta, C_{DeltaT}, C_B, C_{DeltaN}
EDGE: stepI:p1:pt-small | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:perturbation-noA5@L579-L579 | proof step
EDGE: stepI:p1:pt-domain | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:perturbation-noA5@L582-L582 | proof step
EDGE: stepI:p1:pt-frame | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:perturbation-noA5@L584-L584 | proof step
EDGE: stepI:p1:pt-torsion | blueprint-I/parts/p1-iso-linear.tex#bpI:p1:perturbation-noA5@L586-L586 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.AnyOmega.perturbation_noA5_anyOmega_src (KAM/Iso/Linear/FullRangeAnyOmega.lean)
LEAN_NOTE: GAP-I1c audit 2 PASS WITH NOTES; literal SettingSrc (tau>=0), arbitrary tested omega with |omega|<=Theta (ruling 05:10, free omega literal)
NOTE: -

NODE: stepI:p1:pt-small
KIND: step
TITLE: Smallness
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-small@L579-L581
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-small@L579-L581
CONTRACT_ID: stepI:p1:pt-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hypotheses of perturbation-noA5
SOURCE_QUANTIFIERS: delta, d
SOURCE_CONCLUSION: C_{DeltaT} >= max{n, C_G, C_{DeltaN}}; n d/delta <= m, m C_G d/delta <= 1/2, C_{DeltaN} d/delta <= m^2, m C_{DeltaT} d/delta^2 <= 1/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:constants, K:step:p2:pt-small, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:constants | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-small@L580-L580 | definitions of the constants
EDGE: K:step:p2:pt-small | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-small@L580-L580 | same arithmetic on constants
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-small@L580-L580 | direct use of the local H, K, omega, domain or standing constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_pt_small (KAM/Iso/Linear/FullRangeStepsPert.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:pt-domain
KIND: step
TITLE: Domain
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-domain@L582-L583
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-domain@L582-L583
CONTRACT_ID: stepI:p1:pt-domain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hypotheses of perturbation-noA5
SOURCE_QUANTIFIERS: theta, z
SOURCE_CONCLUSION: B_{beta-d}(K~(theta)) subset B_beta(K(theta)) subset D; ¦A~ - A¦ <= M d <= m d
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, K:bp:p2:hamiltonian, bpI:p1:setting#k-bridge
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-domain@L583-L583 | D open domain of H, M from the setting
EDGE: K:bp:p2:hamiltonian | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-domain@L583-L583 | (e): Lipschitz bound for DX_h
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-domain@L583-L583 | supplies the K standing data of the Hamiltonian lemma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1
REVIEWER: sol-review-I-p1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_pt_domain (KAM/Iso/Linear/FullRangeStepsPert.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:pt-frame
KIND: step
TITLE: Frame
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-frame@L584-L585
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-frame@L584-L585
CONTRACT_ID: stepI:p1:pt-frame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hypotheses of perturbation-noA5
SOURCE_QUANTIFIERS: theta
SOURCE_CONCLUSION: ¦L~ - L¦ <= n d/delta, ¦(L~-L)^T¦ <= 2n d/delta on T_{r-delta}; ¦L~¦ <= 2m, ¦L~^T¦ <= 4n m; G~ invertible, ¦B~¦ <= 2m, ¦B~ - B¦ <= C_B d/delta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:cauchy-strip, K:bp:p1:cauchy-corollaries, K:bp:p1:neumann, stepI:p1:pt-small, bpI:p1:setting, K:bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:cauchy-strip | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-frame@L585-L585 | Cauchy estimate for K~ - K
EDGE: K:bp:p1:cauchy-corollaries | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-frame@L585-L585 | transpose bound (p = 2n)
EDGE: K:bp:p1:neumann | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-frame@L585-L585 | Neumann series for G~
EDGE: stepI:p1:pt-small | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-frame@L585-L585 | smallness n d/delta <= m, m C_G d/delta <= 1/2
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-frame@L585-L585 | direct use of the local H, K, omega, domain or standing constants
EDGE: K:bp:p2:constants | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-frame@L585-L585 | definitions of C_G, C_B and m
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_pt_frame (KAM/Iso/Linear/FullRangeStepsPert.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:pt-torsion
KIND: step
TITLE: Normal frame and torsion
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-torsion@L586-L589
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-torsion@L586-L589
CONTRACT_ID: stepI:p1:pt-torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hypotheses of perturbation-noA5
SOURCE_QUANTIFIERS: theta
SOURCE_CONCLUSION: ¦N~ - N¦ <= C_{DeltaN} d/delta, ¦N~¦ <= 2 m^2, ¦N~^T¦ <= 4n m^2 on T_{r-delta}; ¦X~_{N~} - X_N¦ <= C_{DeltaX} d/delta^2 and ¦T~ - T¦ <= C_{DeltaT} d/delta^2 on T_{r-2delta}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:pt-frame, stepI:p1:pt-domain, K:bp:p1:cauchy-corollaries, K:bp:p2:objects, K:bp:p2:frame-basic, K:bp:p2:admissible, bpI:p1:setting#k-bridge, K:bp:p2:constants, bpI:p1:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:pt-frame | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-torsion@L587-L587 | L~, B~ bounds for N~ - N
EDGE: stepI:p1:pt-domain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-torsion@L588-L588 | ¦A~ - A¦
EDGE: K:bp:p1:cauchy-corollaries | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-torsion@L588-L588 | bound on d_omega(N~ - N)
EDGE: K:bp:p2:objects | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-torsion@L588-L588 | X_N and T definitions
EDGE: K:bp:p2:frame-basic | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-torsion@L589-L589 | (d): ¦X_N¦ <= C_X/delta
EDGE: K:bp:p2:admissible | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-torsion@L589-L589 | frame-basic hypotheses (A2)-(A4) are supplied by the hypotheses of this lemma
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-torsion@L589-L589 | supplies the K standing data of frame-basic
EDGE: K:bp:p2:constants | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-torsion@L588-L588 | constants C_{DeltaX}, C_{DeltaT}
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:pt-torsion@L587-L587 | direct use of the local H, K, omega, domain or standing constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p1+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_pt_torsion (KAM/Iso/Linear/FullRangeStepsPert.lean)
LEAN_NOTE: GAP-I1b audit 1 PASS
NOTE: -

NODE: stepI:p1:ea-avg#exactness-route
KIND: route
TITLE: Averages via exactness
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#exactness-route@L317-L319
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#exactness-route@L317-L319
CONTRACT_ID: stepI:p1:ea-avg#exactness-route
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0 where eta^N is used
SOURCE_QUANTIFIERS: l
SOURCE_CONCLUSION: avg(D(H o K)) = 0, avg(Omega_K) = 0, avg(eta^N) = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, stepI:p1:ea-chain, K:bp:p2:averages, K:bp:p2:exactness, bpI:p1:setting#k-bridge
ROUTES: -
ROUTE_FOR: stepI:p1:ea-avg
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#exactness-route@L317-L317 | standing H, K and omega
EDGE: stepI:p1:ea-chain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#exactness-route@L317-L317 | H o K holomorphic and periodic
EDGE: K:bp:p2:averages | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#exactness-route@L318-L318 | zero average of derivatives
EDGE: K:bp:p2:exactness | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#exactness-route@L318-L318 | zero averaged Omega_K and eta^N
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#exactness-route@L318-L318 | K data for exactness
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Linear.step_ea_avg (KAM/Iso/Linear/FullRangeStepsEnergy.lean)
LEAN_NOTE: route closes with ea-avg (GAP-I1b audit 1 PASS)
NOTE: Alternative source route; requires independent delta review. Exactness supplies both avg Omega_K = 0 and avg eta^N = 0.

NODE: stepI:p1:ea-avg#gradient-route
KIND: route
TITLE: Averages via gradient identity
STATEMENT_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#gradient-route@L317-L319
PROOF_SOURCE: blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#gradient-route@L317-L319
CONTRACT_ID: stepI:p1:ea-avg#gradient-route
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting; det G_K != 0 where eta^N is used
SOURCE_QUANTIFIERS: l
SOURCE_CONCLUSION: avg(D(H o K)) = 0, avg(Omega_K) = 0, avg(eta^N) = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, stepI:p1:ea-chain, K:bp:p2:averages, K:bp:p2:exactness, bpI:p1:setting#k-bridge, stepI:p1:ea-gradient
ROUTES: -
ROUTE_FOR: stepI:p1:ea-avg
EDGE: bpI:p1:setting | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#gradient-route@L317-L317 | standing H, K and omega
EDGE: stepI:p1:ea-chain | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#gradient-route@L317-L317 | H o K holomorphic and periodic
EDGE: K:bp:p2:averages | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#gradient-route@L318-L318 | zero average of derivatives
EDGE: K:bp:p2:exactness | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#gradient-route@L318-L318 | zero averaged Omega_K
EDGE: bpI:p1:setting#k-bridge | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#gradient-route@L318-L318 | K data for exactness
EDGE: stepI:p1:ea-gradient | blueprint-I/parts/p1-iso-linear.tex#stepI:p1:ea-avg#gradient-route@L319-L319 | average the identity (c) to deduce avg eta^N = 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-I-p1
REVIEWER: sol-delta-I-a
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27, track-I gap survey GAP-PLAN-I item 3): alternative route; ea-avg closes via its exactness route
NOTE: Alternative source route; requires independent delta review. Exactness supplies avg Omega_K = 0; (c) supplies avg eta^N = 0.
