# Proof dependency database

GRAPH_VERSION: 4
ROOTS: bpI:p0:g1, bpI:p0:head, bpI:p0:kepler, bpI:p0:r3bp
CORPUS: blueprint-I/parts/{p0-conventions,p1-iso-linear,p2-iso-iteration,p3-iso-local-charts,p5-confinement,p6-kepler,p7-delaunay,p8-r3bp}.tex pinned by SHA-256 in docs/graph/I/CORPUS.sha256 (KAM-inp branch inp, blueprint-I after fe7e4a5, 2026-10-27); imported-node locators point into blueprint/ and blueprint-N/ files pinned in docs/graph/I/IMPORTS.sha256
CONVENTIONS: docs/graph/I/SPEC.md "Conventions to watch": 1-periodic angles, averages over [0,1]^n; max norms on R^m, C^m and products, row-sum operator norms in (I7)-(I8); Euclidean rad only in I-R3BP; angles-first (theta,I) in I-G1/I-HEAD vs position-first (q,p) in I-R3BP; isoenergetic ray omega = s omega*, 1 < s < sigma_omega, Diophantine condition on omega*; nu = endpoint margin of the segment relative to the line R omega*; energy row DH(K)N of the extended torsion (omega^T only on invariant tori); C1,C2,C3 of I-G1 chosen after (n,tau,rho,rho_inf,M,sigma_K,sigma_B,sigma_T,mu,gammabar,sigma_omega,nu,omega*) and before (D,H,K,s,gamma,e,E0); (O3) pointwise; eps = 0 allowed in I-HEAD, eps0 depends on (B,s0,r0,h,B',eta) only; mu in [0,mu0) with 0 < mu0 <= 1/2 in I-R3BP, mu0,d,R depend on a+-,e+- only; HL19 signs (L_omega = -d_omega, R_omega = -R); 2pi-periodic Delaunay angles vs period one
STANDING_ASSUMPTIONS: -
EXTERNAL_POLICY: track-I external inputs are the labelled items of the parts' external-fact lists (bpI:p1:ext-*, bpI:p3:ext-*, bpI:p5:ext-*, bpI:p7:x-*, bpI:p8:x-*; an item that only restates another external or points to a proved result is excluded as an alias); every result of another track's blueprint cited by \Kref or \Nref is an IMPORTED node K:<label> or N:<label> (plus the two authorized track-P definition imports P:bpP:p0:fixedsol#IsFixedSolution, P:bpP:p0:newton#IsNewtonSolution, SPEC revision G05) (KIND external, LEAN_STATUS EXTERNAL, STATEMENT_SOURCE in the owning blueprint, NOTE IMPORTED: proved in the track-K (resp. N) graph, node <label>; shared Lean provider), K's Mathlib-level externals included (K:bp:p1:ext-*); any other unproved fact is a step node with NOTE SOURCE_GAP
FROZEN_ANCHORS: bpI:p0:domains#complexStrip, bpI:p0:domains#actionNbhd, bpI:p0:diophantine#IsDiophantine, bpI:p0:hamiltonian#hamiltonianVectorField, bpI:p0:hamiltonian#hamiltonianVectorFieldC, bpI:p0:realham#realHamiltonian, bpI:p0:realham#frequencyMap, bpI:p0:stripdata#IsPrimaryOnStrip, bpI:p0:stripdata#IsRealOnReals, bpI:p0:stripdata#dotC, bpI:p0:stripdata#omegaZero, bpI:p0:stripdata#invarianceError, bpI:p0:stripdata#gramMatrix, bpI:p0:stripdata#normalFrame, bpI:p0:stripdata#torsion, bpI:p0:extended#energyAverage, bpI:p0:extended#extendedTorsion, bpI:p0:extended#extendedTorsionAverage, bpI:p0:bordered#borderedHessian, bpI:p0:hamsol#IsHamiltonianSolutionOn, bpI:p0:primaries#radiusSq, bpI:p0:primaries#radius, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2, bpI:p0:primaries#CollisionFree, bpI:p0:restricted#restrictedHamiltonian, bpI:p0:restricted#restrictedVectorField, bpI:p0:restricted#IsRestrictedSolutionOn, bpI:p0:nearcircular#NearCircular, bpI:p0:keplerborder#keplerBorder, bpI:p0:g1, bpI:p0:head, bpI:p0:kepler, bpI:p0:r3bp
FROZEN_MANIFEST: manifest/frozen-anchors.json | sha256:72c4edf1cb8c091083d8e0f3064d32831a311c5cb26a43ad200b3b6dac4131a8
WRITER: claude-suborch-INP
GLOBAL_REVIEWER: sol-global-I
GLOBAL_REVIEW_REF: docs/graph/I/reviews/GLOBAL-review-3.md

The dependency direction is `NODE -> prerequisite`. Node blocks are assembled from `docs/graph/I/packets/<slice>.nodes.md`; edit those, then re-run `inp_depgraph_assemble.py` (orchestrator-tools).

## Nodes

NODE: bpI:p0:domains#complexStrip
KIND: definition
TITLE: Strip, action neighbourhood: KAM.complexStrip
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:domains@L41-L47
PROOF_SOURCE: -
CONTRACT_ID: kam.complexStrip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: n in N, rho in R
SOURCE_QUANTIFIERS: n, rho
SOURCE_CONCLUSION: defines T_rho = {theta in C^n : for all i, ¦Im theta_i¦ < rho} (KAM.complexStrip n rho)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/ComplexStrip.lean
FROZEN_DECL: KAM.complexStrip
FROZEN_ANCHOR_ID: kam.complexStrip.v1
FROZEN_ABI_SHA256: 91cedb11be4f33139d30fcc5103f7ed5370fa5d89a68f9a3aaf0b061ae2920e7
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.complexStrip (KAM/Frozen/Defs/ComplexStrip.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:domains#actionNbhd
KIND: definition
TITLE: Strip, action neighbourhood: KAM.actionNbhd
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:domains@L41-L47
PROOF_SOURCE: -
CONTRACT_ID: kam.actionNbhd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: B subset R^n, r in R
SOURCE_QUANTIFIERS: B, r
SOURCE_CONCLUSION: defines B_r = {I in C^n : exists J in B, max-norm ¦I-J¦ < r} (KAM.actionNbhd); for real I, I in B_r iff exists J in B with ¦I-J¦ < r
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/ActionNbhd.lean
FROZEN_DECL: KAM.actionNbhd
FROZEN_ANCHOR_ID: kam.actionNbhd.v1
FROZEN_ABI_SHA256: b05e2aeddf393c0b232bd809f64d9d8040e0fdf54248c4f880ab1ad98c040f21
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0+sol-review-I-p0
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.actionNbhd (KAM/Frozen/Defs/ActionNbhd.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:diophantine#IsDiophantine
KIND: definition
TITLE: Diophantine vectors: KAM.IsDiophantine
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:diophantine@L49-L54
PROOF_SOURCE: -
CONTRACT_ID: kam.IsDiophantine
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: gamma, tau in R, omega in R^n
SOURCE_QUANTIFIERS: gamma, tau, omega
SOURCE_CONCLUSION: defines (gamma,tau)-Diophantine: for every k in Z^n minus {0}, gamma/(sum_i ¦k_i¦)^tau <= ¦k.omega¦ (real power)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/IsDiophantine.lean
FROZEN_DECL: KAM.IsDiophantine
FROZEN_ANCHOR_ID: kam.IsDiophantine.v1
FROZEN_ABI_SHA256: 24a486c6ccc5648791465ec3577c2e37fd464ecaec8f0dab9c74a5588535e717
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.IsDiophantine (KAM/Frozen/Defs/IsDiophantine.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:hamiltonian#hamiltonianVectorField
KIND: definition
TITLE: Hamiltonian vector fields: KAM.hamiltonianVectorField
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:hamiltonian@L56-L63
PROOF_SOURCE: -
CONTRACT_ID: kam.hamiltonianVectorField
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: H : R^n x R^n -> R; z a real phase point
SOURCE_QUANTIFIERS: H, z
SOURCE_CONCLUSION: defines X_H(z) = (i -> DH(z)(0,e_i), i -> -DH(z)(e_i,0)) with D the real Frechet derivative
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/HamiltonianVectorField.lean
FROZEN_DECL: KAM.hamiltonianVectorField
FROZEN_ANCHOR_ID: kam.hamiltonianVectorField.v1
FROZEN_ABI_SHA256: 427a145572df4c3e14079cf88feb16d60e1cd92fcd1770faddd36ad706562ca6
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.hamiltonianVectorField (KAM/Frozen/Defs/HamiltonianVectorField.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:hamiltonian#hamiltonianVectorFieldC
KIND: definition
TITLE: Hamiltonian vector fields: KAM.hamiltonianVectorFieldℂ
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:hamiltonian@L56-L63
PROOF_SOURCE: -
CONTRACT_ID: kam.hamiltonianVectorFieldℂ
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: H : C^n x C^n -> C
SOURCE_QUANTIFIERS: H, z
SOURCE_CONCLUSION: defines X_H : C^n x C^n -> C^n x C^n by the same formula with the complex derivative; X_H = (d_I H, -d_theta H)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/HamiltonianVectorFieldC.lean
FROZEN_DECL: KAM.hamiltonianVectorFieldℂ
FROZEN_ANCHOR_ID: kam.hamiltonianVectorFieldℂ.v1
FROZEN_ABI_SHA256: 482764b7e8e1691b3c3c182bca9b959f0d657e126c6b21b837ff0516f91e4f0d
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.hamiltonianVectorFieldℂ (KAM/Frozen/Defs/HamiltonianVectorFieldC.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:realham#realHamiltonian
KIND: definition
TITLE: Real Hamiltonian, frequency map: KAM.realHamiltonian
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:realham@L65-L72
PROOF_SOURCE: -
CONTRACT_ID: kam.realHamiltonian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: h : C^n -> C, f : C^n x C^n -> C; (theta,I) a real phase point
SOURCE_QUANTIFIERS: h, f, (theta,I)
SOURCE_CONCLUSION: defines Ham_{h,f}(theta,I) = Re(h(I) + f(theta,I))
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/RealHamiltonian.lean
FROZEN_DECL: KAM.realHamiltonian
FROZEN_ANCHOR_ID: kam.realHamiltonian.v1
FROZEN_ABI_SHA256: ea510392f643a3fce65df6d4bc826d902d7b2277f67b0c009e3522d5659a0fab
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.realHamiltonian (KAM/Frozen/Defs/RealHamiltonian.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:realham#frequencyMap
KIND: definition
TITLE: Real Hamiltonian, frequency map: KAM.frequencyMap
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:realham@L65-L72
PROOF_SOURCE: -
CONTRACT_ID: kam.frequencyMap
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: h : C^n -> C, I in R^n
SOURCE_QUANTIFIERS: h, I
SOURCE_CONCLUSION: defines the frequency map grad h(I)_i = D(J -> Re h(J))(I) e_i, a real function R^n -> R^n
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/FrequencyMap.lean
FROZEN_DECL: KAM.frequencyMap
FROZEN_ANCHOR_ID: kam.frequencyMap.v1
FROZEN_ABI_SHA256: c9326077b299282bff92fdb8a3a849f512167fd4dc8e859bb0fdf1662f525cc5
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.frequencyMap (KAM/Frozen/Defs/FrequencyMap.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:stripdata#IsPrimaryOnStrip
KIND: definition
TITLE: Torus data on strips: KAM.IsPrimaryOnStrip
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L74-L92
PROOF_SOURCE: -
CONTRACT_ID: kam.IsPrimaryOnStrip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: K : C^n -> C^n x C^n, rho
SOURCE_QUANTIFIERS: K, rho
SOURCE_CONCLUSION: defines K primary on T_rho: K(theta+k) = K(theta) + (k,0) for theta in T_rho, k in Z^n
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/IsPrimaryOnStrip.lean
FROZEN_DECL: KAM.IsPrimaryOnStrip
FROZEN_ANCHOR_ID: kam.IsPrimaryOnStrip.v1
FROZEN_ABI_SHA256: 3e3ec50a4ddc91e4ce8c9cc082a1bfb7387ad08b9dba70baed76847df2f86680
DEPS: bpI:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:domains#complexStrip | blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L77-L77 | strip T_rho
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.IsPrimaryOnStrip (KAM/Frozen/Defs/IsPrimaryOnStrip.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:stripdata#IsRealOnReals
KIND: definition
TITLE: Torus data on strips: KAM.IsRealOnReals
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L74-L92
PROOF_SOURCE: -
CONTRACT_ID: kam.IsRealOnReals
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: K : C^n -> C^n x C^n
SOURCE_QUANTIFIERS: K
SOURCE_CONCLUSION: defines K real on reals: every K(theta), theta in R^n, is a real phase point
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/IsRealOnReals.lean
FROZEN_DECL: KAM.IsRealOnReals
FROZEN_ANCHOR_ID: kam.IsRealOnReals.v1
FROZEN_ABI_SHA256: 6549c22016139f44ca97ba901aa4927905970838ce283fef53b30c223dfabbb5
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.IsRealOnReals (KAM/Frozen/Defs/IsRealOnReals.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:stripdata#dotC
KIND: definition
TITLE: Torus data on strips: KAM.dotℂ
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L74-L92
PROOF_SOURCE: -
CONTRACT_ID: kam.dotℂ
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: u, v in C^n x C^n
SOURCE_QUANTIFIERS: u, v
SOURCE_CONCLUSION: defines the bilinear dot product u.v = sum_i (u_{1,i} v_{1,i} + u_{2,i} v_{2,i}) on C^n x C^n
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/DotC.lean
FROZEN_DECL: KAM.dotℂ
FROZEN_ANCHOR_ID: kam.dotℂ.v1
FROZEN_ABI_SHA256: 6d938a769932067b5668f7e0b3bb92a62331b9be8f6a13b7a625af3b5eed362b
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.dotℂ (KAM/Frozen/Defs/DotC.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:stripdata#omegaZero
KIND: definition
TITLE: Torus data on strips: KAM.omegaZero
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L74-L92
PROOF_SOURCE: -
CONTRACT_ID: kam.omegaZero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: (a,b) in C^n x C^n
SOURCE_QUANTIFIERS: a, b
SOURCE_CONCLUSION: defines Omega_0(a,b) = (-b,a)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/OmegaZero.lean
FROZEN_DECL: KAM.omegaZero
FROZEN_ANCHOR_ID: kam.omegaZero.v1
FROZEN_ABI_SHA256: 32a39d2730c3b399c1bb81f1b709931dbdea47635807e8036db3b25116ef457b
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.omegaZero (KAM/Frozen/Defs/OmegaZero.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:stripdata#invarianceError
KIND: definition
TITLE: Torus data on strips: KAM.invarianceError
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L74-L92
PROOF_SOURCE: -
CONTRACT_ID: kam.invarianceError
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: H : C^n x C^n -> C, K : C^n -> C^n x C^n, omega in R^n, theta in C^n
SOURCE_QUANTIFIERS: H, K, omega, theta
SOURCE_CONCLUSION: defines E_{H,K,omega}(theta) = X_H(K(theta)) - DK(theta) omega
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/InvarianceError.lean
FROZEN_DECL: KAM.invarianceError
FROZEN_ANCHOR_ID: kam.invarianceError.v1
FROZEN_ABI_SHA256: 775e46d01cc020277055f39825a2dbea7f42d822652ba4c92b95c3159fc0a273
DEPS: bpI:p0:hamiltonian#hamiltonianVectorFieldC
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:hamiltonian#hamiltonianVectorFieldC | blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L82-L82 | X_H(K(theta)) with complex H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.invarianceError (KAM/Frozen/Defs/InvarianceError.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:stripdata#gramMatrix
KIND: definition
TITLE: Torus data on strips: KAM.gramMatrix
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L74-L92
PROOF_SOURCE: -
CONTRACT_ID: kam.gramMatrix
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: K : C^n -> C^n x C^n, theta in C^n; no invertibility premise
SOURCE_QUANTIFIERS: K, theta
SOURCE_CONCLUSION: defines the complex n x n Gram matrix G_K(theta)_ij = DK(theta)e_i . DK(theta)e_j
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/GramMatrix.lean
FROZEN_DECL: KAM.gramMatrix
FROZEN_ANCHOR_ID: kam.gramMatrix.v1
FROZEN_ABI_SHA256: 3990b90567c6199a3443b1021021aab73e8e5b521b377b96f62981c2b57834ef
DEPS: bpI:p0:stripdata#dotC
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:stripdata#dotC | blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L83-L83 | entries are bilinear dot products DK e_i . DK e_j
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.gramMatrix (KAM/Frozen/Defs/GramMatrix.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:stripdata#normalFrame
KIND: definition
TITLE: Torus data on strips: KAM.normalFrame
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L74-L92
PROOF_SOURCE: -
CONTRACT_ID: kam.normalFrame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: K, theta; no invertibility premise (matrix inverse of Lean, total)
SOURCE_QUANTIFIERS: K, theta
SOURCE_CONCLUSION: defines N_K(theta)_{.j} = sum_k (G_K^{-1})_{kj} Omega_0(DK(theta)e_k) in C^n x C^n
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/NormalFrame.lean
FROZEN_DECL: KAM.normalFrame
FROZEN_ANCHOR_ID: kam.normalFrame.v1
FROZEN_ABI_SHA256: 86b86c14c2624b16a514c56a00d7ae7b1798ef789d9f1556d2a2c2ac8c4af95b
DEPS: bpI:p0:stripdata#gramMatrix, bpI:p0:stripdata#omegaZero
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:stripdata#gramMatrix | blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L84-L84 | inverse of the Gram matrix
EDGE: bpI:p0:stripdata#omegaZero | blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L84-L84 | Omega_0(DK e_k)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.normalFrame (KAM/Frozen/Defs/NormalFrame.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:stripdata#torsion
KIND: definition
TITLE: Torus data on strips: KAM.torsion
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L74-L92
PROOF_SOURCE: -
CONTRACT_ID: kam.torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: H : C^n x C^n -> C, K, omega in R^n, theta; N the normal frame
SOURCE_QUANTIFIERS: H, K, omega, theta
SOURCE_CONCLUSION: defines T_{H,K,omega}(theta)_ij = N_{.i}.Omega_0(DX_H(K(theta))N_{.j} - D_theta(N_{.j})(theta) omega)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/Torsion.lean
FROZEN_DECL: KAM.torsion
FROZEN_ANCHOR_ID: kam.torsion.v1
FROZEN_ABI_SHA256: 6248d8a94564264c3e8525e65f1a6a645815608c795c7def60f04eea1c61a493
DEPS: bpI:p0:stripdata#normalFrame, bpI:p0:hamiltonian#hamiltonianVectorFieldC, bpI:p0:stripdata#omegaZero, bpI:p0:stripdata#dotC
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:stripdata#normalFrame | blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L86-L86 | N_{.j} the normal frame
EDGE: bpI:p0:hamiltonian#hamiltonianVectorFieldC | blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L86-L86 | DX_H(K(theta))
EDGE: bpI:p0:stripdata#omegaZero | blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L86-L86 | Omega_0 applied to the transport term
EDGE: bpI:p0:stripdata#dotC | blueprint-I/parts/p0-conventions.tex#bpI:p0:stripdata@L86-L86 | N_{.i} . Omega_0(...)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.torsion (KAM/Frozen/Defs/Torsion.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:extended#energyAverage
KIND: definition
TITLE: Energy average and extended torsion: KAM.Iso.energyAverage
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:extended@L96-L109
PROOF_SOURCE: -
CONTRACT_ID: iso.energyAverage
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: H : C^n x C^n -> C, K : C^n -> C^n x C^n; integrability not a premise (Bochner integral)
SOURCE_QUANTIFIERS: H, K
SOURCE_CONCLUSION: defines Ebar_H(K) = int_{[0,1]^n} H(K(theta)) dtheta in C, over real angles
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/EnergyAverage.lean
FROZEN_DECL: KAM.Iso.energyAverage
FROZEN_ANCHOR_ID: iso.energyAverage.v1
FROZEN_ABI_SHA256: 6ad218934c652835e712bbac7ccb96b5642ef3577ffde62883cc9c83969c7e62
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.energyAverage (KAM/Frozen/Iso/Defs/EnergyAverage.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:extended#extendedTorsion
KIND: definition
TITLE: Energy average and extended torsion: KAM.Iso.extendedTorsion
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:extended@L96-L109
PROOF_SOURCE: -
CONTRACT_ID: iso.extendedTorsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: H, K, omega in R^n, theta in C^n; index set {1..n} u {*}
SOURCE_QUANTIFIERS: H, K, omega, theta
SOURCE_CONCLUSION: defines the (n+1)x(n+1) complex matrix T_H(theta) with upper-left block T_{H,K,omega}(theta), last column (omega,0), last row b -> DH(K(theta))(N_{.b}(theta)), last entry 0
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/ExtendedTorsion.lean
FROZEN_DECL: KAM.Iso.extendedTorsion
FROZEN_ANCHOR_ID: iso.extendedTorsion.v1
FROZEN_ABI_SHA256: 7185973f29ba6605872d911458233c3707ce9d85123ecc48508c16e4afb8de64
DEPS: bpI:p0:stripdata#torsion, bpI:p0:stripdata#normalFrame
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:stripdata#torsion | blueprint-I/parts/p0-conventions.tex#bpI:p0:extended@L100-L100 | upper-left block is the torsion
EDGE: bpI:p0:stripdata#normalFrame | blueprint-I/parts/p0-conventions.tex#bpI:p0:extended@L103-L103 | last row DH(K(theta))(N_{.b}(theta))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.extendedTorsion (KAM/Frozen/Iso/Defs/ExtendedTorsion.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:extended#extendedTorsionAverage
KIND: definition
TITLE: Energy average and extended torsion: KAM.Iso.extendedTorsionAverage
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:extended@L96-L109
PROOF_SOURCE: -
CONTRACT_ID: iso.extendedTorsionAverage
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: H, K, omega in R^n
SOURCE_QUANTIFIERS: H, K, omega
SOURCE_CONCLUSION: defines avg(T_H) = (int_{[0,1]^n} T_H(theta)_ij dtheta)_ij over real angles
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/ExtendedTorsionAverage.lean
FROZEN_DECL: KAM.Iso.extendedTorsionAverage
FROZEN_ANCHOR_ID: iso.extendedTorsionAverage.v1
FROZEN_ABI_SHA256: 2ab0d434c6e68a7a98eec3a8c9ecddf7e8b428cb3cadaecfe075e6afcc30078d
DEPS: bpI:p0:extended#extendedTorsion
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:extended#extendedTorsion | blueprint-I/parts/p0-conventions.tex#bpI:p0:extended@L105-L105 | entrywise integral of T_H(theta)_ij
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.extendedTorsionAverage (KAM/Frozen/Iso/Defs/ExtendedTorsionAverage.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:bordered#borderedHessian
KIND: definition
TITLE: Bordered Hessian: KAM.Iso.borderedHessian
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:bordered@L111-L120
PROOF_SOURCE: -
CONTRACT_ID: iso.borderedHessian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: h : C^n -> C, I in R^n; no symmetry assumed
SOURCE_QUANTIFIERS: h, I
SOURCE_CONCLUSION: defines the real (n+1)x(n+1) matrix B_h(I) = [[D(grad h)(I)e_b read at a, grad h(I)],[grad h(I)^T, 0]]
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/BorderedHessian.lean
FROZEN_DECL: KAM.Iso.borderedHessian
FROZEN_ANCHOR_ID: iso.borderedHessian.v1
FROZEN_ABI_SHA256: 857bbb9d614fa8aac46b82c7c926cf5f06d676767abfe86d044ec5c6f3c26505
DEPS: bpI:p0:realham#frequencyMap
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:realham#frequencyMap | blueprint-I/parts/p0-conventions.tex#bpI:p0:bordered@L116-L116 | grad h and its real derivative
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.borderedHessian (KAM/Frozen/Iso/Defs/BorderedHessian.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:hamsol#IsHamiltonianSolutionOn
KIND: definition
TITLE: Hamiltonian solutions with action in $B$: KAM.Iso.IsHamiltonianSolutionOn
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:hamsol@L122-L128
PROOF_SOURCE: -
CONTRACT_ID: iso.IsHamiltonianSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: H : R^n x R^n -> R, B subset R^n, J subset R, z : R -> R^n x R^n
SOURCE_QUANTIFIERS: H, B, J, z
SOURCE_CONCLUSION: defines Sol(H,B,J,z): for all t in J, z(t)_2 in B, H real differentiable at z(t), and z differentiable at t with z'(t) = X_H(z(t))
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/IsHamiltonianSolutionOn.lean
FROZEN_DECL: KAM.Iso.IsHamiltonianSolutionOn
FROZEN_ANCHOR_ID: iso.IsHamiltonianSolutionOn.v1
FROZEN_ABI_SHA256: b20065362bfe0068a5eb3cfdf98a886d7ffd591bdef0464cebfbe3e171d56beb
DEPS: bpI:p0:hamiltonian#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:hamiltonian#hamiltonianVectorField | blueprint-I/parts/p0-conventions.tex#bpI:p0:hamsol@L125-L125 | z'(t) = X_H(z(t))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.IsHamiltonianSolutionOn (KAM/Frozen/Iso/Defs/IsHamiltonianSolutionOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:primaries#radiusSq
KIND: definition
TITLE: Planar Euclidean length, the primaries, collisions: KAM.Iso.radiusSq
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:primaries@L130-L137
PROOF_SOURCE: -
CONTRACT_ID: iso.radiusSq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: q in R^2
SOURCE_QUANTIFIERS: q
SOURCE_CONCLUSION: defines rho_2(q)^2 = q_0^2 + q_1^2
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/RadiusSq.lean
FROZEN_DECL: KAM.Iso.radiusSq
FROZEN_ANCHOR_ID: iso.radiusSq.v1
FROZEN_ABI_SHA256: 5311b4ff1819b9d4cf9fe59159a329131dfd4eb74ea2a6c766c1bdfe565db9f9
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.radiusSq (KAM/Frozen/Iso/Defs/RadiusSq.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:primaries#radius
KIND: definition
TITLE: Planar Euclidean length, the primaries, collisions: KAM.Iso.radius
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:primaries@L130-L137
PROOF_SOURCE: -
CONTRACT_ID: iso.radius
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: q in R^2
SOURCE_QUANTIFIERS: q
SOURCE_CONCLUSION: defines rad(q) = sqrt(q_0^2 + q_1^2) (Euclidean length; radicand nonnegative)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/Radius.lean
FROZEN_DECL: KAM.Iso.radius
FROZEN_ANCHOR_ID: iso.radius.v1
FROZEN_ABI_SHA256: dd2efadd1fe6f1ec3222a177bb283bbe5f17c657bdbf78d4d1cceaa8c5d7c3d1
DEPS: bpI:p0:primaries#radiusSq
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:primaries#radiusSq | blueprint-I/parts/p0-conventions.tex#bpI:p0:primaries@L131-L131 | rad(q) = sqrt of rho_2(q)^2 (the radicand q_0^2+q_1^2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.radius (KAM/Frozen/Iso/Defs/Radius.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:primaries#primary1
KIND: definition
TITLE: Planar Euclidean length, the primaries, collisions: KAM.Iso.primary₁
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:primaries@L130-L137
PROOF_SOURCE: -
CONTRACT_ID: iso.primary₁
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: mu in R
SOURCE_QUANTIFIERS: mu
SOURCE_CONCLUSION: defines a_1(mu) = (-mu,0)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/Primary1.lean
FROZEN_DECL: KAM.Iso.primary₁
FROZEN_ANCHOR_ID: iso.primary₁.v1
FROZEN_ABI_SHA256: ec076b67ffb8c1136b924761bb31caffa4832b565b5916e98e835b8d9b1b10b1
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.primary₁ (KAM/Frozen/Iso/Defs/Primary1.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:primaries#primary2
KIND: definition
TITLE: Planar Euclidean length, the primaries, collisions: KAM.Iso.primary₂
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:primaries@L130-L137
PROOF_SOURCE: -
CONTRACT_ID: iso.primary₂
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: mu in R
SOURCE_QUANTIFIERS: mu
SOURCE_CONCLUSION: defines a_2(mu) = (1-mu,0)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/Primary2.lean
FROZEN_DECL: KAM.Iso.primary₂
FROZEN_ANCHOR_ID: iso.primary₂.v1
FROZEN_ABI_SHA256: ec66ea6ca9c04594189612b9f1dd30eb5c3291cf557af7e90456eba543870c35
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.primary₂ (KAM/Frozen/Iso/Defs/Primary2.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:primaries#CollisionFree
KIND: definition
TITLE: Planar Euclidean length, the primaries, collisions: KAM.Iso.CollisionFree
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:primaries@L130-L137
PROOF_SOURCE: -
CONTRACT_ID: iso.CollisionFree
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: mu in R, z = (q,p) in R^2 x R^2
SOURCE_QUANTIFIERS: mu, z
SOURCE_CONCLUSION: defines collision free: rad(q - a_1(mu)) > 0 and rad(q - a_2(mu)) > 0
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/CollisionFree.lean
FROZEN_DECL: KAM.Iso.CollisionFree
FROZEN_ANCHOR_ID: iso.CollisionFree.v1
FROZEN_ABI_SHA256: 061864862ec1f1c151c4b7bed8e0df1036987b15191542347bfe50a94263ad10
DEPS: bpI:p0:primaries#radius, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p0-conventions.tex#bpI:p0:primaries@L134-L134 | rad(q - a_j(mu)) > 0
EDGE: bpI:p0:primaries#primary1 | blueprint-I/parts/p0-conventions.tex#bpI:p0:primaries@L134-L134 | a_1(mu)
EDGE: bpI:p0:primaries#primary2 | blueprint-I/parts/p0-conventions.tex#bpI:p0:primaries@L134-L134 | a_2(mu)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.CollisionFree (KAM/Frozen/Iso/Defs/CollisionFree.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:restricted#restrictedHamiltonian
KIND: definition
TITLE: Restricted Hamiltonian and field: KAM.Iso.restrictedHamiltonian
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L139-L153
PROOF_SOURCE: -
CONTRACT_ID: iso.restrictedHamiltonian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: mu, z = (q,p) collision free; r_j = rad(q - a_j(mu))
SOURCE_QUANTIFIERS: mu, z
SOURCE_CONCLUSION: defines Ham^R3_mu(q,p) = ¦p¦_2^2/2 + q_1 p_0 - q_0 p_1 - (1-mu)/r_1 - mu/r_2
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/RestrictedHamiltonian.lean
FROZEN_DECL: KAM.Iso.restrictedHamiltonian
FROZEN_ANCHOR_ID: iso.restrictedHamiltonian.v1
FROZEN_ABI_SHA256: cb461337f8575c139de5daa594ad98c79c78610a0b84977605a40e168c2365c3
DEPS: bpI:p0:primaries#radius, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2, bpI:p0:primaries#CollisionFree, bpI:p0:primaries#radiusSq
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L140-L140 | r_j = rad(q - a_j(mu))
EDGE: bpI:p0:primaries#primary1 | blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L140-L140 | a_1(mu)
EDGE: bpI:p0:primaries#primary2 | blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L140-L140 | a_2(mu)
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L140-L140 | defined on collision-free points
EDGE: bpI:p0:primaries#radiusSq | blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L142-L142 | ¦p¦_2^2 = p_0^2+p_1^2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0+sol-review-I-p0
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.restrictedHamiltonian (KAM/Frozen/Iso/Defs/RestrictedHamiltonian.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:restricted#restrictedVectorField
KIND: definition
TITLE: Restricted Hamiltonian and field: KAM.Iso.restrictedVectorField
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L139-L153
PROOF_SOURCE: -
CONTRACT_ID: iso.restrictedVectorField
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: mu, z = (q,p) collision free
SOURCE_QUANTIFIERS: mu, z
SOURCE_CONCLUSION: defines V_mu(q,p) = ((p_0+q_1, p_1-q_0), (p_1,-p_0) - (1-mu)/r_1^3 (q-a_1) - mu/r_2^3 (q-a_2))
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/RestrictedVectorField.lean
FROZEN_DECL: KAM.Iso.restrictedVectorField
FROZEN_ANCHOR_ID: iso.restrictedVectorField.v1
FROZEN_ABI_SHA256: 7f23620e590d0b874e5e94198c0e04331fa179347cb63925313f28703115520a
DEPS: bpI:p0:primaries#radius, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2, bpI:p0:primaries#CollisionFree
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L140-L140 | r_j = rad(q - a_j(mu))
EDGE: bpI:p0:primaries#primary1 | blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L140-L140 | a_1(mu)
EDGE: bpI:p0:primaries#primary2 | blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L140-L140 | a_2(mu)
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L140-L140 | defined on collision-free points
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0+sol-review-I-p0
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.restrictedVectorField (KAM/Frozen/Iso/Defs/RestrictedVectorField.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:restricted#IsRestrictedSolutionOn
KIND: definition
TITLE: Restricted Hamiltonian and field: KAM.Iso.IsRestrictedSolutionOn
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L139-L153
PROOF_SOURCE: -
CONTRACT_ID: iso.IsRestrictedSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: mu in R, J subset R, z : R -> R^2 x R^2
SOURCE_QUANTIFIERS: mu, J, z
SOURCE_CONCLUSION: defines RSol_mu(J,z): for every t in J, z(t) is collision free and z is differentiable at t with z'(t) = V_mu(z(t))
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/IsRestrictedSolutionOn.lean
FROZEN_DECL: KAM.Iso.IsRestrictedSolutionOn
FROZEN_ANCHOR_ID: iso.IsRestrictedSolutionOn.v1
FROZEN_ABI_SHA256: f8e83a3360d7b983683d6d48e29e232ef15fc8c7a9546eede0512d09d6a00059
DEPS: bpI:p0:primaries#CollisionFree, bpI:p0:restricted#restrictedVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L148-L148 | z(t) collision free
EDGE: bpI:p0:restricted#restrictedVectorField | blueprint-I/parts/p0-conventions.tex#bpI:p0:restricted@L148-L148 | z'(t) = V_mu(z(t))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0+sol-review-I-p0
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.IsRestrictedSolutionOn (KAM/Frozen/Iso/Defs/IsRestrictedSolutionOn.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:nearcircular#NearCircular
KIND: definition
TITLE: Near-circular region: KAM.Iso.NearCircular
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:nearcircular@L155-L168
PROOF_SOURCE: -
CONTRACT_ID: iso.NearCircular
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a_-, a_+, e_-, e_+ in R
SOURCE_QUANTIFIERS: a_-, a_+, e_-, e_+
SOURCE_CONCLUSION: defines N(a_-,a_+,e_-,e_+) subset R^2 x R^2: (q,p) such that exists r,a,e in R with r>0, r^2 = q_0^2+q_1^2, a>0, 0<e<1, a_-<a<a_+, e_-<e<e_+, ¦p¦_2^2/2 - 1/r = -1/(2a), q_0p_1-q_1p_0 > 0, (q_0p_1-q_1p_0)^2 = a(1-e^2)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/NearCircular.lean
FROZEN_DECL: KAM.Iso.NearCircular
FROZEN_ANCHOR_ID: iso.NearCircular.v1
FROZEN_ABI_SHA256: b0f2955780d0e1cf7caad9b8f32c05654d72320869a2c0156f3311fbfea5dbf1
DEPS: bpI:p0:primaries#radiusSq
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:primaries#radiusSq | blueprint-I/parts/p0-conventions.tex#bpI:p0:nearcircular@L159-L159 | r^2 = q_0^2+q_1^2 and ¦p¦_2^2 in the energy equation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.NearCircular (KAM/Frozen/Iso/Defs/NearCircular.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:keplerborder#keplerBorder
KIND: definition
TITLE: The Kepler bordered matrix: KAM.Iso.keplerBorder
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:keplerborder@L170-L180
PROOF_SOURCE: -
CONTRACT_ID: iso.keplerBorder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: kappa, Omega in R, L in {L in R : L>0}
SOURCE_QUANTIFIERS: kappa, Omega, L
SOURCE_CONCLUSION: defines the real 3x3 matrix K_{kappa,Omega}(L) = [[-3kappa/L^4,0,kappa/L^3],[0,0,-Omega],[kappa/L^3,-Omega,0]]
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Defs/KeplerBorder.lean
FROZEN_DECL: KAM.Iso.keplerBorder
FROZEN_ANCHOR_ID: iso.keplerBorder.v1
FROZEN_ABI_SHA256: 36e9baac00666553c4182571874d115c3f812a3679f898e30ae5679d367d4984
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.keplerBorder (KAM/Frozen/Iso/Defs/KeplerBorder.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED); formalized, nothing to prove
NOTE: -

NODE: bpI:p0:g1
KIND: theorem
TITLE: I-G1: isoenergetic a-posteriori KAM
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:g1@L215-L253
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L338-L355
CONTRACT_ID: iso.isoenergetic_kam
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 2; tau in R, tau >= n-1; rho, rho_inf in R, 0 < rho_inf < rho; M, sigma_K, sigma_B, sigma_T, mu, gammabar > 0; sigma_omega > 1; nu > 0; omega* in R^n, omega* != 0; for the inner statement: (I1) D open and Z^n-invariant in theta; (I2) H holomorphic on D and Z^n-periodic in theta on D; (I3) Im H = 0 at real phase points of D; (I4) ¦DH¦,¦X_H¦,¦D X_H¦,¦D^2 X_H¦,¦D^2 H¦ <= M on D; (I5) K holomorphic, primary and real on reals on T_rho; (I6) B_mu(K(theta)) subset D and ¦DK(theta)¦ <= sigma_K - mu on T_rho; (I7) det G_K(theta) != 0 and row-sum ¦G_K^{-1}¦ <= sigma_B - mu on T_rho; (I8) det avg(T_H) != 0 for T_H built from (H,K,s omega*), row-sum ¦avg(T_H)^{-1}¦ <= sigma_T - mu; (I9) 1 < s < sigma_omega, nu <= (s-1)¦omega*¦, nu <= (sigma_omega-s)¦omega*¦; (I10) 0 < gamma <= gammabar, omega* in Dio_{gamma,tau}, 0 <= e; (I11) ¦E_{H,K,s omega*}(theta)¦ <= e on T_rho; (I12) ¦Ebar_H(K) - E_0¦ <= e; (I13) C_1 e/(gamma^4 rho^{4 tau}) < 1
SOURCE_QUANTIFIERS: n, tau, rho, rho_inf, M, sigma_K, sigma_B, sigma_T, mu, gammabar, sigma_omega, nu, omega* fixed; then exists C_1, C_2, C_3 > 0; then for all D, H, K, s, gamma, e, E_0 satisfying (I1)-(I13); then exists K_inf, s_inf
SOURCE_CONCLUSION: (O1) K_inf holomorphic, primary and real on reals on T_rho_inf; (O2) E_{H,K_inf,s_inf omega*} = 0 on T_rho_inf; (O3) H(K_inf(theta)) = E_0 for all theta in T_rho_inf (pointwise); (O4) B_{mu/2}(K_inf(theta)) subset D and ¦DK_inf¦ <= sigma_K - mu/2 on T_rho_inf; (O5) ¦K_inf - K¦ <= C_2 e/(gamma^2 rho^{2 tau}) on T_rho_inf; (O6) ¦s_inf omega* - s omega*¦ <= C_3 e/(gamma^2 rho^{2 tau}); with 1 < s_inf < sigma_omega
CONSTANT_SCOPE: C_1, C_2, C_3 chosen after n, tau, rho, rho_inf, M, sigma_K, sigma_B, sigma_T, mu, gammabar, sigma_omega, nu, omega* and before D, H, K, s, gamma, e, E_0; may depend on the former and on none of the latter
FROZEN_FILE: KAM/Frozen/Iso/Theorems/IsoenergeticKam.lean
FROZEN_DECL: KAM.Iso.isoenergetic_kam
FROZEN_ANCHOR_ID: iso.isoenergetic_kam.v1
FROZEN_ABI_SHA256: 165645ea4aeb3d278f29d2336981a4bc924803cea8eaee49efbfca9874203b16
DEPS: bpI:p0:diophantine#IsDiophantine, bpI:p0:domains#complexStrip, bpI:p0:hamiltonian#hamiltonianVectorFieldC, bpI:p0:stripdata#IsPrimaryOnStrip, bpI:p0:stripdata#IsRealOnReals, bpI:p0:stripdata#gramMatrix, bpI:p0:extended#extendedTorsionAverage, bpI:p0:stripdata#invarianceError, bpI:p0:extended#energyAverage, bpI:p2:g1
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p0-conventions.tex#bpI:p0:g1@L232-L232 | omega* in Dio_{gamma,tau}
EDGE: bpI:p0:domains#complexStrip | blueprint-I/parts/p0-conventions.tex#bpI:p0:g1@L226-L226 | strips T_rho, T_rho_inf
EDGE: bpI:p0:hamiltonian#hamiltonianVectorFieldC | blueprint-I/parts/p0-conventions.tex#bpI:p0:g1@L224-L224 | bounds on X_H, D X_H, D^2 X_H
EDGE: bpI:p0:stripdata#IsPrimaryOnStrip | blueprint-I/parts/p0-conventions.tex#bpI:p0:g1@L226-L226 | K primary on T_rho
EDGE: bpI:p0:stripdata#IsRealOnReals | blueprint-I/parts/p0-conventions.tex#bpI:p0:g1@L226-L226 | K real on reals
EDGE: bpI:p0:stripdata#gramMatrix | blueprint-I/parts/p0-conventions.tex#bpI:p0:g1@L228-L228 | det G_K and G_K^{-1} in (I7)
EDGE: bpI:p0:extended#extendedTorsionAverage | blueprint-I/parts/p0-conventions.tex#bpI:p0:g1@L229-L229 | avg(T_H) in (I8)
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p0-conventions.tex#bpI:p0:g1@L233-L233 | E_{H,K,s omega*} in (I11), (O2)
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p0-conventions.tex#bpI:p0:g1@L234-L234 | Ebar_H(K) in (I12)
EDGE: bpI:p2:g1 | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L335-L335 | frozen tag binds this proved result to the I-G1 anchor
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0+sol-review-I-p0
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.isoenergetic_kam (KAM/Frozen/Iso/Theorems/IsoenergeticKam.lean)
LEAN_NOTE: I-G1 anchor SEALED (manifest iso.isoenergetic_kam.v1); provider audit I2-10 PASS WITH NOTES
NOTE: -

NODE: bpI:p0:head
KIND: theorem
TITLE: I-HEAD: all-time action confinement for two degrees of freedom
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:head@L268-L286
PROOF_SOURCE: blueprint-I/parts/p5-confinement.tex#bpI:p0:head@L180-L185
CONTRACT_ID: iso.all_time_confinement
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B subset R^2 open, bounded, nonempty; s_0, r_0 > 0; h holomorphic on B_{r_0}; Im h(I) = 0 for real I in B_{r_0}; det B_h(I) != 0 for every real I in B_{r_0}; B' subset R^2 open with closure compact and contained in B; eta > 0; for the inner statement: f : C^2 x C^2 -> C holomorphic on T_{s_0} x B_{r_0}, Z^2-periodic in theta there, Im f = 0 for real theta and real I in B_{r_0}; epsilon in R, 0 <= epsilon < epsilon_0, ¦f¦ <= epsilon on T_{s_0} x B_{r_0}; z_0 = (theta_0,I_0) real with I_0 in B'
SOURCE_QUANTIFIERS: B, s_0, r_0, h, B', eta fixed; then exists epsilon_0 > 0; then for all f, epsilon (hypotheses), then for all z_0 with I_0 in B'; then exists z; then for all a < 0 < b and y
SOURCE_CONCLUSION: exists z : R -> R^2 x R^2 with z(0) = z_0, Sol(Ham_{h,f},B,R,z), ¦z(t)_2 - I_0¦ < eta for all t in R, and for all a<0<b and y with y(0) = z_0 and Sol(Ham_{h,f},B,(a,b),y): y(t) = z(t) for t in (a,b)
CONSTANT_SCOPE: epsilon_0 > 0 depends on B, s_0, r_0, h, B', eta only (not on f, epsilon, z_0)
FROZEN_FILE: KAM/Frozen/Iso/Theorems/AllTimeConfinement.lean
FROZEN_DECL: KAM.Iso.all_time_confinement
FROZEN_ANCHOR_ID: iso.all_time_confinement.v1
FROZEN_ABI_SHA256: 17ef8e0e953bbc3d0818b1ae5ddea79f637b1acfe7b9adf06e9fee74cad6907d
DEPS: bpI:p0:domains#actionNbhd, bpI:p0:domains#complexStrip, bpI:p0:bordered#borderedHessian, bpI:p0:realham#realHamiltonian, bpI:p0:hamsol#IsHamiltonianSolutionOn, stepI:p5:hd-eps, stepI:p5:hd-fix, stepI:p5:hd-sol, stepI:p5:hd-uniq
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:domains#actionNbhd | blueprint-I/parts/p0-conventions.tex#bpI:p0:head@L269-L269 | B_{r_0}
EDGE: bpI:p0:domains#complexStrip | blueprint-I/parts/p0-conventions.tex#bpI:p0:head@L275-L275 | T_{s_0}
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p0-conventions.tex#bpI:p0:head@L271-L271 | det B_h(I) != 0
EDGE: bpI:p0:realham#realHamiltonian | blueprint-I/parts/p0-conventions.tex#bpI:p0:head@L280-L280 | Ham_{h,f}
EDGE: bpI:p0:hamsol#IsHamiltonianSolutionOn | blueprint-I/parts/p0-conventions.tex#bpI:p0:head@L280-L280 | Sol(Ham_{h,f},B,.,z)
EDGE: stepI:p5:hd-eps | blueprint-I/parts/p5-confinement.tex#bpI:p0:head@L181-L181 | proof of the anchor: this step is part of the proof
EDGE: stepI:p5:hd-fix | blueprint-I/parts/p5-confinement.tex#bpI:p0:head@L182-L182 | proof of the anchor: this step is part of the proof
EDGE: stepI:p5:hd-sol | blueprint-I/parts/p5-confinement.tex#bpI:p0:head@L183-L183 | proof of the anchor: this step is part of the proof
EDGE: stepI:p5:hd-uniq | blueprint-I/parts/p5-confinement.tex#bpI:p0:head@L184-L184 | proof of the anchor: this step is part of the proof
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0
REVIEWER: sol-review-I-p0
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.all_time_confinement (KAM/Frozen/Iso/Theorems/AllTimeConfinement.lean)
LEAN_NOTE: I-HEAD anchor SEALED (manifest iso.all_time_confinement.v1); provider audit I-HEAD-audit-1 PASS
NOTE: -

NODE: bpI:p0:kepler
KIND: theorem
TITLE: I-KEPLER: the classical isoenergetic determinant
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:kepler@L299-L303
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:kepler@L43-L48
CONTRACT_ID: iso.kepler_bordered_det
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega > 0; L > 0
SOURCE_QUANTIFIERS: kappa, Omega, L
SOURCE_CONCLUSION: det K_{kappa,Omega}(L) = 3 kappa Omega^2 / L^4 and det K_{kappa,Omega}(L) > 0
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Iso/Theorems/KeplerBorderedDet.lean
FROZEN_DECL: KAM.Iso.kepler_bordered_det
FROZEN_ANCHOR_ID: iso.kepler_bordered_det.v1
FROZEN_ABI_SHA256: 3c46c0a138ba6567ea3d7a46bfdd0da666047c423b6222bda82f9cb864193cc8
DEPS: bpI:p0:keplerborder#keplerBorder, bpI:p6:kepler
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p0-conventions.tex#bpI:p0:kepler@L300-L300 | det K_{kappa,Omega}(L)
EDGE: bpI:p6:kepler | blueprint-I/parts/p6-kepler.tex#bpI:p6:kepler@L40-L40 | frozen tag binds this proved result to the I-KEPLER anchor
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0+sol-review-I-p0
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.kepler_bordered_det (KAM/Frozen/Iso/Theorems/KeplerBorderedDet.lean)
LEAN_NOTE: sealed frozen theorem anchor (manifest SEALED)
NOTE: -

NODE: bpI:p0:r3bp
KIND: theorem
TITLE: I-R3BP: near-circular region of the restricted three-body problem
STATEMENT_SOURCE: blueprint-I/parts/p0-conventions.tex#bpI:p0:r3bp@L305-L319
PROOF_SOURCE: blueprint-I/parts/p8-r3bp.tex#bpI:p0:r3bp@L214-L232
CONTRACT_ID: iso.restricted_near_circular
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a_-, a_+, e_-, e_+ in R with 0 < a_- < a_+, 0 < e_- < e_+ < 1/4, a_+(1+e_+) < 1; for the inner statement: mu in [0,mu_0), z_0 in N(a_-,a_+,e_-,e_+)
SOURCE_QUANTIFIERS: a_-, a_+, e_-, e_+ fixed; then exists mu_0, d, R in R (0 < mu_0 <= 1/2, d > 0, R > 0); then for all mu in [0,mu_0), z_0 in N; then exists z; then for all a < 0 < b and y
SOURCE_CONCLUSION: N is open and nonempty; and (with the above) exists z : R -> R^2 x R^2 with z(0) = z_0, RSol_mu(R,z), and for all t: rad(q(t)-a_1(mu)) >= d, rad(q(t)-a_2(mu)) >= d, rad(q(t)) <= R, rad(p(t)) <= R; and for all a<0<b and y with y(0) = z_0 and RSol_mu((a,b),y): y(t) = z(t) on (a,b)
CONSTANT_SCOPE: mu_0, d, R depend on a_-, a_+, e_-, e_+ only, not on mu or z_0
FROZEN_FILE: KAM/Frozen/Iso/Theorems/RestrictedNearCircular.lean
FROZEN_DECL: KAM.Iso.restricted_near_circular
FROZEN_ANCHOR_ID: iso.restricted_near_circular.v1
FROZEN_ABI_SHA256: 51ef78464ec9887a4af758841d92ff8ebd3a8b16d5455a50490c8df10bf6cc2e
DEPS: bpI:p0:nearcircular#NearCircular, bpI:p0:restricted#IsRestrictedSolutionOn, bpI:p0:primaries#radius, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2, stepI:p8:pf-coord, stepI:p8:pf-small, stepI:p8:pf-head, stepI:p8:pf-sol, stepI:p8:pf-bounds, stepI:p8:pf-dist, stepI:p8:pf-uniq, bpI:p8:topology, bpI:p8:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:nearcircular#NearCircular | blueprint-I/parts/p0-conventions.tex#bpI:p0:r3bp@L307-L307 | the region N
EDGE: bpI:p0:restricted#IsRestrictedSolutionOn | blueprint-I/parts/p0-conventions.tex#bpI:p0:r3bp@L309-L309 | RSol_mu
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p0-conventions.tex#bpI:p0:r3bp@L311-L311 | rad bounds
EDGE: bpI:p0:primaries#primary1 | blueprint-I/parts/p0-conventions.tex#bpI:p0:r3bp@L311-L311 | a_1(mu)
EDGE: bpI:p0:primaries#primary2 | blueprint-I/parts/p0-conventions.tex#bpI:p0:r3bp@L312-L312 | a_2(mu)
EDGE: stepI:p8:pf-coord | blueprint-I/parts/p8-r3bp.tex#bpI:p0:r3bp@L217-L217 | proof of the anchor: this step is part of the proof
EDGE: stepI:p8:pf-small | blueprint-I/parts/p8-r3bp.tex#bpI:p0:r3bp@L219-L219 | proof of the anchor: this step is part of the proof
EDGE: stepI:p8:pf-head | blueprint-I/parts/p8-r3bp.tex#bpI:p0:r3bp@L221-L221 | proof of the anchor: this step is part of the proof
EDGE: stepI:p8:pf-sol | blueprint-I/parts/p8-r3bp.tex#bpI:p0:r3bp@L223-L223 | proof of the anchor: this step is part of the proof
EDGE: stepI:p8:pf-bounds | blueprint-I/parts/p8-r3bp.tex#bpI:p0:r3bp@L225-L225 | proof of the anchor: this step is part of the proof
EDGE: stepI:p8:pf-dist | blueprint-I/parts/p8-r3bp.tex#bpI:p0:r3bp@L227-L227 | proof of the anchor: this step is part of the proof
EDGE: stepI:p8:pf-uniq | blueprint-I/parts/p8-r3bp.tex#bpI:p0:r3bp@L229-L229 | proof of the anchor: this step is part of the proof
EDGE: bpI:p8:topology | blueprint-I/parts/p8-r3bp.tex#bpI:p0:r3bp@L215-L215 | cited at this line (proof; \ref{bpI:p8:topology})
EDGE: bpI:p8:constants | blueprint-I/parts/p8-r3bp.tex#bpI:p0:r3bp@L215-L215 | cited at this line (proof; \ref{bpI:p8:constants})
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p0+sol-review-I-p0
REVIEWER: sol-delta-I-a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.restricted_near_circular (KAM/Frozen/Iso/Theorems/RestrictedNearCircular.lean)
LEAN_NOTE: I-R3BP anchor SEALED (manifest iso.restricted_near_circular.v1, seal 931c7f6); provider audit I-R3BP-audit-1 PASS
NOTE: -

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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row states this step; parent restricted by N1 (tau>=n-1)
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

NODE: bpI:p2:standing
KIND: definition
TITLE: Standing data of Part~\ref{bpI:p2}
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing@L36-L42
PROOF_SOURCE: -
CONTRACT_ID: bpI:p2:standing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data and standing hypotheses of Part 2; inner hypotheses (I1)-(I4) of the I-G1 statement)
SOURCE_QUANTIFIERS: n, tau, M, sigma_K, sigma_B, sigma_T, sigma_omega, nu, omega*, D, H, E_0, gamma fixed (outermost)
SOURCE_CONCLUSION: defines the standing data of Part 2: n>=2, tau>=n-1, M,sigma_K,sigma_B,sigma_T>0, sigma_omega>1, nu>0, omega* in R^n minus {0}; D subset C^n x C^n and H: C^n x C^n -> C satisfy (I1)-(I4) of I-G1 (D open, Z^n-invariant in theta; H holomorphic, 1-periodic in theta, real at real points of D; ¦DH¦,¦X_H¦,¦DX_H¦,¦D^2 X_H¦,¦D^2 H¦ <= M on D); E_0 in R, gamma>0, omega* in Dio_{gamma,tau}
CONSTANT_SCOPE: all constants (n,tau,M,sigma's,nu,gamma,E_0) are fixed by the package; no dependence
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:diophantine#IsDiophantine, bpI:p0:hamiltonian#hamiltonianVectorFieldC
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing@L41-L41 | omega* in Dio_{gamma,tau}
EDGE: bpI:p0:hamiltonian#hamiltonianVectorFieldC | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing@L40-L40 | X_H and its derivative bounds on D
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.IsoStanding (KAM/Iso/Apost/Defs.lean)
LEAN_NOTE: Definition formalized (structure); audit I-D0-2 PASS (I-D0-1 table), nothing to prove
NOTE: -

NODE: bpI:p2:standing#k-bridge
KIND: step
TITLE: Bridge: Part 2 standing data contains K's standing data (h := H, B(frak) := D)
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L44-L48
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L44-L48
CONTRACT_ID: bpI:p2:standing#k-bridge
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p2:standing; for the frequency specialization take s>1. The r,K and Gram premises of Part 1 are supplied locally when that setting is used. K standing and K objects are targets of the identification, not extra hypotheses.
SOURCE_QUANTIFIERS: Part 2 standing data fixed; h:=H, mathfrak B:=D; for each s>1 set omega:=s omega*. For any local r,K satisfying the Part 1 strip, image and (where needed) Gram premises, use the indicated common objects.
SOURCE_CONCLUSION: The H,D,n,tau,M data meet K:bp:p2:standing after the frequency is specialized to omega=s omega*, whose Diophantinity is supplied by bpI:p2:ray. Thus K:bp:p2:hamiltonian applies on D. The common data for bpI:p1:setting agree; its r,K,image and frame premises are still checked at consumers. L,G,B,N,P,A,T,E,Omega_K,E_sym,E_red,Q,eta are K:bp:p2:objects with h:=H; Y:=DH(K)N, script-T:=avg extendedTorsion, and E^omega(K):=energyAverage(H,K)-E_0. No unbordered A5 or other result-specific premise is asserted.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, K:bp:p2:standing, K:bp:p2:hamiltonian, bpI:p1:setting, bpI:p2:ray, K:bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L44-L44 | the package of Part 2
EDGE: K:bp:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L44-L44 | K standing data with h := H, B(frak) := D
EDGE: K:bp:p2:hamiltonian | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L45-L45 | K:bp:p2:hamiltonian applies to H on D
EDGE: bpI:p1:setting | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L45-L45 | Assumption bpI:p1:setting holds for omega = s omega*, s>1
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L46-L46 | omega = s omega* is (gamma,tau)-Diophantine for s>1 (premise of bpI:p1:setting)
EDGE: K:bp:p2:objects | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:standing#k-bridge@L46-L46 | objects are those of K:bp:p2:objects with h := H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.IsoStanding.setting (KAM/Iso/Apost/Standing.lean)
LEAN_NOTE: audit I2-1 PASS WITH NOTES: Part-1 Setting and K-standing at s*omega
NOTE: No SOURCE_GAP for the common-data transfer: n>=2,tau>=n-1 and all K Hamiltonian bounds are present, and the ray lemma pays Diophantinity. The sentence about Part 1 is read in its local r,K context; B1,B2,B4 supply its remaining premises wherever the frame is used. This bridge does not imply A5 or every K theorem hypothesis.

NODE: bpI:p2:ray
KIND: lemma
TITLE: Frequencies on the ray
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:ray@L50-L59
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:ray@L60-L65
CONTRACT_ID: bpI:p2:ray
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p2:standing (gamma, tau, omega* in Dio_{gamma,tau}, sigma_omega); s, sbar in R; omega = s omega*, omegabar = sbar omega*
SOURCE_QUANTIFIERS: standing data fixed; s, sbar in R
SOURCE_CONCLUSION: (a) s>0 gives omega in Dio_{gamma s,tau}; s>=1 gives omega in Dio_{gamma,tau}; gamma <= ¦omega*_1¦ <= ¦omega*¦; ¦omegabar-omega¦ = ¦sbar-s¦¦omega*¦. (b) nu(s):=min{s-1,sigma_omega-s}¦omega*¦ satisfies nu(sbar) >= nu(s)-¦omegabar-omega¦; if nu(s)>=nu' and ¦omegabar-omega¦ <= d < nu' then 1<sbar<sigma_omega and nu(sbar) >= nu'-d > 0
CONSTANT_SCOPE: gamma, tau, sigma_omega, omega* as in the standing data; nu' and d free
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p0:diophantine#IsDiophantine, stepI:p2:ray-dio, stepI:p2:ray-margin
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:ray@L50-L50 | omega*, gamma, tau, sigma_omega
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:ray@L53-L53 | Dio_{gamma,tau} membership
EDGE: stepI:p2:ray-dio | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:ray@L61-L61 | proof step of this result
EDGE: stepI:p2:ray-margin | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:ray@L63-L63 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.ray (KAM/Iso/Apost/Standing.lean); KAM.Iso.Apost.rayMargin (KAM/Iso/Apost/Defs.lean)
LEAN_NOTE: audit I2-1 PASS WITH NOTES: all six conjuncts
NOTE: -

NODE: stepI:p2:ray-dio
KIND: step
TITLE: Diophantine
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-dio@L61-L62
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-dio@L61-L62
CONTRACT_ID: stepI:p2:ray-dio
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega* in Dio_{gamma,tau}; s>0 (s>=1 for the same gamma)
SOURCE_QUANTIFIERS: omega* fixed; s; k in Z^n minus {0}
SOURCE_CONCLUSION: ¦k.s omega*¦ = ¦s¦¦k.omega*¦ >= ¦s¦gamma(sum ¦k_i¦)^{-tau}; k = e_1 gives gamma <= ¦omega*_1¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p1:ray, bpI:p0:diophantine#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-dio@L62-L62 | omega* in Dio_{gamma,tau}
EDGE: bpI:p1:ray | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-dio@L62-L62 | s omega* Diophantine with the constant of omega* for s>=1
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-dio@L62-L62 | Diophantine inequality
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.ray (KAM/Iso/Apost/Standing.lean)
LEAN_NOTE: Rule 05:10: ray conjuncts (a),(c) resp. (d),(e); I2-1-audit-1.md:40 and proof narrative (Standing:76-102) confirm by line range; parent ray PROVED.
NOTE: -

NODE: stepI:p2:ray-margin
KIND: step
TITLE: Margins
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-margin@L63-L64
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-margin@L63-L64
CONTRACT_ID: stepI:p2:ray-margin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ¦sbar-s¦ definitions; sigma_omega
SOURCE_QUANTIFIERS: s, sbar in R; omega*
SOURCE_CONCLUSION: sbar-1 >= s-1-¦sbar-s¦ and sigma_omega-sbar >= sigma_omega-s-¦sbar-s¦; multiplying by ¦omega*¦: nu(sbar) >= nu(s)-¦omegabar-omega¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ray-margin@L64-L64 | sigma_omega and omega* from the standing data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.ray (KAM/Iso/Apost/Standing.lean)
LEAN_NOTE: Rule 05:10: ray conjuncts (a),(c) resp. (d),(e); I2-1-audit-1.md:40 and proof narrative (Standing:76-102) confirm by line range; parent ray PROVED.
NOTE: -

NODE: bpI:p2:constants
KIND: definition
TITLE: Constants
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:constants@L67-L91
PROOF_SOURCE: -
CONTRACT_ID: bpI:p2:constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (definition; inputs mu,nu>0, 0<rho_infty<rho; the K constants of K:bp:p2:constants)
SOURCE_QUANTIFIERS: n, tau, M, sigma_K, sigma_B, sigma_T fixed; then the K constants; then the hat-constants in the stated order; then (mu,nu) and (rho,rho_infty)
SOURCE_CONCLUSION: Use K constants kappa=tau+n>=2n-1>=3, a=2kappa+2>=8, c_R,m,Theta,C_X,C_T,C_Omega,C_sym,C_red,C_xi0,C_G,C_B,C_DeltaN,C_DeltaX,C_DeltaT. In the following formulas all hat-C names carry hats; C_P,C_Y,C_DeltaScriptT do not: hatC_S=max{C_xi0,m Theta+2n c_R m^5}; hatC_xiN=hatC_S+2n c_R m; hatC_g=C_T hatC_xiN+Theta hatC_S+2n m^2 Theta; hatC_xi=max{c_R hatC_g,Theta hatC_xiN}; hatC_DeltaK=2m^2 hatC_xi; hatC_Delta=max{hatC_DeltaK,Theta^2 hatC_S}; C_P=m^2+n+m^3+C_X; hatC_partial=C_P hatC_xi+2m^2 Theta hatC_g; hatC_lin=C_red hatC_xi+C_sym hatC_g+Theta C_Omega hatC_S; hatC_E1=4m^2 Theta^2 hatC_lin+m hatC_DeltaK^2+Theta hatC_S hatC_partial; hatC_E2=n Theta^2(2n m+C_Omega)c_R hatC_g+m hatC_DeltaK^2; hatC_E=max{hatC_E1,hatC_E2}; C_Y=n m(2m^2+C_DeltaN); C_DeltaScriptT=C_DeltaT+8n^2 m^4+1+C_Y; hatc_step=2Theta^3 max{C_sym,m C_DeltaScriptT hatC_Delta}; hatc_sum=4Theta^2 hatC_Delta max{n,C_B,m^2 C_DeltaScriptT}. For mu,nu>0 and 0<rho_infty<rho: hatc_*=max{2^{2a}hatC_E,hatc_step max{1,2/mu},2hatc_sum/mu,4Theta^2 hatC_Delta/nu}; delta_0=min{1,(rho-rho_infty)/8}.
CONSTANT_SCOPE: the K constants and all hat constants except hat-c_* and delta_0 depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* in addition on (mu,nu); delta_0 on (rho,rho_infty); all finite, >=1 unless stated
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:constants, bpI:p2:standing, bpI:p2:standing#k-bridge
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:constants@L69-L69 | the K constants kappa,a,c_R,m,Theta,C_* used as inputs
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:constants@L69-L69 | constants depend on n,tau,M,sigma_K,sigma_B,sigma_T, nu from the standing data
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:constants@L69-L69 | applies K:bp:p2:constants under the Part 2 standing data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.iso_constants_spec (KAM/Iso/Apost/Constants.lean); KAM.Iso.Apost.hatCS (KAM/Iso/Apost/Defs.lean)
LEAN_NOTE: audit I2-2 PASS WITH NOTES (defs by I-D0-2); iso_constants_spec = Appendix A conjunction
NOTE: -

NODE: bpI:p2:admissible
KIND: definition
TITLE: Isoenergetic admissible parameterization
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L93-L112
PROOF_SOURCE: -
CONTRACT_ID: bpI:p2:admissible
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p2:standing; r,beta>0, 0<=eps<=1, s>1, omega := s omega*; K: C^n -> C^n x C^n
SOURCE_QUANTIFIERS: standing data and constants fixed; r, beta, eps, s, K
SOURCE_CONCLUSION: defines (r,beta,eps,s)-admissible: (B1) K holomorphic, primary, real on reals on T_r; (B2) B_beta(K(theta)) in D on T_r; (B3) ¦DK¦<=sigma_K on T_r; (B4) det G_K != 0, ¦B¦<=sigma_B on T_r; (B5) det avg T_H != 0 and ¦avg T_H^{-1}¦<=sigma_T; (B6) ¦E_{H,K,omega}¦<=eps on T_r; (B7) ¦Ebar_H(K)-E_0¦<=eps; and records gamma <= ¦omega¦ <= Theta (bpI:p2:freq, via K:bp:p2:frequency with A3,A4,A6 = B3,B4,B6 and omega in Dio_{gamma,tau}) and gamma delta^j <= Theta for delta<=1, j>=0
CONSTANT_SCOPE: sigma_K, sigma_B, sigma_T, gamma, E_0 as in the standing data; Theta, m from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p2:constants, bpI:p2:standing#k-bridge, bpI:p0:domains#complexStrip, bpI:p0:stripdata#IsPrimaryOnStrip, bpI:p0:stripdata#IsRealOnReals, bpI:p0:stripdata#gramMatrix, bpI:p0:extended#extendedTorsionAverage, bpI:p0:stripdata#invarianceError, bpI:p0:extended#energyAverage, bpI:p1:extended-basic, K:bp:p2:frequency, K:bp:p2:admissible, bpI:p2:ray
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L94-L94 | sigma_K,sigma_B,sigma_T,D,H,E_0,gamma
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L110-L110 | m, Theta in the frequency bound
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L105-L105 | K:bp:p2:frequency applied under the standing data
EDGE: bpI:p0:domains#complexStrip | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L97-L97 | strip T_r
EDGE: bpI:p0:stripdata#IsPrimaryOnStrip | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L97-L97 | K primary on T_r
EDGE: bpI:p0:stripdata#IsRealOnReals | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L97-L97 | K real on reals
EDGE: bpI:p0:stripdata#gramMatrix | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L100-L100 | det G_K
EDGE: bpI:p0:extended#extendedTorsionAverage | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L101-L101 | avg T_H
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L102-L102 | E_{H,K,omega}
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L103-L103 | Ebar_H(K)
EDGE: bpI:p1:extended-basic | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L101-L101 | T_H and its average are defined by this lemma
EDGE: K:bp:p2:frequency | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L105-L105 | frequency bound gamma<=¦omega¦<=Theta
EDGE: K:bp:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L105-L105 | premise form (A3,A4,A6) of the frequency bound
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:admissible@L106-L106 | omega = s omega* in Dio_{gamma,tau}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.IsoAdmissible (KAM/Iso/Apost/Defs.lean); KAM.Iso.Apost.IsoAdmissible.freq (KAM/Iso/Apost/Standing.lean)
LEAN_NOTE: Definition formalized (I-D0-2 PASS); freq display proved in audit I2-1 PASS WITH NOTES
NOTE: -

NODE: bpI:p2:correction
KIND: lemma
TITLE: Size of the isoenergetic correction
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L132-L150
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L151-L166
CONTRACT_ID: bpI:p2:correction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p2:standing; s>1, omega = s omega*, 0<delta<=1, 2delta<r, 0<=eps<=1; K (r,beta,eps,s)-admissible (bpI:p2:admissible)
SOURCE_QUANTIFIERS: standing data, constants fixed; r, beta, s, delta, eps, K; then the border-solve data eta^L, eta^N, eta^omega, T, Y, sigma, xi^L_0 are defined from K
SOURCE_CONCLUSION: Lemma bpI:p1:border-solve applies with eta^L = -N^T Omega_0 E, eta^N = L^T Omega_0 E, eta^omega = -E^omega(K), T = T_{H,K,omega}, Y = DH(K)N, sigma = sigma_T, xi^L_0 = 0; xi, DeltaK := P xi are holomorphic, 1-periodic, real on reals, xi^omega in R; Deltaomega := -omega xi^omega, omegabar = sbar omega*, sbar = s(1-xi^omega); estimates ¦xi_0¦,¦xi^omega¦ <= C_S eps/(gamma delta^{kappa+1}), ¦xi^N¦ <= C_xiN eps/(gamma delta^{kappa+1}), ¦g^L¦ <= C_g eps/(gamma delta^{kappa+2}) on T_{r-delta}; ¦xi¦ <= C_xi eps/(gamma^2 delta^a), ¦DeltaK¦ <= C_DeltaK eps/(gamma^2 delta^a), ¦d_omega xi¦ <= C_g eps/(gamma delta^{kappa+2}), ¦d_omega DeltaK¦ <= C_partial eps/(gamma^2 delta^{a+1}) on T_{r-2delta}; ¦Deltaomega¦ = ¦sbar-s¦¦omega*¦ <= Theta^2 C_S eps/(gamma^2 delta^a); with d := C_Delta eps/(gamma^2 delta^a): ¦DeltaK¦ <= d on T_{r-2delta} and ¦Deltaomega¦ <= d
CONSTANT_SCOPE: Constants of Definition bpI:p2:constants: all depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* also on (mu,nu); delta_0 on (rho,rho_infty); no dependence on K, s, e, gamma, omega*, sigma_omega; Gamma_delta = c_R gamma^{-1} delta^{-kappa}
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible, bpI:p2:standing#k-bridge, bpI:p1:border-solve, stepI:p2:co-data, stepI:p2:co-xi0, stepI:p2:co-xi, stepI:p2:co-omega, stepI:p2:co-dk, stepI:p2:co-reg
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L133-L133 | gamma, omega*, M, sigma_T, E_0
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L141-L141 | hat constants C_S,...,C_partial,C_Delta, Theta, c_R, kappa, a
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L133-L133 | K is (r,beta,eps,s)-admissible; B1-B7 and the frequency bound
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L133-L133 | applies the Part 1 lemma and K objects under the standing data
EDGE: bpI:p1:border-solve | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L133-L133 | the bordered solve is applied with the stated data
EDGE: stepI:p2:co-data | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L152-L152 | proof step of this result
EDGE: stepI:p2:co-xi0 | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L154-L154 | proof step of this result
EDGE: stepI:p2:co-xi | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L156-L156 | proof step of this result
EDGE: stepI:p2:co-omega | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L160-L160 | proof step of this result
EDGE: stepI:p2:co-dk | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L162-L162 | proof step of this result
EDGE: stepI:p2:co-reg | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:correction@L164-L164 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: audit I2-3 PASS WITH NOTES: complete correction bounds and regularity
NOTE: -

NODE: stepI:p2:co-data
KIND: step
TITLE: Hypotheses of the border solve
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L152-L153
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L152-L153
CONTRACT_ID: stepI:p2:co-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K admissible; omega = s omega*, s>1; 0<delta<=1, 2delta<r; standing data
SOURCE_QUANTIFIERS: K, eps, delta, r fixed
SOURCE_CONCLUSION: the hypotheses of border-solve hold: omega in Dio_{gamma,tau}, gamma<=¦omega¦<=Theta; on T_{r-delta} H_L = 2n m^2 eps, H_N = 2n m eps, H_T = C_T/delta; eta^L,eta^N,T holomorphic, 1-periodic, real on reals; avg eta^N = 0; Y holomorphic, periodic, real on reals with ¦Y¦ <= M sigma_K sigma_B <= m^3 =: H_Y; avg T_H invertible with ¦script-T^{-1}¦ <= sigma_T <= m; eta^omega real, ¦eta^omega¦ <= eps
CONSTANT_SCOPE: m, C_T, Theta from the constants; no new constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:admissible, bpI:p2:standing, bpI:p2:constants, bpI:p2:standing#k-bridge, bpI:p1:geometry-noA5, bpI:p1:energy-approx, bpI:p1:extended-basic, K:bp:p2:periodicity, K:bp:p2:frame-basic
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | freq bound (bpI:p2:freq), B5, B7
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | M, E_0 real, D, H
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | m, Theta, C_T, H_Y
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | K periodicity and frame results applied under the standing data
EDGE: bpI:p1:geometry-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | H_L, H_N, H_T bounds
EDGE: bpI:p1:energy-approx | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | avg eta^N = 0 (d) and avg(H o K) real (a)
EDGE: bpI:p1:extended-basic | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | Y holomorphic, periodic, real; bound on Y; avg T_H = script-T
EDGE: K:bp:p2:periodicity | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | eta^L, eta^N, T holomorphic, periodic, real on reals
EDGE: K:bp:p2:frame-basic | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-data@L153-L153 | eta^L, eta^N, T holomorphic, periodic, real on reals
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction, KAM.Iso.Apost.CorrectionAux.correction_core, KAM.Iso.Apost.isoNewS_smul_sub, KAM.Iso.Apost.isoNewS_smul_eq, KAM.Iso.Apost.CorrectionAux.norm_fderiv_frameMat_le (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: Rule 05:10: I2-3-audit-1.md:47 (Correction.lean:385-438 matches blueprint p2 L132-166) with items 3-5; bodies are step-labelled locals in correction_core (205-335); parent correction PROVED. Lean proves H_L,H_N on T_r (stronger).
NOTE: -

NODE: stepI:p2:co-xi0
KIND: step
TITLE: The constants $\xi_0,\xi^\omega$
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L154-L155
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L154-L155
CONTRACT_ID: stepI:p2:co-xi0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:correction, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:correction, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: S_* <= C_S eps/(gamma delta^{kappa+1}) (first entry <= 2n m(m Theta + c_R C_T)eps/(gamma delta^{kappa+1}), second <= (Theta + 2n c_R m^4) eps/(gamma delta^kappa))
CONSTANT_SCOPE: C_S from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p2:co-data, bpI:p1:border-solve, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p2:co-data | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L155-L155 | proof step of this result
EDGE: bpI:p1:border-solve | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L155-L155 | the quantity S_* of the border solve
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L155-L155 | C_xi0, C_S, c_R, Theta, m
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L155-L155 | gamma, sigma_T
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi0@L155-L155 | gamma delta^j <= Theta absorption
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction, KAM.Iso.Apost.CorrectionAux.correction_core, KAM.Iso.Apost.isoNewS_smul_sub, KAM.Iso.Apost.isoNewS_smul_eq, KAM.Iso.Apost.CorrectionAux.norm_fderiv_frameMat_le (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: Rule 05:10: I2-3-audit-1.md:47 (Correction.lean:385-438 matches blueprint p2 L132-166) with items 3-5; bodies are step-labelled locals in correction_core (205-335); parent correction PROVED. Lean proves H_L,H_N on T_r (stronger).
NOTE: -

NODE: stepI:p2:co-xi
KIND: step
TITLE: $\xi^N,g^L,\xi^L$
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L156-L159
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L156-L159
CONTRACT_ID: stepI:p2:co-xi
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:correction, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:correction, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: ¦xi^N¦ <= S_*+Gamma_delta H_N <= C_xiN eps/(gamma delta^{kappa+1}); ¦g^L¦ <= C_g eps/(gamma delta^{kappa+2}); ¦xi^L¦ <= c_R C_g eps/(gamma^2 delta^{2kappa+2}); ¦xi¦ <= C_xi eps/(gamma^2 delta^a); ¦DeltaK¦ <= ¦P¦¦xi¦ <= C_DeltaK eps/(gamma^2 delta^a); d_omega xi = (g^L,-eta^N) with ¦eta^N¦ <= C_g eps/(gamma delta^{kappa+2})
CONSTANT_SCOPE: C_xiN, C_g, C_xi, C_DeltaK from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p2:co-data, stepI:p2:co-xi0, bpI:p1:border-solve, bpI:p2:constants, bpI:p2:standing, K:bp:p2:frame-basic, bpI:p2:standing#k-bridge, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p2:co-data | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L157-L157 | proof step of this result
EDGE: stepI:p2:co-xi0 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L157-L157 | proof step of this result
EDGE: bpI:p1:border-solve | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L157-L157 | (b),(c): bounds on xi^N, g^L, xi^L and d_omega xi
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L158-L158 | C_xiN, C_g, C_xi, C_DeltaK, c_R
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L158-L158 | gamma, Theta
EDGE: K:bp:p2:frame-basic | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L159-L159 | bound ¦P¦ <= 2 m^2 on T_{r-2delta} used in ¦DeltaK¦ <= ¦P¦¦xi¦
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L159-L159 | K frame bounds under the standing data
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-xi@L159-L159 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction, KAM.Iso.Apost.CorrectionAux.correction_core, KAM.Iso.Apost.isoNewS_smul_sub, KAM.Iso.Apost.isoNewS_smul_eq, KAM.Iso.Apost.CorrectionAux.norm_fderiv_frameMat_le (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: Rule 05:10: I2-3-audit-1.md:47 (Correction.lean:385-438 matches blueprint p2 L132-166) with items 3-5; bodies are step-labelled locals in correction_core (205-335); parent correction PROVED. Lean proves H_L,H_N on T_r (stronger).
NOTE: -

NODE: stepI:p2:co-omega
KIND: step
TITLE: The frequency correction
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L160-L161
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L160-L161
CONTRACT_ID: stepI:p2:co-omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:correction, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:correction, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: ¦Deltaomega¦ = ¦omega¦¦xi^omega¦ <= Theta^2 C_S eps/(gamma^2 delta^a) and Deltaomega = -xi^omega s omega*, so ¦Deltaomega¦ = ¦sbar-s¦¦omega*¦
CONSTANT_SCOPE: C_S, Theta from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p2:co-xi0, bpI:p2:ray, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p2:co-xi0 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L161-L161 | bound on xi^omega
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L161-L161 | ¦omegabar-omega¦ = ¦sbar-s¦¦omega*¦ (ray (a))
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L161-L161 | C_S, Theta
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L161-L161 | gamma, omega*
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-omega@L161-L161 | ¦omega¦ <= Theta (bpI:p2:freq)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction, KAM.Iso.Apost.CorrectionAux.correction_core, KAM.Iso.Apost.isoNewS_smul_sub, KAM.Iso.Apost.isoNewS_smul_eq, KAM.Iso.Apost.CorrectionAux.norm_fderiv_frameMat_le (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: Rule 05:10: I2-3-audit-1.md:47 (Correction.lean:385-438 matches blueprint p2 L132-166) with items 3-5; bodies are step-labelled locals in correction_core (205-335); parent correction PROVED. Lean proves H_L,H_N on T_r (stronger).
NOTE: -

NODE: stepI:p2:co-dk
KIND: step
TITLE: Derivative of the correction along $\omega$
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L162-L163
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L162-L163
CONTRACT_ID: stepI:p2:co-dk
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:correction, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:correction, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: ¦d_omega L¦ <= m^2+n eps/delta, ¦d_omega N¦ <= m^3+C_X/delta, ¦d_omega P¦ <= C_P/delta on T_{r-delta}; ¦d_omega DeltaK¦ <= C_P C_xi eps/(gamma^2 delta^{a+1}) + 2 m^2 C_g eps/(gamma delta^{kappa+2}) <= C_partial eps/(gamma^2 delta^{a+1})
CONSTANT_SCOPE: C_P, C_partial, C_X from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:frame-identities, bpI:p2:standing#k-bridge, stepI:p2:co-xi, stepI:p2:co-data, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible, bpI:p1:geometry-noA5
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:frame-identities | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | d_omega L = AL - DE, d_omega N = AN - X_N (c)
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | K frame identities under the standing data
EDGE: stepI:p2:co-xi | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | bounds on xi and d_omega xi
EDGE: stepI:p2:co-data | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | data of the border solve (eps bound B6)
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | C_P, C_X, C_partial, m
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | gamma
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | B6: ¦E¦ <= eps
EDGE: bpI:p1:geometry-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-dk@L163-L163 | Provides the DE and X_N bounds used in the two frame derivative estimates.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction, KAM.Iso.Apost.CorrectionAux.correction_core, KAM.Iso.Apost.isoNewS_smul_sub, KAM.Iso.Apost.isoNewS_smul_eq, KAM.Iso.Apost.CorrectionAux.norm_fderiv_frameMat_le (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: Rule 05:10: I2-3-audit-1.md:47 (Correction.lean:385-438 matches blueprint p2 L132-166) with items 3-5; bodies are step-labelled locals in correction_core (205-335); parent correction PROVED. Lean proves H_L,H_N on T_r (stronger).
NOTE: -

NODE: stepI:p2:co-reg
KIND: step
TITLE: Regularity
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L164-L165
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L164-L165
CONTRACT_ID: stepI:p2:co-reg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:correction, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:correction, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: xi and P are holomorphic, 1-periodic and real on reals, hence DeltaK=P xi is holomorphic, 1-periodic and real on reals on T_{r-2delta}; xi^omega is real by border-solve(e). Since hatC_DeltaK,Theta^2 hatC_S<=hatC_Delta, ¦DeltaK¦<=d there and ¦Deltaomega¦<=d.
CONSTANT_SCOPE: C_Delta from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:border-solve, K:bp:p2:periodicity, bpI:p2:standing#k-bridge, stepI:p2:co-data, stepI:p2:co-xi, stepI:p2:co-omega, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:border-solve | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | (a),(e): xi holomorphic, periodic, real on reals
EDGE: K:bp:p2:periodicity | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | P holomorphic, periodic, real on reals
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | K periodicity under the standing data
EDGE: stepI:p2:co-data | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | hypotheses (realness) of the border solve
EDGE: stepI:p2:co-xi | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | ¦DeltaK¦ bound
EDGE: stepI:p2:co-omega | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | ¦Deltaomega¦ bound
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | C_Delta >= C_DeltaK, Theta^2 C_S
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:co-reg@L165-L165 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.correction, KAM.Iso.Apost.CorrectionAux.correction_core, KAM.Iso.Apost.isoNewS_smul_sub, KAM.Iso.Apost.isoNewS_smul_eq, KAM.Iso.Apost.CorrectionAux.norm_fderiv_frameMat_le (KAM/Iso/Apost/Correction.lean)
LEAN_NOTE: Rule 05:10: I2-3-audit-1.md:47 (Correction.lean:385-438 matches blueprint p2 L132-166) with items 3-5; bodies are step-labelled locals in correction_core (205-335); parent correction PROVED. Lean proves H_L,H_N on T_r (stronger).
NOTE: -

NODE: bpI:p2:newton-error
KIND: lemma
TITLE: The new errors
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L168-L181
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L182-L193
CONTRACT_ID: bpI:p2:newton-error
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of bpI:p2:correction (standing data; s>1; 0<delta<=1; 2delta<r; K admissible); d < beta; C_sym eps/(gamma delta^{kappa+1}) <= 1/2; Kbar := K+DeltaK on T_{r-2delta}, Kbar := K elsewhere
SOURCE_QUANTIFIERS: standing data and constants fixed; r,beta,s,delta,eps,K as in bpI:p2:correction; use its constructed xi,DeltaK,Deltaomega,omegabar and d := hatC_Delta eps/(gamma^2 delta^a), subject to the additional two inequalities; define Kbar and the new errors as displayed; no new independent beta or d
SOURCE_CONCLUSION: Kbar(T_{r-2delta}) in D; S := I - Omega_0 E_sym invertible with ¦S^{-1}¦<=2 on T_{r-2delta}; Ebar := E_{H,Kbar,omegabar} = P S^{-1} E_lin + Delta^2 X + xi^omega d_omega DeltaK with E_lin := E_red xi + Omega_0 E_sym d_omega xi - (0,Omega_K omega) xi^omega, Delta^2 X := X_H(Kbar)-X_H(K)-A DeltaK; Ebar^omega := Ebar_H(Kbar)-E_0 = E^omega_lin + avg(Delta^2 H), E^omega_lin = avg(D(H o K) xi^L), Delta^2 H := H(Kbar)-H(K)-DH(K)DeltaK; ¦Ebar¦ <= C_E eps^2/(gamma^4 delta^{2a}) on T_{r-2delta} and ¦Ebar^omega¦ <= C_E eps^2/(gamma^4 delta^{2a})
CONSTANT_SCOPE: Constants of Definition bpI:p2:constants: all depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* also on (mu,nu); delta_0 on (rho,rho_infty); no dependence on K, s, e, gamma, omega*, sigma_omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible, bpI:p2:standing#k-bridge, bpI:p2:correction, stepI:p2:ne-invert, stepI:p2:ne-expand, stepI:p2:ne-reduce, stepI:p2:ne-est, stepI:p2:ne-energy
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L169-L169 | gamma, M, D, H
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L169-L169 | C_sym, C_E, kappa, a
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L169-L169 | K is (r,beta,eps,s)-admissible; B1-B7 and the frequency bound
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L184-L184 | K frame identities applied under the Part 2 standing data
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L169-L169 | setting of the lemma; DeltaK, Deltaomega, d, xi
EDGE: stepI:p2:ne-invert | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L183-L183 | proof step of this result
EDGE: stepI:p2:ne-expand | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L185-L185 | proof step of this result
EDGE: stepI:p2:ne-reduce | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L187-L187 | proof step of this result
EDGE: stepI:p2:ne-est | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L189-L189 | proof step of this result
EDGE: stepI:p2:ne-energy | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:newton-error@L191-L191 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.newton_error (KAM/Iso/Apost/NewtonError.lean)
LEAN_NOTE: audit I2-4 PASS WITH NOTES: all six conclusions
NOTE: -

NODE: stepI:p2:ne-invert
KIND: step
TITLE: Invertibility and domain
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L183-L184
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L183-L184
CONTRACT_ID: stepI:p2:ne-invert
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:newton-error, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:newton-error, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: S invertible with ¦S^{-1}¦<=2; Q P = S so Q^{-1} = P S^{-1}; Kbar(theta) in B_beta(K(theta)) in D and the segment [K,Kbar] in D
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:geometry-noA5, K:bp:p1:neumann, K:bp:p2:frame-identities, bpI:p2:standing#k-bridge, bpI:p2:correction, bpI:p2:admissible, bpI:p2:standing, bpI:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:geometry-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | ¦Omega_0 E_sym¦ <= 1/2
EDGE: K:bp:p1:neumann | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | Neumann series: ¦S^{-1}¦ <= 2
EDGE: K:bp:p2:frame-identities | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | Q P = S (f)
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | K frame identities under the standing data
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | ¦DeltaK¦ <= d
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | B2: B_beta(K) in D
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | D open, convex ball in D
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-invert@L184-L184 | Uses constants or exponents fixed by this package.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.NewtonErrorAux.sMat_bounds, KAM.Iso.Apost.NewtonErrorAux.isoResidual_eq_frame, KAM.Iso.Apost.newton_error (KAM/Iso/Apost/NewtonError.lean)
LEAN_NOTE: Rule 05:10: I2-4-audit-1.md:61-66 (table by Lean line ranges 321-328, 331-361, 374-438, 451-570) and 'Expansion and reduction/Invariance bound/Energy' paragraphs; parent newton-error PROVED. Lean uses M for source m; D(H o K) bound sharper than source form.
NOTE: -

NODE: stepI:p2:ne-expand
KIND: step
TITLE: Expansion
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L185-L186
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L185-L186
CONTRACT_ID: stepI:p2:ne-expand
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:newton-error, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:newton-error, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: Ebar = X_H(K+DeltaK)-(L+D DeltaK)(omega+Deltaomega) = E + A DeltaK - d_omega DeltaK - L Deltaomega + Delta^2 X - D DeltaK Deltaomega, and D DeltaK Deltaomega = -xi^omega d_omega DeltaK
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:correction, stepI:p2:ne-invert, bpI:p2:standing#k-bridge, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L186-L186 | definitions of DeltaK, Deltaomega, xi^omega
EDGE: stepI:p2:ne-invert | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L186-L186 | Kbar in D so X_H(Kbar) is defined
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L186-L186 | K objects (L, A, E) under the standing data
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L186-L186 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-expand@L186-L186 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.NewtonErrorAux.sumVec_invarianceError_isoNewtonMap (KAM/Iso/Apost/NewtonError.lean)
LEAN_NOTE: Rule 05:10: I2-4-audit-1.md:61-66 (table by Lean line ranges 321-328, 331-361, 374-438, 451-570) and 'Expansion and reduction/Invariance bound/Energy' paragraphs; parent newton-error PROVED. Lean uses M for source m; D(H o K) bound sharper than source form.
NOTE: -

NODE: stepI:p2:ne-reduce
KIND: step
TITLE: Reduction by $Q$
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L187-L188
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L187-L188
CONTRACT_ID: stepI:p2:ne-reduce
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:newton-error, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:newton-error, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: Q(E + A DeltaK - d_omega DeltaK - L Deltaomega) = Lambda xi - d_omega xi + (omega,0) xi^omega - eta + E_lin = E_lin by the first two border equations; applying Q^{-1} = P S^{-1} gives (bpI:p2:newerr)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:reduced, bpI:p2:standing#k-bridge, bpI:p1:border-solve, bpI:p2:correction, stepI:p2:ne-expand, stepI:p2:ne-invert, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:reduced | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | (b): reduction of the equation by Q
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | Part 1 reduced lemma under the standing data
EDGE: bpI:p1:border-solve | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | first two equations of (b)
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | the data of the correction
EDGE: stepI:p2:ne-expand | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | expanded error
EDGE: stepI:p2:ne-invert | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | Q^{-1} = P S^{-1}
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-reduce@L188-L188 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.NewtonErrorAux.sumVec_error_eq (KAM/Iso/Apost/NewtonError.lean)
LEAN_NOTE: Rule 05:10: I2-4-audit-1.md:61-66 (table by Lean line ranges 321-328, 331-361, 374-438, 451-570) and 'Expansion and reduction/Invariance bound/Energy' paragraphs; parent newton-error PROVED. Lean uses M for source m; D(H o K) bound sharper than source form.
NOTE: -

NODE: stepI:p2:ne-est
KIND: step
TITLE: Estimates
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L189-L190
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L189-L190
CONTRACT_ID: stepI:p2:ne-est
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:newton-error, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:newton-error, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: ¦E_lin¦ <= C_lin eps^2/(gamma^2 delta^{a+1}); ¦Delta^2 X¦ <= M¦DeltaK¦^2 <= m C_DeltaK^2 eps^2/(gamma^4 delta^{2a}); ¦xi^omega d_omega DeltaK¦ <= C_S C_partial eps^2/(gamma^3 delta^{kappa+a+2}); with ¦P¦¦S^{-1}¦ <= 4 m^2: ¦Ebar¦ <= C_E1 eps^2/(gamma^4 delta^{2a})
CONSTANT_SCOPE: C_lin, C_E1 from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:geometry-noA5, bpI:p2:correction, K:bp:p2:hamiltonian, bpI:p2:standing#k-bridge, stepI:p2:ne-reduce, stepI:p2:ne-invert, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:geometry-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | bounds on E_red, E_sym, Omega_K
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | bounds on xi, d_omega xi, xi^omega, d_omega DeltaK
EDGE: K:bp:p2:hamiltonian | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | (e): ¦Delta^2 X¦ <= M¦DeltaK¦^2
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | K Hamiltonian lemma under the standing data
EDGE: stepI:p2:ne-reduce | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | E_lin and the representation of Ebar
EDGE: stepI:p2:ne-invert | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | ¦S^{-1}¦ <= 2
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | C_red, C_sym, C_Omega, C_lin, C_E1, Theta, m
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | gamma, M
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-est@L190-L190 | gamma <= Theta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.NewtonErrorAux.norm_error_le, KAM.Iso.Apost.NewtonErrorAux.norm_isoQuadX_le (KAM/Iso/Apost/NewtonError.lean)
LEAN_NOTE: Rule 05:10: I2-4-audit-1.md:61-66 (table by Lean line ranges 321-328, 331-361, 374-438, 451-570) and 'Expansion and reduction/Invariance bound/Energy' paragraphs; parent newton-error PROVED. Lean uses M for source m; D(H o K) bound sharper than source form.
NOTE: -

NODE: stepI:p2:ne-energy
KIND: step
TITLE: The energy error
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L191-L192
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L191-L192
CONTRACT_ID: stepI:p2:ne-energy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:newton-error, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:newton-error, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: Ebar^omega = E^omega + avg(DH(K)DeltaK) + avg(Delta^2 H); avg(DH(K)DeltaK) = -E^omega + E^omega_lin; ¦Delta^2 H¦ <= (M/2)¦DeltaK¦^2; ¦D(H o K)¦ <= n Theta(2n m + C_Omega) eps/(gamma delta^{kappa+1}) on R^n; the product with ¦xi^L¦ is <= C_E2 eps^2/(gamma^4 delta^{2a}); so ¦Ebar^omega¦ <= C_E eps^2/(gamma^4 delta^{2a})
CONSTANT_SCOPE: C_E2, C_E from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:energy-approx, bpI:p1:border-solve, K:bp:p1:taylor, bpI:p2:correction, stepI:p2:ne-invert, bpI:p2:standing#k-bridge, bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible, bpI:p1:geometry-noA5, K:bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:energy-approx | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | (f): avg(DH(K)DeltaK) and the bound on D(H o K)
EDGE: bpI:p1:border-solve | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | third equation avg(Y xi^N) = eta^omega
EDGE: K:bp:p1:taylor | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | Taylor remainder ¦Delta^2 H¦ <= (M/2)¦DeltaK¦^2
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | bounds on xi^L, eta^N, DeltaK
EDGE: stepI:p2:ne-invert | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | segment [K,Kbar] in D
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | Part 1 energy lemma under the standing data
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | M, omega, D^2 H bound
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | C_E2, C_E, C_Omega, Theta, m
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | gamma delta^{kappa+1} <= Theta
EDGE: bpI:p1:geometry-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | the bound on Omega_K and the eta bounds supply the displayed estimate for D(H o K)
EDGE: K:bp:p1:ext-integral | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:ne-energy@L192-L192 | continuous integrands on the compact real cube; linearity of the energy average and norm bounded by the unit-cube supremum
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.NewtonErrorAux.energyAverage_sub_eq, KAM.Iso.Apost.NewtonErrorAux.norm_energyAverage_sub_le, KAM.Iso.Apost.NewtonErrorAux.norm_isoQuadH_le (KAM/Iso/Apost/NewtonError.lean)
LEAN_NOTE: Rule 05:10: I2-4-audit-1.md:61-66 (table by Lean line ranges 321-328, 331-361, 374-438, 451-570) and 'Expansion and reduction/Invariance bound/Energy' paragraphs; parent newton-error PROVED. Lean uses M for source m; D(H o K) bound sharper than source form.
NOTE: -

NODE: bpI:p2:torsion
KIND: lemma
TITLE: The new averaged extended torsion
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L205-L213
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L214-L225
CONTRACT_ID: bpI:p2:torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data; K (r,beta,eps,s)-admissible; 0<delta<=1, 4delta<r; Kbar, omegabar as in bpI:p2:newton-error; d<beta; 2 m C_DeltaScriptT d/delta^2 <= 1
SOURCE_QUANTIFIERS: standing data and constants fixed; r,beta,eps,s,delta,K as stated, with 4delta<r; use the correction/new-error constructions Kbar,omegabar and d := hatC_Delta eps/(gamma^2 delta^a); impose the stated smallness conditions on this d, not a new independent parameter
SOURCE_CONCLUSION: omegabar in R^n; T_H for (Kbar,omegabar) defined on T_{r-3delta}; Kbar holomorphic on T_{r-2delta}, primary, real on reals; det Gbar != 0 on T_{r-3delta} with ¦DKbar¦ <= 2m, ¦Bbar¦ <= 2m; B_{beta-d}(Kbar) in D on T_{r-2delta}; ¦DKbar-DK¦ <= nd/delta and ¦Bbar-B¦ <= C_B d/delta on T_{r-3delta}; avg Tbar := avg T_H(Kbar,omegabar) defined, invertible, ¦avg Tbar - avg T¦ <= C_DeltaScriptT d/delta^2, ¦avg Tbar^{-1} - avg T^{-1}¦ <= 2 m^2 C_DeltaScriptT d/delta^2
CONSTANT_SCOPE: Constants of Definition bpI:p2:constants: all depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* also on (mu,nu); delta_0 on (rho,rho_infty); no dependence on K, s, e, gamma, omega*, sigma_omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible, bpI:p2:standing#k-bridge, bpI:p2:newton-error, bpI:p2:correction, stepI:p2:to-frame, stepI:p2:to-omega, stepI:p2:to-row, stepI:p2:to-avg, stepI:p2:to-inv
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L206-L206 | standing data
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L206-L206 | C_DeltaScriptT, C_B, m
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L206-L206 | K is (r,beta,eps,s)-admissible; B1-B7 and the frequency bound
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L222-L222 | K averages/matrix lemmas applied to the displayed full-matrix difference
EDGE: bpI:p2:newton-error | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L206-L206 | Kbar, omegabar as in the new-error lemma
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L216-L216 | the correction supplies norm(Kbar-K) <= d for the frame perturbation application
EDGE: stepI:p2:to-frame | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L215-L215 | proof step of this result
EDGE: stepI:p2:to-omega | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L217-L217 | proof step of this result
EDGE: stepI:p2:to-row | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L219-L219 | proof step of this result
EDGE: stepI:p2:to-avg | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L221-L221 | proof step of this result
EDGE: stepI:p2:to-inv | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:torsion@L223-L223 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.torsion_step (KAM/Iso/Apost/Torsion.lean)
LEAN_NOTE: audit I2-5 PASS WITH NOTES: exact design-v2 statement
NOTE: Preextract candidate edge to bpI:p2:iteration (parenthetical forward pointer to (iii),(iv)) dropped: forward pointer, would create a cycle.

NODE: stepI:p2:to-frame
KIND: step
TITLE: Frame
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L215-L216
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L215-L216
CONTRACT_ID: stepI:p2:to-frame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:torsion, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:torsion, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: ball B_{beta-d}(Kbar) in D, derivative and Gram-inverse bounds, ¦Nbar-N¦ <= C_DeltaN d/delta, ¦Nbar¦ <= 2m^2 on T_{r-3delta}, ¦Tbar_omega - T_omega¦ <= C_DeltaT d/delta^2 on T_{r-4delta}; Nbar, Tbar_omega holomorphic on T_{r-3delta} so T_H(Kbar,omegabar) is continuous on R^n and its average is defined
CONSTANT_SCOPE: C_DeltaN and the old K torsion constant C_DeltaT from bpI:p2:constants; the inherited smallness uses C_DeltaScriptT >= C_DeltaT
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:perturbation-noA5, bpI:p2:correction, bpI:p2:newton-error, bpI:p1:extended-basic, bpI:p2:standing#k-bridge, bpI:p2:constants, bpI:p2:admissible, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:perturbation-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | perturbation lemma applied with Ktilde = Kbar
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | ¦Kbar-K¦ <= d on T_{r-2delta}
EDGE: bpI:p2:newton-error | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | Kbar := K+DeltaK
EDGE: bpI:p1:extended-basic | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | average of T_H defined for Kbar
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | Part 1 perturbation lemma under the standing data
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | C_DeltaT, C_DeltaN, m
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | B1-B4 hypotheses of the perturbation lemma
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-frame@L216-L216 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.torsion_step, KAM.Iso.Apost.TorsionAux.isoNewtonMap_differentiableOn (KAM/Iso/Apost/Torsion.lean)
LEAN_NOTE: audit I2-5 PASS WITH NOTES: to-frame mapped to torsion_step assembly and aux lemmas
NOTE: SOURCE_GAP: scoped to the final parenthetical application of bpI:p1:extended-basic at L216 with Kbar and omegabar. That lemma assumes bpI:p1:setting, including a positive Diophantine constant for this same frequency. The torsion lemma explicitly uses no Diophantine property of omegabar, and none is supplied here; the k-bridge concerns the old omega=s omega*. The frame perturbation application at the old omega is paid by the stated local data. The printed holomorphy/continuity discussion suggests a direct finite-frequency proof, but this record does not silently strengthen the cited Part 1 contract or add Diophantinity as a source hypothesis.

NODE: stepI:p2:to-omega
KIND: step
TITLE: Effect of the frequency on the torsion block
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L217-L218
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L217-L218
CONTRACT_ID: stepI:p2:to-omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:torsion, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:torsion, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: T_{omegabar}(Kbar)-T_omega(Kbar) = -Nbar^T Omega_0 [D Nbar_j Deltaomega]_j; ¦d_{Deltaomega} Nbar¦ <= n¦Deltaomega¦ 2m^2/delta on T_{r-4delta}; ¦Nbar^T¦ <= 4 n m^2; hence the difference is <= 8 n^2 m^4 d/delta on T_{r-4delta}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:cauchy-corollaries, stepI:p2:to-frame, bpI:p2:correction, bpI:p0:stripdata#torsion, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:cauchy-corollaries | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | Cauchy estimate with loss delta
EDGE: stepI:p2:to-frame | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | bound on Nbar
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | ¦Deltaomega¦ <= d
EDGE: bpI:p0:stripdata#torsion | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | torsion entries N_i.Omega_0(A N_j - D N_j omega)
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | m
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-omega@L218-L218 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.TorsionDiff.torsion_sub_freq, KAM.Iso.Apost.TorsionDiff.norm_torsion_sub_freq_le (KAM/Iso/Apost/TorsionDiff.lean)
LEAN_NOTE: audit I2-5 PASS WITH NOTES: to-omega affine identity and Cauchy bound
NOTE: -

NODE: stepI:p2:to-row
KIND: step
TITLE: Effect on the energy row
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L219-L220
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L219-L220
CONTRACT_ID: stepI:p2:to-row
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:torsion, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:torsion, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: Ybar-Y = (DH(Kbar)-DH(K))Nbar + DH(K)(Nbar-N); ¦DH(Kbar)-DH(K)¦ <= M d; ¦Ybar-Y¦ <= C_Y d/delta on T_{r-3delta}
CONSTANT_SCOPE: C_Y from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:increments-open, stepI:p2:to-frame, bpI:p2:correction, stepI:p2:ne-invert, bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:increments-open | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | F = DH: ¦DH(Kbar)-DH(K)¦ <= M d
EDGE: stepI:p2:to-frame | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | bounds on Nbar and Nbar-N
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | ¦Kbar-K¦ <= d
EDGE: stepI:p2:ne-invert | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | segment [K,Kbar] in D
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | M, ¦D^2 H¦ <= M on D
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | C_Y, C_DeltaN, m
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-row@L220-L220 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.TorsionDiff.energyRow_sub, KAM.Iso.Apost.TorsionDiff.sum_norm_energyRow_sub_le (KAM/Iso/Apost/TorsionDiff.lean)
LEAN_NOTE: audit I2-5 PASS WITH NOTES: to-row exact splitting and row estimate
NOTE: -

NODE: stepI:p2:to-avg
KIND: step
TITLE: The average
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L221-L222
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L221-L222
CONTRACT_ID: stepI:p2:to-avg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:torsion, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:torsion, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: avg Tbar - avg T = avg of [[Tbar_{omegabar}-T_omega, Deltaomega],[Ybar-Y, 0]] on R^n in T_{r-4delta}; its norm <= max{C_DeltaT^K d/delta^2 + 8 n^2 m^4 d/delta + d, C_Y d/delta} <= C_DeltaScriptT d/delta^2
CONSTANT_SCOPE: C_DeltaScriptT from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p2:averages, K:bp:p2:matrix, bpI:p2:standing#k-bridge, stepI:p2:to-frame, stepI:p2:to-omega, stepI:p2:to-row, bpI:p2:correction, bpI:p1:extended-basic, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p2:averages | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | (a): average of the difference
EDGE: K:bp:p2:matrix | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | (c): norm of the block matrix
EDGE: bpI:p2:standing#k-bridge | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | K averages/matrix lemmas under the standing data
EDGE: stepI:p2:to-frame | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | bound on Tbar_omega - T_omega
EDGE: stepI:p2:to-omega | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | effect of the frequency on the torsion block
EDGE: stepI:p2:to-row | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | bound on Ybar - Y
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | ¦Deltaomega¦ <= d
EDGE: bpI:p1:extended-basic | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | block structure of T_H and its average
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | C_DeltaScriptT
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-avg@L222-L222 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.TorsionDiff.norm_extendedTorsionAverage_sub_le, KAM.Iso.Apost.TorsionDiff.torsion_diff_arith (KAM/Iso/Apost/TorsionDiff.lean)
LEAN_NOTE: audit I2-5 PASS WITH NOTES: to-avg block difference, integral norm, domination
NOTE: -

NODE: stepI:p2:to-inv
KIND: step
TITLE: Inverse (Lemma~A.1)
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L223-L224
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L223-L224
CONTRACT_ID: stepI:p2:to-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:torsion, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:torsion, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: ¦avg T^{-1}¦ ¦avg Tbar-avg T¦<=1/2. Neumann gives invertibility and ¦avg Tbar^{-1}-avg T^{-1}¦<=2 sigma_T^2 ¦avg Tbar-avg T¦<=2m^2 C_DeltaScriptT d/delta^2, in the max-row-sum norm on C^{(n+1)x(n+1)}.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:neumann, stepI:p2:to-avg, bpI:p2:admissible, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:neumann | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L224-L224 | Neumann series (HL19 Lemma A.1)
EDGE: stepI:p2:to-avg | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L224-L224 | difference bound for the averages
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L224-L224 | B5: ¦avg T^{-1}¦ <= sigma_T
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L224-L224 | sigma_T <= m, C_DeltaScriptT
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:to-inv@L224-L224 | sigma_T
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.torsion_step (KAM/Iso/Apost/Torsion.lean)
LEAN_NOTE: audit I2-5 PASS WITH NOTES: to-inv assembly via neumann_fintype in torsion_step
NOTE: -

NODE: bpI:p2:step
KIND: proposition
TITLE: The isoenergetic step
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L227-L241
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L242-L250
CONTRACT_ID: bpI:p2:step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data; r>0, 0<delta<=1, 4delta<r, beta>0, 0<=eps<=1, s>1; K (r,beta,eps,s)-admissible; c_step eps/(gamma^4 delta^{2a}) <= min{1,beta}; Kbar, omegabar as in correction and new-error; d := C_Delta eps/(gamma^2 delta^a)
SOURCE_QUANTIFIERS: standing data, constants fixed; r, delta, beta, eps, s, K
SOURCE_CONCLUSION: (a) Kbar holomorphic, primary on T_{r-2delta}, real on reals; (b) ¦Kbar-K¦ <= d <= beta/2 on T_{r-2delta}, B_{beta-d}(Kbar(theta)) in D, ¦sbar-s¦¦omega*¦ <= d; (c) ¦E_{H,Kbar,omegabar}¦ <= C_E eps^2/(gamma^4 delta^{2a}) on T_{r-2delta} and ¦Ebar_H(Kbar)-E_0¦ <= C_E eps^2/(gamma^4 delta^{2a}); (d) ¦DKbar-DK¦ <= nd/delta, det Gbar != 0, ¦Bbar-B¦ <= C_B d/delta on T_{r-3delta}; (e) avg T_H(Kbar,omegabar) invertible with ¦avg Tbar^{-1}-avg T^{-1}¦ <= 2 m^2 C_DeltaScriptT d/delta^2
CONSTANT_SCOPE: Constants of Definition bpI:p2:constants: all depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* also on (mu,nu); delta_0 on (rho,rho_infty); no dependence on K, s, e, gamma, omega*, sigma_omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible, bpI:p2:correction, bpI:p2:newton-error, stepI:p2:st-small, stepI:p2:st-error, stepI:p2:st-frame
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L228-L228 | standing data
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L230-L230 | c_step, C_Delta, C_E, C_B, C_DeltaScriptT, a, m
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L228-L228 | K is (r,beta,eps,s)-admissible; B1-B7 and the frequency bound
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L232-L232 | Kbar, omegabar, d from the correction lemma
EDGE: bpI:p2:newton-error | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L232-L232 | errors of Kbar
EDGE: stepI:p2:st-small | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L243-L243 | proof step of this result
EDGE: stepI:p2:st-error | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L246-L246 | proof step of this result
EDGE: stepI:p2:st-frame | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:step@L248-L248 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-global-I
REVIEWER: sol-delta-I-global
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.step (KAM/Iso/Apost/Step.lean)
LEAN_NOTE: audit I2-6 PASS WITH NOTES: all conclusions (a)-(e)
NOTE: -

NODE: stepI:p2:st-small
KIND: step
TITLE: Smallness
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-small@L243-L245
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-small@L243-L245
CONTRACT_ID: stepI:p2:st-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:step, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:step, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: C_sym eps/(gamma delta^{kappa+1}) <= Theta^3 C_sym X <= 1/2; d <= Theta^2 C_Delta X <= beta/2; 2 m C_DeltaScriptT d/delta^2 <= 2 m Theta^2 C_DeltaScriptT C_Delta X <= 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:admissible, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-small@L244-L244 | gamma <= Theta (bpI:p2:freq) and gamma^2 delta^{a-2} <= Theta^2
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-small@L244-L244 | c_step, C_sym, C_Delta, C_DeltaScriptT, Theta, m
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-small@L244-L244 | gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.Arith.iso_step_small (KAM/Iso/Apost/ConstantsArith.lean)
LEAN_NOTE: audit I2-2 PASS WITH NOTES: exactly the three scalar conclusions of st-small
NOTE: -

NODE: stepI:p2:st-error
KIND: step
TITLE: Correction and errors
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L246-L247
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L246-L247
CONTRACT_ID: stepI:p2:st-error
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:step, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:step, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: (a) Kbar holomorphic, primary, real on reals (Kbar(theta+k) = K(theta)+(k,0)+DeltaK(theta)); (b) except the ball; (c) both errors <= C_E eps^2/(gamma^4 delta^{2a})
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:correction, bpI:p2:newton-error, stepI:p2:st-small, bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L247-L247 | DeltaK holomorphic, periodic, real; ¦DeltaK¦ <= d; ¦Deltaomega¦ <= d
EDGE: bpI:p2:newton-error | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L247-L247 | error bounds (c)
EDGE: stepI:p2:st-small | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L247-L247 | hypotheses d<beta and C_sym eps/(gamma delta^{kappa+1}) <= 1/2 of new-error
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L247-L247 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L247-L247 | Uses constants or exponents fixed by this package.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-error@L247-L247 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.step (KAM/Iso/Apost/Step.lean); KAM.Iso.Apost.torsion_step (KAM/Iso/Apost/Torsion.lean)
LEAN_NOTE: Rule 05:10: I2-6-audit-1.md:32-36 maps blueprint L234-238 items (a)-(e) to Step.lean:54-80; parent step PROVED.
NOTE: -

NODE: stepI:p2:st-frame
KIND: step
TITLE: Ball, frame, torsion
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L248-L249
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L248-L249
CONTRACT_ID: stepI:p2:st-frame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:step, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:step, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: B_{beta-d}(Kbar) in D from perturbation-noA5(a); (d) and (e) are bpI:p2:torsion
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:perturbation-noA5, bpI:p2:torsion, bpI:p2:correction, stepI:p2:st-small, bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:perturbation-noA5 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | (a): the ball
EDGE: bpI:p2:torsion | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | (d),(e)
EDGE: bpI:p2:correction | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | ¦Kbar-K¦ <= d input of the perturbation lemma
EDGE: stepI:p2:st-small | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | d <= beta/2 and the smallness of torsion
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | Uses constants or exponents fixed by this package.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:st-frame@L249-L249 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.step (KAM/Iso/Apost/Step.lean); KAM.Iso.Apost.torsion_step (KAM/Iso/Apost/Torsion.lean)
LEAN_NOTE: Rule 05:10: I2-6-audit-1.md:32-36 maps blueprint L234-238 items (a)-(e) to Step.lean:54-80; parent step PROVED.
NOTE: -

NODE: bpI:p2:schedule
KIND: definition
TITLE: Schedule
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:schedule@L255-L259
PROOF_SOURCE: -
CONTRACT_ID: bpI:p2:schedule
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<rho_infty<rho; gamma>0; e>=0
SOURCE_QUANTIFIERS: rho, rho_infty, gamma, e fixed; delta_s, r_s, eps_s, d_s defined for s>=0
SOURCE_CONCLUSION: defines delta_s := 2^{-s} delta_0, r_s := rho - 8 delta_0(1-2^{-s}), eps_0 := e, eps_{s+1} := C_E eps_s^2/(gamma^4 delta_s^{2a}), d_s := C_Delta eps_s/(gamma^2 delta_s^a); then r_0 = rho, r_{s+1} = r_s - 4 delta_s, rho_infty <= rho - 8 delta_0 < r_s, delta_s <= 1, 4 delta_s < r_s
CONSTANT_SCOPE: C_E, C_Delta, a, delta_0 from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:schedule@L256-L256 | delta_0, a, C_E, C_Delta
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:schedule@L256-L256 | gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.schedule (KAM/Apost/Schedule.lean); KAM.Iso.Apost.isoEpsSeq, KAM.Iso.Apost.isoDSeq (KAM/Iso/Apost/Defs.lean)
LEAN_NOTE: audit I2-7 PASS WITH NOTES: schedule reused; sequences are definitions (I-D0-2)
NOTE: Candidate edge to K:bp:p2:schedule dropped: '(as K:bp:p2:schedule)' is a comparison; the facts r_{s+1}=r_s-4 delta_s, delta_s<=1, 4 delta_s < r_s are routine algebra of the stated formulas.

NODE: bpI:p2:error-decay
KIND: lemma
TITLE: Decay
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:error-decay@L261-L263
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:error-decay@L264-L266
CONTRACT_ID: bpI:p2:error-decay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: schedule of bpI:p2:schedule; q := 2^{2a} C_E e/(gamma^4 delta_0^{2a}) <= 1
SOURCE_QUANTIFIERS: rho, rho_infty, gamma, e fixed
SOURCE_CONCLUSION: eps_s <= q^{2^s-1} 2^{-2as} e <= 2^{-2as} e; eps_s/delta_s^j <= e/delta_0^j for 0<=j<=2a; sum_s eps_s/delta_s^j <= 2e/delta_0^j for 0<=j<=2a-1
CONSTANT_SCOPE: C_E, a, delta_0 from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:schedule, bpI:p2:constants, bpI:p2:standing, K:bp:p1:iteration
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:error-decay@L262-L262 | eps_s, delta_s recursion
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:error-decay@L262-L262 | C_E, a, delta_0
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:error-decay@L262-L262 | gamma
EDGE: K:bp:p1:iteration | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:error-decay@L265-L265 | iteration lemma with p = 2a
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.iso_error_decay (KAM/Iso/Apost/Schedule.lean)
LEAN_NOTE: audit I2-7 PASS WITH NOTES: full decay contract, exact design type
NOTE: L265 explicitly supplies the scalar recurrence with Qprime=hatC_E/(gamma^4 delta_0^{2a}) and invokes K:bp:p1:iteration with p=2a; the remaining sums are geometric. The reference to K decay compares the proof and does not import its fixed C_E as an extra theorem hypothesis.

NODE: bpI:p2:iteration
KIND: proposition
TITLE: The induction
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L268-L283
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L284-L292
CONTRACT_ID: bpI:p2:iteration
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p2:standing; K and s=s_0>1 satisfy (I5)-(I12) of I-G1 on T_rho with margin mu: B1; B_mu(K) in D; ¦DK¦<=sigma_K-mu; det G != 0, ¦B¦<=sigma_B-mu; det avg T_H != 0, ¦avg T_H^{-1}¦<=sigma_T-mu; ¦E_{H,K,s omega*}¦<=e, ¦Ebar_H(K)-E_0¦<=e; nu(s_0)>=nu; e<=1; c_* e/(gamma^4 delta_0^{2a}) <= 1
SOURCE_QUANTIFIERS: standing data, constants, schedule fixed; then K, s_0, e; then there are K_j, s_j (K_0 = K) for all j
SOURCE_CONCLUSION: with D_j := sum_{i<j} d_i, for every j: (i) K_j is (r_j,mu-D_j,eps_j,s_j)-admissible, eps_j<=e<=1; (ii) D_j<=mu/4, D_j<=nu/2, ¦K_j-K¦<=D_j on T_{r_j}, ¦s_j-s_0¦¦omega*¦<=D_j, nu(s_j)>=nu-D_j>=nu/2, 1<s_j<sigma_omega; (iii) ¦DK_j¦ <= sigma_K-mu+sum nd_i/delta_i <= sigma_K-mu/2; (iv) ¦B_j¦ <= sigma_B-mu+sum C_B d_i/delta_i <= sigma_B-mu/2; (v) ¦avg T_j^{-1}¦ <= sigma_T-mu+sum 2 m^2 C_DeltaScriptT d_i/delta_i^2 <= sigma_T-mu/2; (vi) ¦K_{j+1}-K_j¦<=d_j, ¦DK_{j+1}-DK_j¦<=nd_j/delta_j on T_{r_{j+1}}, ¦s_{j+1}-s_j¦¦omega*¦<=d_j
CONSTANT_SCOPE: Constants of Definition bpI:p2:constants: all depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* also on (mu,nu); delta_0 on (rho,rho_infty); no dependence on K, s, e, gamma, omega*, sigma_omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing, bpI:p2:constants, bpI:p2:admissible, bpI:p2:schedule, bpI:p2:ray, stepI:p2:it-sums, stepI:p2:it-stepsmall, stepI:p2:it-step
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L269-L269 | standing data
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L271-L271 | c_*, delta_0, a
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L269-L269 | admissibility of K_j
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L275-L275 | r_j, delta_j, eps_j, d_j
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L276-L276 | nu(s_j) and 1<s_j<sigma_omega
EDGE: stepI:p2:it-sums | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L285-L285 | proof step of this result
EDGE: stepI:p2:it-stepsmall | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L288-L288 | proof step of this result
EDGE: stepI:p2:it-step | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:iteration@L290-L290 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.iteration (KAM/Iso/Apost/Iteration.lean)
LEAN_NOTE: audit I2-8 PASS: all six conclusions
NOTE: -

NODE: stepI:p2:it-sums
KIND: step
TITLE: Summed bounds
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L285-L287
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L285-L287
CONTRACT_ID: stepI:p2:it-sums
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:iteration, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:iteration, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: gamma <= Theta; sum_i d_i/delta_i^k <= 2 Theta^2 C_Delta X for k=0,1,2; hence sum d_i <= min{mu/4,nu/2}, sum n d_i/delta_i <= mu/4, sum C_B d_i/delta_i <= mu/4, sum 2 m^2 C_DeltaScriptT d_i/delta_i^2 <= mu/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:admissible, bpI:p2:error-decay, bpI:p2:schedule, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L286-L286 | gamma <= Theta from K admissible (bpI:p2:freq)
EDGE: bpI:p2:error-decay | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L286-L286 | eps_s/delta_s^j and sum bounds
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L286-L286 | d_i := C_Delta eps_i/(gamma^2 delta_i^a)
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L287-L287 | c_* >= 2^{2a}C_E, 2 c_sum/mu, 4 Theta^2 C_Delta/nu; C_B, C_DeltaScriptT
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-sums@L286-L286 | gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-b
REVIEWER: sol-delta-I-d
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.iso_sums_le (KAM/Iso/Apost/Iteration.lean)
LEAN_NOTE: audit I2-8 PASS: it-sums sums and five bounds (scalar helper iso_iteration_sums in I2-2)
NOTE: -

NODE: stepI:p2:it-stepsmall
KIND: step
TITLE: Step smallness
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L288-L289
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L288-L289
CONTRACT_ID: stepI:p2:it-stepsmall
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:iteration, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:iteration, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: c_step eps_j/(gamma^4 delta_j^{2a}) <= c_step X <= min{1,mu/2} <= min{1,mu-D_j}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p2:it-sums, bpI:p2:error-decay, bpI:p2:schedule, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p2:it-sums | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L289-L289 | X <= 1/c_* and D_j <= mu/4
EDGE: bpI:p2:error-decay | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L289-L289 | eps_j <= e and eps_j/delta_j^{2a} <= e/delta_0^{2a}
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L289-L289 | eps_j, delta_j
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L289-L289 | c_step <= c_*
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-stepsmall@L289-L289 | gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.iso_stepsmall_seq (KAM/Iso/Apost/Iteration.lean)
LEAN_NOTE: audit I2-8 PASS: every-stage step-smallness bound
NOTE: -

NODE: stepI:p2:it-step
KIND: step
TITLE: Base and induction
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L290-L291
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L290-L291
CONTRACT_ID: stepI:p2:it-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:iteration, with its definitions and inherited packages. For the induction transition assume (i)-(v) at j, as explicitly stated at L291. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:iteration, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: (i)-(v) at j+1 and (vi) at j: Proposition step applies with (r_j,delta_j,mu-D_j,eps_j,s_j) and yields K_{j+1} := Kbar_j, s_{j+1} := sbar_j; 1<s_{j+1}<sigma_omega and nu(s_{j+1}) >= nu-D_{j+1}; B1-B7 for K_{j+1}; (iii)-(v) with the summed bounds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:step, stepI:p2:it-sums, stepI:p2:it-stepsmall, bpI:p2:ray, bpI:p2:admissible, bpI:p2:schedule, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:step | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | Proposition step applied at each j
EDGE: stepI:p2:it-sums | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | summed bounds D_{j+1} <= nu/2, mu/4
EDGE: stepI:p2:it-stepsmall | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | smallness hypothesis of the step
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | (b): 1<sbar_j<sigma_omega, nu(sbar_j) >= nu(s_j)-d_j
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | admissibility at j and j+1; B3-B5
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | r_{j+1} = r_j-4 delta_j, d_j
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | c_*, C_B, C_DeltaScriptT
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:it-step@L291-L291 | standing data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-delta-I-d
REVIEWER: sol-delta-I-f
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.iso_stage_succ, KAM.Iso.Apost.iso_ray_step (KAM/Iso/Apost/Iteration.lean)
LEAN_NOTE: audit I2-8 PASS: induction step and ray step
NOTE: -

NODE: bpI:p2:limit
KIND: proposition
TITLE: The limit
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L294-L304
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L305-L314
CONTRACT_ID: bpI:p2:limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of bpI:p2:iteration; K_infty := lim K_j on T_{rho_infty}, K_infty := K elsewhere; s_infty := lim s_j
SOURCE_QUANTIFIERS: as in bpI:p2:iteration; then K_infty, s_infty
SOURCE_CONCLUSION: (a) limits exist; K_j -> K_infty and DK_j -> DK_infty uniformly on T_{rho_infty}; K_infty holomorphic, primary, real on reals; (b) ¦K_infty-K¦ <= 2 C_Delta e/(gamma^2 delta_0^a) <= mu/4 and ¦s_infty omega*-s_0 omega*¦ <= 2 C_Delta e/(gamma^2 delta_0^a) <= nu/2; (c) 1<s_infty<sigma_omega (nu(s_infty)>=nu/2); (d) B_{mu/2}(K_infty(theta)) in D and ¦DK_infty¦ <= sigma_K-mu/2 on T_{rho_infty}; (e) E_{H,K_infty,s_infty omega*} = 0 on T_{rho_infty}
CONSTANT_SCOPE: Constants of Definition bpI:p2:constants: all depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); hat-c_* also on (mu,nu); delta_0 on (rho,rho_infty); no dependence on K, s, e, gamma, omega*, sigma_omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:iteration, bpI:p2:standing, bpI:p2:constants, stepI:p2:lim-conv, stepI:p2:lim-close, stepI:p2:lim-margins, stepI:p2:lim-inv, bpI:p2:admissible, bpI:p2:schedule
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L295-L295 | the sequence (K_j,s_j) and (i)-(vi)
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L295-L295 | standing data
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L298-L298 | C_Delta, delta_0, a
EDGE: stepI:p2:lim-conv | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L306-L306 | proof step of this result
EDGE: stepI:p2:lim-close | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L308-L308 | proof step of this result
EDGE: stepI:p2:lim-margins | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L310-L310 | proof step of this result
EDGE: stepI:p2:lim-inv | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L312-L312 | proof step of this result
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L295-L295 | The setting of iteration includes admissibility and its scheduled sequences.
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:limit@L295-L295 | The setting of iteration includes admissibility and its scheduled sequences.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: isoLimit, isoSLimit, limit, isoLimit_eq, isoLimit_of_not_mem, isoLimit_tendsto, isoSLimit_tendsto, isoLimit_eq_iff, isoSLimit_eq_iff (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: audit I2-9 PASS WITH NOTES (selectors with convergence and uniqueness; I-G1 itself separate)
NOTE: -

NODE: stepI:p2:lim-conv
KIND: step
TITLE: Convergence
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L306-L307
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L306-L307
CONTRACT_ID: stepI:p2:lim-conv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:limit, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:limit, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: sum d_j <= 2 C_Delta e/(gamma^2 delta_0^a) and sum n d_j/delta_j <= 2n C_Delta e/(gamma^2 delta_0^{a+1}) converge; K_j, DK_j uniformly Cauchy, (s_j) Cauchy (omega* != 0); uniform limits give holomorphy, primary, real on reals and DK_infty = lim DK_j: (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:error-decay, K:bp:p1:uniform-limits, bpI:p2:iteration, bpI:p2:schedule, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:error-decay | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | convergence of the sums sum d_j and sum nd_j/delta_j
EDGE: K:bp:p1:uniform-limits | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | holomorphy, primary, real and DK_infty = lim DK_j
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | (vi) increments bounds
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | T_{rho_infty} in T_{r_j}: rho_infty < r_j
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | C_Delta, delta_0
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-conv@L307-L307 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: isoLimit_eq_of_tendsto, isoSLimit_eq_of_tendsto, isoDSeq_summable_tsum_le, isoDSeq_div_summable, exists_tendsto_of_dist_ray, tendsto_isoSLimit, isoLimit_tendsto, isoSLimit_tendsto (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: audit I2-9 PASS WITH NOTES; rows lim-conv
NOTE: -

NODE: stepI:p2:lim-close
KIND: step
TITLE: Closeness and frequency
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L308-L309
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L308-L309
CONTRACT_ID: stepI:p2:lim-close
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:limit, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:limit, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: ¦K_infty-K¦ <= sup D_j and ¦s_infty-s_0¦¦omega*¦ <= sup D_j <= min{mu/4,nu/2}: (b); nu(s_infty) >= nu/2 > 0: (c)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p2:it-sums, bpI:p2:iteration, bpI:p2:ray, stepI:p2:lim-conv, bpI:p2:standing, bpI:p2:constants, bpI:p2:schedule
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p2:it-sums | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | sup_j D_j <= min{mu/4,nu/2}
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | (ii): ¦K_j-K¦ <= D_j, nu(s_j) >= nu-D_j
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | nu(.) of ray (b): continuity of nu(s)
EDGE: stepI:p2:lim-conv | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | existence of the limits K_infty, s_infty
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | Uses constants or exponents fixed by this package.
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-close@L309-L309 | Uses the scheduled eps_j,delta_j,d_j or their partial sums.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.limit (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: Rule 05:10: I2-9-audit-1.md:61 and narrative on Limit.lean:408-428 (ray displacement, nu/2 margin, derivative and ball estimates); parent limit PROVED. (c) via ray Lipschitz at s_inf, same conclusion.
NOTE: -

NODE: stepI:p2:lim-margins
KIND: step
TITLE: Margins
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L310-L311
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L310-L311
CONTRACT_ID: stepI:p2:lim-margins
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:limit, with its definitions and inherited packages. For the ball inclusion take theta in T_{rho_infty} and ¦z-K_infty(theta)¦<mu/2. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:limit, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: z in D (¦z-K(theta)¦<3mu/4 and B_mu(K) in D); ¦DK_infty¦ = lim ¦DK_j¦ <= sigma_K-mu/2: (d)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:iteration, stepI:p2:lim-close, stepI:p2:lim-conv, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L311-L311 | B_mu(K) in D (I6) and (iii)
EDGE: stepI:p2:lim-close | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L311-L311 | ¦K_infty-K¦ <= mu/4
EDGE: stepI:p2:lim-conv | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L311-L311 | DK_infty = lim DK_j
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L311-L311 | D
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-margins@L311-L311 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Apost.limit (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: Rule 05:10: I2-9-audit-1.md:61 and narrative on Limit.lean:408-428 (ray displacement, nu/2 margin, derivative and ball estimates); parent limit PROVED. (c) via ray Lipschitz at s_inf, same conclusion.
NOTE: -

NODE: stepI:p2:lim-inv
KIND: step
TITLE: Invariance
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L312-L313
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L312-L313
CONTRACT_ID: stepI:p2:lim-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:limit, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:limit, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: E_j(theta) = X_H(K_j(theta)) - DK_j(theta) s_j omega* -> E_{H,K_infty,s_infty omega*}(theta) and ¦E_j¦ -> 0, so E_{H,K_infty,s_infty omega*} = 0 on T_{rho_infty}: (e)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:iteration, bpI:p2:error-decay, stepI:p2:lim-conv, stepI:p2:lim-margins, bpI:p2:standing, bpI:p0:stripdata#invarianceError, bpI:p2:admissible, bpI:p2:constants, bpI:p2:schedule
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | B6: ¦E_j¦ <= eps_j
EDGE: bpI:p2:error-decay | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | eps_j <= 2^{-2aj} e
EDGE: stepI:p2:lim-conv | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | K_j -> K_infty, DK_j -> DK_infty, s_j -> s_infty
EDGE: stepI:p2:lim-margins | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | K_infty(theta) in D
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | X_H continuous on D
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | E_{H,K,omega} = X_H(K) - DK omega
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | Uses B-component premises or frequency bound in the inherited admissible context.
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | Uses constants or exponents fixed by this package.
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:lim-inv@L313-L313 | Uses the scheduled eps_j,delta_j,d_j or their partial sums.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: isoEpsSeq_tendsto_zero, lim_invariance_moving (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: audit I2-9 PASS WITH NOTES; rows lim-inv
NOTE: -

NODE: bpI:p2:energy-limit
KIND: lemma
TITLE: Passage of the energy average to the limit
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L316-L318
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L319-L324
CONTRACT_ID: bpI:p2:energy-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of bpI:p2:limit
SOURCE_QUANTIFIERS: as in bpI:p2:limit
SOURCE_CONCLUSION: Ebar_H(K_infty) = E_0 and Ebar_H(K_j) -> Ebar_H(K_infty)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:limit, bpI:p2:standing, bpI:p0:extended#energyAverage, stepI:p2:el-unif, stepI:p2:el-int
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L317-L317 | the setting and K_j -> K_infty
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L317-L317 | H, E_0
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L317-L317 | Ebar_H
EDGE: stepI:p2:el-unif | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L320-L320 | proof step of this result
EDGE: stepI:p2:el-int | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:energy-limit@L322-L322 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: energy_limit, tendsto_energyAverage_of_uniform (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: audit I2-9 PASS WITH NOTES
NOTE: -

NODE: stepI:p2:el-unif
KIND: step
TITLE: Uniform convergence of $H\circ K_j$ on $\R^n$
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L320-L321
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L320-L321
CONTRACT_ID: stepI:p2:el-unif
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:energy-limit, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:energy-limit, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: ¦H(K_j)-H(K_infty)¦ <= M¦K_j-K_infty¦ -> 0 uniformly on R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:increments-open, bpI:p2:limit, bpI:p2:iteration, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:increments-open | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L321-L321 | F = H, ¦DH¦ <= M
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L321-L321 | (b): ¦K_infty-K¦ <= mu/4 and uniform convergence
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L321-L321 | ¦K_j-K¦ <= D_j <= mu/4 and B_mu(K) in D
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L321-L321 | ¦DH¦ <= M on D
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-unif@L321-L321 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: tendsto_energyAverage_of_uniform (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: audit I2-9 PASS WITH NOTES; row el-unif / el-int
NOTE: -

NODE: stepI:p2:el-int
KIND: step
TITLE: Integrals
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L322-L323
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L322-L323
CONTRACT_ID: stepI:p2:el-int
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:energy-limit, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:energy-limit, in the same order; the quantities constructed by earlier proof steps remain derived. For each j>=0.
SOURCE_CONCLUSION: H o K_infty integrable on [0,1]^n; ¦Ebar_H(K_j)-Ebar_H(K_infty)¦ <= sup ¦H(K_j)-H(K_infty)¦ -> 0; hence Ebar_H(K_infty) = E_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:ext-integral, stepI:p2:el-unif, bpI:p2:limit, bpI:p2:iteration, bpI:p2:error-decay, bpI:p2:standing, bpI:p0:extended#energyAverage, bpI:p2:admissible, bpI:p2:schedule
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:ext-integral | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | integrability of the continuous periodic H o K_infty
EDGE: stepI:p2:el-unif | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | uniform convergence of H o K_j
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | K_infty continuous, primary
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | B7: ¦Ebar_H(K_j)-E_0¦ <= eps_j
EDGE: bpI:p2:error-decay | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | eps_j -> 0
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | H periodic in theta
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | Ebar_H
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | Uses B-component premises or frequency bound in the inherited admissible context.
EDGE: bpI:p2:schedule | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:el-int@L323-L323 | Uses the scheduled eps_j,delta_j,d_j or their partial sums.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: tendsto_energyAverage_of_uniform (KAM/Iso/Apost/Limit.lean)
LEAN_NOTE: audit I2-9 PASS WITH NOTES; row el-unif / el-int
NOTE: -

NODE: bpI:p2:g1
KIND: theorem
TITLE: I-G1 with explicit constants
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L329-L337
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L338-L355
CONTRACT_ID: bpI:p2:g1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=2, tau>=n-1, 0<rho_infty<rho; M,sigma_K,sigma_B,sigma_T,mu,gammabar>0; sigma_omega>1; nu>0; omega* in R^n minus {0} (the data of I-G1 fixed); Definition bpI:p2:constants; for the inner statement D,H,K,s,gamma,e,E_0 satisfying (I1)-(I13) of I-G1
SOURCE_QUANTIFIERS: n, tau, rho, rho_infty, M, sigma_K, sigma_B, sigma_T, mu, gammabar, sigma_omega, nu, omega* fixed; then C_1, C_2, C_3 > 0; then for all D, H, K, s, gamma, e, E_0 satisfying (I1)-(I13): (O1)-(O6)
SOURCE_CONCLUSION: with C_1 := rho^{4 tau} max{gammabar^4, c_* delta_0^{-2a}}, C_2 = C_3 := 2 C_Delta rho^{2 tau} delta_0^{-a}: C_1,C_2,C_3>0 and the conclusions (O1)-(O6) of I-G1 hold
CONSTANT_SCOPE: C_1,C_2,C_3 depend only on (n,tau,rho,rho_infty,M,sigma_K,sigma_B,sigma_T,mu,gammabar,nu); fixed before D,H,K,s,gamma,e,E_0; do not use omega*, sigma_omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:constants, bpI:p2:standing, stepI:p2:g1-constants, stepI:p2:g1-standing, stepI:p2:g1-e, stepI:p2:g1-dict, stepI:p2:g1-apply, stepI:p2:g1-o, stepI:p2:g1-o2, stepI:p2:g1-o3
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L330-L330 | C_1,C_2,C_3 defined from C_Delta, c_*, delta_0, a
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L334-L334 | (I1)-(I4), E_0, gamma, omega* in Dio
EDGE: stepI:p2:g1-constants | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L339-L339 | proof step of this result
EDGE: stepI:p2:g1-standing | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L341-L341 | proof step of this result
EDGE: stepI:p2:g1-e | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L343-L343 | proof step of this result
EDGE: stepI:p2:g1-dict | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L345-L345 | proof step of this result
EDGE: stepI:p2:g1-apply | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L347-L347 | proof step of this result
EDGE: stepI:p2:g1-o | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L349-L349 | proof step of this result
EDGE: stepI:p2:g1-o2 | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L351-L351 | proof step of this result
EDGE: stepI:p2:g1-o3 | blueprint-I/parts/p2-iso-iteration.tex#bpI:p2:g1@L353-L353 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2
REVIEWER: sol-review-I-p2
LEAN_STATUS: PROVED
LEAN_REF: g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES (explicit-constant I-G1 body; frozen anchor sealed separately)
NOTE: -

NODE: stepI:p2:g1-constants
KIND: step
TITLE: The constants
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-constants@L339-L340
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-constants@L339-L340
CONTRACT_ID: stepI:p2:g1-constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Only the fixed outer I-G1 data n,tau,rho,rho_infty,M,sigma_K,sigma_B,sigma_T,mu,gammabar,sigma_omega,nu,omega* with their stated guards. C_1,C_2,C_3 are the displayed choices; finiteness and positivity follow from their definitions.
SOURCE_QUANTIFIERS: Fix the outer data first; construct C_1,C_2,C_3 from the displayed formulas, independently of omega*,sigma_omega; only afterward quantify D,H,K,s,gamma,e,E_0 in the theorem. No inner datum is assumed here.
SOURCE_CONCLUSION: C_1 >= rho^{4tau} gammabar^4 > 0 and C_2 > 0; their dependence is read off the definitions (rho^{4tau}, rho^{2tau} real powers of a positive number)
CONSTANT_SCOPE: C_1,C_2,C_3 depend only on (n,tau,rho,rho_infty,M,sigma_K,sigma_B,sigma_T,mu,gammabar,nu)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-constants@L340-L340 | finiteness, positivity and dependence of all constants
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-constants@L340-L340 | n, tau, M, sigma's, nu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: isoC1_pos, isoC2_pos (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES
NOTE: -

NODE: stepI:p2:g1-standing
KIND: step
TITLE: Standing data
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-standing@L341-L342
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-standing@L341-L342
CONTRACT_ID: stepI:p2:g1-standing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (I1)-(I4), E_0 in R, gamma>0, omega* in Dio_{gamma,tau} (I10)
SOURCE_QUANTIFIERS: data and D,H,E_0,gamma fixed
SOURCE_CONCLUSION: (I1)-(I4), E_0 in R, gamma>0 and omega* in Dio_{gamma,tau} from (I10), together with the fixed outer data, are exactly bpI:p2:standing.
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-standing@L342-L342 | the stated hypotheses are exactly the standing data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES; IsoStanding construction inside g1_explicit (G1:106-124)
NOTE: -

NODE: stepI:p2:g1-e
KIND: step
TITLE: Size of the errors
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-e@L343-L344
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-e@L343-L344
CONTRACT_ID: stepI:p2:g1-e
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:g1, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:g1, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: e < gamma^4/gammabar^4 <= 1, and c_* e/(gamma^4 delta_0^{2a}) < 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p2:g1-constants, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p2:g1-constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-e@L344-L344 | C_1 >= rho^{4tau} gammabar^4 and C_1 >= rho^{4tau}c_* delta_0^{-2a}
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-e@L344-L344 | c_*, delta_0, a
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-e@L344-L344 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: iso_g1_error_small (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES
NOTE: -

NODE: stepI:p2:g1-dict
KIND: step
TITLE: Dictionary for the hypotheses
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L345-L346
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L345-L346
CONTRACT_ID: stepI:p2:g1-dict
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:g1, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:g1, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: (I5): B1; (I6): B_mu(K) in D, ¦DK¦<=sigma_K-mu; (I7): det G != 0, ¦B¦<=sigma_B-mu; (I8): det avg T_H != 0, ¦avg T_H^{-1}¦ <= sigma_T-mu (average defined by extended-basic); (I9): s>1 and nu(s)>=nu; (I11)=B6, (I12)=B7; s>1 gives s omega* in Dio_{gamma,tau}; so K is (rho,mu,e,s)-admissible with the sharper constants
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:admissible, bpI:p1:extended-basic, bpI:p2:ray, stepI:p2:g1-e, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L346-L346 | identification of (I5)-(I12) with B1-B7 (sharper constants)
EDGE: bpI:p1:extended-basic | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L346-L346 | the average avg T_H is defined
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L346-L346 | s>1 gives s omega* in Dio_{gamma,tau}
EDGE: stepI:p2:g1-e | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L346-L346 | e<=1 so that eps = e is in the admissible range 0<=eps<=1 (prose L114-115)
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-dict@L346-L346 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: norm_le_of_rowSum_le_of_nonempty, margin_of_le, g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES; dictionary G1:128-146
NOTE: Preextract candidate edge to bpI:p0:totality dropped (administrative pointer, deleted in I-p0; the remark (T2) is a Lean-totality note, not a consumed fact).

NODE: stepI:p2:g1-apply
KIND: step
TITLE: Iteration and limit
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L347-L348
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L347-L348
CONTRACT_ID: stepI:p2:g1-apply
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:g1, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:g1, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: Propositions bpI:p2:iteration and bpI:p2:limit apply and give K_infty, s_infty
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:iteration, bpI:p2:limit, stepI:p2:g1-dict, stepI:p2:g1-e, stepI:p2:g1-standing, bpI:p2:constants, bpI:p2:standing, bpI:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:iteration | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | proposition applied
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | proposition applied
EDGE: stepI:p2:g1-dict | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | supplies the admissibility hypotheses (I5)-(I12)
EDGE: stepI:p2:g1-e | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | e<=1 and c_* e/(gamma^4 delta_0^{2a}) <= 1
EDGE: stepI:p2:g1-standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | standing data holds
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | constants
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
EDGE: bpI:p2:admissible | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-apply@L348-L348 | Uses B-component premises or frequency bound in the inherited admissible context.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES; applies Apost.limit, G1:147-149
NOTE: -

NODE: stepI:p2:g1-o
KIND: step
TITLE: (O1), (O4)--(O6)
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L349-L350
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L349-L350
CONTRACT_ID: stepI:p2:g1-o
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:g1, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:g1, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: (O1) is limit (a); (O4) is limit (d); (O5) ¦K_infty-K¦ <= 2 C_Delta e/(gamma^2 delta_0^a) = C_2 e/(gamma^2 rho^{2tau}) on T_{rho_infty}; (O6) ¦s_infty omega*-s omega*¦ <= C_3 e/(gamma^2 rho^{2tau}); 1<s_infty<sigma_omega by (c)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:limit, stepI:p2:g1-apply, stepI:p2:g1-constants, bpI:p2:constants, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L350-L350 | (a),(b),(c),(d)
EDGE: stepI:p2:g1-apply | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L350-L350 | limit applied
EDGE: stepI:p2:g1-constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L350-L350 | C_2,C_3 definitions/positivity
EDGE: bpI:p2:constants | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L350-L350 | C_Delta, delta_0, a
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o@L350-L350 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES; G1:156-164
NOTE: -

NODE: stepI:p2:g1-o2
KIND: step
TITLE: (O2)
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o2@L351-L352
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o2@L351-L352
CONTRACT_ID: stepI:p2:g1-o2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:g1, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:g1, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: (O2): E_{H,K_infty,s_infty omega*} = 0 on T_{rho_infty}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p2:limit, stepI:p2:g1-apply, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o2@L352-L352 | (e)
EDGE: stepI:p2:g1-apply | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o2@L352-L352 | limit applied
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o2@L352-L352 | Uses the standing H,D,omega*,gamma,sigmas and ray data.
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES; G1:147-149,161
NOTE: -

NODE: stepI:p2:g1-o3
KIND: step
TITLE: (O3)
STATEMENT_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L353-L354
PROOF_SOURCE: blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L353-L354
CONTRACT_ID: stepI:p2:g1-o3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: The stated local context and premises of bpI:p2:g1, with its definitions and inherited packages. Bounds and conclusions of cited prerequisite nodes are derived in this proof, not additional hypotheses.
SOURCE_QUANTIFIERS: All data quantified in bpI:p2:g1, in the same order; the quantities constructed by earlier proof steps remain derived. All pointwise formulas are on the strip or real cube stated in this step.
SOURCE_CONCLUSION: Assumption bpI:p1:setting holds with r = rho_infty, omega = s_infty omega*; by energy-conservation (b), H(K_infty(theta)) = E_0 for all theta in T_{rho_infty} (pointwise); no frame or Gram determinant of K_infty is used
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p2:energy-limit, bpI:p1:energy-conservation, bpI:p2:limit, stepI:p2:g1-o2, stepI:p2:g1-apply, bpI:p2:ray, bpI:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | Assumption bpI:p1:setting holds with r = rho_infty, omega = s_infty omega*
EDGE: bpI:p2:energy-limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | Ebar_H(K_infty) = E_0
EDGE: bpI:p1:energy-conservation | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | (b): H(K_infty) = E_0 pointwise
EDGE: bpI:p2:limit | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | K_infty regularity, (d) and (e)
EDGE: stepI:p2:g1-o2 | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | (O2): E = 0
EDGE: stepI:p2:g1-apply | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | limit applied
EDGE: bpI:p2:ray | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | s_infty omega* in Dio_{gamma,tau} since s_infty>1
EDGE: bpI:p2:standing | blueprint-I/parts/p2-iso-iteration.tex#stepI:p2:g1-o3@L354-L354 | E_0, D, H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p2+sol-review-I-p2
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: g1_explicit (KAM/Iso/Apost/G1.lean)
LEAN_NOTE: audit I2-10 PASS WITH NOTES; G1:151-155,161
NOTE: Preextract candidate edge to bpI:p1:o3 dropped (deleted administrative remark; the used fact is carried by bpI:p1:energy-conservation).

NODE: bpI:p3:setting
KIND: definition
TITLE: Data of Part~\ref{bpI:p3}
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:setting@L34-L46
PROOF_SOURCE: -
CONTRACT_ID: bpI:p3:setting
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data and standing hypotheses of Part 3: the I-HEAD data with n=2, B' nonempty, tau := 2)
SOURCE_QUANTIFIERS: B, s_0, r_0, h, B', eta, f, epsilon fixed (outermost); H := h+f
SOURCE_CONCLUSION: defines the data of Part 3: the data of I-HEAD with n=2: B in R^2 open, bounded, nonempty; s_0,r_0>0; h holomorphic on B_{r_0}, Im h = 0 and det B_h != 0 at every real I in B_{r_0}; B' in R^2 open with compact closure in B; eta>0; B' != empty; tau := 2 (> n-1 = 1); f: C^2 x C^2 -> C holomorphic on T_{s_0} x B_{r_0}, 1-periodic in theta there, real at real theta and real I in B_{r_0}, epsilon in R, 0<=epsilon, ¦f¦<=epsilon on T_{s_0} x B_{r_0}; H := h+f; iota: R^2 -> C^2 the inclusion, U := iota^{-1}(B_{r_0}) open with B in U
CONSTANT_SCOPE: all objects are fixed by the package; no dependence
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:bordered#borderedHessian, bpI:p0:domains#complexStrip, K:bp:p4:freq-map, bpI:p0:domains#actionNbhd
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:setting@L36-L36 | det B_h
EDGE: bpI:p0:domains#complexStrip | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:setting@L42-L42 | strip T_{s_0}
EDGE: K:bp:p4:freq-map | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:setting@L45-L45 | (i): iota B in B_{r_0}, so B in U
EDGE: bpI:p0:domains#actionNbhd | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:setting@L35-L35 | the domain B_{r_0} and its real preimage U
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: HeadData, BaseData, PerturbData, realAct, toC, totalH, realPart, rhoInf, fractD (KAM/Iso/Confinement/Setting.lean)
LEAN_NOTE: definition formalized; audit P5-0 PASS WITH NOTES (data of I-HEAD; no theorem needed)
NOTE: No edge to bpI:p0:head: the data are those of the I-HEAD statement (naming the hypotheses, not consuming the conclusion). No bridge edge: the K Part 4 bridge itself depends on this package.

NODE: bpI:p3:setting#k-bridge
KIND: step
TITLE: Bridge: K's Part 4 data is the Part 3 data (without Kolmogorov and boundary-layer hypotheses)
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:setting#k-bridge@L48-L50
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:setting#k-bridge@L48-L50
CONTRACT_ID: bpI:p3:setting#k-bridge
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting; only its common analytic/domain data are compared with K Part 4
SOURCE_QUANTIFIERS: n=2, B open bounded, h holomorphic on B_{r_0}, f as in the data
SOURCE_CONCLUSION: identifies the shared n=2, tau=2, B, s_0, r_0, h and perturbation data with the corresponding components of K Part 4, and imports the same shrunken domains/constants; the Kolmogorov and boundary-layer premises of K are explicitly excluded, not proved; the K tools used here use only this shared core, with epsilon <= 1 supplied where required
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, K:bp:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:setting#k-bridge@L48-L48 | the package of Part 3
EDGE: K:bp:p4:data | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:setting#k-bridge@L48-L48 | K's Part 4 setting
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.fractD_eq_domainD, KAM.Iso.Charts.totalH_eq_hbold (KAM/Iso/Charts/Defs.lean)
LEAN_NOTE: elementary bridge theorems; audit I-D0-1 PASS, I-D0-2 PASS
NOTE: This is a restriction to the common analytic/domain core, as the source explicitly says at L48-L50; it does not establish the full stronger K:bp:p4:data package. K h-bounded L173-L180, derivative-bounds L198-L222, freq-map L240-L273, and h1-open/holo L316-L327 use no L_h or C_B. No blanket discharge of every K hypothesis is claimed.

NODE: bpI:p3:constants
KIND: definition
TITLE: Constants of the data
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:constants@L52-L79
PROOF_SOURCE: -
CONTRACT_ID: bpI:p3:constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (definition; the data of Part 3; the K Part 4 constants)
SOURCE_QUANTIFIERS: (B,s_0,r_0,h,B',eta) fixed; then s, delta_*, mu, rho, rho_infty, D, D', M_h, c, c-bar, F_j, M; then d_B, eta_1, S; then m_h, M_g, S_h; then nu, sigma_omega, sigma_K, sigma_B, sigma_T, eps_T, e
SOURCE_CONCLUSION: defines (a) s := min{s_0,1}, delta_* := (1/4)min{s,r_0}, mu := delta_*/2, rho := s/4, rho_infty := s/8, D-frak := T_{s/2} x B_{r_0/2}, D' := T_{3s/4} x B_{3r_0/4}, M_h := sup{¦h¦: B_{3r_0/4}}, c-bar := max{1,c(2,j),c(4,j): j=1,2,3}, F_j := c-bar delta_*^{-j}, M := c-bar(M_h+1) delta_*^{-3}; (b) d_B := inf{¦I-J¦: I in closure B', J in R^2 minus B} > 0, eta_1 := min{eta,d_B/2}, S := {I: dist(I, closure B') <= d_B/2}; (c) m_h := min_S ¦grad h¦, M_g := max_S ¦grad h¦, S_h := max_S ¦B_h^{-1}¦ (row-sum norm); (d) nu := m_h/4, sigma_omega := 4M_g/m_h + 2, sigma_K := sigma_B := 1+mu, sigma_T := 2S_h+mu, eps_T := 1/(4 S_h F_2), e := F_1 eps (C_e := F_1)
CONSTANT_SCOPE: L78 says all the listed quantities depend only on (B,s_0,r_0,h,B',eta), eta only through eta_1, not on f, epsilon or any point. However L76 explicitly defines e = F_1 epsilon; thus that sentence cannot literally include e. All fixed coefficients, including C_e = F_1, have the stated independence; e retains its explicit epsilon dependence. This textual scope inconsistency is reported separately, not silently repaired.
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, K:bp:p4:data, bpI:p3:setting#k-bridge, K:bp:p4:h-bounded, K:bp:p1:cauchy-open, bpI:p3:ext-compact, bpI:p0:bordered#borderedHessian
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:constants@L52-L52 | (B,s_0,r_0,h,B',eta)
EDGE: K:bp:p4:data | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:constants@L53-L53 | K constants s, delta_*, mu, rho, rho_infty, D, D'
EDGE: bpI:p3:setting#k-bridge | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:constants@L53-L53 | K's Part 4 constants taken verbatim
EDGE: K:bp:p4:h-bounded | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:constants@L58-L58 | M_h < infinity
EDGE: K:bp:p1:cauchy-open | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:constants@L58-L58 | constants c(m,j)
EDGE: bpI:p3:ext-compact | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:constants@L62-L62 | d_B > 0 for compact closure B' in open B
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:constants@L69-L69 | B_h^{-1} in S_h
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.rhoIso, dB, eta1, sSet, mhConst, MgConst, ShConst, nuConst, sigmaOmegaConst, sigmaKConst, sigmaTConst, epsT (KAM/Iso/Charts/Defs.lean)
LEAN_NOTE: definitions landed, literal formulas; audit I-D0-1 PASS, I-D0-2 PASS
NOTE: SOURCE_SCOPE_INCONSISTENCY: e := F_1 epsilon at L76 conflicts with the blanket epsilon-independence sentence at L78 if e is included. No estimate or constant choice here uses independence of e.

NODE: bpI:p3:compact
KIND: lemma
TITLE: $\mathcal S$ and the constants are well defined
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:compact@L81-L83
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:compact@L84-L97
CONTRACT_ID: bpI:p3:compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting and Definition bpI:p3:constants
SOURCE_QUANTIFIERS: (B,s_0,r_0,h,B',eta) fixed
SOURCE_CONCLUSION: S is compact, closure B' in S in B, and 0<m_h<=M_g<infinity, 0<S_h<infinity
CONSTANT_SCOPE: m_h, M_g, S_h depend only on (B,s_0,r_0,h,B',eta)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:constants, stepI:p3:cp-compact, stepI:p3:cp-grad, stepI:p3:cp-inverse
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:compact@L81-L81 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:compact@L81-L81 | S, m_h, M_g, S_h
EDGE: stepI:p3:cp-compact | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:compact@L85-L85 | proof step of this result
EDGE: stepI:p3:cp-grad | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:compact@L89-L89 | proof step of this result
EDGE: stepI:p3:cp-inverse | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:compact@L92-L92 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3
REVIEWER: sol-review-I-p3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.compact, continuousOn_norm_inv, continuousOn_borderedHessian, frequencyMap_ne_zero_of_det_ne_zero (KAM/Iso/Charts/Constants.lean)
LEAN_NOTE: audit I3-1 PASS WITH NOTES; I3-2 PASS (compact exact design type)
NOTE: -

NODE: stepI:p3:cp-compact
KIND: step
TITLE: Compactness and inclusion
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-compact@L85-L88
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-compact@L85-L88
CONTRACT_ID: stepI:p3:cp-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d_B definition; closure B' compact; B open bounded
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: S is closed and bounded, hence compact; if I not in B then dist(I, closure B') >= d_B > d_B/2, so S in B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:constants, bpI:p3:setting, bpI:p3:ext-compact
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-compact@L86-L86 | S, d_B
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-compact@L86-L86 | B' with compact closure in the open bounded B
EDGE: bpI:p3:ext-compact | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-compact@L86-L86 | closed bounded sets in R^2 are compact; continuity of distance
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3
REVIEWER: sol-review-I-p3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.compact, continuousOn_norm_inv, continuousOn_borderedHessian, frequencyMap_ne_zero_of_det_ne_zero (KAM/Iso/Charts/Constants.lean)
LEAN_NOTE: step inside KAM.Iso.Charts.compact; audit I3-1 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:cp-grad
KIND: step
TITLE: The gradient is nonzero
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-grad@L89-L91
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-grad@L89-L91
CONTRACT_ID: stepI:p3:cp-grad
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting and constants
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: grad h != 0 on U (so on S); grad h continuous, so ¦grad h¦ attains a positive minimum m_h and a finite maximum M_g on S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:det-identity, K:bp:p4:freq-map, bpI:p3:setting#k-bridge, bpI:p3:ext-compact, bpI:p3:constants, bpI:p3:setting, stepI:p3:cp-compact
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:det-identity | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-grad@L90-L90 | (a): grad h(I) != 0 on U
EDGE: K:bp:p4:freq-map | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-grad@L91-L91 | (iii): grad h differentiable, hence continuous
EDGE: bpI:p3:setting#k-bridge | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-grad@L91-L91 | supplies the premises of the applied K Part 4 result under the Part 3 data
EDGE: bpI:p3:ext-compact | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-grad@L91-L91 | extrema on compact sets
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-grad@L91-L91 | S, m_h, M_g
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-grad@L90-L90 | S in B in U
EDGE: stepI:p3:cp-compact | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-grad@L91-L91 | S is compact and contained in B, as established above
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.compact, continuousOn_norm_inv, continuousOn_borderedHessian, frequencyMap_ne_zero_of_det_ne_zero (KAM/Iso/Charts/Constants.lean)
LEAN_NOTE: step inside KAM.Iso.Charts.compact; audit I3-1 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:cp-inverse
KIND: step
TITLE: The bordered inverse
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-inverse@L92-L96
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-inverse@L92-L96
CONTRACT_ID: stepI:p3:cp-inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting and constants
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: B_h^{-1} = adj B_h/det B_h has continuous real entries on U; its row-sum norm is continuous, hence bounded on S: 0<S_h<infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p4:freq-map, bpI:p3:setting#k-bridge, K:bp:p1:holomorphic-regularity, K:bp:p1:ext-cramer, K:bp:p1:real-inverse, bpI:p3:ext-compact, bpI:p3:setting, bpI:p3:constants, bpI:p0:bordered#borderedHessian, stepI:p3:cp-compact
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p4:freq-map | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-inverse@L93-L93 | (iii): entries of B_h continuous
EDGE: bpI:p3:setting#k-bridge | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-inverse@L93-L93 | supplies the premises of the applied K Part 4 result under the Part 3 data
EDGE: K:bp:p1:holomorphic-regularity | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-inverse@L94-L94 | continuity of second derivatives of holomorphic h
EDGE: K:bp:p1:ext-cramer | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-inverse@L95-L95 | B_h^{-1} = adj B_h/det B_h
EDGE: K:bp:p1:real-inverse | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-inverse@L96-L96 | inverse of a real matrix is real
EDGE: bpI:p3:ext-compact | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-inverse@L96-L96 | bounded on the compact S
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-inverse@L94-L94 | det B_h != 0 on U (hypothesis), iota U in B_{r_0}
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-inverse@L96-L96 | S_h
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-inverse@L93-L93 | entries of B_h
EDGE: stepI:p3:cp-compact | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cp-inverse@L96-L96 | S is compact and contained in B, as established above
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.compact, continuousOn_norm_inv, continuousOn_borderedHessian, frequencyMap_ne_zero_of_det_ne_zero (KAM/Iso/Charts/Constants.lean)
LEAN_NOTE: step inside KAM.Iso.Charts.compact; audit I3-1 PASS WITH NOTES
NOTE: -

NODE: bpI:p3:ext-ift
KIND: external
TITLE: Inverse function theorem
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:ext-ift@L102-L104
PROOF_SOURCE: -
CONTRACT_ID: bpI:p3:ext-ift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Omega in R^m open, F: Omega -> R^m is C^1, DF(c) invertible
SOURCE_QUANTIFIERS: Omega, F, c
SOURCE_CONCLUSION: there is an open W containing c, W in Omega, with F|_W a homeomorphism onto an open set with C^1 inverse; the restriction to an open W' in W has the same property
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3
REVIEWER: sol-review-I-p3
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p3:ext-compact
KIND: external
TITLE: Compactness
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:ext-compact@L105-L106
PROOF_SOURCE: -
CONTRACT_ID: bpI:p3:ext-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K compact subset of R^2; continuous function on K; K covered by open sets
SOURCE_QUANTIFIERS: K, function, cover
SOURCE_CONCLUSION: the function attains its extrema; the cover has a finite subcover (Heine-Borel)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3
REVIEWER: sol-review-I-p3
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p3:ext-lebesgue
KIND: external
TITLE: Lebesgue measure on $\R^2$
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:ext-lebesgue@L107-L107
PROOF_SOURCE: -
CONTRACT_ID: bpI:p3:ext-lebesgue
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lebesgue measure on R^2
SOURCE_QUANTIFIERS: sets in R^2
SOURCE_CONCLUSION: monotone and countably subadditive on outer measures; a nonempty open set has positive measure; a bounded set has finite measure
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3
REVIEWER: sol-review-I-p3
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p3:det-identity
KIND: lemma
TITLE: The bordered determinant
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:det-identity@L116-L123
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:det-identity@L124-L132
CONTRACT_ID: bpI:p3:det-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting; I in U; g := grad h(I); grad^2 h(I) := D(grad h)(I) (real symmetric)
SOURCE_QUANTIFIERS: I in U
SOURCE_CONCLUSION: det B_h(I) = - g^perp . grad^2 h(I) g^perp; consequently (a) grad h(I) != 0 whenever det B_h(I) != 0 (in particular on U); (b) if g != 0 then det B_h(I) != 0 iff det(g, grad^2 h(I) g^perp) != 0, and det(g, grad^2 h(I) g^perp) = g^perp . grad^2 h(I) g^perp = - det B_h(I)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, K:bp:p4:freq-map, bpI:p3:setting#k-bridge, bpI:p0:bordered#borderedHessian, stepI:p3:di-expand, stepI:p3:di-conseq
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:det-identity@L117-L117 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
EDGE: K:bp:p4:freq-map | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:det-identity@L117-L117 | (iii): grad^2 h real symmetric
EDGE: bpI:p3:setting#k-bridge | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:det-identity@L117-L117 | supplies the premises of the applied K Part 4 result under the Part 3 data
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:det-identity@L118-L118 | det B_h(I)
EDGE: stepI:p3:di-expand | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:det-identity@L125-L125 | proof step of this result
EDGE: stepI:p3:di-conseq | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:det-identity@L130-L130 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3
REVIEWER: sol-review-I-p3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.det_identity, borderedHessian_det_eq, hessR_transpose (KAM/Iso/Charts/Coordinates.lean); KAM.Iso.Charts.frequencyMap_ne_zero_of_det_ne_zero (KAM/Iso/Charts/Constants.lean)
LEAN_NOTE: parts (a),(b) covered; audit I3-1 PASS WITH NOTES, I3-2 PASS
NOTE: -

NODE: stepI:p3:di-expand
KIND: step
TITLE: Expansion
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:di-expand@L125-L129
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:di-expand@L125-L129
CONTRACT_ID: stepI:p3:di-expand
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; I in U; g and real Hessian as defined in det-identity
SOURCE_QUANTIFIERS: I in U
SOURCE_CONCLUSION: B_h = [[h_11,h_12,h_1],[h_12,h_22,h_2],[h_1,h_2,0]]; det B_h = -(h_22 h_1^2 - 2 h_12 h_1 h_2 + h_11 h_2^2) = - g^perp . grad^2 h g^perp
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:bordered#borderedHessian, bpI:p1:trivial, stepI:p1:tr-compare, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:di-expand@L126-L126 | definition of B_h
EDGE: bpI:p1:trivial | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:di-expand@L126-L126 | B_h as the torsion of the trivial torus
EDGE: stepI:p1:tr-compare | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:di-expand@L126-L126 | identification of the entries of B_h
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:di-expand@L126-L126 | local Part 3 data, including h, B', f or epsilon
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.det_identity, borderedHessian_det_eq, hessR_transpose (KAM/Iso/Charts/Coordinates.lean); KAM.Iso.Charts.frequencyMap_ne_zero_of_det_ne_zero (KAM/Iso/Charts/Constants.lean)
LEAN_NOTE: borderedHessian_det_eq; audit I3-1 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:di-conseq
KIND: step
TITLE: Consequences
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:di-conseq@L130-L131
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:di-conseq@L130-L131
CONTRACT_ID: stepI:p3:di-conseq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; I in U; for (b), g != 0
SOURCE_QUANTIFIERS: I in U
SOURCE_CONCLUSION: (a) g=0 gives 0 = det B_h so det B_h != 0 forces g != 0; (b) det(g,w) = g^perp . w with w = grad^2 h g^perp
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p3:di-expand, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p3:di-expand | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:di-conseq@L131-L131 | the identity det B_h = - g^perp . grad^2 h g^perp
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:di-conseq@L131-L131 | local Part 3 data, including h, B', f or epsilon
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.det_identity, borderedHessian_det_eq, hessR_transpose (KAM/Iso/Charts/Coordinates.lean); KAM.Iso.Charts.frequencyMap_ne_zero_of_det_ne_zero (KAM/Iso/Charts/Constants.lean)
LEAN_NOTE: det_identity last equality gives equivalence; audit I3-1 PASS WITH NOTES
NOTE: -

NODE: bpI:p3:coordinates
KIND: definition
TITLE: Direction coordinates at a point
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:coordinates@L134-L149
PROOF_SOURCE: -
CONTRACT_ID: bpI:p3:coordinates
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting; c in closure B', g_c := grad h(c) != 0, q_c := g_c . g_c > 0
SOURCE_QUANTIFIERS: c fixed; then w in R^2; I in U_c
SOURCE_CONCLUSION: defines a_c(w) := g_c.w/q_c, b_c(w) := det(g_c,w)/q_c (w = a_c g_c + b_c g_c^perp); on {a_c>0} the slope sigma_c(w) := b_c(w)/a_c(w); U_c := {I in U: a_c(grad h(I)) > 0} open with c in U_c; m_c(I) := sigma_c(grad h(I)), Phi_c(I) := (h(I), m_c(I)); Phi_c is C^1 on U_c, Phi_c(c) = (h(c),0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:det-identity, K:bp:p4:freq-map, bpI:p3:setting#k-bridge, K:bp:p1:holomorphic-regularity
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:coordinates@L135-L135 | c in closure B', U, h
EDGE: bpI:p3:det-identity | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:coordinates@L135-L135 | (a): g_c = grad h(c) != 0
EDGE: K:bp:p4:freq-map | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:coordinates@L148-L148 | grad h is C^1 on U
EDGE: bpI:p3:setting#k-bridge | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:coordinates@L148-L148 | supplies the premises of the applied K Part 4 result under the Part 3 data
EDGE: K:bp:p1:holomorphic-regularity | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:coordinates@L148-L148 | the Hessian entries are continuous, so the displayed derivative of grad h is continuous
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.perp, det2, aCoord, bCoord, slope, hessR, chartDom, chartM, chartPhi, jac2 (KAM/Iso/Charts/Defs.lean); KAM.Iso.Charts.coordinates (KAM/Iso/Charts/Coordinates.lean)
LEAN_NOTE: defs audit I-D0-1/2 PASS; C1 chart/openness theorem audit I3-1 PASS WITH NOTES
NOTE: -

NODE: bpI:p3:slope-ray
KIND: claim
TITLE: Slopes encode rays
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:slope-ray@L151-L156
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:slope-ray@L151-L156
CONTRACT_ID: bpI:p3:slope-ray
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a_c(w), a_c(w') > 0; I in U_c; omega* with a_c(omega*) > 0
SOURCE_QUANTIFIERS: c, w, w', I, omega*
SOURCE_CONCLUSION: sigma_c(w) = sigma_c(w') iff w' = lambda w with lambda > 0, lambda = a_c(w')/a_c(w); m_c(I) = sigma_c(omega*) iff grad h(I) = s omega* with s = a_c(grad h(I))/a_c(omega*) > 0, and then s = ¦grad h(I)¦/¦omega*¦ for the max norm
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:coordinates, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:slope-ray@L152-L152 | a_c, sigma_c, m_c, U_c
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:slope-ray@L154-L154 | local Part 3 data, including h, B', f or epsilon
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.slope_ray (KAM/Iso/Charts/Coordinates.lean)
LEAN_NOTE: audit I3-1 PASS WITH NOTES, I3-2 PASS
NOTE: Remark node kept: consumed by stepI:p3:pt-parallel (it supplies grad h(I_pm) = s omega*_pm).

NODE: bpI:p3:chart
KIND: lemma
TITLE: Local chart
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:chart@L158-L164
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:chart@L165-L175
CONTRACT_ID: bpI:p3:chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting; c in closure B'
SOURCE_QUANTIFIERS: for every c in closure B', D Phi_c(c) is invertible; for every prescribed open neighbourhood O of c there is an open W with c in W subset U_c intersect O
SOURCE_CONCLUSION: D Phi_c(c) is invertible with det D Phi_c(c) = - det B_h(c)/q_c != 0; hence there is an open W in U_c with c in W such that Phi_c|_W: W -> V := Phi_c(W) is a homeomorphism onto an open set with C^1 inverse, and W may be taken inside any prescribed open neighbourhood of c
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:coordinates, stepI:p3:ch-deriv, stepI:p3:ch-det, stepI:p3:ch-ift
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:chart@L159-L159 | c in closure B', det B_h != 0
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:chart@L159-L159 | Phi_c, q_c
EDGE: stepI:p3:ch-deriv | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:chart@L166-L166 | proof step of this result
EDGE: stepI:p3:ch-det | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:chart@L170-L170 | proof step of this result
EDGE: stepI:p3:ch-ift | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:chart@L173-L173 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.chart, fderiv_chartM_apply, jac2_chartPhi, bijective_of_jac_ne_zero (KAM/Iso/Charts/Chart.lean)
LEAN_NOTE: exact design type; audit I3-2 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:ch-deriv
KIND: step
TITLE: Derivative of $h$ and of $m_c$
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-deriv@L166-L169
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-deriv@L166-L169
CONTRACT_ID: stepI:p3:ch-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; c in closure B'; direction u in R^2; coordinates of bpI:p3:coordinates
SOURCE_QUANTIFIERS: c in closure B' fixed; every real direction u and increment dw
SOURCE_CONCLUSION: D sigma_c(g_c)[dw] = det(g_c,dw)/q_c; D m_c(c)u = (grad^2 h(c) g_c^perp).u/q_c
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p4:freq-map, bpI:p3:setting#k-bridge, bpI:p3:coordinates, bpI:p3:setting, bpI:p1:ext-chain
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p4:freq-map | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-deriv@L167-L167 | (ii): Dh(c)u = g_c.u; (iii): symmetry
EDGE: bpI:p3:setting#k-bridge | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-deriv@L167-L167 | supplies the premises of the applied K Part 4 result under the Part 3 data
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-deriv@L167-L167 | sigma_c, m_c, q_c
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-deriv@L167-L167 | local Part 3 data, including h, B', f or epsilon
EDGE: bpI:p1:ext-chain | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-deriv@L168-L168 | chain rule for sigma_c composed with grad h
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.chart, fderiv_chartM_apply, jac2_chartPhi, bijective_of_jac_ne_zero (KAM/Iso/Charts/Chart.lean)
LEAN_NOTE: fderiv_chartM_apply; audit I3-2 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:ch-det
KIND: step
TITLE: Determinant
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-det@L170-L172
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-det@L170-L172
CONTRACT_ID: stepI:p3:ch-det
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; c in closure B'; coordinates of bpI:p3:coordinates
SOURCE_QUANTIFIERS: c in closure B'
SOURCE_CONCLUSION: det D Phi_c(c) = det(g_c, grad^2 h(c) g_c^perp)/q_c = - det B_h(c)/q_c != 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p3:ch-deriv, bpI:p3:det-identity, bpI:p3:setting, bpI:p3:coordinates
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p3:ch-deriv | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-det@L171-L171 | rows g_c^T and (grad^2 h(c) g_c^perp)^T/q_c
EDGE: bpI:p3:det-identity | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-det@L171-L171 | (b): det(g, grad^2 h g^perp) = - det B_h
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-det@L172-L172 | c in closure B' in B in U, iota U in B_{r_0}, det B_h != 0
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-det@L171-L171 | q_c, gradient or slope/chart coordinates
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.chart, fderiv_chartM_apply, jac2_chartPhi, bijective_of_jac_ne_zero (KAM/Iso/Charts/Chart.lean)
LEAN_NOTE: jac2_chartPhi; audit I3-2 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:ch-ift
KIND: step
TITLE: Inverse function theorem
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-ift@L173-L174
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-ift@L173-L174
CONTRACT_ID: stepI:p3:ch-ift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; c in closure B'; an arbitrary prescribed open neighbourhood of c
SOURCE_QUANTIFIERS: c in closure B'
SOURCE_CONCLUSION: the inverse function theorem gives W; intersecting with a prescribed neighbourhood of c keeps the conclusion
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:ext-ift, bpI:p3:coordinates, stepI:p3:ch-det, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:ext-ift | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-ift@L174-L174 | inverse function theorem (Y1)
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-ift@L174-L174 | U_c open, Phi_c C^1
EDGE: stepI:p3:ch-det | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-ift@L174-L174 | D Phi_c(c) invertible
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ch-ift@L174-L174 | local Part 3 data, including h, B', f or epsilon
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.chart, fderiv_chartM_apply, jac2_chartPhi, bijective_of_jac_ne_zero (KAM/Iso/Charts/Chart.lean)
LEAN_NOTE: bijective_of_jac_ne_zero + chart; audit I3-2 PASS WITH NOTES
NOTE: -

NODE: bpI:p3:patch
KIND: definition
TITLE: Patch
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:patch@L177-L186
PROOF_SOURCE: -
CONTRACT_ID: bpI:p3:patch
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting; c in closure B'; W as in the chart lemma; delta_E, delta_m, rho_c > 0; V = Phi_c(W)
SOURCE_QUANTIFIERS: (c, W, delta_E, delta_m, rho_c)
SOURCE_CONCLUSION: defines a patch p = (c,W,delta_E,delta_m,rho_c) with (P1) W in {¦I-c¦<eta_1/4} (so W in S); (P2) the box Q = [h(c)-delta_E, h(c)+delta_E] x [-delta_m,delta_m] lies in V; (P3) rho_c <= eta_1/4, {¦I-c¦<rho_c} in W and there ¦h(I)-h(c)¦<delta_E/2 and ¦m_c(I)¦<delta_m/4; Phi_p^{-1}: V -> W the inverse
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:chart, bpI:p3:coordinates, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:chart | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:patch@L178-L178 | W, V as in the chart lemma
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:patch@L178-L178 | Phi_c, m_c
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:patch@L181-L181 | eta_1, S
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:patch@L178-L178 | c in closure B'
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3
REVIEWER: sol-review-I-p3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.IsPatch, IsPatch.toEnergyPatch (KAM/Iso/Charts/Defs.lean); KAM.Iso.Charts.exists_isPatch (KAM/Iso/Charts/Chart.lean)
LEAN_NOTE: patch certificate defined (audit I-D0-1 PASS); existence by exists_isPatch (audit I3-2)
NOTE: -

NODE: bpI:p3:cover
KIND: lemma
TITLE: Finite cover
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:cover@L188-L192
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:cover@L193-L199
CONTRACT_ID: bpI:p3:cover
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting and Definition bpI:p3:constants
SOURCE_QUANTIFIERS: (B,s_0,r_0,h,B',eta) fixed; then finitely many patches p_j
SOURCE_CONCLUSION: there are finitely many patches p_j = (c_j,W_j,delta_{E,j},delta_{m,j},rho_j), j in P, with closure B' in the union of {¦I-c_j¦<rho_j}; the family depends only on (B,s_0,r_0,h,B',eta)
CONSTANT_SCOPE: the family P, p_j depends only on (B,s_0,r_0,h,B',eta)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:patch, bpI:p3:constants, stepI:p3:cv-local, stepI:p3:cv-compact
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:cover@L189-L189 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:cover@L189-L189 | the patches
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:cover@L189-L189 | eta_1
EDGE: stepI:p3:cv-local | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:cover@L194-L194 | proof step of this result
EDGE: stepI:p3:cv-compact | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:cover@L197-L197 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3
REVIEWER: sol-review-I-p3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.cover, exists_isPatch, exists_window (KAM/Iso/Charts/Chart.lean)
LEAN_NOTE: exact design type; audit I3-2 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:cv-local
KIND: step
TITLE: A patch at every $c\in\overline{B'}$
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-local@L194-L196
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-local@L194-L196
CONTRACT_ID: stepI:p3:cv-local
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting and constants; c in closure B'
SOURCE_QUANTIFIERS: c in closure B'
SOURCE_CONCLUSION: a patch exists at every c: W with (P1); delta_E, delta_m small for (P2); rho_c small for (P3)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:chart, bpI:p3:patch, bpI:p3:coordinates, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:chart | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-local@L195-L195 | W inside the neighbourhood
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-local@L195-L195 | (P1)-(P3)
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-local@L196-L196 | h, m_c continuous on U_c, m_c(c)=0, Phi_c(c)
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-local@L195-L195 | eta_1
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-local@L194-L194 | c in closure B'
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.cover, exists_isPatch, exists_window (KAM/Iso/Charts/Chart.lean)
LEAN_NOTE: exists_isPatch/exists_window; audit I3-2 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:cv-compact
KIND: step
TITLE: Compactness
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-compact@L197-L198
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-compact@L197-L198
CONTRACT_ID: stepI:p3:cv-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting and constants
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: finite subcover
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p3:cv-local, bpI:p3:ext-compact, bpI:p3:setting, bpI:p3:patch
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p3:cv-local | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-compact@L198-L198 | a patch at every c
EDGE: bpI:p3:ext-compact | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-compact@L198-L198 | Heine-Borel
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-compact@L198-L198 | closure B' compact
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:cv-compact@L198-L198 | rho_c is the radius component of the constructed patch
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.cover, exists_isPatch, exists_window (KAM/Iso/Charts/Chart.lean)
LEAN_NOTE: inside cover; audit I3-2 PASS WITH NOTES
NOTE: -

NODE: bpI:p3:dio-open
KIND: lemma
TITLE: Diophantine vectors in an open set
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:dio-open@L204-L209
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:dio-open@L210-L215
CONTRACT_ID: bpI:p3:dio-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: tau = 2; O in R^2 nonempty, open, bounded
SOURCE_QUANTIFIERS: O fixed; then gamma>0, omega
SOURCE_CONCLUSION: there are gamma>0 and omega in O cap Dio_{gamma,2}
CONSTANT_SCOPE: gamma depends on O (and tau=2)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p0:g3, bpI:p0:diophantine#IsDiophantine, stepI:p3:do-positive, stepI:p3:do-choice
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p0:g3 | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:dio-open@L212-L212 | measure estimate G3 (frozen KAM.volume_not_diophantine_le)
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:dio-open@L205-L205 | Dio_{gamma,2}
EDGE: stepI:p3:do-positive | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:dio-open@L211-L211 | proof step of this result
EDGE: stepI:p3:do-choice | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:dio-open@L213-L213 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3
REVIEWER: sol-review-I-p3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.dio_open (KAM/Iso/Charts/Rays.lean)
LEAN_NOTE: uses verbatim G3 premise (ruled); audit I3-3 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:do-positive
KIND: step
TITLE: Positive measure
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:do-positive@L211-L212
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:do-positive@L211-L212
CONTRACT_ID: stepI:p3:do-positive
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: O nonempty open bounded; n=2, tau=2>1
SOURCE_QUANTIFIERS: O fixed
SOURCE_CONCLUSION: 0<meas O<infinity and G3 gives C>=0 with meas{omega in O not in Dio_{alpha,2}} <= C alpha for all alpha>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:ext-lebesgue, K:bp:p0:g3, bpI:p0:diophantine#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:ext-lebesgue | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:do-positive@L212-L212 | positivity and finiteness of the measure
EDGE: K:bp:p0:g3 | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:do-positive@L212-L212 | measure of non-Diophantine vectors
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:do-positive@L212-L212 | Dio_{alpha,2}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3
REVIEWER: sol-review-I-p3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.dio_open (KAM/Iso/Charts/Rays.lean)
LEAN_NOTE: measure argument inside dio_open; audit I3-3 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:do-choice
KIND: step
TITLE: Choice of $\gamma$
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:do-choice@L213-L214
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:do-choice@L213-L214
CONTRACT_ID: stepI:p3:do-choice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: O nonempty, open and bounded in R^2; tau = 2
SOURCE_QUANTIFIERS: O fixed
SOURCE_CONCLUSION: gamma := meas O/(2(C+1)) gives meas{omega in O not in Dio_{gamma,2}} <= C gamma < meas O so O cap Dio_{gamma,2} is nonempty
CONSTANT_SCOPE: gamma depends on O only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p3:do-positive, bpI:p3:ext-lebesgue, bpI:p0:diophantine#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p3:do-positive | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:do-choice@L214-L214 | the constant C and meas O
EDGE: bpI:p3:ext-lebesgue | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:do-choice@L214-L214 | subadditivity
EDGE: bpI:p0:diophantine#IsDiophantine | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:do-choice@L214-L214 | Dio_{gamma,2}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.dio_open (KAM/Iso/Charts/Rays.lean)
LEAN_NOTE: inside dio_open; audit I3-3 PASS WITH NOTES
NOTE: -

NODE: bpI:p3:rays
KIND: lemma
TITLE: Rays in a sector
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:rays@L217-L222
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:rays@L223-L230
CONTRACT_ID: bpI:p3:rays
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c in closure B'; J in R nonempty open bounded interval; Assumption bpI:p3:setting and Definition bpI:p3:constants (m_h, coordinates a_c, sigma_c)
SOURCE_QUANTIFIERS: c, J fixed; then gamma>0 and omega*
SOURCE_CONCLUSION: there are gamma>0 and omega* in R^2 with omega* in Dio_{gamma,2}, a_c(omega*)>0, sigma_c(omega*) in J, m_h/4 < ¦omega*¦ < m_h/2
CONSTANT_SCOPE: gamma, omega* depend on (c,J) and the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:constants, bpI:p3:coordinates, stepI:p3:ry-open, stepI:p3:ry-dio, bpI:p3:compact
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:rays@L218-L218 | c in closure B'
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:rays@L220-L220 | m_h
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:rays@L218-L218 | a_c, sigma_c
EDGE: stepI:p3:ry-open | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:rays@L224-L224 | proof step of this result
EDGE: stepI:p3:ry-dio | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:rays@L228-L228 | proof step of this result
EDGE: bpI:p3:compact | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:rays@L227-L227 | m_h > 0 makes the chosen norm-shell witness belong to O
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-delta-I-b
REVIEWER: sol-delta-I-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.rays, aCoord_slope_dir, isOpen_sector, frequencyMap_ne_zero_of_mem_closure (KAM/Iso/Charts/Rays.lean)
LEAN_NOTE: exact design signature; audit I3-3 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:ry-open
KIND: step
TITLE: An open nonempty set
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ry-open@L224-L227
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ry-open@L224-L227
CONTRACT_ID: stepI:p3:ry-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting and constants; c in closure B'; J a nonempty open bounded interval
SOURCE_QUANTIFIERS: c, J fixed
SOURCE_CONCLUSION: O := {a_c>0, sigma_c in J, m_h/4<¦omega¦<m_h/2} is open, bounded and nonempty (omega_t = t(g_c+varsigma g_c^perp) with t = (3/8)m_h/¦g_c+varsigma g_c^perp¦ lies in O)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:coordinates, bpI:p3:constants, bpI:p3:setting, bpI:p3:compact
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ry-open@L225-L225 | a_c, sigma_c, g_c^perp
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ry-open@L225-L225 | m_h
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ry-open@L226-L226 | local Part 3 data, including h, B', f or epsilon
EDGE: bpI:p3:compact | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ry-open@L227-L227 | positive finite m_h, M_g, S_h and attained bounds on S
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.rays, aCoord_slope_dir, isOpen_sector, frequencyMap_ne_zero_of_mem_closure (KAM/Iso/Charts/Rays.lean)
LEAN_NOTE: aCoord_slope_dir, isOpen_sector; audit I3-3 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:ry-dio
KIND: step
TITLE: Diophantine
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ry-dio@L228-L229
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ry-dio@L228-L229
CONTRACT_ID: stepI:p3:ry-dio
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting and constants; c in closure B'; J a nonempty open bounded interval; O is the set defined in ry-open
SOURCE_QUANTIFIERS: c, J fixed
SOURCE_CONCLUSION: Lemma dio-open applied to O gives gamma>0 and omega* in O cap Dio_{gamma,2}
CONSTANT_SCOPE: gamma depends on O
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:dio-open, stepI:p3:ry-open, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:dio-open | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ry-dio@L229-L229 | Diophantine vector in the open set O
EDGE: stepI:p3:ry-open | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ry-dio@L229-L229 | O is open, bounded, nonempty
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ry-dio@L229-L229 | local Part 3 data, including h, B', f or epsilon
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.rays, aCoord_slope_dir, isOpen_sector, frequencyMap_ne_zero_of_mem_closure (KAM/Iso/Charts/Rays.lean)
LEAN_NOTE: inside rays via dio_open; audit I3-3 PASS WITH NOTES
NOTE: -

NODE: bpI:p3:patch-rays
KIND: definition
TITLE: Rays of a patch
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:patch-rays@L232-L240
PROOF_SOURCE: -
CONTRACT_ID: bpI:p3:patch-rays
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting; patch p = (c,W,delta_E,delta_m,rho_c) of the cover
SOURCE_QUANTIFIERS: p fixed; then omega*_{p,+-}, gamma_{p,+-}, m_{p,+-}
SOURCE_CONCLUSION: for each patch choose by Lemma rays with J_+ = (delta_m/2,delta_m), J_- = (-delta_m,-delta_m/2) vectors omega*_{p,+-} and gamma_{p,+-}>0 with omega*_{p,+-} in Dio_{gamma_{p,+-},2}, a_c(omega*_{p,+-})>0, m_h/4<¦omega*_{p,+-}¦<m_h/2; m_{p,+-} := sigma_c(omega*_{p,+-}), m_{p,+} in (delta_m/2,delta_m), m_{p,-} in (-delta_m,-delta_m/2); 2¦P¦ rays, chosen once, depending only on (B,s_0,r_0,h,B',eta)
CONSTANT_SCOPE: omega*_{p,+-}, gamma_{p,+-} depend only on (B,s_0,r_0,h,B',eta)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:cover, bpI:p3:rays, bpI:p3:patch, bpI:p3:coordinates, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:cover | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:patch-rays@L233-L233 | the finite family of patches
EDGE: bpI:p3:rays | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:patch-rays@L233-L233 | Lemma rays with J_+-
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:patch-rays@L233-L233 | delta_m, c of the patch
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:patch-rays@L237-L237 | sigma_c, a_c
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:patch-rays@L235-L235 | m_h
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:patch-rays@L232-L232 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3
REVIEWER: sol-review-I-p3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.IsRay (KAM/Iso/Charts/Defs.lean); KAM.Iso.Charts.patch_rays (KAM/Iso/Charts/Rays.lean)
LEAN_NOTE: exact existence form, both signed rays at same patch; audit I3-3 PASS WITH NOTES
NOTE: -

NODE: bpI:p3:points
KIND: lemma
TITLE: The two points on the energy curve
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:points@L242-L257
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:points@L258-L269
CONTRACT_ID: bpI:p3:points
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting; p a patch; E in R with ¦E-h(c)¦<=delta_E; omega*_+-, m_+- the data of Definition patch-rays
SOURCE_QUANTIFIERS: patch p and E in its energy window fixed; define I_+-(E); for every I_0 with norm(I_0-c) < rho_c, the additional position and ordering conclusions hold
SOURCE_CONCLUSION: (E,m_+-) in Q in V; I_+-(E) := Phi_p^{-1}(E,m_+-) in W real points; (a) h(I_+-)=E, m_c(I_+-)=m_+-, grad h(I_+-) = s_+-^o omega*_+- with s_+-^o = ¦grad h(I_+-)¦/¦omega*_+-¦ in (2, 4M_g/m_h); (b) ¦I_+--c¦<eta_1/4, I_+- in S in B, I_- != I_+, and ¦I_+--I_0¦<eta_1/2 for ¦I_0-c¦<rho_c; (c) m_c(I_-) <= -delta_m/2, m_c(I_+) >= delta_m/2, ¦m_c(I_0)¦<delta_m/4; Phi_p maps {I in W: h(I)=E, ¦m_c(I)¦<=delta_m} homeomorphically onto {E} x [-delta_m,delta_m]; claims involving I_0 in (b),(c) are conditional on norm(I_0-c) < rho_c; I_0 is not asserted to lie on h=E
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:patch, bpI:p3:patch-rays, bpI:p3:constants, bpI:p3:coordinates, stepI:p3:pt-exist, stepI:p3:pt-parallel, stepI:p3:pt-position, stepI:p3:pt-segment
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:points@L243-L243 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:points@L243-L243 | patch, Q, V, (P1)-(P3)
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:points@L243-L243 | omega*_+-, m_+-
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:points@L250-L250 | M_g, m_h, eta_1, S
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:points@L246-L246 | Phi_c, m_c
EDGE: stepI:p3:pt-exist | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:points@L259-L259 | proof step of this result
EDGE: stepI:p3:pt-parallel | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:points@L261-L261 | proof step of this result
EDGE: stepI:p3:pt-position | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:points@L265-L265 | proof step of this result
EDGE: stepI:p3:pt-segment | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:points@L267-L267 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.points, bijOn_energySegment (KAM/Iso/Charts/Points.lean)
LEAN_NOTE: one-ray lemma, both signs are instances; audit I3-3 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:pt-exist
KIND: step
TITLE: Existence
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-exist@L259-L260
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-exist@L259-L260
CONTRACT_ID: stepI:p3:pt-exist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; p a patch with its selected rays; E real with norm(E-h(c)) <= delta_E
SOURCE_QUANTIFIERS: p, E fixed
SOURCE_CONCLUSION: (E,m_+-) in Q in V = Phi_c(W)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:patch, bpI:p3:patch-rays, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-exist@L260-L260 | (P2): Q in V
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-exist@L260-L260 | m_+- in (+-delta_m/2, +-delta_m)
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-exist@L260-L260 | local Part 3 data, including h, B', f or epsilon
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.points, bijOn_energySegment (KAM/Iso/Charts/Points.lean)
LEAN_NOTE: inside KAM.Iso.Charts.points; audit I3-3 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:pt-parallel
KIND: step
TITLE: Parallel gradient
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-parallel@L261-L264
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-parallel@L261-L264
CONTRACT_ID: stepI:p3:pt-parallel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting and constants; p a patch with its selected rays; E real with norm(E-h(c)) <= delta_E
SOURCE_QUANTIFIERS: p, E fixed
SOURCE_CONCLUSION: h(I_+-)=E, m_c(I_+-)=sigma_c(omega*_+-); grad h(I_+-) = s^o omega*_+- with s^o = ¦grad h(I_+-)¦/¦omega*_+-¦; I_+- in S so m_h <= ¦grad h(I_+-)¦ <= M_g; hence 2<s^o<4M_g/m_h
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p3:pt-exist, bpI:p3:slope-ray, bpI:p3:patch, bpI:p3:patch-rays, bpI:p3:constants, bpI:p3:coordinates, bpI:p3:setting, bpI:p3:compact
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p3:pt-exist | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-parallel@L262-L262 | I_+-(E) is defined
EDGE: bpI:p3:slope-ray | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-parallel@L263-L263 | grad h(I_+-) = s omega*_+-
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-parallel@L264-L264 | (P1): I_+- in W in S
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-parallel@L264-L264 | m_h/4<¦omega*_+-¦<m_h/2, a_c(omega*)>0
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-parallel@L264-L264 | m_h, M_g, eta_1, d_B, S
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-parallel@L262-L262 | Phi_c, a_c, U_c
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-parallel@L262-L262 | local Part 3 data, including h, B', f or epsilon
EDGE: bpI:p3:compact | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-parallel@L264-L264 | positive finite m_h, M_g, S_h and attained bounds on S
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.points, bijOn_energySegment (KAM/Iso/Charts/Points.lean)
LEAN_NOTE: inside KAM.Iso.Charts.points; audit I3-3 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:pt-position
KIND: step
TITLE: Position
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-position@L265-L266
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-position@L265-L266
CONTRACT_ID: stepI:p3:pt-position
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting and constants; p a patch with its selected rays; E real with norm(E-h(c)) <= delta_E; for claims about I_0, norm(I_0-c) < rho_c
SOURCE_QUANTIFIERS: p, E fixed; every I_0 in R^2 with norm(I_0-c) < rho_c
SOURCE_CONCLUSION: ¦I_+--c¦<eta_1/4; ¦I_+--I_0¦<eta_1/2; I_- != I_+ since m_c(I_-)<0<m_c(I_+); ordering (c)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:patch, stepI:p3:pt-exist, bpI:p3:patch-rays, bpI:p3:setting, bpI:p3:constants, bpI:p3:coordinates
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-position@L266-L266 | (P1), (P3)
EDGE: stepI:p3:pt-exist | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-position@L266-L266 | I_+-(E) in W
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-position@L266-L266 | signs and ranges of m_+-
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-position@L266-L266 | local Part 3 data, including h, B', f or epsilon
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-position@L266-L266 | standing constants in this step and its local conclusion
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-position@L266-L266 | q_c, gradient or slope/chart coordinates
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.points, bijOn_energySegment (KAM/Iso/Charts/Points.lean)
LEAN_NOTE: inside KAM.Iso.Charts.points; audit I3-3 PASS WITH NOTES
NOTE: -

NODE: stepI:p3:pt-segment
KIND: step
TITLE: Energy segment
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-segment@L267-L268
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-segment@L267-L268
CONTRACT_ID: stepI:p3:pt-segment
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; p a patch; E real with norm(E-h(c)) <= delta_E
SOURCE_QUANTIFIERS: p, E fixed
SOURCE_CONCLUSION: Phi_p restricts to a homeomorphism from {I in W: h(I)=E, norm(m_c(I))<=delta_m} onto {E} x [-delta_m,delta_m], with preimage exactly that set
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:patch, bpI:p3:coordinates, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-segment@L268-L268 | Phi_p homeomorphism W to V and Q in V
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-segment@L268-L268 | Phi_c = (h, m_c)
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:pt-segment@L268-L268 | local Part 3 data, including h, B', f or epsilon
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.points, bijOn_energySegment (KAM/Iso/Charts/Points.lean)
LEAN_NOTE: bijOn_energySegment named in audit I3-3 PASS WITH NOTES
NOTE: -

NODE: bpI:p3:hypothesis-d
KIND: lemma
TITLE: The hypotheses (I1)--(I4) for $H=h+f$
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:hypothesis-d@L274-L279
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:hypothesis-d@L280-L287
CONTRACT_ID: bpI:p3:hypothesis-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting with epsilon <= 1; D := D-frak = T_{s/2} x B_{r_0/2}
SOURCE_QUANTIFIERS: as in the data; D, H
SOURCE_CONCLUSION: (I1)-(I4) of I-G1 hold for (D,H) with the constant M of Definition bpI:p3:constants; for z in D and j=1,2,3: ¦D^j f(z)¦ <= F_j epsilon, in particular ¦X_f(z)¦ <= F_1 epsilon and ¦D^2 f(z)¦ <= F_2 epsilon
CONSTANT_SCOPE: M, F_j depend only on (B,s_0,r_0,h,B',eta)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:constants, K:bp:p4:h1, K:bp:p4:derivative-bounds, bpI:p3:setting#k-bridge, stepI:p3:hd-open, stepI:p3:hd-bounds
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:hypothesis-d@L275-L275 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:hypothesis-d@L276-L276 | M, F_j, D-frak
EDGE: K:bp:p4:h1 | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:hypothesis-d@L282-L282 | (I1)-(I3) via K Part 4's H1
EDGE: K:bp:p4:derivative-bounds | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:hypothesis-d@L285-L285 | Cauchy bounds on derivatives
EDGE: bpI:p3:setting#k-bridge | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:hypothesis-d@L282-L282 | supplies the premises of the applied K Part 4 result under the Part 3 data
EDGE: stepI:p3:hd-open | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:hypothesis-d@L281-L281 | proof step of this result
EDGE: stepI:p3:hd-bounds | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:hypothesis-d@L284-L284 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: hypothesis_d (KAM/Iso/Charts/Torus.lean)
LEAN_NOTE: audit I3-4 PASS WITH NOTES + I3-5 PASS WITH NOTES
NOTE: Preextract candidate edge to bpI:p0:g1 dropped: the statement only names hypotheses (I1)-(I4) of I-G1 (a check that they hold), it does not consume the conclusion.

NODE: stepI:p3:hd-open
KIND: step
TITLE: (I1)--(I3)
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-open@L281-L283
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-open@L281-L283
CONTRACT_ID: stepI:p3:hd-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; epsilon <= 1; D := D-frak
SOURCE_QUANTIFIERS: D := D-frak
SOURCE_CONCLUSION: D open and invariant under theta -> theta+k; H holomorphic on D in T_{s_0} x B_{r_0}, 1-periodic in theta, real at real phase points of D
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:step:p4:h1-open, K:step:p4:h1-holo, K:bp:p4:h1, bpI:p3:setting#k-bridge, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: K:step:p4:h1-open | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-open@L282-L282 | D open and translation invariant
EDGE: K:step:p4:h1-holo | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-open@L282-L282 | H holomorphic, periodic
EDGE: K:bp:p4:h1 | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-open@L282-L282 | H1 of K Part 4
EDGE: bpI:p3:setting#k-bridge | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-open@L282-L282 | supplies the premises of the applied K Part 4 result under the Part 3 data
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-open@L282-L282 | D-frak
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-open@L283-L283 | f real at real points; h real
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: TorusAux.differentiableOn_totalH (KAM/Iso/Charts/Torus.lean)
LEAN_NOTE: audit I3-4 PASS WITH NOTES; row hd-open
NOTE: -

NODE: stepI:p3:hd-bounds
KIND: step
TITLE: (I4)
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-bounds@L284-L286
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-bounds@L284-L286
CONTRACT_ID: stepI:p3:hd-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; epsilon <= 1; D := D-frak
SOURCE_QUANTIFIERS: D := D-frak
SOURCE_CONCLUSION: ¦DH¦,¦X_H¦,¦DX_H¦,¦D^2 X_H¦ <= M on D; ¦D^j H¦ <= c-bar(M_h+epsilon) delta_*^{-j} <= M for j=2; ¦D^j f¦ <= F_j epsilon
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p4:derivative-bounds, K:step:p4:db-cauchy, bpI:p3:setting#k-bridge, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p4:derivative-bounds | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-bounds@L285-L285 | (a),(c),(d)
EDGE: K:step:p4:db-cauchy | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-bounds@L285-L285 | Cauchy estimates step
EDGE: bpI:p3:setting#k-bridge | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-bounds@L285-L285 | supplies the premises of the applied K Part 4 result under the Part 3 data
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-bounds@L286-L286 | M, F_j, c-bar, M_h, delta_*
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:hd-bounds@L285-L285 | epsilon<=1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: hypothesis_d (KAM/Iso/Charts/Torus.lean)
LEAN_NOTE: audit I3-4 PASS WITH NOTES; hypothesis_d is stated to give all five Hamiltonian bounds and the j=1,2,3 estimates
NOTE: -

NODE: bpI:p3:torus
KIND: lemma
TITLE: The flat torus of $H=h+f$
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L289-L302
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L303-L318
CONTRACT_ID: bpI:p3:torus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting with epsilon <= 1; D = D-frak; I in B real; omega* in R^2, s' in R with grad h(I) = s' omega*; omega := s' omega*; K(theta) := (theta,I)
SOURCE_QUANTIFIERS: I, omega*, s' fixed; then for theta in T_{s/2}
SOURCE_CONCLUSION: for theta in T_{s/2}: (a) K holomorphic, primary, real on reals, K(T_{s/2}) in D, DK(theta)v = (v,0), ¦DK¦=1, G_K = I_2, ¦G_K^{-1}¦=1, N_{.j} = (0,e_j); for theta in T_rho: B_mu(K(theta)) in D; (b) E_{H,K,omega} = X_f(K(theta)), ¦E¦ <= F_1 epsilon; (c) T_H(theta) = B_h(I)+R(theta), ¦R¦ <= 2 F_2 epsilon, ¦avg T_H - B_h(I)¦ <= 2F_2 epsilon; (d) if I in S and epsilon <= eps_T then det avg T_H != 0, ¦avg T_H^{-1}¦ <= 2S_h = sigma_T - mu; (e) ¦Ebar_H(K)-h(I)¦ <= epsilon, hence ¦Ebar_H(K)-E_0¦ <= epsilon whenever h(I)=E_0; explicitly R(theta) has upper-left block (partial_{I_i} partial_{I_j} f), last row (partial_{I_b} f)^T, and last column zero, all evaluated at (theta,I)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:constants, bpI:p0:stripdata#IsPrimaryOnStrip, bpI:p0:stripdata#IsRealOnReals, bpI:p0:stripdata#gramMatrix, bpI:p0:stripdata#normalFrame, bpI:p0:stripdata#invarianceError, bpI:p0:extended#extendedTorsionAverage, bpI:p0:extended#energyAverage, stepI:p3:to-torus, stepI:p3:to-error, stepI:p3:to-torsion, stepI:p3:to-neumann, stepI:p3:to-energy, bpI:p0:extended#extendedTorsion
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L290-L290 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L298-L298 | mu, rho, F_1, F_2, S_h, eps_T, sigma_T
EDGE: bpI:p0:stripdata#IsPrimaryOnStrip | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L293-L293 | K primary
EDGE: bpI:p0:stripdata#IsRealOnReals | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L293-L293 | K real on reals
EDGE: bpI:p0:stripdata#gramMatrix | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L293-L293 | G_K
EDGE: bpI:p0:stripdata#normalFrame | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L293-L293 | N_{.j}
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L295-L295 | E_{H,K,omega}
EDGE: bpI:p0:extended#extendedTorsionAverage | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L297-L297 | avg T_H
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L299-L299 | Ebar_H(K)
EDGE: stepI:p3:to-torus | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L304-L304 | proof step of this result
EDGE: stepI:p3:to-error | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L308-L308 | proof step of this result
EDGE: stepI:p3:to-torsion | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L310-L310 | proof step of this result
EDGE: stepI:p3:to-neumann | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L314-L314 | proof step of this result
EDGE: stepI:p3:to-energy | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L316-L316 | proof step of this result
EDGE: bpI:p0:extended#extendedTorsion | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:torus@L296-L296 | the unaveraged extended-torsion matrix in the block identity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: torus (KAM/Iso/Charts/Torus.lean)
LEAN_NOTE: audit I3-4 PASS WITH NOTES (interface note)
NOTE: -

NODE: stepI:p3:to-torus
KIND: step
TITLE: The torus and its frame
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torus@L304-L307
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torus@L304-L307
CONTRACT_ID: stepI:p3:to-torus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; epsilon <= 1; D := D-frak; I in B real; grad h(I) = s' omega*, omega := s' omega*; K(theta) := (theta,I)
SOURCE_QUANTIFIERS: I in B real
SOURCE_CONCLUSION: K affine, primary, real on reals, DK=(id,0), G_K=I_2, N_{.j}=(0,e_j) constant; ¦DK v¦=¦v¦; K(T_{s/2}) in T_{s/2} x B in D; for theta in T_rho, B_mu(K(theta)) in D
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:tr-torus, stepI:p1:tr-frame, bpI:p1:trivial, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p1:tr-torus | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torus@L305-L305 | K affine, primary, DK, G_K = I
EDGE: stepI:p1:tr-frame | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torus@L305-L305 | N_{.j} = (0,e_j)
EDGE: bpI:p1:trivial | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torus@L305-L305 | trivial-torus lemma (K and the frame do not involve the Hamiltonian)
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torus@L306-L306 | mu, rho, D-frak, s, r_0
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torus@L306-L306 | B in B_{r_0}, I real in B
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: TorusAux.toC_mem_half, TorusAux.unperturbed_mem, TorusAux.real_mem (KAM/Iso/Charts/Torus.lean)
LEAN_NOTE: audit I3-4 PASS WITH NOTES; row to-torus
NOTE: -

NODE: stepI:p3:to-error
KIND: step
TITLE: The error
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-error@L308-L309
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-error@L308-L309
CONTRACT_ID: stepI:p3:to-error
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; epsilon <= 1; D := D-frak; I in B real; omega := grad h(I); K(theta) := (theta,I)
SOURCE_QUANTIFIERS: I in B real, omega = grad h(I)
SOURCE_CONCLUSION: E_{H,K,omega} = X_f(K(theta)) and ¦X_f¦ <= F_1 epsilon on D
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:trivial, stepI:p1:tr-field, stepI:p3:to-torus, bpI:p3:hypothesis-d, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:trivial | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-error@L309-L309 | grad h(I) = omega as the frequency of the trivial torus
EDGE: stepI:p1:tr-field | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-error@L309-L309 | (d_a h(I))_a = grad h(I) = omega
EDGE: stepI:p3:to-torus | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-error@L309-L309 | DK omega = (omega,0)
EDGE: bpI:p3:hypothesis-d | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-error@L309-L309 | ¦X_f¦ <= F_1 epsilon
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-error@L309-L309 | F_1
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-error@L309-L309 | H = h+f
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: TorusAux.invarianceError_flat (KAM/Iso/Charts/Torus.lean)
LEAN_NOTE: audit I3-4 PASS WITH NOTES; row to-error
NOTE: -

NODE: stepI:p3:to-torsion
KIND: step
TITLE: Torsion and border
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion@L310-L313
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion@L310-L313
CONTRACT_ID: stepI:p3:to-torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; epsilon <= 1; D := D-frak; I in B real; omega := grad h(I); K(theta) := (theta,I)
SOURCE_QUANTIFIERS: I in B real
SOURCE_CONCLUSION: T_ij = d_i d_j h(I) + d_{I_i}d_{I_j} f(theta,I); last column omega = grad h(I); last row Y_b = d_b h(I) + d_{I_b} f(theta,I); T_H = B_h(I) + R with R the f-part, ¦R¦ <= 2F_2 epsilon (row-sums), avg T_H defined (integrable) and ¦avg T_H - B_h(I)¦ <= 2F_2 epsilon, avg B_h = B_h
CONSTANT_SCOPE: F_2 from the constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:tr-compare, bpI:p3:hypothesis-d, K:bp:p1:ext-integral, stepI:p3:to-torus, bpI:p3:constants, bpI:p3:setting
ROUTES: stepI:p3:to-torsion#flat-route, stepI:p3:to-torsion#citation-route
ROUTE_FOR: -
EDGE: stepI:p1:tr-compare | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion@L313-L313 | upper-left block and border of B_h(I)
EDGE: bpI:p3:hypothesis-d | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion@L313-L313 | ¦D^2 f¦ <= F_2 epsilon, ¦X_f¦ <= F_1 epsilon
EDGE: K:bp:p1:ext-integral | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion@L313-L313 | ¦avg¦ <= sup
EDGE: stepI:p3:to-torus | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion@L311-L311 | frame N_{.j} = (0,e_j), D_theta N = 0
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion@L313-L313 | F_1, F_2
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion@L313-L313 | H = h+f; B_h from h
EDGE: stepI:p3:to-torsion#flat-route | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion@L310-L313 | alternative derivation offered by the proof (route)
EDGE: stepI:p3:to-torsion#citation-route | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion@L310-L313 | alternative derivation offered by the proof (route)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-delta-I-b
REVIEWER: sol-delta-I-c
LEAN_STATUS: PROVED
LEAN_REF: TorusAux.torsion_flat, TorusAux.energyRow_flat, TorusAux.extendedTorsion_flat, TorusAux.norm_flatRemainder_le, TorusAux.norm_extendedAverage_sub_le (KAM/Iso/Charts/Torus.lean)
LEAN_NOTE: audit I3-4 PASS WITH NOTES; rows to-torsion (documented flat route)
NOTE: The direct DH(K)N calculation uses no invariance-error identity. The to-error dependency belongs only to the citation route, where E = X_f is substituted in eta^L. Both alternatives retain their own actual torsion-formula and frame prerequisites.

NODE: stepI:p3:to-torsion#p1-setting
KIND: step
TITLE: Unproved full Part 1 setting required by the cited shortcut
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#p1-setting@L310-L313
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#p1-setting@L310-L313
CONTRACT_ID: stepI:p3:to-torsion#p1-setting
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; epsilon <= 1; D := D-frak; I in B real; omega := grad h(I); K(theta) := (theta,I)
SOURCE_QUANTIFIERS: as in the torus lemma
SOURCE_CONCLUSION: the shortcut invoking Part 1 last-row and extended-basic requires its full standing setting for H, D-frak, K and this same omega; (I1)-(I4), K(T_{s/2}) subset D and det G_K = 1 are supplied locally, but gamma>0 and omega in Dio_{gamma,2} are not established in the generic torus statement
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p1:setting, bpI:p3:hypothesis-d, stepI:p3:to-torus, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p1:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#p1-setting@L312-L312 | Assumption bpI:p1:setting, needed by last-row and extended-basic
EDGE: bpI:p3:hypothesis-d | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#p1-setting@L312-L312 | (I1)-(I4) for (D,H)
EDGE: stepI:p3:to-torus | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#p1-setting@L312-L312 | K holomorphic, primary, real on reals; K(T_{s/2}) in D; det G_K = 1
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#p1-setting@L312-L312 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27, track-I gap survey GAP-PLAN-I item 3): the flat route is the one implemented
NOTE: SOURCE_GAP: literal use of the full statements bpI:p1:last-row and extended-basic at L312-L313 lacks a Diophantine premise in the generic torus lemma. This is an attempted premise-discharge obligation, not an assumption that the entire Part 1 setting already holds, and not a gap in the separate direct flat-formula route. The actual ray application later supplies Diophantinity; that does not prove this generic premise.

NODE: stepI:p3:to-neumann
KIND: step
TITLE: Invertibility
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-neumann@L314-L315
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-neumann@L314-L315
CONTRACT_ID: stepI:p3:to-neumann
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; epsilon <= 1; D := D-frak; I in B real; omega := grad h(I); K(theta) := (theta,I); I in S; epsilon <= eps_T
SOURCE_QUANTIFIERS: I in S
SOURCE_CONCLUSION: ¦B_h^{-1}¦¦avg R¦ <= 1/2 so avg T_H = B_h + avg R is invertible with ¦avg T_H^{-1}¦ <= 2 S_h = sigma_T - mu (real matrix)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:bp:p1:neumann, K:bp:p1:real-inverse, stepI:p3:to-torsion, bpI:p3:constants, bpI:p3:setting, bpI:p3:compact
ROUTES: -
ROUTE_FOR: -
EDGE: K:bp:p1:neumann | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-neumann@L315-L315 | Neumann series
EDGE: K:bp:p1:real-inverse | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-neumann@L315-L315 | real inverse
EDGE: stepI:p3:to-torsion | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-neumann@L315-L315 | ¦avg R¦ <= 2F_2 epsilon, avg T_H = B_h + avg R
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-neumann@L315-L315 | S_h, F_2, eps_T, sigma_T, mu
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-neumann@L315-L315 | local Part 3 data, including h, B', f or epsilon
EDGE: bpI:p3:compact | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-neumann@L315-L315 | positive finite m_h, M_g, S_h and attained bounds on S
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: TorusAux.extendedAverage_inv (KAM/Iso/Charts/Torus.lean)
LEAN_NOTE: audit I3-4 PASS WITH NOTES; row to-neumann
NOTE: -

NODE: stepI:p3:to-energy
KIND: step
TITLE: Energy average
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-energy@L316-L317
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-energy@L316-L317
CONTRACT_ID: stepI:p3:to-energy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H(K(theta)) = h(I)+f(theta,I); ¦f¦<=epsilon on T_{s_0} x B_{r_0}
SOURCE_QUANTIFIERS: I in B real
SOURCE_CONCLUSION: ¦Ebar_H(K) - h(I)¦ = ¦int f(theta,I) dtheta¦ <= epsilon
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p0:extended#energyAverage, K:bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-energy@L317-L317 | ¦f¦ <= epsilon on T_{s_0} x B_{r_0}, H = h+f
EDGE: bpI:p0:extended#energyAverage | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-energy@L317-L317 | Ebar_H(K)
EDGE: K:bp:p1:ext-integral | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-energy@L317-L317 | integral of continuous f on the unit cube; linearity and norm bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: TorusAux.norm_energyAverage_sub_le (KAM/Iso/Charts/Torus.lean)
LEAN_NOTE: audit I3-4 PASS WITH NOTES; row to-energy
NOTE: -

NODE: bpI:p3:apply
KIND: lemma
TITLE: One application of I-G1
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L320-L333
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L334-L349
CONTRACT_ID: bpI:p3:apply
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting; patch p with ray omega* = omega*_{p,+-}, gamma = gamma_{p,+-}; epsilon <= 1, epsilon <= eps_T, epsilon < eps^{p,+-} := gamma^4 rho^8/(C_1^{p,+-} F_1); E in R with ¦E-h(c)¦<=delta_E; I := I_+-(E), s' := s^o_+-
SOURCE_QUANTIFIERS: patch p fixed; I-G1 applied with n=2, tau=2, rho=s/4, rho_infty=s/8, the constants M, sigma_K, sigma_B, sigma_T, mu, sigma_omega, nu, gammabar := gamma, omega*; then C_i^{p,+-}; then for all f, epsilon, E
SOURCE_CONCLUSION: the hypotheses (I1)-(I13) of I-G1 hold for D = D-frak, H = h+f, K(theta) = (theta,I), s = s^o_+-, gamma, e = F_1 epsilon, E_0 = E; consequently there are K_infty and s_infty in (1,sigma_omega) with (O1)-(O6), in particular ¦K_infty-K¦ <= C_2 F_1 epsilon/(gamma^2 rho^4) on T_{rho_infty}, ¦(s_infty - s^o_+-) omega*¦ <= C_3 F_1 epsilon/(gamma^2 rho^4)
CONSTANT_SCOPE: C_i^{p,+-} (the I-G1 constants) depend only on (B,s_0,r_0,h,B',eta) and the ray
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:constants, bpI:p0:g1, bpI:p3:patch, bpI:p3:patch-rays, bpI:p3:points, stepI:p3:ap-d, stepI:p3:ap-k, stepI:p3:ap-t, stepI:p3:ap-ray, stepI:p3:ap-error, stepI:p3:ap-small, stepI:p3:ap-conclusion, bpI:p3:compact, bpI:p3:apply#constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L321-L321 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L322-L322 | M, sigma's, mu, sigma_omega, nu, rho, rho_infty, F_1, eps_T
EDGE: bpI:p0:g1 | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L321-L321 | I-G1 applied
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L327-L327 | delta_E, c, (E,m_+-)
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L321-L321 | omega*_{p,+-}, gamma_{p,+-}
EDGE: bpI:p3:points | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L327-L327 | I_+-(E), s^o_+-
EDGE: stepI:p3:ap-d | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L335-L335 | proof step of this result
EDGE: stepI:p3:ap-k | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L337-L337 | proof step of this result
EDGE: stepI:p3:ap-t | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L339-L339 | proof step of this result
EDGE: stepI:p3:ap-ray | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L341-L341 | proof step of this result
EDGE: stepI:p3:ap-error | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L343-L343 | proof step of this result
EDGE: stepI:p3:ap-small | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L345-L345 | proof step of this result
EDGE: stepI:p3:ap-conclusion | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L347-L347 | proof step of this result
EDGE: bpI:p3:compact | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L322-L322 | positive finite m_h, M_g, S_h and attained bounds on S
EDGE: bpI:p3:apply#constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply@L322-L322 | the same per-ray C_i chosen at L321-L322
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: apply, apply_local (KAM/Iso/Charts/Apply.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; conditional on the I-G1 statement as in the design (IG1Statement premise)
NOTE: -

NODE: stepI:p3:ap-d
KIND: step
TITLE: (I1)--(I4)
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-d@L335-L336
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-d@L335-L336
CONTRACT_ID: stepI:p3:ap-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: local data of apply: fixed patch and selected ray; epsilon <= 1, epsilon <= eps_T, epsilon < eps^{p,+-}; E in the patch energy window
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: (I1)-(I4) of I-G1 hold for D-frak, H = h+f with the constant M
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:hypothesis-d, bpI:p3:setting, bpI:p3:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:hypothesis-d | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-d@L336-L336 | (I1)-(I4)
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-d@L336-L336 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-d@L336-L336 | standing constants in this step and its local conclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: apply_local (KAM/Iso/Charts/Apply.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; rows ap-d through ap-conclusion
NOTE: -

NODE: stepI:p3:ap-k
KIND: step
TITLE: (I5)--(I7)
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-k@L337-L338
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-k@L337-L338
CONTRACT_ID: stepI:p3:ap-k
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: local data of apply: fixed patch and selected ray; epsilon <= 1, epsilon <= eps_T, epsilon < eps^{p,+-}; E in the patch energy window; I := I_+-(E)
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: (I5)-(I7): K holomorphic, primary, real on reals on T_rho; B_mu(K) in D, ¦DK¦ = 1 = sigma_K - mu; det G_K = 1, ¦G_K^{-1}¦ = 1 = sigma_B - mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:torus, bpI:p3:points, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:torus | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-k@L338-L338 | (a)
EDGE: bpI:p3:points | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-k@L338-L338 | (b): I_+- in B
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-k@L338-L338 | sigma_K, sigma_B, mu, rho
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-k@L338-L338 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: apply_local (KAM/Iso/Charts/Apply.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; rows ap-d through ap-conclusion
NOTE: -

NODE: stepI:p3:ap-t
KIND: step
TITLE: (I8)
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-t@L339-L340
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-t@L339-L340
CONTRACT_ID: stepI:p3:ap-t
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: local data of apply: fixed patch and selected ray; epsilon <= 1, epsilon <= eps_T, epsilon < eps^{p,+-}; E in the patch energy window; I := I_+-(E)
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: (I8): det avg T_H != 0 and ¦avg T_H^{-1}¦ <= sigma_T - mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:points, bpI:p3:torus, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:points | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-t@L340-L340 | (a): grad h(I_+-) = s^o omega*; (b): I_+- in S
EDGE: bpI:p3:torus | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-t@L340-L340 | (d)
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-t@L340-L340 | sigma_T, mu, eps_T
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-t@L340-L340 | local Part 3 data, including h, B', f or epsilon
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: apply_local (KAM/Iso/Charts/Apply.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; rows ap-d through ap-conclusion
NOTE: -

NODE: stepI:p3:ap-ray
KIND: step
TITLE: (I9)
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-ray@L341-L342
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-ray@L341-L342
CONTRACT_ID: stepI:p3:ap-ray
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: local data of apply: fixed patch and selected ray; E in the patch energy window; s := s^o_+-
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: (I9): 1<s<sigma_omega, (s-1)¦omega*¦ > nu and (sigma_omega-s)¦omega*¦ > nu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:points, bpI:p3:patch-rays, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:points | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-ray@L342-L342 | (a): s^o in (2, 4M_g/m_h)
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-ray@L342-L342 | m_h/4 < ¦omega*¦ < m_h/2
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-ray@L342-L342 | nu, sigma_omega
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-ray@L342-L342 | local Part 3 data, including h, B', f or epsilon
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: apply_local (KAM/Iso/Charts/Apply.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; rows ap-d through ap-conclusion
NOTE: -

NODE: stepI:p3:ap-error
KIND: step
TITLE: (I10)--(I12)
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-error@L343-L344
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-error@L343-L344
CONTRACT_ID: stepI:p3:ap-error
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: local data of apply: fixed patch and selected ray; epsilon <= 1, epsilon <= eps_T, epsilon < eps^{p,+-}; E in the patch energy window; E_0 := E; e := F_1 epsilon
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: (I10)-(I12): 0<gamma<=gammabar = gamma, omega* in Dio_{gamma,2}, e = F_1 epsilon >= 0; (I11) E bound from torus (b); (I12) ¦Ebar_H(K)-E_0¦ <= epsilon <= F_1 epsilon = e
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:patch-rays, bpI:p3:torus, bpI:p3:points, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-error@L344-L344 | gamma>0, omega* in Dio_{gamma,2}
EDGE: bpI:p3:torus | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-error@L344-L344 | (b), (e)
EDGE: bpI:p3:points | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-error@L344-L344 | (a): h(I) = E = E_0
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-error@L344-L344 | F_1 >= 1, e = F_1 epsilon
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-error@L344-L344 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: apply_local (KAM/Iso/Charts/Apply.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; rows ap-d through ap-conclusion
NOTE: -

NODE: stepI:p3:ap-small
KIND: step
TITLE: (I13)
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-small@L345-L346
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-small@L345-L346
CONTRACT_ID: stepI:p3:ap-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: epsilon < eps^{p,+-} = gamma^4 rho^8/(C_1 F_1)
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: (I13): C_1 e/(gamma^4 rho^{4 tau}) = C_1 F_1 epsilon/(gamma^4 rho^8) < 1 (trivially if epsilon = 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:constants, bpI:p3:patch-rays, bpI:p3:setting, bpI:p3:apply#constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-small@L346-L346 | e = F_1 epsilon, rho = s/4, tau = 2
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-small@L346-L346 | gamma = gamma_{p,+-}
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-small@L346-L346 | local Part 3 data, including h, B', f or epsilon
EDGE: bpI:p3:apply#constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-small@L346-L346 | the same per-ray C_i chosen at L321-L322
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: apply_local (KAM/Iso/Charts/Apply.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; rows ap-d through ap-conclusion
NOTE: -

NODE: stepI:p3:ap-conclusion
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-conclusion@L347-L348
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-conclusion@L347-L348
CONTRACT_ID: stepI:p3:ap-conclusion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: local data and smallness assumptions of apply; I := I_+-(E), s := s^o_+-, E_0 := E, e := F_1 epsilon; use the constants selected before f, epsilon and E
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: Theorem I-G1 gives K_infty, s_infty in (1,sigma_omega) with (O1)-(O6); C_2 e/(gamma^2 rho^{2 tau}) = C_2 F_1 epsilon/(gamma^2 rho^4)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:g1, stepI:p3:ap-d, stepI:p3:ap-k, stepI:p3:ap-t, stepI:p3:ap-ray, stepI:p3:ap-error, stepI:p3:ap-small, bpI:p3:constants, bpI:p3:setting, bpI:p3:apply#constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:g1 | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-conclusion@L348-L348 | I-G1 applied
EDGE: stepI:p3:ap-d | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-conclusion@L348-L348 | (I1)-(I4)
EDGE: stepI:p3:ap-k | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-conclusion@L348-L348 | (I5)-(I7)
EDGE: stepI:p3:ap-t | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-conclusion@L348-L348 | (I8)
EDGE: stepI:p3:ap-ray | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-conclusion@L348-L348 | (I9)
EDGE: stepI:p3:ap-error | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-conclusion@L348-L348 | (I10)-(I12)
EDGE: stepI:p3:ap-small | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-conclusion@L348-L348 | (I13)
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-conclusion@L348-L348 | F_1, rho
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-conclusion@L348-L348 | local Part 3 data, including h, B', f or epsilon
EDGE: bpI:p3:apply#constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:ap-conclusion@L348-L348 | the same per-ray C_i chosen at L321-L322
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: apply_local (KAM/Iso/Charts/Apply.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; rows ap-d through ap-conclusion
NOTE: -

NODE: bpI:p3:uniform
KIND: definition
TITLE: Uniform constants
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:uniform@L359-L369
PROOF_SOURCE: -
CONTRACT_ID: bpI:p3:uniform
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the patches p_j (j in P) of the cover, their rays, and the constants C_i^{j,+-} of Lemma apply
SOURCE_QUANTIFIERS: the data, then patches, rays, gamma_{j,+-}, C_i^{j,+-}
SOURCE_CONCLUSION: defines C_K := max_{j,+-} F_1 max{C_2^{j,+-},C_3^{j,+-}}/(gamma_{j,+-}^2 rho^4) and eps_1 := min{1, eps_T, min_j delta_{E,j}/2, min_{j,+-} eps^{j,+-}, eta_1/(2C_K)} in (0,1]; neither depends on f, epsilon, E, I_0
CONSTANT_SCOPE: C_K, eps_1 depend only on (B,s_0,r_0,h,B',eta); order of choice (B,s_0,r_0,h,B',eta) -> D-frak, mu, delta_*, M, F_j, S, m_h, M_g, S_h, nu, sigma's -> patches -> rays, gamma_{j,+-} -> C_i^{j,+-} -> C_K, eps_1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:cover, bpI:p3:patch-rays, bpI:p3:apply, bpI:p3:patch, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:cover | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:uniform@L360-L360 | patches p_j
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:uniform@L360-L360 | rays and gamma_{j,+-}
EDGE: bpI:p3:apply | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:uniform@L360-L360 | constants C_i^{j,+-}, eps^{j,+-}
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:uniform@L365-L365 | delta_{E,j}
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:uniform@L362-L362 | F_1, eps_T, eta_1, rho
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:uniform@L360-L360 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3
REVIEWER: sol-review-I-p3
LEAN_STATUS: PROVED
LEAN_REF: uniform (KAM/Iso/Charts/Tori.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; existence form approved by the design (D16)
NOTE: -

NODE: bpI:p3:tori
KIND: proposition
TITLE: Invariant tori on both sides: output of Part~\ref{bpI:p3}
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L371-L387
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L388-L405
CONTRACT_ID: bpI:p3:tori
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Assumption bpI:p3:setting (the data of I-HEAD with n=2, B' nonempty, eta>0, tau=2); eps_1, C_K as in Definition uniform; rho_infty = s/8; f, epsilon with the hypotheses of I-HEAD and epsilon<eps_1; I_0 in closure B'; E in R with ¦E-h(I_0)¦<=epsilon
SOURCE_QUANTIFIERS: geometric data (B,s_0,r_0,h,B',eta) fixed; patches, rays, their gamma and C_i fixed in the order of uniform; then eps_1 and C_K; then for every f, 0 <= epsilon < eps_1, I_0 in closure B' and E with norm(E-h(I_0)) <= epsilon, there exist j and for each sign K_+-, s_+-, I_+-
SOURCE_CONCLUSION: there are j in P with ¦I_0-c_j¦<rho_j and for each sign a map K_+-, s_+- in (1,sigma_omega) and a real point I_+- in R^2 with, for H = h+f, omega*_+- = omega*_{j,+-}, omega_+- = s_+- omega*_+-: (T1) K_+- holomorphic on T_{rho_infty}, primary, real on reals, real-analytic on R^2; (T2) E_{H,K_+-,omega_+-} = 0 on T_{rho_infty}, omega*_+- in Dio_{gamma_{j,+-},2}, omega_+- in R^2 minus {0}; (T3) H(K_+-(theta)) = E on T_{rho_infty} (pointwise), Ham_{h,f}(K_+-(theta)) = E for real theta; (T4) ¦K_+-(theta) - (theta,I_+-)¦ <= C_K epsilon on T_{rho_infty}, u_+-, v_+- holomorphic 1-periodic with ¦u¦,¦v¦ <= C_K epsilon, ¦Du¦,¦Dv¦ <= 4C_K epsilon/rho_infty on T_{rho_infty/2}; (T5) h(I_+-) = E, grad h(I_+-) = s^o_+- omega*_+- with s^o in (2,4M_g/m_h), ¦omega_+- - grad h(I_+-)¦ <= C_K epsilon, positive multiples of omega*_+-; (T6) I_+- in B, ¦I_+--I_0¦<eta_1/2<=eta/2, ¦K_+-(theta)_2 - I_0¦<eta and K_+-(theta)_2 in S in B for real theta, B_{mu/2}(K_+-(theta)) in D-frak and ¦DK_+-¦ <= sigma_K - mu/2 on T_{rho_infty}; (T7) ordering of slopes: I_+- = Phi_j^{-1}(E,m_{j,+-}), m_{c_j}(I_-) <= -delta_{m,j}/2, m_{c_j}(I_+) >= delta_{m,j}/2, ¦m_{c_j}(I_0)¦<delta_{m,j}/4; in T2 omega_+- is nonresonant; in T5 norm(omega_+- - grad h(I_+-)) = abs(s_+- - s^o_+-) norm(omega*_+-); I_0 in T7 need not lie on the energy arc
CONSTANT_SCOPE: eps_1, C_K, rho_infty, P, sigma_omega, M_g depend only on (B,s_0,r_0,h,B',eta); K_+-, s_+-, I_+-, j depend on f, epsilon, E, I_0
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:uniform, bpI:p3:constants, bpI:p0:domains#complexStrip, bpI:p0:stripdata#IsPrimaryOnStrip, bpI:p0:stripdata#IsRealOnReals, bpI:p0:stripdata#invarianceError, bpI:p0:realham#realHamiltonian, stepI:p3:tori-patch, stepI:p3:tori-base, stepI:p3:tori-ig1, stepI:p3:tori-close, stepI:p3:tori-position, bpI:p3:patch, bpI:p3:patch-rays, bpI:p3:coordinates
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L372-L372 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
EDGE: bpI:p3:uniform | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L372-L372 | eps_1, C_K
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L385-L385 | sigma_omega, M_g, rho_infty
EDGE: bpI:p0:domains#complexStrip | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L376-L376 | strip T_{rho_infty}
EDGE: bpI:p0:stripdata#IsPrimaryOnStrip | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L376-L376 | K_+- primary
EDGE: bpI:p0:stripdata#IsRealOnReals | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L376-L376 | K_+- real on reals
EDGE: bpI:p0:stripdata#invarianceError | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L377-L377 | E_{H,K,omega}
EDGE: bpI:p0:realham#realHamiltonian | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L378-L378 | Ham_{h,f}
EDGE: stepI:p3:tori-patch | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L389-L389 | proof step of this result
EDGE: stepI:p3:tori-base | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L392-L392 | proof step of this result
EDGE: stepI:p3:tori-ig1 | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L394-L394 | proof step of this result
EDGE: stepI:p3:tori-close | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L398-L398 | proof step of this result
EDGE: stepI:p3:tori-position | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L401-L401 | proof step of this result
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L374-L374 | patch centres, radii and delta_m
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L374-L374 | omega*_{j,+-}, gamma_{j,+-}, m_{j,+-}
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:tori@L383-L383 | Phi_j and m_{c_j} in T7
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: tori, exists_ray_consts, part3_tori_of (KAM/Iso/Charts/Tori.lean); KAM.Iso.Confinement.TorusOutput.realRestriction_analyticOnNhd, KAM.Iso.Confinement.TorusOutput.realHamiltonian_realRestriction_eq, KAM.Iso.Charts.tori_ig1_full (KAM/Iso/Charts/ToriIG1.lean)
LEAN_NOTE: re-closed after survey 2.5 over-claim revert: T1 real-analyticity and real-theta T3 for the tori witnesses now stated (GAP-I3T-audit-3.md:14-17,55-56,61 PASS as consequences); remaining clauses as previously audited
NOTE: Preextract candidate edge to bpI:p0:g1 at the statement dropped: I-G1 is consumed in stepI:p3:tori-ig1 and tori-position (the statement quotes it as provenance).

NODE: stepI:p3:tori-patch
KIND: step
TITLE: Choice of the patch
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-patch@L389-L391
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-patch@L389-L391
CONTRACT_ID: stepI:p3:tori-patch
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; 0 <= epsilon < eps_1; f as in I-HEAD; I_0 in closure B'; E real with norm(E-h(I_0)) <= epsilon; patches, rays and uniform constants fixed before f, epsilon, E, I_0
SOURCE_QUANTIFIERS: I_0 in closure B', E fixed
SOURCE_CONCLUSION: there is j with ¦I_0-c_j¦<rho_j; ¦h(I_0)-h(c)¦<delta_E/2; hence ¦E-h(c)¦ <= epsilon + delta_E/2 <= delta_E
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:cover, bpI:p3:patch, bpI:p3:uniform, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:cover | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-patch@L390-L390 | balls cover closure B'
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-patch@L390-L390 | (P3): ¦h(I_0)-h(c)¦<delta_E/2
EDGE: bpI:p3:uniform | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-patch@L391-L391 | eps_1 <= delta_{E,j}/2
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-patch@L390-L390 | data of Part 3 (B, s_0, r_0, h, B', eta, tau=2, f, eps, H=h+f)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audited declaration states this step (to-torsion pieces partial, I-G1 assembly open)
NOTE: -

NODE: stepI:p3:tori-base
KIND: step
TITLE: The base points
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-base@L392-L393
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-base@L392-L393
CONTRACT_ID: stepI:p3:tori-base
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; 0 <= epsilon < eps_1; f as in I-HEAD; I_0 in closure B'; E real with norm(E-h(I_0)) <= epsilon; patches, rays and uniform constants fixed before f, epsilon, E, I_0
SOURCE_QUANTIFIERS: as in the proposition
SOURCE_CONCLUSION: I_+-:=I_+-(E), s^o_+- from points: T5 (first part), T7, I_+- in B, ¦I_+--I_0¦<eta_1/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:points, stepI:p3:tori-patch, bpI:p3:setting, bpI:p3:constants, bpI:p3:coordinates
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:points | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-base@L393-L393 | (a),(b),(c)
EDGE: stepI:p3:tori-patch | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-base@L393-L393 | j and ¦E-h(c)¦<=delta_E
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-base@L393-L393 | local Part 3 data, including h, B', f or epsilon
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-base@L393-L393 | standing constants in this step and its local conclusion
EDGE: bpI:p3:coordinates | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-base@L393-L393 | q_c, gradient or slope/chart coordinates
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: toriSide_of_applyOut (KAM/Iso/Charts/Tori.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; row tori-base/close/position
NOTE: -

NODE: stepI:p3:tori-ig1
KIND: step
TITLE: Application of I-G1
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-ig1@L394-L397
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-ig1@L394-L397
CONTRACT_ID: stepI:p3:tori-ig1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; 0 <= epsilon < eps_1; f as in I-HEAD; I_0 in closure B'; E real with norm(E-h(I_0)) <= epsilon; patches, rays and uniform constants fixed before f, epsilon, E, I_0
SOURCE_QUANTIFIERS: as in the proposition
SOURCE_CONCLUSION: K_+- := K_infty, s_+- := s_infty in (1,sigma_omega); T1 from (O1) and real-analyticity on R^n; T2 from (O2), omega*_+- Dio is a property of the ray; T3 from (O3) and Ham_{h,f} = Re H = H at real points; T5: (O6) with C_3 F_1 epsilon/(gamma^2 rho^4) <= C_K epsilon, multiples positive since s_+- > 1, s^o > 2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:apply, bpI:p0:g1, bpI:p3:uniform, stepI:p3:tori-base, bpI:p3:patch-rays, K:bp:p1:real-restriction, bpI:p0:realham#realHamiltonian, bpI:p3:setting, bpI:p3:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:apply | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-ig1@L395-L395 | application of I-G1 for the patch p_j and ray +-
EDGE: bpI:p0:g1 | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-ig1@L395-L395 | (O1)-(O6)
EDGE: bpI:p3:uniform | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-ig1@L395-L395 | eps_1 <= min{1,eps_T,eps^{j,+-}}, C_K
EDGE: stepI:p3:tori-base | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-ig1@L395-L395 | I_+-(E), s^o_+- used in apply
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-ig1@L396-L396 | omega*_+- in Dio_{gamma_{j,+-},2}
EDGE: K:bp:p1:real-restriction | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-ig1@L396-L396 | real-analytic restriction to R^2
EDGE: bpI:p0:realham#realHamiltonian | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-ig1@L396-L396 | Ham_{h,f} = Re H = H at real points where H is real
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-ig1@L396-L396 | local Part 3 data, including h, B', f or epsilon
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-ig1@L395-L395 | standing constants in this step and its local conclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.Charts.tori_ig1_full (KAM/Iso/Charts/ToriIG1.lean)
LEAN_NOTE: GAP-I3T-audit-3.md:60 PASS (round 3, PASS WITH NOTES): both signs, common constants, fixed rays, literal T1/T2/T3/T5; tori constructed from source data
NOTE: -

NODE: stepI:p3:tori-close
KIND: step
TITLE: Closeness and derivatives
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-close@L398-L400
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-close@L398-L400
CONTRACT_ID: stepI:p3:tori-close
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; 0 <= epsilon < eps_1; f as in I-HEAD; I_0 in closure B'; E real with norm(E-h(I_0)) <= epsilon; patches, rays and uniform constants fixed before f, epsilon, E, I_0
SOURCE_QUANTIFIERS: as in the proposition
SOURCE_CONCLUSION: T4: u_+-,v_+- holomorphic 1-periodic on T_{rho_infty}, ¦u¦,¦v¦ <= C_K epsilon, ¦Du¦,¦Dv¦ <= 4C_K epsilon/rho_infty on T_{rho_infty/2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p3:tori-ig1, bpI:p3:uniform, K:bp:p1:cauchy-strip, bpI:p0:stripdata#IsPrimaryOnStrip, bpI:p3:constants, bpI:p3:setting, bpI:p0:g1
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p3:tori-ig1 | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-close@L399-L399 | (O5) with K_+- = K_infty
EDGE: bpI:p3:uniform | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-close@L399-L399 | C_K
EDGE: K:bp:p1:cauchy-strip | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-close@L400-L400 | Cauchy estimate on the strip, n=2, delta = rho_infty/2
EDGE: bpI:p0:stripdata#IsPrimaryOnStrip | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-close@L399-L399 | K_+- and K primary give 1-periodicity of the difference
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-close@L400-L400 | rho_infty = s/8
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-close@L399-L399 | local Part 3 data, including h, B', f or epsilon
EDGE: bpI:p0:g1 | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-close@L399-L399 | the O5 conclusion for the already selected I-G1 output
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: du_dv_bound, toriSide_of_applyOut (KAM/Iso/Charts/Tori.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; rows tori-close
NOTE: -

NODE: stepI:p3:tori-position
KIND: step
TITLE: Position
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-position@L401-L404
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-position@L401-L404
CONTRACT_ID: stepI:p3:tori-position
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; 0 <= epsilon < eps_1; f as in I-HEAD; I_0 in closure B'; E real with norm(E-h(I_0)) <= epsilon; patches, rays and uniform constants fixed before f, epsilon, E, I_0
SOURCE_QUANTIFIERS: as in the proposition
SOURCE_CONCLUSION: T6: ¦K_+-(theta)_2 - I_+-¦ <= C_K epsilon<eta_1/2, so ¦K_+-(theta)_2 - I_0¦ < eta_1 <= eta; dist(K_+-(theta)_2, closure B') < eta_1 <= d_B/2 so K_+-(theta)_2 in S in B; B_{mu/2}(K_+-) in D-frak and ¦DK_+-¦ <= sigma_K - mu/2 are (O4)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:compact, bpI:p0:g1, stepI:p3:tori-ig1, stepI:p3:tori-close, stepI:p3:tori-base, bpI:p3:uniform, bpI:p3:constants, bpI:p3:setting
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:compact | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-position@L403-L403 | S in B
EDGE: bpI:p0:g1 | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-position@L403-L403 | (O4)
EDGE: stepI:p3:tori-ig1 | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-position@L402-L402 | K_+- = K_infty with (O4)
EDGE: stepI:p3:tori-close | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-position@L402-L402 | ¦K_+--K¦ <= C_K epsilon
EDGE: stepI:p3:tori-base | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-position@L402-L402 | ¦I_+--I_0¦<eta_1/2
EDGE: bpI:p3:uniform | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-position@L402-L402 | eps_1 <= eta_1/(2C_K)
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-position@L402-L402 | eta_1, d_B, S, sigma_K, mu, D-frak
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:tori-position@L403-L403 | local Part 3 data, including h, B', f or epsilon
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p3+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: toriSide_of_applyOut (KAM/Iso/Charts/Tori.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; row tori-base/close/position
NOTE: -

NODE: bpI:p3:apply#constants
KIND: step
TITLE: Select the per-ray frozen I-G1 constants before the perturbation
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply#constants@L321-L322
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply#constants@L321-L322
CONTRACT_ID: bpI:p3:apply#constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: geometric/domain data (B,s_0,r_0,h,B',eta); a patch with one selected ray; n=2, tau=2, the fixed constants of p3:constants and gammabar := gamma_{p,+-}
SOURCE_QUANTIFIERS: geometric data, patch, ray and gamma fixed first; then choose C_1,C_2,C_3 > 0; then for all D,H,K,s,gamma,e,E_0 satisfying the frozen hypotheses
SOURCE_CONCLUSION: choose one tuple C_i^{p,+-} from bpI:p0:g1 with n=2, tau=2, rho=s/4, rho_infty=s/8, M, sigma_K, sigma_B, sigma_T, mu, sigma_omega, nu, gammabar and omega* fixed as in L321-L322; retain the frozen conditional conclusion for that same tuple
CONSTANT_SCOPE: C_i depend only on the geometric data and the fixed ray, never on f, epsilon, E, I_0
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p3:setting, bpI:p3:constants, bpI:p3:compact, bpI:p3:patch, bpI:p3:patch-rays, bpI:p0:g1
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply#constants@L321-L321 | geometric data only
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply#constants@L322-L322 | positive widths and fixed parameters
EDGE: bpI:p3:compact | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply#constants@L322-L322 | m_h, M_g and S_h positive finite
EDGE: bpI:p3:patch | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply#constants@L321-L321 | fixed patch
EDGE: bpI:p3:patch-rays | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply#constants@L321-L321 | gamma positive and omega* nonzero
EDGE: bpI:p0:g1 | blueprint-I/parts/p3-iso-local-charts.tex#bpI:p3:apply#constants@L321-L321 | frozen existential constants with this quantifier order
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-I-p3
REVIEWER: sol-delta-I-b
LEAN_STATUS: PROVED
LEAN_REF: apply (KAM/Iso/Charts/Apply.lean)
LEAN_NOTE: audit I3-5 PASS WITH NOTES; named with apply (retained full gate body)
NOTE: Proposed by independent review; requires a different delta reviewer.

NODE: stepI:p3:to-torsion#flat-route
KIND: route
TITLE: Torsion and averaging by direct flat formula
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L311-L313
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L311-L313
CONTRACT_ID: stepI:p3:to-torsion#flat-route
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; epsilon <= 1; D := D-frak; I in B real; omega := grad h(I); K(theta) := (theta,I)
SOURCE_QUANTIFIERS: I and omega as in torus; theta in T_{s/2}
SOURCE_CONCLUSION: T_ij = d_i d_j h(I) + d_{I_i}d_{I_j} f(theta,I); last column omega = grad h(I); last row Y_b = d_b h(I) + d_{I_b} f(theta,I); T_H = B_h(I) + R with R the f-part, ¦R¦ <= 2F_2 epsilon (row-sums), avg T_H defined (integrable) and ¦avg T_H - B_h(I)¦ <= 2F_2 epsilon, avg B_h = B_h
CONSTANT_SCOPE: F_1,F_2 from p3:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:tr-compare, bpI:p3:hypothesis-d, K:bp:p1:ext-integral, stepI:p3:to-torus, bpI:p3:constants, bpI:p3:setting, bpI:p0:extended#extendedTorsion, bpI:p0:extended#extendedTorsionAverage, K:bp:p1:holomorphic-regularity, bpI:p1:ext-chain, bpI:p0:stripdata#torsion
ROUTES: -
ROUTE_FOR: stepI:p3:to-torsion
EDGE: stepI:p1:tr-compare | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L313-L313 | same flat data, frame, error and derivative bounds used in L311-L313
EDGE: bpI:p3:hypothesis-d | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L313-L313 | same flat data, frame, error and derivative bounds used in L311-L313
EDGE: K:bp:p1:ext-integral | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L313-L313 | same flat data, frame, error and derivative bounds used in L311-L313
EDGE: stepI:p3:to-torus | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L311-L311 | N_j = (0,e_j) and D_theta N_j = 0 in the torsion calculation
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L313-L313 | same flat data, frame, error and derivative bounds used in L311-L313
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L313-L313 | same flat data, frame, error and derivative bounds used in L311-L313
EDGE: bpI:p0:extended#extendedTorsion | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L312-L312 | the explicitly stated direct value Y_b = DH(K) N_b
EDGE: bpI:p0:extended#extendedTorsionAverage | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L313-L313 | entrywise unit-cube average
EDGE: K:bp:p1:holomorphic-regularity | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L313-L313 | continuity of the first and second derivative entries in the displayed flat formula
EDGE: bpI:p1:ext-chain | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L312-L312 | differentiate H=h+f and evaluate on the constant normal frame
EDGE: bpI:p0:stripdata#torsion | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#flat-route@L311-L311 | the defining torsion formula with constant N gives T_ij from DX_H and D_theta N = 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-delta-I-b
REVIEWER: sol-delta-I-c
LEAN_STATUS: PROVED
LEAN_REF: TorusAux.torsion_flat, TorusAux.energyRow_flat, TorusAux.extendedTorsion_flat, TorusAux.norm_flatRemainder_le (KAM/Iso/Charts/Torus.lean)
LEAN_NOTE: audit I3-4 PASS WITH NOTES; the documented flat route is the one implemented
NOTE: The source supplies the direct value DH(K)N_b at L312 and the full R formula at L313 (stated at L296-L297). Continuity of these explicit derivative entries on the compact real cube and the already cited ext-integral give the average and bound; this route does not generalize the Part 1 lemmas or assume a Diophantine omega. Requires independent delta review.

NODE: stepI:p3:to-torsion#citation-route
KIND: route
TITLE: Torsion and averaging by the cited Part 1 shortcut
STATEMENT_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L311-L313
PROOF_SOURCE: blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L311-L313
CONTRACT_ID: stepI:p3:to-torsion#citation-route
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Part 3 setting; epsilon <= 1; D := D-frak; I in B real; omega := grad h(I); K(theta) := (theta,I)
SOURCE_QUANTIFIERS: I and omega as in torus; theta in T_{s/2}
SOURCE_CONCLUSION: T_ij = d_i d_j h(I) + d_{I_i}d_{I_j} f(theta,I); last column omega = grad h(I); last row Y_b = d_b h(I) + d_{I_b} f(theta,I); T_H = B_h(I) + R with R the f-part, ¦R¦ <= 2F_2 epsilon (row-sums), avg T_H defined (integrable) and ¦avg T_H - B_h(I)¦ <= 2F_2 epsilon, avg B_h = B_h
CONSTANT_SCOPE: F_1,F_2 from p3:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p1:tr-compare, bpI:p3:hypothesis-d, K:bp:p1:ext-integral, stepI:p3:to-torus, stepI:p3:to-error, bpI:p3:constants, bpI:p3:setting, stepI:p3:to-torsion#p1-setting, bpI:p1:last-row, bpI:p1:extended-basic, bpI:p0:stripdata#torsion
ROUTES: -
ROUTE_FOR: stepI:p3:to-torsion
EDGE: stepI:p1:tr-compare | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L313-L313 | same flat data, frame, error and derivative bounds used in L311-L313
EDGE: bpI:p3:hypothesis-d | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L313-L313 | same flat data, frame, error and derivative bounds used in L311-L313
EDGE: K:bp:p1:ext-integral | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L313-L313 | same flat data, frame, error and derivative bounds used in L311-L313
EDGE: stepI:p3:to-torus | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L311-L311 | N_j = (0,e_j) and D_theta N_j = 0 in the torsion calculation
EDGE: stepI:p3:to-error | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L312-L312 | E = X_f gives eta^L_b = -partial_I_b f in the cited last-row calculation
EDGE: bpI:p3:constants | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L313-L313 | same flat data, frame, error and derivative bounds used in L311-L313
EDGE: bpI:p3:setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L313-L313 | same flat data, frame, error and derivative bounds used in L311-L313
EDGE: stepI:p3:to-torsion#p1-setting | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L312-L312 | missing full-package premise discharge for the citations
EDGE: bpI:p1:last-row | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L312-L312 | last-row identity (a)
EDGE: bpI:p1:extended-basic | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L313-L313 | integrability and identification of the average
EDGE: bpI:p0:stripdata#torsion | blueprint-I/parts/p3-iso-local-charts.tex#stepI:p3:to-torsion#citation-route@L311-L311 | the defining torsion formula with constant N gives T_ij from DX_H and D_theta N = 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-delta-I-b
REVIEWER: sol-delta-I-c
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27, track-I gap survey GAP-PLAN-I item 3): alternative route not used; the flat route is implemented
NOTE: This route retains the actual Part 1 citations and their exposed SOURCE_GAP premise check. It is an alternative to the direct flat-formula route, not a mandatory extra premise for that route.

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

NODE: bpI:p6:det-formula
KIND: lemma
TITLE: Determinant of the Kepler bordered matrix
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:det-formula@L13-L19
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:det-formula@L20-L35
CONTRACT_ID: bpI:p6:det-formula
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega in R and L > 0 (no sign condition on kappa, Omega)
SOURCE_QUANTIFIERS: kappa, Omega, L
SOURCE_CONCLUSION: det K_{kappa,Omega}(L) = 3 kappa Omega^2 / L^4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:expand, stepI:p6:eval, bpI:p0:keplerborder#keplerBorder
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:expand | blueprint-I/parts/p6-kepler.tex#bpI:p6:det-formula@L21-L21 | proof step: Sarrus expansion
EDGE: stepI:p6:eval | blueprint-I/parts/p6-kepler.tex#bpI:p6:det-formula@L29-L29 | proof step: evaluation of the expansion
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#bpI:p6:det-formula@L16-L16 | K_{kappa,Omega}(L) is the frozen Kepler bordered matrix
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.keplerBorder_det (KAM/Iso/Kepler.lean)
LEAN_NOTE: audit W1-seal-1 PASS: all real kappa, Omega, positive L, exact rational determinant
NOTE: -

NODE: stepI:p6:expand
KIND: step
TITLE: Expansion
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:expand@L21-L28
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:expand@L21-L28
CONTRACT_ID: stepI:p6:expand
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega in R, L > 0; entries of K_{kappa,Omega}(L) from Definition keplerborder
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: K = (k_ij) with k11=-3kappa/L^4, k13=k31=kappa/L^3, k23=k32=-Omega, other entries 0; det K = k11k22k33+k12k23k31+k13k21k32-k13k22k31-k12k21k33-k11k23k32
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:keplerborder#keplerBorder
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#stepI:p6:expand@L23-L23 | entries of the frozen matrix keplerBorder (carrier L > 0)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.keplerBorder_det (KAM/Iso/Kepler.lean)
LEAN_NOTE: Rule 05:10: proof body Kepler.lean:21-29 (Matrix.det_fin_three Sarrus; only -k11 k23 k32 survives); W1-seal-audit-1.md:148 confirms content; parent bpI:p6:kepler PROVED.
NOTE: -

NODE: stepI:p6:eval
KIND: step
TITLE: Evaluation
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:eval@L29-L34
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:eval@L29-L34
CONTRACT_ID: stepI:p6:eval
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Sarrus expansion of step expand; k12 = k21 = k22 = k33 = 0
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: det K_{kappa,Omega}(L) = -k11 k23 k32 = 3 kappa Omega^2 / L^4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:expand
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:expand | blueprint-I/parts/p6-kepler.tex#stepI:p6:eval@L30-L30 | uses the entries and the expansion of the previous step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.keplerBorder_det (KAM/Iso/Kepler.lean)
LEAN_NOTE: Rule 05:10: proof body Kepler.lean:21-29 (Matrix.det_fin_three Sarrus; only -k11 k23 k32 survives); W1-seal-audit-1.md:148 confirms content; parent bpI:p6:kepler PROVED.
NOTE: -

NODE: bpI:p6:kepler
KIND: theorem
TITLE: I-KEPLER, proof
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:kepler@L37-L42
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:kepler@L43-L48
CONTRACT_ID: bpI:p6:kepler
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega > 0; L > 0
SOURCE_QUANTIFIERS: kappa, Omega first, then L in the subtype {L : R | 0 < L}
SOURCE_CONCLUSION: det K_{kappa,Omega}(L) = 3 kappa Omega^2 / L^4 and det K_{kappa,Omega}(L) > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:k-value, stepI:p6:k-pos, bpI:p0:keplerborder#keplerBorder
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:k-value | blueprint-I/parts/p6-kepler.tex#bpI:p6:kepler@L44-L44 | proof step Value
EDGE: stepI:p6:k-pos | blueprint-I/parts/p6-kepler.tex#bpI:p6:kepler@L46-L46 | proof step Positivity
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#bpI:p6:kepler@L38-L38 | K_{kappa,Omega}(L) is the frozen matrix keplerBorder
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.kepler_bordered_det (KAM/Frozen/Iso/Theorems/KeplerBorderedDet.lean); KAM.Iso.keplerBorder_det_pos (KAM/Iso/Kepler.lean)
LEAN_NOTE: I-KEPLER anchor SEALED (manifest); audit W1-seal-1 PASS WITH NOTES
NOTE: Proof of the frozen anchor bpI:p0:kepler (see its EDGE there); statement reference to the anchor dropped by SPEC (proved-in)

NODE: stepI:p6:k-value
KIND: step
TITLE: Value
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:k-value@L44-L44
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:k-value@L44-L44
CONTRACT_ID: stepI:p6:k-value
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega > 0, L > 0
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: det K_{kappa,Omega}(L) = 3 kappa Omega^2 / L^4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:det-formula
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:det-formula | blueprint-I/parts/p6-kepler.tex#stepI:p6:k-value@L44-L44 | the determinant formula, valid for all real kappa, Omega
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.keplerBorder_det (KAM/Iso/Kepler.lean)
LEAN_NOTE: Lean statement holds for all real kappa, Omega (stronger than kappa,Omega>0); W1-seal-audit-1.md:47 PASS.
NOTE: -

NODE: stepI:p6:k-pos
KIND: step
TITLE: Positivity
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:k-pos@L46-L47
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:k-pos@L46-L47
CONTRACT_ID: stepI:p6:k-pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa > 0, Omega != 0, L > 0; value of step k-value
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: 3 kappa Omega^2 / L^4 > 0, hence det K > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:k-value
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:k-value | blueprint-I/parts/p6-kepler.tex#stepI:p6:k-pos@L46-L46 | the value whose numerator and denominator are shown positive
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: no audit row names or confirms this step
NOTE: -

NODE: bpI:p6:kep-ham
KIND: definition
TITLE: The Kepler--rotation Hamiltonian
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-ham@L58-L67
PROOF_SOURCE: -
CONTRACT_ID: bpI:p6:kep-ham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: kappa, Omega in R
SOURCE_QUANTIFIERS: kappa, Omega, then I in C^2 with I_1 != 0
SOURCE_CONCLUSION: defines h_{kappa,Omega}(I) = -kappa/(2 I_1^2) - Omega I_2 on C^2 (Lean division; value at I_1 = 0 never used); holomorphic on the open set {I_1 != 0}; real at real I with I_1 != 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerRotH, differentiableOn_keplerRotH, keplerRotH_real (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; definition + holomorphy off I_1=0 + reality
NOTE: standing definition package of Parts 6-8 (SPEC)

NODE: bpI:p6:kep-border
KIND: lemma
TITLE: Frequency map and bordered Hessian of $h_{\kappa,\Omega}$
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L69-L87
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L88-L108
CONTRACT_ID: bpI:p6:kep-border
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega in R; I in R^2 with I_1 > 0
SOURCE_QUANTIFIERS: kappa, Omega, then I
SOURCE_CONCLUSION: frequencyMap h_{kappa,Omega} I = (kappa/I_1^3, -Omega); D(frequencyMap h)(I) = [[-3kappa/I_1^4,0],[0,0]]; borderedHessian h_{kappa,Omega} I = reindex_eps K_{kappa,Omega}(I_1); det borderedHessian h I = 3 kappa Omega^2 / I_1^4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:kep-ham, bpI:p0:realham#frequencyMap, bpI:p0:bordered#borderedHessian, bpI:p0:keplerborder#keplerBorder, stepI:p6:kb-real, stepI:p6:kb-grad, stepI:p6:kb-hess, stepI:p6:kb-entries, stepI:p6:kb-det
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L72-L72 | the Hamiltonian h_{kappa,Omega}
EDGE: bpI:p0:realham#frequencyMap | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L72-L72 | frozen frequencyMap of h
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L79-L79 | frozen borderedHessian of h
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L79-L79 | frozen keplerBorder K_{kappa,Omega}(I_1)
EDGE: stepI:p6:kb-real | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L89-L89 | proof step
EDGE: stepI:p6:kb-grad | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L94-L94 | proof step
EDGE: stepI:p6:kb-hess | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L98-L98 | proof step
EDGE: stepI:p6:kb-entries | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L101-L101 | proof step
EDGE: stepI:p6:kb-det | blueprint-I/parts/p6-kepler.tex#bpI:p6:kep-border@L106-L106 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: frequencyMap_keplerRotH, fderiv_frequencyMap_keplerRotH, borderedHessian_keplerRotH, det_borderedHessian_keplerRotH, finThreeEquivSumUnit (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; all four clauses of the lemma
NOTE: -

NODE: stepI:p6:kb-real
KIND: step
TITLE: Real part near a real point
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-real@L89-L92
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-real@L89-L92
CONTRACT_ID: stepI:p6:kb-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega in R; I in R^2 with I_1 > 0; V = {J in R^2 : J_1 > 0} open
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: for J in V, h_{kappa,Omega}(iota J) is real and equals phi(J) = -kappa/(2 J_1^2) - Omega J_2; Re h(iota J) = phi(J) on the neighbourhood V of I
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-real@L90-L90 | h_{kappa,Omega} evaluated at real points
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: re_keplerRotH_real, keplerRotH_real (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; named step kb-real (private helper re_keplerRotH_real)
NOTE: -

NODE: stepI:p6:kb-grad
KIND: step
TITLE: Gradient
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-grad@L94-L96
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-grad@L94-L96
CONTRACT_ID: stepI:p6:kb-grad
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step kb-real; germ locality of the Frechet derivative
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: frequencyMap h J0 = grad phi(J0) = (kappa/J_1^3, -Omega) for J0 in V; on V the map frequencyMap h coincides with g(J) = (kappa J_1^-3, -Omega)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:kb-real, bpI:p0:realham#frequencyMap, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:kb-real | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-grad@L95-L95 | Re h o iota agrees with phi near J0
EDGE: bpI:p0:realham#frequencyMap | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-grad@L95-L95 | frequencyMap is the real gradient of Re h o iota
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-grad@L95-L95 | the Hamiltonian h
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: frequencyMap_keplerRotH, hasFDerivAt_keplerRotH_real (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; named step kb-grad
NOTE: -

NODE: stepI:p6:kb-hess
KIND: step
TITLE: Derivative of the frequency map
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-hess@L98-L99
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-hess@L98-L99
CONTRACT_ID: stepI:p6:kb-hess
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa,Omega in R; I in R^2 with I_1>0; h=h_{kappa,Omega} of Definition kep-ham
SOURCE_QUANTIFIERS: For every kappa,Omega in R and every real I with I_1>0
SOURCE_CONCLUSION: D(frequencyMap h)(I) = Dg(I), first row (-3kappa I_1^-4, 0), second row 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:kb-grad, bpI:p0:realham#frequencyMap, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:kb-grad | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-hess@L98-L98 | frequencyMap h = g on the open set V, so derivatives agree
EDGE: bpI:p0:realham#frequencyMap | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-hess@L98-L98 | frequencyMap h
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-hess@L98-L99 | h or h~ is the Hamiltonian fixed by the Kepler package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: fderiv_frequencyMap_keplerRotH, hasFDerivAt_frequencyMap_keplerRotH (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; named step kb-hess
NOTE: -

NODE: stepI:p6:kb-entries
KIND: step
TITLE: Entries of the bordered matrix
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L101-L104
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L101-L104
CONTRACT_ID: stepI:p6:kb-entries
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa,Omega in R; I in R^2 with I_1>0; h=h_{kappa,Omega} of Definition kep-ham; epsilon is the fixed bijection Fin 3 equiv Fin 2 plus Unit used in the enclosing statement
SOURCE_QUANTIFIERS: For every kappa,Omega in R and every real I with I_1>0
SOURCE_CONCLUSION: entries of borderedHessian h I: Dg(I) block, border entries g(I)_a, corner 0; these coincide with the entries of K_{kappa,Omega}(I_1); so borderedHessian h I = reindex_eps K_{kappa,Omega}(I_1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:bordered#borderedHessian, stepI:p6:kb-hess, stepI:p6:kb-grad, bpI:p0:keplerborder#keplerBorder, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L101-L101 | definition of the bordered Hessian: block, border and corner entries
EDGE: stepI:p6:kb-hess | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L102-L102 | the Hessian block Dg(I)
EDGE: stepI:p6:kb-grad | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L102-L102 | the border entries g(I)_a
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L103-L103 | entrywise comparison with keplerBorder at L = I_1
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-entries@L101-L104 | h or h~ is the Hamiltonian fixed by the Kepler package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: borderedHessian_keplerRotH (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; named step kb-entries
NOTE: -

NODE: stepI:p6:kb-det
KIND: step
TITLE: Determinant
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-det@L106-L107
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-det@L106-L107
CONTRACT_ID: stepI:p6:kb-det
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa,Omega in R; I in R^2 with I_1>0; h=h_{kappa,Omega} of Definition kep-ham; epsilon is that same index bijection
SOURCE_QUANTIFIERS: For every kappa,Omega in R and every real I with I_1>0
SOURCE_CONCLUSION: det borderedHessian h I = det K_{kappa,Omega}(I_1) = 3 kappa Omega^2 / I_1^4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p6:kb-entries, bpI:p6:det-formula, bpI:p0:bordered#borderedHessian, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p6:kb-entries | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-det@L106-L106 | borderedHessian h I = reindex K
EDGE: bpI:p6:det-formula | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-det@L107-L107 | value of det K at L = I_1 > 0
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-det@L106-L106 | determinant of the frozen bordered Hessian
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:kb-det@L106-L107 | h or h~ is the Hamiltonian fixed by the Kepler package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: det_borderedHessian_keplerRotH (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-1 PASS WITH NOTES; named step kb-det (uses I-0 keplerBorder_det)
NOTE: -

NODE: bpI:p6:conversion-map
KIND: definition
TITLE: Period-one conversion map
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion-map@L112-L117
PROOF_SOURCE: -
CONTRACT_ID: bpI:p6:conversion-map
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (a definition)
SOURCE_QUANTIFIERS: theta, I in R^2 (and in C^2)
SOURCE_CONCLUSION: defines S(theta, I) = (2 pi theta, I/(2 pi)) on R^2 x R^2 and on C^2 x C^2; linear isomorphism; maps Z^2-translations of theta to 2 pi Z^2-translations of (ell, g)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: periodOneMap, periodOneMapC, periodOneCLM, periodOneInvCLM (KAM/Iso/Conversion.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; definition landed
NOTE: 2 pi conversion package of Parts 6-8 (SPEC); the K reference in its \source is provenance

NODE: bpI:p6:conversion
KIND: lemma
TITLE: Conversion
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L119-L141
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L142-L155
CONTRACT_ID: bpI:p6:conversion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa, Omega in R; kappa' = kappa (2 pi)^2, Omega' = Omega/(2 pi); (a) H differentiable; (b) I in C^2 with I_1 != 0; (c),(d) I in R^2 with I_1 > 0
SOURCE_QUANTIFIERS: kappa, Omega first (then kappa', Omega'), then H or I
SOURCE_CONCLUSION: (a) D S^T J D S = J = D S J D S^T, D S X_{H o S} = X_H o S, and w solves w' = X_{H o S}(w) iff S w solves y' = X_H(y); (b) h_{kappa,Omega}(I/(2 pi)) = h_{kappa',Omega'}(I), so h~ is the Kepler-rotation Hamiltonian of the converted constants, holomorphic on {I_1 != 0}, real at real I; (c) grad h~(I) = (kappa'/I_1^3, -Omega') = (1/(2 pi)) grad h_{kappa,Omega}(I/(2 pi)); (d) K_{kappa',Omega'}(I_1) = D K_{kappa,Omega}(I_1/(2 pi)) D with D = diag(1/(2 pi), 1/(2 pi), 1), borderedHessian h~ I = reindex K_{kappa',Omega'}(I_1), det = 3 kappa' Omega'^2 / I_1^4 = 3 kappa Omega^2 / I_1^4; for kappa = Omega = 1, kappa' = (2pi)^2 > 0, Omega' = 1/(2pi) > 0 and det borderedHessian h~ I = 3/I_1^4 > 0 for real I_1 > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:conversion-map, bpI:p6:kep-ham, bpI:p0:keplerborder#keplerBorder, bpI:p0:bordered#borderedHessian, stepI:p6:cv-sympl, stepI:p6:cv-ham, stepI:p6:cv-border
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L122-L122 | the conversion S
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L126-L126 | h_{kappa,Omega} and h_{kappa',Omega'}
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L132-L132 | K_{kappa,Omega} and K_{kappa',Omega'}
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L133-L133 | borderedHessian of h~
EDGE: stepI:p6:cv-sympl | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L143-L143 | proof of (a)
EDGE: stepI:p6:cv-ham | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L149-L149 | proof of (b)
EDGE: stepI:p6:cv-border | blueprint-I/parts/p6-kepler.tex#bpI:p6:conversion@L151-L151 | proof of (c) and (d)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-review-I-p67
REVIEWER: sol-delta-I-c
LEAN_STATUS: PROVED
LEAN_REF: periodOneMap_symplectic, periodOneMap_hamiltonianVectorField, periodOneMap_hasDerivAt_iff, keplerRotH_comp_div, frequencyMap_comp_div, keplerBorder_conversion, borderedHessian_conversion (KAM/Iso/Conversion.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; parts (a)-(d); (b) proved in stronger total-division form
NOTE: -

NODE: stepI:p6:cv-sympl
KIND: step
TITLE: Symplectic
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-sympl@L143-L147
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-sympl@L143-L147
CONTRACT_ID: stepI:p6:cv-sympl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S as in Definition conversion-map; J = [[0,1],[-1,0]]; H differentiable
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: D S = diag(2pi,2pi,1/(2pi),1/(2pi)); D S^T J D S = J = D S J D S^T; D S X_{H o S} = X_H o S; d/dt (S w) = D S w'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:conversion-map
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-sympl@L143-L143 | D S of the conversion map
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: periodOneMap_symplectic, periodOneMap_hamiltonianVectorField, periodOneMap_hasDerivAt_iff (KAM/Iso/Conversion.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; named step cv-sympl
NOTE: -

NODE: stepI:p6:cv-ham
KIND: step
TITLE: Hamiltonian
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-ham@L149-L149
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-ham@L149-L149
CONTRACT_ID: stepI:p6:cv-ham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I in C^2 with I_1 != 0
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: h_{kappa,Omega}(I/(2 pi)) = h_{kappa',Omega'}(I) (field arithmetic)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:kep-ham, bpI:p6:conversion-map
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-ham@L149-L149 | h_{kappa,Omega} at I/(2 pi) and h_{kappa',Omega'} at I
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-ham@L149-L149 | the substitution I -> I/(2 pi) is the action part of S
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerRotH_comp_div (KAM/Iso/Conversion.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; named step cv-ham
NOTE: -

NODE: stepI:p6:cv-border
KIND: step
TITLE: Frequencies and bordered Hessian
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L151-L154
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L151-L154
CONTRACT_ID: stepI:p6:cv-border
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lemma kep-border for (kappa', Omega'); part (b); I real with I_1 > 0
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: grad h~(I) = (kappa'/I_1^3, -Omega') = (1/(2 pi)) grad h_{kappa,Omega}(I/(2 pi)); K_{kappa',Omega'}(I_1) = D K_{kappa,Omega}(I_1/(2 pi)) D entrywise; borderedHessian h~ I = reindex K_{kappa',Omega'}(I_1); det = 3 kappa' Omega'^2/I_1^4 = 3 kappa Omega^2/I_1^4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:kep-border, stepI:p6:cv-ham, bpI:p6:kep-ham, bpI:p6:conversion-map, bpI:p0:keplerborder#keplerBorder, bpI:p6:det-formula
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:kep-border | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L151-L151 | applied to (kappa', Omega')
EDGE: stepI:p6:cv-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L151-L151 | part (b): h~ = h_{kappa',Omega'}
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L151-L151 | h~ is a Kepler-rotation Hamiltonian
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L151-L151 | chain rule for I -> I/(2 pi)
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L153-L153 | entries of K_{kappa',Omega'}(I_1)
EDGE: bpI:p6:det-formula | blueprint-I/parts/p6-kepler.tex#stepI:p6:cv-border@L154-L154 | det K_{kappa,Omega}(L) at L = I_1/(2 pi) gives the second value of the determinant
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: frequencyMap_comp_div, keplerBorder_conversion, borderedHessian_conversion (KAM/Iso/Conversion.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; named step cv-border
NOTE: -

NODE: bpI:p6:nondeg
KIND: corollary
TITLE: Nondegeneracy in period-one variables
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L157-L159
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L160-L163
CONTRACT_ID: bpI:p6:nondeg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa = Omega = 1; B subset {I in R^2 : I_1 > 0}; 0 < r_0 <= (1/2) inf_B I_1
SOURCE_QUANTIFIERS: B and r_0 (B_{r_0} as in Part 0)
SOURCE_CONCLUSION: h~ = h_{(2pi)^2,1/(2pi)} holomorphic on {I in C^2 : I_1 != 0}, real at real I, det borderedHessian h~ I = 3/I_1^4 > 0 for real I with I_1 > 0; h~ holomorphic on B_{r_0}, every real I in B_{r_0} has I_1 > 0, and det borderedHessian h~ I != 0 for every real I in B_{r_0} (nondegeneracy hypothesis of the frozen I-HEAD)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:conversion, bpI:p6:kep-border, bpI:p6:kep-ham, bpI:p0:bordered#borderedHessian, bpI:p0:domains#actionNbhd, stepI:p6:nd-domain, stepI:p6:nd-concl
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:conversion | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L158-L158 | (b),(d): h~ and its bordered Hessian determinant
EDGE: bpI:p6:kep-border | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L158-L158 | determinant formula for real I with I_1 > 0
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L158-L158 | h~ = h_{(2pi)^2,1/(2pi)}
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L158-L158 | borderedHessian h~
EDGE: bpI:p0:domains#actionNbhd | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L158-L158 | B_{r_0} is the frozen action neighbourhood
EDGE: stepI:p6:nd-domain | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L161-L161 | proof step Domain
EDGE: stepI:p6:nd-concl | blueprint-I/parts/p6-kepler.tex#bpI:p6:nondeg@L162-L162 | proof step Conclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: nondeg_period_one (KAM/Iso/Conversion.lean); differentiableOn_keplerRotH, keplerRotH_real, det_borderedHessian_keplerRotH (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; nondeg_period_one plus imported I-1 API cover all clauses (I-2 audit says so)
NOTE: -

NODE: stepI:p6:nd-domain
KIND: step
TITLE: Domain
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-domain@L161-L161
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-domain@L161-L161
CONTRACT_ID: stepI:p6:nd-domain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B subset {I_1 > 0}, 0 < r_0 <= (1/2) inf_B I_1; I in B_{r_0}
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: there is J in B with |Re I_1 - J_1| < r_0 <= J_1/2, so Re I_1 > J_1/2 > 0; hence I_1 != 0, and I_1 > 0 for real I
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:domains#actionNbhd
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:domains#actionNbhd | blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-domain@L161-L161 | definition of B_{r_0}: I within r_0 of some J in B
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: nondeg_period_one (KAM/Iso/Conversion.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; named step nd-domain
NOTE: -

NODE: stepI:p6:nd-concl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-concl@L162-L162
PROOF_SOURCE: blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-concl@L162-L162
CONTRACT_ID: stepI:p6:nd-concl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: kappa=Omega=1, h_tilde=h_{(2 pi)^2,1/(2 pi)}; B subset {I in R^2:I_1>0}, 0<r_0<=inf_B I_1/2, as in the enclosing nondegeneracy corollary
SOURCE_QUANTIFIERS: With kappa=Omega=1 fixed, for every B,r_0 satisfying the enclosing corollary, and every real I in B_{r_0} for the determinant assertion
SOURCE_CONCLUSION: h~ holomorphic on B_{r_0}, real at real I, and det borderedHessian h~ I = 3/I_1^4 > 0 for real I in B_{r_0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:conversion, bpI:p6:kep-border, stepI:p6:nd-domain, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:conversion | blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-concl@L162-L162 | (b),(d) with kappa = Omega = 1
EDGE: bpI:p6:kep-border | blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-concl@L162-L162 | bordered Hessian determinant
EDGE: stepI:p6:nd-domain | blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-concl@L162-L162 | I_1 != 0 (and > 0 for real I) on B_{r_0}
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p6-kepler.tex#stepI:p6:nd-concl@L162-L162 | h or h~ is the Hamiltonian fixed by the Kepler package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: nondeg_period_one (KAM/Iso/Conversion.lean); det_borderedHessian_keplerRotH (KAM/Iso/KeplerHamiltonian.lean)
LEAN_NOTE: audit I-2 PASS WITH NOTES; named step nd-concl
NOTE: -

NODE: bpI:p7:x-hol
KIND: external
TITLE: Holomorphic functions of several variables
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-hol@L32-L34
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: holomorphic functions on open subsets of C^m
SOURCE_CONCLUSION: sums, products, compositions and quotients (nonvanishing denominator) of holomorphic functions are holomorphic; exp, sin, cos entire; z^{-1/2} = exp(-(1/2) Log z) holomorphic on {Re z > 0} with |z^{-1/2}| = |z|^{-1/2} <= (Re z)^{-1/2} and z^{-1/2} = 1/sqrt z for z > 0; sqrt holomorphic on {Re z > 0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p7:x-weier
KIND: external
TITLE: Weierstrass
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-weier@L35-L35
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-weier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a sequence of holomorphic functions on an open set of C^m converging uniformly
SOURCE_QUANTIFIERS: open set U in C^m, functions f_m
SOURCE_CONCLUSION: the uniform limit is holomorphic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p7:x-param
KIND: external
TITLE: Parameter integrals
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-param@L36-L36
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-param
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Phi holomorphic on an open U in C^m x C with (q, t mu) in U for all t in [0,1]
SOURCE_QUANTIFIERS: Phi, U
SOURCE_CONCLUSION: (q, mu) -> int_0^1 Phi(q, t mu) dt is holomorphic on that set
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p7:x-schwarz
KIND: external
TITLE: Schwarz lemma (maximum modulus)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-schwarz@L37-L37
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-schwarz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g holomorphic on a neighbourhood of the closed disc D(0, varrho), g(0) = 0
SOURCE_QUANTIFIERS: g, varrho, then mu with |mu| <= varrho
SOURCE_CONCLUSION: |g(mu)| <= (|mu|/varrho) max_{|zeta| = varrho} |g(zeta)|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p7:x-ift
KIND: external
TITLE: Inverse function theorem (real-analytic)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-ift@L38-L38
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-ift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: real-analytic map between open subsets of R^m with invertible differential at every point
SOURCE_QUANTIFIERS: the map
SOURCE_CONCLUSION: it is a local real-analytic diffeomorphism; if bijective, it is a real-analytic diffeomorphism
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p7:x-forms
KIND: external
TITLE: Exterior calculus on open subsets of $\R^m$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:x-forms@L39-L40
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:x-forms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: forms on open subsets of R^m; F smooth with F^*(sum p_i dq_i) = sum P_i dQ_i + dS for a smooth S
SOURCE_QUANTIFIERS: F, S
SOURCE_CONCLUSION: d^2 = 0; d commutes with pull-back by smooth maps; a form is determined by its values on tangent vectors; and DF^T J DF = J (sum dP_i wedge dQ_i standing for -J in the order Q, P)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpI:p7:ham-eq
KIND: lemma
TITLE: Hamilton's equations
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L51-L57
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L58-L70
CONTRACT_ID: bpI:p7:ham-eq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu in R; W_mu as in section data
SOURCE_QUANTIFIERS: mu in R, then z in W_mu / J subset R, z : J -> R^2 x R^2
SOURCE_CONCLUSION: H^R3_mu is C^infty (real-analytic) on W_mu and V_mu = X_{H^R3_mu} = (d_p H, -d_q H) at every point of W_mu; RSol_mu(J,z) holds iff for every t in J: z(t) in W_mu and z differentiable at t with z'(t) = X_H(z(t)); IsRestrictedSolutionOn iff IsSolIn for V_mu on W_mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:sec-ham#data, bpI:p0:restricted#restrictedHamiltonian, bpI:p0:restricted#restrictedVectorField, bpI:p0:restricted#IsRestrictedSolutionOn, bpI:p0:primaries#CollisionFree, bpN:p3:newton-reduction, stepI:p7:he-smooth, stepI:p7:he-deriv, stepI:p7:he-sol
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:sec-ham#data | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L52-L52 | W_mu and the formulas for H^R3_mu, V_mu
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L52-L52 | frozen restrictedHamiltonian
EDGE: bpI:p0:restricted#restrictedVectorField | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L52-L52 | frozen restrictedVectorField
EDGE: bpI:p0:restricted#IsRestrictedSolutionOn | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L53-L53 | RSol_mu
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L53-L53 | collision-freeness clause
EDGE: bpN:p3:newton-reduction | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L54-L54 | shared ODE layer: IsRestrictedSolutionOn iff IsSolIn
EDGE: stepI:p7:he-smooth | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L59-L59 | proof step
EDGE: stepI:p7:he-deriv | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L61-L61 | proof step
EDGE: stepI:p7:he-sol | blueprint-I/parts/p7-delaunay.tex#bpI:p7:ham-eq@L69-L69 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: analyticOnNhd_restrictedHamTotal, restrictedVectorField_eq_hamiltonian, isRestrictedSolutionOn_iff, restrictedHamiltonian_eq (KAM/Iso/RestrictedHam.lean)
LEAN_NOTE: audit I-3 PASS WITH NOTES (p7:ham-eq rows); steps he-* not named in audit, left
NOTE: -

NODE: stepI:p7:he-smooth
KIND: step
TITLE: Smoothness
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-smooth@L59-L59
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-smooth@L59-L59
CONTRACT_ID: stepI:p7:he-smooth
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu in R; z = (q,p) in W_mu
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: r_j^2 = theta(q - a_j) is a polynomial positive on W_mu; r_j and 1/r_j are C^infty (real-analytic) on W_mu; the remaining terms of H^R3_mu are polynomial
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:sec-ham#data, bpI:p0:primaries#radiusSq, bpI:p0:primaries#radius, bpI:p0:restricted#restrictedHamiltonian
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:sec-ham#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-smooth@L59-L59 | W_mu, r_j
EDGE: bpI:p0:primaries#radiusSq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-smooth@L59-L59 | r_j^2 = radiusSq
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-smooth@L59-L59 | r_j = rad
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-smooth@L59-L59 | terms of H^R3_mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.he_smooth (KAM/Iso/TransferStepNodes.lean)
LEAN_NOTE: GAP-I7b (audit PASS WITH NOTES)
NOTE: -

NODE: stepI:p7:he-deriv
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L67
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L67
CONTRACT_ID: stepI:p7:he-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu in R; z=(q,p) in the collision-free set W_mu of L48-49; r_j=rad(q-primary_j(mu))
SOURCE_QUANTIFIERS: For every mu in R and every z in W_mu
SOURCE_CONCLUSION: (d_p H, -d_q H) = ((p_0+q_1, p_1-q_0), (p_1,-p_0) - (1-mu)(q-a_1)/r_1^3 - mu (q-a_2)/r_2^3) = V_mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:he-smooth, bpI:p0:restricted#restrictedHamiltonian, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2, bpI:p0:restricted#restrictedVectorField, bpI:p7:sec-ham#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:he-smooth | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L61 | differentiability of H^R3_mu on W_mu
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L61 | the Hamiltonian differentiated
EDGE: bpI:p0:primaries#primary1 | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L61 | a_1(mu)
EDGE: bpI:p0:primaries#primary2 | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L61 | a_2(mu)
EDGE: bpI:p0:restricted#restrictedVectorField | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L67-L67 | the display of V_mu in Definition restricted
EDGE: bpI:p7:sec-ham#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-deriv@L61-L67 | r_j and W_mu are fixed in the section data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.restrictedVectorField_eq_hamiltonian (KAM/Iso/RestrictedHam.lean)
LEAN_NOTE: Frozen V_mu = (d_pH, -d_qH) of restrictedHamTotal at every collision-free z; I-3-audit-1.md:34 PASS (row labelled p7:ham-eq).
NOTE: -

NODE: stepI:p7:he-sol
KIND: step
TITLE: Solution predicates
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69
CONTRACT_ID: stepI:p7:he-sol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu in R; J subset R; z:R->R^2 x R^2; W_mu and the restricted Hamiltonian/field are the section data of L48-49
SOURCE_QUANTIFIERS: For every mu in R, J subset R and z:R->R^2 x R^2; equivalence at every t in J
SOURCE_CONCLUSION: the clauses of RSol_mu are z(t) in W_mu and z'(t) = V_mu(z(t)) = X_H(z(t)); the reduction to IsSolIn is the cited N result
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:primaries#CollisionFree, bpI:p0:restricted#IsRestrictedSolutionOn, bpI:p0:restricted#restrictedVectorField, stepI:p7:he-deriv, bpN:p3:newton-reduction, bpI:p7:sec-ham#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69 | first clause of RSol_mu is collision-freeness
EDGE: bpI:p0:restricted#IsRestrictedSolutionOn | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69 | RSol_mu
EDGE: bpI:p0:restricted#restrictedVectorField | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69 | V_mu
EDGE: stepI:p7:he-deriv | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69 | V_mu = X_H
EDGE: bpN:p3:newton-reduction | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69 | reduction to IsSolIn
EDGE: bpI:p7:sec-ham#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:he-sol@L69-L69 | r_j and W_mu are fixed in the section data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.isRestrictedSolutionOn_iff (KAM/Iso/RestrictedHam.lean); KAM.ODE.restricted_reduction (KAM/ODE/NewtonReduction.lean)
LEAN_NOTE: Composite: RSol clauses (z(t) in W_mu, z'=X_H) by isRestrictedSolutionOn_iff (I-3-audit-1.md:35); reduction to IsSolutionIn by restricted_reduction (N3-8-audit-1.md:41, cross-track).
NOTE: -

NODE: bpI:p7:kepler-eq
KIND: proposition
TITLE: Kepler's equation, analytic solution
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L91-L114
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L115-L135
CONTRACT_ID: bpI:p7:kepler-eq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < e_1 < 1; e_2 = (1+e_1)/2, vartheta_* = (1+e_2)/2, y_0 = arcosh(vartheta_*/e_2), delta_K = (1/2)(1-vartheta_*) y_0, delta_E = min{e_2-e_1, (1-vartheta_*) y_0/(2 cosh y_0)}; P(e_1) = {(ell,e) in C^2 : |Im ell| < delta_K, dist(e, [-e_1,e_1]) < delta_E}
SOURCE_QUANTIFIERS: e_1 in (0,1), then the constants e_2, vartheta_*, y_0, delta_K, delta_E, then (ell, e) in P(e_1)
SOURCE_CONCLUSION: P is open, contains {(ell,e) real : |e| <= e_1}, |e| < e_1 + delta_E <= e_2, |Im e| < delta_E; there is a unique holomorphic u : P -> C with |Im u| <= y_0 and u - e sin u = ell; (a) |sin u|,|cos u| <= cosh y_0 = vartheta_*/e_2, |e cos u| <= vartheta_* < 1, |1 - e cos u| >= 1 - vartheta_*; (b) d_ell u = 1/(1 - e cos u), d_e u = sin u/(1 - e cos u), u(ell,0) = ell, u(ell+2pi,e) = u(ell,e) + 2pi, sin u, cos u, (1-e cos u)^-1 holomorphic and 2pi-periodic in ell; (c) u real at real points, exactly one real solution u_R(ell,e) for real ell and e in (-1,1), u_R real-analytic on R x (-1,1), u_R(.,e) an increasing diffeomorphism of R with u_R(0,e) = 0, u_R(2pi,e) = 2pi, u = u_R on real points of every P(e_1)
CONSTANT_SCOPE: e_2, vartheta_*, y_0, delta_K, delta_E depend only on e_1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ke-const, stepI:p7:ke-trig, stepI:p7:ke-contr, stepI:p7:ke-hol, stepI:p7:ke-a, stepI:p7:ke-b, stepI:p7:ke-c
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ke-const | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L116-L116 | proof step Constants
EDGE: stepI:p7:ke-trig | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L119-L119 | proof step Trigonometric bounds
EDGE: stepI:p7:ke-contr | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L121-L121 | proof step Contraction
EDGE: stepI:p7:ke-hol | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L125-L125 | proof step Holomorphy
EDGE: stepI:p7:ke-a | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L129-L129 | proof of (a)
EDGE: stepI:p7:ke-b | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L131-L131 | proof of (b)
EDGE: stepI:p7:ke-c | blueprint-I/parts/p7-delaunay.tex#bpI:p7:kepler-eq@L133-L133 | proof of (c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerEq_tube, keplerTube_real_points, eccAnomC_periodic, eccAnomC_zero_ecc, hasDerivAt_eccAnomC_ell, hasDerivAt_eccAnomC_ecc, isOpen_keplerTube (KAM/Kepler/KeplerTube.lean); eccAnom_eq, analyticOnNhd_eccAnom, strictMono_eccAnom (KAM/Kepler/Equation.lean)
LEAN_NOTE: audit KEP-4 PASS WITH NOTES (complex tube) + KEP-2 PASS (real part c); full real slice by KEP-4 N1 composition
NOTE: Part 7 L113 sourcegap: Chi05 gives no domain; the blueprint supplies the full argument in this node and its steps

NODE: stepI:p7:ke-const
KIND: step
TITLE: Constants
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-const@L116-L117
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-const@L116-L117
CONTRACT_ID: stepI:p7:ke-const
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < e_1 < 1 and the constants of Proposition kepler-eq
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: 0 < e_1 < e_2 < vartheta_* < 1, vartheta_*/e_2 > 1, y_0 > 0, e_2 cosh y_0 = vartheta_*, e_2 sinh y_0 <= vartheta_* y_0, delta_K + e_2 sinh y_0 + delta_E cosh y_0 <= y_0; for (ell,e) in P: |e| < e_2, |Re e| < e_2, |Im e| < delta_E
CONSTANT_SCOPE: constants depend only on e_1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerConstants_pos, tube_bounds (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-4 PASS WITH NOTES; scalar constants/tube helpers (KAM.Kepler.Tube.*); parent keplerEq_tube covers
NOTE: -

NODE: stepI:p7:ke-trig
KIND: step
TITLE: Trigonometric bounds
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-trig@L119-L119
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-trig@L119-L119
CONTRACT_ID: stepI:p7:ke-trig
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u = x + iy in C; e in C
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: |sin u|^2 = sin^2 x + sinh^2 y, |cos u|^2 = cos^2 x + sinh^2 y, both <= cosh^2 y; |Re sin u| <= cosh y, |Im sin u| <= sinh|y|; |Im(e sin u)| <= |Re e| sinh|y| + |Im e| cosh y
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: norm_sin_le, abs_re_sin_le, abs_im_sin_le (KAM/Kepler/EquationComplex.lean)
LEAN_NOTE: audit KEP-3 PASS WITH NOTES; named I ke-trig (namespace KAM.Kepler.EqC)
NOTE: -

NODE: stepI:p7:ke-contr
KIND: step
TITLE: A contraction
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-contr@L121-L123
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-contr@L121-L123
CONTRACT_ID: stepI:p7:ke-contr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: steps ke-const, ke-trig; S = {u : |Im u| <= y_0} closed convex complete; (ell,e) in P; Phi_{ell,e}(u) = ell + e sin u
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: Phi_{ell,e}(S) subset S and Phi is a vartheta_*-contraction of S; hence a unique fixed point u(ell,e) in S, i.e. a unique solution of Kepler's equation in S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ke-const, stepI:p7:ke-trig, K:bp:p1:ext-mvt, K:bp:p1:ext-banach
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ke-const | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-contr@L122-L122 | delta_K + e_2 sinh y_0 + delta_E cosh y_0 <= y_0 and the bounds on e
EDGE: stepI:p7:ke-trig | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-contr@L122-L122 | bounds of Im(e sin u) and ¦cos u¦
EDGE: K:bp:p1:ext-mvt | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-contr@L123-L123 | mean value inequality on the convex S
EDGE: K:bp:p1:ext-banach | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-contr@L123-L123 | Banach fixed point theorem
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: existsUnique_keplerOp (KAM/Kepler/EquationComplex.lean); keplerData_tube (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-3/KEP-4 PASS WITH NOTES; named I ke-contr; instantiated on tube (Tube.keplerData_tube)
NOTE: -

NODE: stepI:p7:ke-hol
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L125-L127
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L125-L127
CONTRACT_ID: stepI:p7:ke-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: steps ke-const, ke-contr, ke-trig; u_0 = ell, u_{m+1} = Phi_{ell,e}(u_m)
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: each u_m is holomorphic on P with values in S; |u_m - u| <= vartheta_*^{m+1}/(1 - vartheta_*) uniformly on P; hence u is holomorphic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ke-contr, stepI:p7:ke-const, stepI:p7:ke-trig, bpI:p7:x-hol, bpI:p7:x-weier
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ke-contr | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L125-L125 | S is Phi-invariant and Phi is a contraction with fixed point u
EDGE: stepI:p7:ke-const | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L126-L126 | delta_K < y_0, e_2 cosh y_0 = vartheta_*
EDGE: stepI:p7:ke-trig | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L126-L126 | ¦sin ell¦ <= cosh y_0 for ¦Im ell¦ < y_0
EDGE: bpI:p7:x-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L125-L125 | u_m holomorphic as compositions
EDGE: bpI:p7:x-weier | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-hol@L127-L127 | uniform limit of holomorphic functions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerSol_analyticOnNhd (KAM/Kepler/EquationComplex.lean); eccAnomC_analyticOnNhd (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-3/KEP-4 PASS WITH NOTES; named I ke-hol (analytic IFT route instead of uniform limit)
NOTE: -

NODE: stepI:p7:ke-a
KIND: step
TITLE: (a)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-a@L129-L129
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-a@L129-L129
CONTRACT_ID: stepI:p7:ke-a
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u in S; steps ke-trig, ke-const
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: |sin u|,|cos u| <= cosh y_0 = vartheta_*/e_2, |e cos u| <= vartheta_* < 1, |1 - e cos u| >= 1 - vartheta_* on P
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ke-contr, stepI:p7:ke-trig, stepI:p7:ke-const
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ke-contr | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-a@L129-L129 | u in S
EDGE: stepI:p7:ke-trig | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-a@L129-L129 | trigonometric bounds
EDGE: stepI:p7:ke-const | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-a@L129-L129 | e_2 cosh y_0 = vartheta_*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerEq_tube, tube_bounds (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-4 PASS WITH NOTES; keplerEq_tube gives all four analytic bounds
NOTE: -

NODE: stepI:p7:ke-b
KIND: step
TITLE: (b)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-b@L131-L131
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-b@L131-L131
CONTRACT_ID: stepI:p7:ke-b
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: part (a); u holomorphic with u - e sin u = ell
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: (1 - e cos u) d_ell u = 1, (1 - e cos u) d_e u = sin u, hence the formulas; u(ell,0) = ell; u(ell + 2pi, e) = u(ell,e) + 2pi by uniqueness in S; sin u, cos u, (1-e cos u)^-1 holomorphic and 2pi-periodic in ell
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ke-hol, stepI:p7:ke-a, stepI:p7:ke-contr
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ke-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-b@L131-L131 | u holomorphic, so the identity can be differentiated
EDGE: stepI:p7:ke-a | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-b@L131-L131 | 1 - e cos u != 0 to divide
EDGE: stepI:p7:ke-contr | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-b@L131-L131 | uniqueness of the solution in S
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerSol_fderiv, keplerSol_shift (KAM/Kepler/EquationComplex.lean); hasDerivAt_eccAnomC_ell, hasDerivAt_eccAnomC_ecc, eccAnomC_periodic, eccAnomC_zero_ecc (KAM/Kepler/KeplerTube.lean)
LEAN_NOTE: audit KEP-3/KEP-4 PASS WITH NOTES; named I ke-b
NOTE: -

NODE: stepI:p7:ke-c
KIND: step
TITLE: (c)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L133-L134
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L133-L134
CONTRACT_ID: stepI:p7:ke-c
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: For the real-line assertion ell in R and e in (-1,1); for comparison with the complex branch 0<e_1<1 and (ell,e) a real point of P(e_1), with constants defined in L94-100
SOURCE_QUANTIFIERS: For every ell in R and e in (-1,1) there exists exactly one real u_R(ell,e); for each e choose e_1 with |e|<e_1<1 to compare the analytic branch; assertions on u_R hold on R x (-1,1)
SOURCE_CONCLUSION: phi(u) = ell + e sin u is a |e|-contraction of R with a unique real fixed point u_R(ell,e); u = u_R at real points of P; u_R real-analytic on R x (-1,1), d_ell u_R > 0, u_R(.,e) an increasing diffeomorphism of R, u_R(0,e) = 0, u_R(2pi,e) = 2pi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ke-contr, stepI:p7:ke-hol, K:bp:p1:holomorphic-analytic, stepI:p7:ke-b, K:bp:p1:ext-banach, K:bp:p1:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ke-contr | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L133-L133 | uniqueness in S gives u = u_R at real points of P
EDGE: stepI:p7:ke-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L134-L134 | u_R is the restriction of a holomorphic function
EDGE: K:bp:p1:holomorphic-analytic | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L134-L134 | holomorphic implies real-analytic
EDGE: stepI:p7:ke-b | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L134-L134 | d_ell u_R = 1/(1 - e cos u_R)
EDGE: K:bp:p1:ext-banach | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L133-L133 | the complete nonempty real line carries the contraction with constant abs(e) < 1
EDGE: K:bp:p1:ext-mvt | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ke-c@L133-L133 | abs(e cos u) <= abs(e) bounds the derivative on the convex real line
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: keplerSol_real (KAM/Kepler/EquationComplex.lean); keplerTube_real_points (KAM/Kepler/KeplerTube.lean); eccAnom_eq, strictMono_eccAnom, analyticOnNhd_eccAnom (KAM/Kepler/Equation.lean)
LEAN_NOTE: audit KEP-3/KEP-4/KEP-2 PASS (WITH NOTES); named I ke-c; real slice KEP-4 N1
NOTE: -

NODE: bpI:p7:elements
KIND: definition
TITLE: Kepler region and elements
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:elements@L144-L156
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:elements
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (definition; typing data (q,p) in R^2 x R^2, q != 0)
SOURCE_QUANTIFIERS: (q,p)
SOURCE_CONCLUSION: defines E(q,p) = (1/2)|p|_2^2 - 1/|q|_2, the open region C = {q != 0, E < 0, Gamma > 0, Gamma^2 < -1/(2E)} and on C the elements L = 1/sqrt(-2E), G = Gamma, a = L^2, e = sqrt(1 + 2E Gamma^2), with L > G > 0, e in (0,1), E = -1/(2a), Gamma^2 = a(1 - e^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: kE, keplerRegion, elemL, elemA, elemEcc, isOpen_keplerRegion (KAM/Kepler/Energy.lean); eccOf_mem_Ioo, delaunay_elements (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-1 (addendum PASS) + KEP-5 (addendum PASS)
NOTE: notation of Part 7 L20-27 (Gamma, E, C_0, e(L,G)) is used here

NODE: bpI:p7:orbit-maps
KIND: definition
TITLE: Orbit maps
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps@L158-L168
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:orbit-maps
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: ell, g, L, e, k; u = u(ell,e) of Proposition kepler-eq
SOURCE_QUANTIFIERS: (ell, g, L, e, k), then (ell, g, L, G) in D_R
SOURCE_CONCLUSION: defines Q_el(ell,g,L,e,k) (X = L^2(c-e), Y = L^2 k s, P_X = -s/(L D), P_Y = k c/(L D), q = R(g)(X,Y), p = R(g)(P_X,P_Y), D = 1 - e c) and the Delaunay orbit map Q(ell,g,L,G) = Q_el(ell,g,L,e(L,G),G/L) with e(L,G) = sqrt(1 - G^2/L^2); on D_R = R^2 x C_0 all quantities are real and D >= 1 - e > 0 (u = u_R)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:kepler-eq
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps@L159-L159 | u = u(ell,e), and u = u_R on the real domain
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: eccOf, deDom (KAM/Kepler/Energy.lean); orbitFrame, orbitMapR, delaunay, orbitMapR_radius_bounds (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-1 (addendum PASS) + KEP-5 (addendum PASS); real definitions; holomorphic extension is bpI:p7:orbit-maps-e
NOTE: -

NODE: bpI:p7:orbit-maps-e
KIND: proposition
TITLE: Orbit maps near $e=0$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps-e@L170-L174
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps-e@L175-L179
CONTRACT_ID: bpI:p7:orbit-maps-e
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < e_1 < 1; P = P(e_1) as in Proposition kepler-eq
SOURCE_QUANTIFIERS: e_1, then (ell,g,L,e,k)
SOURCE_CONCLUSION: Q_el is holomorphic on {(ell,g,L,e,k) : (ell,e) in P, g in C, L in C minus {0}, k in C}, 2pi-periodic in ell and g, real on real points with |e| <= e_1; holomorphic on a neighbourhood of e = 0 (P contains the disc |e| < delta_E), e.g. with k = sqrt(1 - e^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:kepler-eq, bpI:p7:orbit-maps, stepI:p7:om-hol, stepI:p7:om-per
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps-e@L171-L171 | P(e_1) and the solution u
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps-e@L171-L171 | the map Q_el
EDGE: stepI:p7:om-hol | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps-e@L176-L176 | proof step Holomorphy
EDGE: stepI:p7:om-per | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-maps-e@L178-L178 | proof step Periodicity, reality
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: orbitMapC_differentiableOn, orbitMapC_periodic, orbitMapC_real, orbitMapC_ofReal, orbitDomC_mem_ofReal (KAM/Kepler/OrbitComplex.lean); KAM.Iso.orbitMapC_k_holomorphic (KAM/Iso/TransferStepNodes.lean)
LEAN_NOTE: holomorphy/periodicity/reality clauses KEP-9 PASS WITH NOTES; k = sqrt(1-e^2) clause GAP-I7b-audit-1.md:42 PASS (orbitMapC_k_holomorphic); re-closed after survey 2.5 over-claim revert
NOTE: -

NODE: stepI:p7:om-hol
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-hol@L176-L176
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-hol@L176-L176
CONTRACT_ID: stepI:p7:om-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Proposition kepler-eq (a); (ell,e) in P
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: u, c, s holomorphic, |D| >= 1 - vartheta_* > 0; Q_el holomorphic as polynomial in (c,s,e,k,L,1/L,1/D) and entire R(g); k = sqrt(1 - e^2) holomorphic since |e| < e_2 < 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:kepler-eq, bpI:p7:orbit-maps, bpI:p7:x-hol
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-hol@L176-L176 | holomorphy of u and the bound ¦1 - e cos u¦ >= 1 - vartheta_*
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-hol@L176-L176 | formulas for X, Y, P_X, P_Y
EDGE: bpI:p7:x-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-hol@L176-L176 | holomorphy of compositions, R(g) entire, principal square root
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: KAM.Kepler.orbitStep_om_hol (KAM/Iso/DelaunayStepNodes.lean)
LEAN_NOTE: GAP-I7a (audit PASS WITH NOTES)
NOTE: -

NODE: stepI:p7:om-per
KIND: step
TITLE: Periodicity, reality
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-per@L178-L178
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-per@L178-L178
CONTRACT_ID: stepI:p7:om-per
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Proposition kepler-eq (b),(c)
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: Q_el is 2pi-periodic in ell and g and real at real points with |e| <= e_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:kepler-eq, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-per@L178-L178 | (b) periodicity of u, (c) reality of u
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:om-per@L178-L178 | R is 2pi-periodic and the formulas are real at real arguments
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: KAM.Kepler.orbitMapC_periodic, KAM.Kepler.orbitMapC_real (KAM/Kepler/OrbitComplex.lean)
LEAN_NOTE: Both 2pi shifts in ell and g on orbitDomC; reality at real points with |e|<=e1; KEP-9-audit-1.md:39,43 PASS (rows labelled orbit-maps-e).
NOTE: -

NODE: bpI:p7:orbit-identities
KIND: proposition
TITLE: Identities for the orbit maps
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L181-L190
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L191-L203
CONTRACT_ID: bpI:p7:orbit-identities
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R, e = e(L,G), (q,p) = Q(ell,g,L,G), r = |q|_2, u, c, s, D as in Definition orbit-maps
SOURCE_QUANTIFIERS: (ell,g,L,G) in D_R
SOURCE_CONCLUSION: (a) r = L^2 D = L^2(1 - e cos u), L^2(1-e) <= r <= L^2(1+e), |p|_2^2 = (1 + e cos u)/(L^2 D); (b) Gamma(q,p) = G, q.p = L e sin u; (c) E(q,p) = -1/(2L^2), Q(D_R) subset C, elements of Q(ell,g,L,G) are L, G, a = L^2, e; (d) (L e sin u)^2 = -G^2 + 2r - r^2/L^2, L^2 e cos u = L^2 - r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps, bpI:p7:elements, stepI:p7:oi-r, stepI:p7:oi-gam, stepI:p7:oi-en, stepI:p7:oi-d
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L182-L182 | Q and u, c, s, D
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L186-L186 | elements of Definition elements and the region C
EDGE: stepI:p7:oi-r | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L194-L194 | proof of (a)
EDGE: stepI:p7:oi-gam | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L197-L197 | proof of (b)
EDGE: stepI:p7:oi-en | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L200-L200 | proof of (c)
EDGE: stepI:p7:oi-d | blueprint-I/parts/p7-delaunay.tex#bpI:p7:orbit-identities@L202-L202 | proof of (d)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_radius, orbitMapR_radius_bounds, orbitMapR_speed_sq, orbitMapR_cross, orbitMapR_dot, orbitMapR_energy, orbitMapR_radial, delaunay_mem_region, delaunay_elements (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-5 PASS (addendum closes H01); rows (a)-(d)
NOTE: -

NODE: stepI:p7:oi-r
KIND: step
TITLE: Radius
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-r@L194-L195
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-r@L194-L195
CONTRACT_ID: stepI:p7:oi-r
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G = L k, k^2 = 1 - e^2, c^2 + s^2 = 1 (real case); R(g) orthogonal
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: r^2 = L^4 D^2, r = L^2 D > 0, |p|_2^2 = (1 + e c)/(L^2 D)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-r@L194-L194 | X, Y, P_X, P_Y, D >= 1 - e > 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_radius, orbitMapR_radius_bounds, orbitMapR_speed_sq (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-5 PASS; row (a)
NOTE: -

NODE: stepI:p7:oi-gam
KIND: step
TITLE: Angular momentum, radial momentum
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-gam@L197-L198
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-gam@L197-L198
CONTRACT_ID: stepI:p7:oi-gam
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R=R^2 x C_0 with 0<G<L; e=e(L,G), k=G/L, (q,p)=Q(ell,g,L,G), u,c,s,D as in the orbit-map definitions
SOURCE_QUANTIFIERS: For every (ell,g,L,G) in D_R, with the orbit quantities fixed as in the enclosing proposition
SOURCE_CONCLUSION: Gamma = X P_Y - Y P_X = L k = G and q.p = X P_X + Y P_Y = L e s
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-gam@L197-L197 | X, Y, P_X, P_Y
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_cross, orbitMapR_dot (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-5 PASS; row (b)
NOTE: -

NODE: stepI:p7:oi-en
KIND: step
TITLE: Energy
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-en@L200-L200
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-en@L200-L200
CONTRACT_ID: stepI:p7:oi-en
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R=R^2 x C_0 with 0<G<L; e=e(L,G), k=G/L, (q,p)=Q(ell,g,L,G), u,c,s,D as in the orbit-map definitions
SOURCE_QUANTIFIERS: For every (ell,g,L,G) in D_R, with the orbit quantities fixed as in the enclosing proposition
SOURCE_CONCLUSION: E = (1/2)|p|^2 - 1/r = -1/(2L^2); Q(ell,g,L,G) lies in C with elements L, G, L^2, e
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:oi-r, bpI:p7:elements, bpI:p7:orbit-maps, stepI:p7:oi-gam
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:oi-r | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-en@L200-L200 | r and ¦p¦^2
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-en@L200-L200 | membership in C (G > 0, G^2 < L^2 = -1/(2E)) and the elements
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-en@L200-L200 | p and q of the orbit map
EDGE: stepI:p7:oi-gam | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-en@L200-L200 | Gamma(q,p) = G is needed for the strict angular-momentum inequality and recovery of the elements
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_energy, delaunay_mem_region, delaunay_elements (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-5 PASS; row (c)
NOTE: -

NODE: stepI:p7:oi-d
KIND: step
TITLE: (d)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-d@L202-L202
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-d@L202-L202
CONTRACT_ID: stepI:p7:oi-d
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R=R^2 x C_0 with 0<G<L; e=e(L,G), k=G/L, (q,p)=Q(ell,g,L,G), u,c,s,D as in the orbit-map definitions
SOURCE_QUANTIFIERS: For every (ell,g,L,G) in D_R, with the orbit quantities fixed as in the enclosing proposition
SOURCE_CONCLUSION: L^2 e c = L^2 - r and (L e s)^2 = -G^2 + 2r - r^2/L^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:oi-r, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:oi-r | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-d@L202-L202 | r = L^2 (1 - e c)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:oi-d@L202-L202 | the calculation uses the Delaunay orbit map or its element formulas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_radial (KAM/Kepler/Orbit.lean)
LEAN_NOTE: audit KEP-5 PASS; row (d)
NOTE: -

NODE: bpI:p7:symplectic
KIND: proposition
TITLE: The Delaunay map is symplectic
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L205-L217
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L218-L240
CONTRACT_ID: bpI:p7:symplectic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R (open in R^4); F = 2 L e sin u; for the consequence, U subset R^4 open (target, coordinates (q,p)), H: U -> R of class C^1, W := {w in D_R : Q(w) in U} (open in R^4 since Q is continuous on the open set D_R)
SOURCE_QUANTIFIERS: w in D_R; U open; H: U -> R, C^1; then w in W
SOURCE_CONCLUSION: Q^*(sum p_i dq_i) = L dell + G dg + dF; D Q^T J D Q = J = D Q J D Q^T; Q^*(sum dq_i wedge dp_i) = dell wedge dL + dg wedge dG; D Q(w) invertible; on W: D Q X_{H o Q} = X_H o Q, i.e. w' = X_{H o Q}(w) iff d/dt Q(w) = X_H(Q(w)) for C^1 curves w in W
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps, stepI:p7:sy-g, stepI:p7:sy-coord, stepI:p7:sy-compare, stepI:p7:sy-ext, stepI:p7:sy-field
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L206-L206 | the map Q on D_R
EDGE: stepI:p7:sy-g | blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L219-L219 | proof step
EDGE: stepI:p7:sy-coord | blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L222-L222 | proof step
EDGE: stepI:p7:sy-compare | blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L234-L234 | proof step
EDGE: stepI:p7:sy-ext | blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L236-L236 | proof step
EDGE: stepI:p7:sy-field | blueprint-I/parts/p7-delaunay.tex#bpI:p7:symplectic@L239-L239 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sonnet-amend-I-p1
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: delaunay_symplectic, delaunay_liouville, delaunay_hasFDerivAt, delaunay_fderiv_equiv, delaunay_hamiltonianVectorField (KAM/Kepler/DelaunaySymplectic.lean)
LEAN_NOTE: audit KEP-6 PASS WITH NOTES; curve iff of Hamiltonian transport not a separate decl (follows from invertibility); steps sy-* left
NOTE: -

NODE: stepI:p7:sy-g
KIND: step
TITLE: Reduction of the angle $g$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-g@L219-L220
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-g@L219-L220
CONTRACT_ID: stepI:p7:sy-g
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q = R(g) xi, xi = (X,Y), pi = (P_X,P_Y), p = R(g) pi
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: p.dq = pi.dxi + G dg
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps, bpI:p7:orbit-identities
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-g@L219-L219 | xi, pi and the rotation form of q, p
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-g@L220-L220 | (b): Gamma = X P_Y - Y P_X = G
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27, track-I gap survey GAP-PLAN-I item 3): the Lean proves symplecticity column-wise and never forms pi dxi
NOTE: -

NODE: stepI:p7:sy-coord
KIND: step
TITLE: Coordinates $(u,L,e)$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-coord@L222-L232
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-coord@L222-L232
CONTRACT_ID: stepI:p7:sy-coord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: on D_R use (u, L, e) in place of (ell, L, G); X = L^2(c-e), Y = L^2 k s
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: pi.dxi = L(1 + e c) du + 2 e s dL + L s de
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps, bpI:p7:kepler-eq
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-coord@L222-L222 | X, Y, P_X, P_Y
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-coord@L222-L222 | d_ell u > 0 and u = u_R: (ell,L,G) -> (u,L,e) is a diffeomorphism
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27, track-I gap survey GAP-PLAN-I item 3): the Lean proves symplecticity column-wise and never forms pi dxi
NOTE: -

NODE: stepI:p7:sy-compare
KIND: step
TITLE: Comparison with $L\,d\ell$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-compare@L234-L234
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-compare@L234-L234
CONTRACT_ID: stepI:p7:sy-compare
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R=R^2 x C_0 with 0<G<L; e=e(L,G), k=G/L, (q,p)=Q(ell,g,L,G), u,c,s,D as in the orbit-map definitions; the one-form calculation is on D_R, F=2Le sin u
SOURCE_QUANTIFIERS: For every (ell,g,L,G) in D_R, with the orbit quantities fixed as in the enclosing proposition
SOURCE_CONCLUSION: pi.dxi - L dell = dF with F = 2 L e s; Q^*(sum p_i dq_i) = L dell + G dg + dF
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:sy-g, stepI:p7:sy-coord, bpI:p7:kepler-eq, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:sy-g | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-compare@L234-L234 | p.dq = pi.dxi + G dg
EDGE: stepI:p7:sy-coord | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-compare@L234-L234 | pi.dxi
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-compare@L234-L234 | ell = u - e sin u relates dell to du, de
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-compare@L234-L234 | the calculation uses the Delaunay orbit map or its element formulas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27, track-I gap survey GAP-PLAN-I item 3): the Lean proves symplecticity column-wise and never forms pi dxi
NOTE: -

NODE: stepI:p7:sy-ext
KIND: step
TITLE: Exterior derivative
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-ext@L236-L237
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-ext@L236-L237
CONTRACT_ID: stepI:p7:sy-ext
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q is the Delaunay map on D_R as fixed in the symplectic proposition; F=2Le sin u; no one-form identity or invertibility is assumed as a source premise
SOURCE_QUANTIFIERS: For every (ell,g,L,G) in D_R, with the orbit quantities fixed as in the enclosing proposition
SOURCE_CONCLUSION: Q^*(sum dp_i wedge dq_i) = dL wedge dell + dG wedge dg, i.e. D Q^T J D Q = J, det D Q != 0, D Q J D Q^T = J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:sy-compare, bpI:p7:x-forms, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:sy-compare | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-ext@L236-L236 | Q^*(sum p_i dq_i) = L dell + G dg + dF
EDGE: bpI:p7:x-forms | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-ext@L236-L236 | d^2 = 0, pull-back commutes with d, form determined by values on vectors
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-ext@L236-L237 | the calculation uses the Delaunay orbit map or its element formulas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: KAM.Kepler.delaunayStep_sy_ext (KAM/Iso/DelaunayStepNodes.lean)
LEAN_NOTE: GAP-I7a; form statement under cv-sympl precedent, ruling 05:10
NOTE: -

NODE: stepI:p7:sy-field
KIND: step
TITLE: Hamiltonian fields
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-field@L239-L239
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-field@L239-L239
CONTRACT_ID: stepI:p7:sy-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q is the Delaunay map on D_R; U subset R^4 open, H: U -> R of class C^1; W = {w in D_R : Q(w) in U} open; Q(w) lies in the open domain U of H for every w in W, so the chain rule applies at every point of W
SOURCE_QUANTIFIERS: for every open U and C^1 H: U -> R, every w in W; then for every C^1 curve w in W
SOURCE_CONCLUSION: on W: D Q X_{H o Q} = X_H o Q; for C^1 curves w in W: w' = X_{H o Q}(w) iff d/dt Q(w) = X_H(Q(w))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:sy-ext, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:sy-ext | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-field@L239-L239 | D Q J D Q^T = J
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sy-field@L239-L239 | the calculation uses the Delaunay orbit map or its element formulas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-amend
REVIEWER: sol-delta2-I-amend
LEAN_STATUS: PROVED
LEAN_REF: KAM.Kepler.delaunayStep_sy_field (KAM/Iso/DelaunayStepNodes.lean)
LEAN_NOTE: GAP-I7a (audit PASS WITH NOTES)
NOTE: -

NODE: bpI:p7:chart
KIND: theorem
TITLE: Delaunay chart
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L242-L246
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L247-L261
CONTRACT_ID: bpI:p7:chart
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none beyond the definitions of Q, C_0, C, D_R
SOURCE_QUANTIFIERS: Q on D_R
SOURCE_CONCLUSION: Q is 2pi-periodic in ell and g and induces a bijection (R/2piZ)^2 x C_0 -> C; Q : D_R -> C is a surjective real-analytic local diffeomorphism; the induced map on the quotient is a real-analytic diffeomorphism onto the open set C, symplectic by Proposition symplectic; E o Q = -1/(2L^2), Gamma o Q = G; the loci e = 0 and e = 1 are excluded from C_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps, bpI:p7:elements, bpI:p7:symplectic, bpI:p7:orbit-identities, stepI:p7:ch-reg, stepI:p7:ch-inj, stepI:p7:ch-surj1, stepI:p7:ch-surj2, stepI:p7:ch-surj3, stepI:p7:ch-diffeo
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L243-L243 | the map Q and D_R
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L243-L243 | the region C and the elements
EDGE: bpI:p7:symplectic | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L243-L243 | symplectic quotient map
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L244-L244 | E o Q and Gamma o Q
EDGE: stepI:p7:ch-reg | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L248-L248 | proof step
EDGE: stepI:p7:ch-inj | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L250-L250 | proof step
EDGE: stepI:p7:ch-surj1 | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L252-L252 | proof step
EDGE: stepI:p7:ch-surj2 | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L256-L256 | proof step
EDGE: stepI:p7:ch-surj3 | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L258-L258 | proof step
EDGE: stepI:p7:ch-diffeo | blueprint-I/parts/p7-delaunay.tex#bpI:p7:chart@L260-L260 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: orbitMapR_periodic, delaunay_mem_region, delaunay_elements (KAM/Kepler/Orbit.lean); delaunay_periodic, delaunay_eq_iff, keplerRegion_subset_image, delaunay_localDiffeo (KAM/Kepler/DelaunayChart.lean); delaunay_symplectic (KAM/Kepler/DelaunaySymplectic.lean)
LEAN_NOTE: audit KEP-5 PASS + KEP-7 PASS WITH NOTES + KEP-6 PASS WITH NOTES; periodic, bijection, surjective local diffeo, symplectic, E and Gamma along Q
NOTE: -

NODE: stepI:p7:ch-reg
KIND: step
TITLE: Regularity
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248
CONTRACT_ID: stepI:p7:ch-reg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ell,g,L,G) in D_R, so 0 < G < L and 1-G^2/L^2 > 0; e(L,G) = sqrt(1-G^2/L^2)
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: Q is real-analytic on D_R; D Q invertible; Q(D_R) subset C
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:kepler-eq, bpI:p7:orbit-maps, bpI:p7:symplectic, bpI:p7:orbit-identities, bpI:p7:x-hol, K:bp:p1:holomorphic-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248 | (c): u_R real-analytic
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248 | Q built from u_R, e(L,G), R(g)
EDGE: bpI:p7:symplectic | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248 | invertibility of D Q
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248 | (c): Q(D_R) subset C
EDGE: bpI:p7:x-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248 | the positive square-root formula for e extends holomorphically locally on C_0
EDGE: K:bp:p1:holomorphic-analytic | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-reg@L248-L248 | restrict the local holomorphic square-root formula to real actions to justify real analyticity of e
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: delaunay_localDiffeo (KAM/Kepler/DelaunayChart.lean)
LEAN_NOTE: audit KEP-7 PASS WITH NOTES; named step (ch-reg)
NOTE: -

NODE: stepI:p7:ch-inj
KIND: step
TITLE: Injectivity modulo $2\pi$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-inj@L250-L250
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-inj@L250-L250
CONTRACT_ID: stepI:p7:ch-inj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q(ell,g,L,G) = (q,p)
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: L, G, e, r are determined by (q,p); cos u and sin u are determined, so u and ell modulo 2pi; (X,Y) is determined and nonzero so g modulo 2pi: injectivity modulo 2pi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-identities, bpI:p7:elements, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-inj@L250-L250 | L = 1/sqrt(-2E), G = Gamma, cos u = (1 - r/L^2)/e, sin u = q.p/(L e)
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-inj@L250-L250 | elements of (q,p)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-inj@L250-L250 | X, Y and q = R(g)(X,Y)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: delaunay_eq_iff (KAM/Kepler/DelaunayChart.lean)
LEAN_NOTE: audit KEP-7 PASS WITH NOTES; named step (ch-inj)
NOTE: -

NODE: stepI:p7:ch-surj1
KIND: step
TITLE: Surjectivity: the elements
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj1@L252-L255
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj1@L252-L255
CONTRACT_ID: stepI:p7:ch-surj1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (q,p) in C
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: elements L, G, e with (L,G) in C_0, e = e(L,G); (q.p)^2 = 2r - r^2/L^2 - G^2 (*)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:elements
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj1@L252-L252 | definition of L, G, e on C
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerRegion_subset_image (KAM/Kepler/DelaunayChart.lean)
LEAN_NOTE: audit KEP-7 PASS WITH NOTES; named step (ch-surj1..3)
NOTE: -

NODE: stepI:p7:ch-surj2
KIND: step
TITLE: Surjectivity: the anomaly
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj2@L256-L256
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj2@L256-L256
CONTRACT_ID: stepI:p7:ch-surj2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step ch-surj1
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: c = (1 - r/L^2)/e, s = q.p/(L e) satisfy c^2 + s^2 = 1; there are u, ell = u - e sin u, g with Q-coordinates (X,Y) and R(g)(X,Y) = q
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:ch-surj1, bpI:p7:kepler-eq, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:ch-surj1 | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj2@L256-L256 | relation (*)
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj2@L256-L256 | (c): u = u_R(ell,e) by uniqueness
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj2@L256-L256 | X, Y, D
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerRegion_subset_image (KAM/Kepler/DelaunayChart.lean)
LEAN_NOTE: audit KEP-7 PASS WITH NOTES; named step (ch-surj1..3)
NOTE: -

NODE: stepI:p7:ch-surj3
KIND: step
TITLE: Surjectivity: the momentum
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj3@L258-L258
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj3@L258-L258
CONTRACT_ID: stepI:p7:ch-surj3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: steps ch-surj2; (q,p') = Q(ell,g,L,G)
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: p' = p, so Q(ell,g,L,G) = (q,p): surjectivity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-identities, stepI:p7:ch-surj2, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj3@L258-L258 | (b),(c): E, Gamma and q.p of Q
EDGE: stepI:p7:ch-surj2 | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj3@L258-L258 | the chosen (ell,g,L,G)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-surj3@L258-L258 | Q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: keplerRegion_subset_image (KAM/Kepler/DelaunayChart.lean)
LEAN_NOTE: audit KEP-7 PASS WITH NOTES; named step (ch-surj1..3)
NOTE: -

NODE: stepI:p7:ch-diffeo
KIND: step
TITLE: Quotient diffeomorphism
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260
CONTRACT_ID: stepI:p7:ch-diffeo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q is the Delaunay map D_R -> C defined from the orbit formulas; no regularity, injectivity, surjectivity or periodicity conclusion is an added premise
SOURCE_QUANTIFIERS: On D_R, for all ell,g,L,G and all integer translates in ell,g; the induced map from (R/(2 pi Z))^2 x C_0 to C is the same quotient map as in the chart theorem
SOURCE_CONCLUSION: Q is 2pi-periodic in ell, g; the quotient map is a bijective local diffeomorphism, hence a real-analytic diffeomorphism onto C
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:kepler-eq, stepI:p7:ch-reg, stepI:p7:ch-inj, stepI:p7:ch-surj3, bpI:p7:x-ift, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260 | (b): periodicity of u
EDGE: stepI:p7:ch-reg | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260 | local diffeomorphism
EDGE: stepI:p7:ch-inj | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260 | injectivity modulo 2pi
EDGE: stepI:p7:ch-surj3 | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260 | surjectivity
EDGE: bpI:p7:x-ift | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260 | bijective local real-analytic diffeomorphism is a diffeomorphism
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:ch-diffeo@L260-L260 | the calculation uses the Delaunay orbit map or its element formulas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: delaunay_localDiffeo, delaunay_periodic (KAM/Kepler/DelaunayChart.lean)
LEAN_NOTE: audit KEP-7 PASS WITH NOTES; named step (ch-reg, ch-diffeo)
NOTE: -

NODE: bpI:p7:sec-ham#data
KIND: definition
TITLE: Data of section Hamilton's equations: W_mu and r_j
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham@L48-L49
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:sec-ham#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu in R; Definitions primaries and restricted
SOURCE_QUANTIFIERS: mu in R
SOURCE_CONCLUSION: defines W_mu = {z = (q,p) : CollisionFree mu z} = {q != a_1(mu), q != a_2(mu)}, open, and r_j = rad(q - a_j(mu)); H^R3_mu and V_mu are given on W_mu by the formulas of Definition restricted
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:primaries#CollisionFree, bpI:p0:primaries#radius, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2, bpI:p0:restricted#restrictedHamiltonian, bpI:p0:restricted#restrictedVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham#data@L48-L48 | W_mu is the collision-free set
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham#data@L48-L48 | r_j = rad(q - a_j(mu))
EDGE: bpI:p0:primaries#primary1 | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham#data@L48-L48 | a_1(mu)
EDGE: bpI:p0:primaries#primary2 | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham#data@L48-L48 | a_2(mu)
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham#data@L49-L49 | H^R3_mu on W_mu
EDGE: bpI:p0:restricted#restrictedVectorField | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-ham#data@L49-L49 | V_mu on W_mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p67a
REVIEWER: sol-review-I-p67
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: data definition not named in any audited table
NOTE: section data node (SPEC): openness of W_mu is consumed by the ODE layer

NODE: bpI:p7:near-circular
KIND: lemma
TITLE: The preimage of the near-circular region
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:near-circular@L263-L272
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:near-circular@L273-L279
CONTRACT_ID: bpI:p7:near-circular
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a_-, a_+, e_-, e_+ in R; N = N(a_-,a_+,e_-,e_+) of Definition nearcircular
SOURCE_QUANTIFIERS: a_-, a_+, e_-, e_+
SOURCE_CONCLUSION: N = {(q,p) in C : a_- < a(q,p) < a_+, e_- < e(q,p) < e_+} = Q({(ell,g,L,G) in D_R : a_- < L^2 < a_+, e_- < e(L,G) < e_+}); the witnesses r, a, e of NearCircular are |q|_2, a(q,p), e(q,p) and unique; N is open, nonempty iff there is (L,G) in C_0 with a_- < L^2 < a_+, e_- < e(L,G) < e_+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:nearcircular#NearCircular, bpI:p7:elements, bpI:p7:orbit-maps, stepI:p7:nc-sub, stepI:p7:nc-sup, stepI:p7:nc-image
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:nearcircular#NearCircular | blueprint-I/parts/p7-delaunay.tex#bpI:p7:near-circular@L264-L264 | the frozen set N
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#bpI:p7:near-circular@L266-L266 | C, a(q,p), e(q,p)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:near-circular@L267-L267 | Q and D_R
EDGE: stepI:p7:nc-sub | blueprint-I/parts/p7-delaunay.tex#bpI:p7:near-circular@L274-L274 | proof step
EDGE: stepI:p7:nc-sup | blueprint-I/parts/p7-delaunay.tex#bpI:p7:near-circular@L276-L276 | proof step
EDGE: stepI:p7:nc-image | blueprint-I/parts/p7-delaunay.tex#bpI:p7:near-circular@L278-L278 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: NearCircularWitness, nearCircular_witness_unique, nearCircular_eq, nearCircular_eq_image, isOpen_nearCircular, nearCircular_nonempty_iff (KAM/Iso/NearCircular.lean)
LEAN_NOTE: audit I-4 PASS WITH NOTES (infrastructure; does not seal I-R3BP)
NOTE: -

NODE: stepI:p7:nc-sub
KIND: step
TITLE: $\subseteq$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-sub@L274-L274
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-sub@L274-L274
CONTRACT_ID: stepI:p7:nc-sub
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (q,p) in N with witnesses r, a, e
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: q != 0, r = |q|_2, a = -1/(2E) forced, Gamma > 0, Gamma^2 < -1/(2E), so (q,p) in C with a = a(q,p), e = e(q,p), and the bounds hold
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:nearcircular#NearCircular, bpI:p7:elements
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:nearcircular#NearCircular | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-sub@L274-L274 | defining equations E = -1/(2a), Gamma^2 = a(1-e^2), 0 < ... bounds
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-sub@L274-L274 | C, a(q,p), e(q,p)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: nearCircular_eq, NearCircularWitness (KAM/Iso/NearCircular.lean)
LEAN_NOTE: audit I-4 PASS WITH NOTES; both inclusions of nearCircular_eq
NOTE: -

NODE: stepI:p7:nc-sup
KIND: step
TITLE: $\supseteq$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-sup@L276-L276
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-sup@L276-L276
CONTRACT_ID: stepI:p7:nc-sup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (q,p) in C with a_- < a < a_+, e_- < e < e_+
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: witnesses r = |q|_2, a = a(q,p), e = e(q,p) satisfy the equations of NearCircular, so (q,p) in N
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:elements, bpI:p0:nearcircular#NearCircular
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-sup@L276-L276 | E = -1/(2a), Gamma^2 = a(1 - e^2) are the definitions
EDGE: bpI:p0:nearcircular#NearCircular | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-sup@L276-L276 | equations to be verified
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: nearCircular_eq, NearCircularWitness (KAM/Iso/NearCircular.lean)
LEAN_NOTE: audit I-4 PASS WITH NOTES; both inclusions of nearCircular_eq
NOTE: -

NODE: stepI:p7:nc-image
KIND: step
TITLE: Image of the chart
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-image@L278-L278
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-image@L278-L278
CONTRACT_ID: stepI:p7:nc-image
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: steps nc-sub, nc-sup; Theorem chart; Proposition orbit-identities (c)
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: the elements of Q(ell,g,L,G) are (L,G,L^2,e(L,G)); N is the Q-image of the stated set; N is open since a, e are continuous on the open set C
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:chart, bpI:p7:orbit-identities, bpI:p7:orbit-maps, stepI:p7:nc-sub, stepI:p7:nc-sup, bpI:p7:elements
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:chart | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-image@L278-L278 | Q maps onto C
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-image@L278-L278 | (c): elements of Q(ell,g,L,G)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-image@L278-L278 | Q
EDGE: stepI:p7:nc-sub | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-image@L278-L278 | first description of N
EDGE: stepI:p7:nc-sup | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-image@L278-L278 | first description of N
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nc-image@L278-L278 | a(.), e(.) continuous on the open set C
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: nearCircular_eq_image, isOpen_nearCircular (KAM/Iso/NearCircular.lean)
LEAN_NOTE: audit I-4 PASS WITH NOTES
NOTE: -

NODE: bpI:p7:h0
KIND: lemma
TITLE: Unperturbed Hamiltonian in Delaunay variables
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:h0@L281-L285
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:h0@L286-L288
CONTRACT_ID: bpI:p7:h0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H^K(q,p) = E(q,p) - Gamma(q,p) for q != 0
SOURCE_QUANTIFIERS: (ell,g,L,G) in D_R; collision-free z at mu = 0
SOURCE_CONCLUSION: H^K o Q(ell,g,L,G) = -1/(2L^2) - G on D_R; H^R3_0(z) = H^K(z) for collision-free z
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-maps, bpI:p0:restricted#restrictedHamiltonian, stepI:p7:h0-formula, bpI:p7:elements
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:h0@L282-L282 | Q on D_R
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#bpI:p7:h0@L283-L283 | H^R3_0
EDGE: stepI:p7:h0-formula | blueprint-I/parts/p7-delaunay.tex#bpI:p7:h0@L287-L287 | proof step
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#bpI:p7:h0@L282-L283 | H^K is defined as E(q,p) - Gamma(q,p)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-review-I-p67
REVIEWER: sol-delta-I-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Kepler.delaunay_hamiltonian (KAM/Kepler/Orbit.lean); KAM.Iso.restrictedHamTotal_zero, KAM.Iso.restrictedHamiltonian_eq (KAM/Iso/RestrictedHam.lean)
LEAN_NOTE: First clause: delaunay_hamiltonian (kE - planeCross o Q = -1/(2L^2) - G on deDom; KEP-5-audit-1.md:58). Second clause: restrictedHamTotal_zero + restrictedHamiltonian_eq (rfl) (I-3-audit-1.md:36).
NOTE: -

NODE: stepI:p7:h0-formula
KIND: step
TITLE: Formula
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:h0-formula@L287-L287
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:h0-formula@L287-L287
CONTRACT_ID: stepI:p7:h0-formula
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H^K is defined on q!=0 by E(q,p)-Gamma(q,p); for the first claim (ell,g,L,G) in D_R; for the second z is collision-free at mu=0
SOURCE_QUANTIFIERS: For every (ell,g,L,G) in D_R for the composition identity; separately for every z collision-free at mu=0
SOURCE_CONCLUSION: H^K = E - Gamma, equal to -1/(2L^2) - G along Q; at mu = 0 H^R3_0 has (1-0)/r_1 = 1/|q| and 0/r_2 = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-identities, bpI:p0:restricted#restrictedHamiltonian, bpI:p7:elements, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:h0-formula@L287-L287 | (b),(c): Gamma = G, E = -1/(2L^2)
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#stepI:p7:h0-formula@L287-L287 | H^R3_0
EDGE: bpI:p7:elements | blueprint-I/parts/p7-delaunay.tex#stepI:p7:h0-formula@L287-L287 | H^K is defined as E(q,p) - Gamma(q,p)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:h0-formula@L287-L287 | Q,D_R and its action parameters occur directly in the formula
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: KAM.Kepler.delaunay_hamiltonian (KAM/Kepler/Orbit.lean); KAM.Iso.restrictedHamTotal_zero, KAM.Iso.restrictedHamiltonian_eq (KAM/Iso/RestrictedHam.lean)
LEAN_NOTE: Rule 05:10, conditional on parent bpI:p7:h0 being PROVED in this same map: KEP-5-audit-1.md:58, I-3-audit-1.md:36.
NOTE: -

NODE: bpI:p7:complex-domain
KIND: lemma
TITLE: Eccentricity on a complex neighbourhood
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:complex-domain@L339-L345
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:complex-domain@L346-L351
CONTRACT_ID: bpI:p7:complex-domain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K as in section data; delta_E of Proposition kepler-eq; tau := min{e_-^2/2, e_- delta_E}
SOURCE_QUANTIFIERS: K first, then delta_1 depending only on K, then (L,G) in K_{delta_1} with nearest (L',G') in K
SOURCE_CONCLUSION: there is delta_1 in (0, min{delta_K, m_L, m_G}/2], depending only on K, such that for (L,G) in K_{delta_1}: Re L > m_L/2, L != 0, |G^2/L^2 - G'^2/L'^2| < tau, so e(L,G) = sqrt(1 - G^2/L^2) (principal branch) is holomorphic on K_{delta_1}, real positive at real points of C_0 within K_{delta_1}, e^2 = 1 - G^2/L^2, |e(L,G) - e(L',G')| < delta_E, dist(e,[-e_1,e_1]) < delta_E, |e| < e_2; real points of K_{delta_1} lie in C_0; Q is holomorphic on U(delta_1), 2pi-periodic in ell and g, real at real points where it agrees with the real orbit map
CONSTANT_SCOPE: delta_1 depends only on K
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:sec-complex#data, bpI:p7:kepler-eq, bpI:p7:orbit-maps-e, bpI:p7:orbit-maps, stepI:p7:cd-uc, stepI:p7:cd-branch
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#bpI:p7:complex-domain@L340-L340 | K, K_delta, m_L, m_G, e_-, e_1, e_2, delta_K, U(delta)
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#bpI:p7:complex-domain@L341-L341 | delta_E, P(e_1), delta_K
EDGE: bpI:p7:orbit-maps-e | blueprint-I/parts/p7-delaunay.tex#bpI:p7:complex-domain@L343-L343 | holomorphy, periodicity and reality of Q_el on P(e_1)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:complex-domain@L343-L343 | Q = Q_el(ell,g,L,e(L,G),G/L) and the real orbit map
EDGE: stepI:p7:cd-uc | blueprint-I/parts/p7-delaunay.tex#bpI:p7:complex-domain@L347-L347 | proof step
EDGE: stepI:p7:cd-branch | blueprint-I/parts/p7-delaunay.tex#bpI:p7:complex-domain@L349-L349 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: complex_domain_spec, complexDelta_ratio_bound, complexDelta_radicand_disk, complexDelta_ecc_sq, delaunayC_periodic, complexDelta, ComplexDomainData (KAM/Iso/ComplexDomain.lean)
LEAN_NOTE: audit I-6 audit-2 PASS (closes audit-1 F1/N1)
NOTE: -

NODE: stepI:p7:cd-uc
KIND: step
TITLE: Uniform continuity
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:cd-uc@L347-L347
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:cd-uc@L347-L347
CONTRACT_ID: stepI:p7:cd-uc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K as in section data
SOURCE_QUANTIFIERS: For the fixed nonempty compact K, first choose delta_1>0 in the stated range depending only on K, then for every (L,G) in K_{delta_1} and nearest (L_prime,G_prime) in K
SOURCE_CONCLUSION: There exists delta_1 in (0,min{delta_K,m_L,m_G}/2], depending only on K, such that for every (L,G) in K_{delta_1} with nearest (L_prime,G_prime) in K, Re L>m_L/2, L!=0 and |G^2/L^2-G_prime^2/L_prime^2|<min{e_-^2/2,e_- delta_E}; at real points the positivity conclusions used for L,G also hold
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:sec-complex#data, bpI:p7:kepler-eq, bpI:p8:x-topo
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:cd-uc@L347-L347 | K, m_L, m_G, delta_K
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:cd-uc@L347-L347 | delta_K
EDGE: bpI:p8:x-topo | blueprint-I/parts/p7-delaunay.tex#stepI:p7:cd-uc@L347-L347 | the closed bounded neighbourhood of compact K is compact in the finite-dimensional real carrier
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: exists_radius, GoodRadius, complexTau (KAM/Iso/ComplexDomain.lean)
LEAN_NOTE: audit I-6 audit-1 PASS WITH NOTES + audit-2 PASS; named step cd-uc (KAM.Iso.ComplexDomainAux)
NOTE: SOURCE_GAP: the passage from continuity on the compact complex action neighbourhood to uniform continuity (Heine-Cantor, identifying C^2 with R^4) is neither proved nor enumerated among the permitted external inputs. x-topo supplies closed-bounded compactness, but does not state Heine-Cantor. This records an input-policy gap, not a false estimate.

NODE: stepI:p7:cd-branch
KIND: step
TITLE: Branches
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:cd-branch@L349-L350
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:cd-branch@L349-L350
CONTRACT_ID: stepI:p7:cd-branch
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step cd-uc; w = 1 - G^2/L^2, w' = e'^2 with e' = e(L',G') in [e_-, e_1]
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: Re(1 - G^2/L^2) >= e_-^2/2 > 0; e(L,G) holomorphic; |e - e'| <= |w - w'|/e_- < delta_E, so dist(e,[-e_1,e_1]) < delta_E; real points: e^2 in (0,1) so (L,G) in C_0; remaining statements from orbit-maps-e and u = u_R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:cd-uc, bpI:p7:sec-complex#data, bpI:p7:kepler-eq, bpI:p7:x-hol, bpI:p7:orbit-maps-e
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:cd-uc | blueprint-I/parts/p7-delaunay.tex#stepI:p7:cd-branch@L349-L349 | ¦w - w'¦ < tau
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:cd-branch@L349-L349 | e_-, e_1
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:cd-branch@L349-L349 | delta_E; u = u_R on real points
EDGE: bpI:p7:x-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:cd-branch@L349-L349 | principal square root holomorphic on Re z > 0
EDGE: bpI:p7:orbit-maps-e | blueprint-I/parts/p7-delaunay.tex#stepI:p7:cd-branch@L350-L350 | remaining statements follow from the holomorphy of Q_el on P(e_1)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: sqrt_branch, cd_diff_ecc, cd_real (KAM/Iso/ComplexDomain.lean)
LEAN_NOTE: audit I-6 audit-1 PASS WITH NOTES + audit-2 PASS; named step cd-branch (KAM.Iso.ComplexDomainAux)
NOTE: -

NODE: bpI:p7:shift-def
KIND: definition
TITLE: Potential of the shift
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift-def@L356-L362
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:shift-def
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S = {Re z > 0}; Xi = {(q,mu) in C^2 x C : vartheta(q), vartheta(q + mu e), vartheta(q - (1-mu) e) in S}
SOURCE_QUANTIFIERS: (q,mu) in Xi
SOURCE_CONCLUSION: defines w(q) = vartheta(q)^{-1/2}, Psi(q,mu) = (1-mu) vartheta(q + mu e)^{-1/2} + mu vartheta(q - (1-mu) e)^{-1/2}, Psi(q,0) = w(q), holomorphic on the open set Xi; for real q, mu: (q,mu) in Xi iff q != 0 and q collision free for mu, and then w(q) = 1/rad(q), Psi(q,mu) = (1-mu)/rad(q - a_1(mu)) + mu/rad(q - a_2(mu))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:x-hol, bpI:p0:primaries#CollisionFree, bpI:p0:primaries#radius, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:x-hol | blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift-def@L360-L360 | holomorphy of the quotient and the principal power on Re z > 0
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift-def@L361-L361 | collision freedom for mu in the real characterization of Xi
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift-def@L361-L361 | rad in w(q) and Psi
EDGE: bpI:p0:primaries#primary1 | blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift-def@L361-L361 | a_1(mu) = -mu e
EDGE: bpI:p0:primaries#primary2 | blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift-def@L361-L361 | a_2(mu) = (1-mu) e
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: vtheta, clen, e0, shiftW, shiftPsi, shiftXi (KAM/Iso/ShiftPotential.lean)
LEAN_NOTE: audit I-5 PASS WITH NOTES; definitions landed
NOTE: standing definition package of Parts 7-8 (SPEC)

NODE: bpI:p7:shift
KIND: lemma
TITLE: The shift potential is analytic with the factor $\mu$ removed
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift@L364-L378
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift@L379-L393
CONTRACT_ID: bpI:p7:shift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < r_min <= rho_max < 1; eps_0 > 0 with eps_0(eps_0 + 2 rho_max) < r_min^2 and eps_0(eps_0 + 4) < (1 - rho_max)^2; mu_2 = eps_0/2, c_* = min{r_min^2 - eps_0(eps_0 + 2 rho_max), (1 - rho_max)^2 - eps_0(eps_0 + 4)}, O = {q in C^2 : exists q' in R^2, r_min <= |q'|_2 <= rho_max, |q - q'|_2 < eps_0/2}
SOURCE_QUANTIFIERS: r_min, rho_max, then eps_0 (hence mu_2, c_*, O, C_sh), then (q, mu)
SOURCE_CONCLUSION: O x closed disc D(0,mu_2) subset Xi; there Re vartheta >= c_* for the three arguments, so |w|, |vartheta^{-1/2}| <= c_*^{-1/2}; there is a holomorphic f : O x D(0,mu_2) -> C with mu f(q,mu) = w(q) - Psi(q,mu), f(q,mu) = -int_0^1 d_mu Psi(q, t mu) dt, |f| <= C_sh := 6/(eps_0 sqrt(c_*)); f(q,0) = 1/|q| + q_0/|q|^3 - 1/|q - e|; for real q in O and real |mu| < mu_2 the point (q,mu) is collision free and f(q,mu) is real
CONSTANT_SCOPE: C_sh, mu_2 depend only on (r_min, rho_max)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:shift-def, bpI:p0:primaries#CollisionFree, stepI:p7:sh-pos, stepI:p7:sh-bound, stepI:p7:sh-div, stepI:p7:sh-zero, stepI:p7:sh-real
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:shift-def | blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift@L365-L365 | Xi, w, Psi
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift@L376-L376 | collision freedom for real q in O and real mu
EDGE: stepI:p7:sh-pos | blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift@L380-L380 | proof step
EDGE: stepI:p7:sh-bound | blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift@L386-L386 | proof step
EDGE: stepI:p7:sh-div | blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift@L388-L388 | proof step
EDGE: stepI:p7:sh-zero | blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift@L390-L390 | proof step
EDGE: stepI:p7:sh-real | blueprint-I/parts/p7-delaunay.tex#bpI:p7:shift@L392-L392 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: shift_domain, shift_value_zero, shift_mul_eq, shift_holomorphic, shiftF_eq_integral, shift_bound, shift_real, shiftF (KAM/Iso/ShiftPotential.lean)
LEAN_NOTE: audit I-5 PASS WITH NOTES; |vtheta^-1/2|<=c*^-1/2 only in private norm_cpow_neg_half_le (N1)
NOTE: -

NODE: stepI:p7:sh-pos
KIND: step
TITLE: Positivity of the radicands
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-pos@L380-L384
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-pos@L380-L384
CONTRACT_ID: stepI:p7:sh-pos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q in O with q' as in the definition; |mu| <= mu_2
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: the three radicands have Re vartheta >= c_*; hence O x closed disc subset Xi and |vartheta^{-1/2}| <= (Re vartheta)^{-1/2} <= c_*^{-1/2}; radicands real and positive for real q, mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:shift-def, bpI:p7:x-hol
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:shift-def | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-pos@L380-L380 | Xi and the radicands of w, Psi
EDGE: bpI:p7:x-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-pos@L384-L384 | bound ¦z^{-1/2}¦ <= (Re z)^{-1/2}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: shift_domain, norm_cpow_neg_half_le (KAM/Iso/ShiftPotential.lean)
LEAN_NOTE: audit I-5 PASS WITH NOTES; named sh-pos; N1: |vtheta^-1/2| bound only via private lemma, not in public type
NOTE: -

NODE: stepI:p7:sh-bound
KIND: step
TITLE: Bound of the numerator
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-bound@L386-L386
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-bound@L386-L386
CONTRACT_ID: stepI:p7:sh-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step sh-pos
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: |Psi| <= (3/2) c_*^{-1/2}, |w| <= c_*^{-1/2}; g_q(mu) = w(q) - Psi(q,mu) satisfies |g_q| <= 3 c_*^{-1/2} on the closed disc and g_q(0) = 0; g_q holomorphic near the closed disc
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:sh-pos, bpI:p7:shift-def
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:sh-pos | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-bound@L386-L386 | bounds on the radicands
EDGE: bpI:p7:shift-def | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-bound@L386-L386 | Psi(q,0) = w(q) and the definition of Psi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: shift_bound (KAM/Iso/ShiftPotential.lean)
LEAN_NOTE: audit I-5 PASS WITH NOTES; named sh-bound
NOTE: -

NODE: stepI:p7:sh-div
KIND: step
TITLE: Division by $\mu$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-div@L388-L388
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-div@L388-L388
CONTRACT_ID: stepI:p7:sh-div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<r_min<=rho_max<1; choose epsilon_0>0 satisfying the two inequalities in L363, then mu_2=epsilon_0/2, c_* and O as in L365-368; Psi,w,Xi are the shift potential definitions
SOURCE_QUANTIFIERS: For fixed r_min,rho_max and an admissible epsilon_0, define mu_2,c_*,O; construct f on O x D(0,mu_2), then for every (q,mu) there, including mu=0
SOURCE_CONCLUSION: f(q,mu) = -int_0^1 d_mu Psi(q,t mu) dt is holomorphic on O x D(0,mu_2), mu f = g_q, and |f| <= 6/(eps_0 sqrt(c_*)) (by continuity at mu = 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:shift-def, stepI:p7:sh-pos, stepI:p7:sh-bound, bpI:p7:x-param, bpI:p7:x-schwarz, K:bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:shift-def | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-div@L388-L388 | Psi
EDGE: stepI:p7:sh-pos | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-div@L388-L388 | {q} x closed disc subset Xi
EDGE: stepI:p7:sh-bound | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-div@L388-L388 | ¦g_q¦ <= 3 c_*^{-1/2}, g_q(0) = 0
EDGE: bpI:p7:x-param | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-div@L388-L388 | holomorphy of the parameter integral
EDGE: bpI:p7:x-schwarz | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-div@L388-L388 | Schwarz lemma bound
EDGE: K:bp:p1:ext-integral | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-div@L388-L388 | the existing FTC clause applied to t -> Psi(q,t mu) gives mu f(q,mu)=w(q)-Psi(q,mu)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: shift_mul_eq, shift_holomorphic, shiftF_eq_integral, shift_bound (KAM/Iso/ShiftPotential.lean)
LEAN_NOTE: audit I-5 PASS WITH NOTES; named sh-div
NOTE: The fundamental theorem of calculus invoked at L386 is the clause int_a^b phi_prime=phi(b)-phi(a) of the already imported K:bp:p1:ext-integral. On t in [0,1], (q,t mu) lies in Xi, where Psi is holomorphic; the curve is C^1 and its derivative is mu partial_mu Psi(q,t mu). This adds a direct use of an existing permitted input, not a new import or an invented proof.

NODE: stepI:p7:sh-zero
KIND: step
TITLE: Value at $\mu=0$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-zero@L390-L390
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-zero@L390-L390
CONTRACT_ID: stepI:p7:sh-zero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step sh-div
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: f(q,0) = -d_mu Psi(q,0) = w(q) + q_0 vartheta(q)^{-3/2} - vartheta(q - e)^{-1/2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:sh-div, bpI:p7:shift-def
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:sh-div | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-zero@L390-L390 | definition of f
EDGE: bpI:p7:shift-def | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-zero@L390-L390 | Psi and w
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: shift_value_zero (KAM/Iso/ShiftPotential.lean)
LEAN_NOTE: audit I-5 PASS WITH NOTES; named sh-zero
NOTE: -

NODE: stepI:p7:sh-real
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-real@L392-L392
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-real@L392-L392
CONTRACT_ID: stepI:p7:sh-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: steps sh-pos, sh-div, sh-zero; real (q,mu)
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: f is real for real q in O and real mu: f = (w - Psi)/mu for mu != 0 and the formula of sh-zero for mu = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:sh-pos, stepI:p7:sh-div, stepI:p7:sh-zero, bpI:p7:shift-def
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:sh-pos | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-real@L392-L392 | radicands real positive
EDGE: stepI:p7:sh-div | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-real@L392-L392 | mu f = w - Psi
EDGE: stepI:p7:sh-zero | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-real@L392-L392 | value at mu = 0
EDGE: bpI:p7:shift-def | blueprint-I/parts/p7-delaunay.tex#stepI:p7:sh-real@L392-L392 | real characterization of Xi, w, Psi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: shift_real (KAM/Iso/ShiftPotential.lean)
LEAN_NOTE: audit I-5 PASS WITH NOTES; named sh-real
NOTE: -

NODE: bpI:p7:exact-ham
KIND: proposition
TITLE: Exact restricted Hamiltonian in Delaunay variables
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:exact-ham@L395-L413
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:exact-ham@L414-L425
CONTRACT_ID: bpI:p7:exact-ham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K subset C_0 nonempty compact with rho_max = max_K L^2(1+e) < 1; r_min, eps_0, mu_2, c_*, C_sh as in Lemma shift for (r_min, rho_max)
SOURCE_QUANTIFIERS: K first, then (r_min, rho_max, eps_0, mu_2, c_*, C_sh), then delta_2 and F, then real (w, mu)
SOURCE_CONCLUSION: there exist delta_2 in (0,delta_1] and holomorphic F : U(delta_2) x D(0,mu_2) -> C, F_mu(w) = f(q(w),mu), q(w) the position part of Q(w), with (i) |F_mu(w)| <= C_F := C_sh = 6/(eps_0 sqrt(c_*)); (ii) F_mu(ell+2pi,g,L,G) = F_mu(ell,g+2pi,L,G) = F_mu(w), F_mu(w) real for real w in U(delta_2), real |mu| < mu_2; (iii) for real w in U(delta_2), real |mu| < mu_2: (L,G) in C_0, Q(w) collision free, H^R3_mu(Q(w)) = -1/(2L^2) - G + mu F_mu(w); (iv) every real (ell,g,L,G) with (L,G) in K lies in U(delta_2)
CONSTANT_SCOPE: constants (delta_2, mu_2, C_F) depend on K only (not on mu)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:shift, bpI:p7:sec-complex#data, bpI:p7:complex-domain, bpI:p7:orbit-maps, bpI:p0:restricted#restrictedHamiltonian, bpI:p0:primaries#CollisionFree, stepI:p7:eh-shell, stepI:p7:eh-delta, stepI:p7:eh-hol, stepI:p7:eh-exact
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:shift | blueprint-I/parts/p7-delaunay.tex#bpI:p7:exact-ham@L396-L396 | Lemma shift for (r_min, rho_max); f, O, C_sh
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#bpI:p7:exact-ham@L396-L396 | K, r_min, rho_max, U(delta)
EDGE: bpI:p7:complex-domain | blueprint-I/parts/p7-delaunay.tex#bpI:p7:exact-ham@L396-L396 | delta_1 and holomorphy of Q on U(delta_1)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:exact-ham@L398-L398 | Q and its position part q(w)
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#bpI:p7:exact-ham@L404-L404 | frozen H^R3_mu in (iii)
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p7-delaunay.tex#bpI:p7:exact-ham@L404-L404 | collision-freeness in (iii)
EDGE: stepI:p7:eh-shell | blueprint-I/parts/p7-delaunay.tex#bpI:p7:exact-ham@L415-L415 | proof step
EDGE: stepI:p7:eh-delta | blueprint-I/parts/p7-delaunay.tex#bpI:p7:exact-ham@L417-L417 | proof step
EDGE: stepI:p7:eh-hol | blueprint-I/parts/p7-delaunay.tex#bpI:p7:exact-ham@L420-L420 | proof step
EDGE: stepI:p7:eh-exact | blueprint-I/parts/p7-delaunay.tex#bpI:p7:exact-ham@L422-L422 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: exact_ham, exact_radius_spec, exact_positions_mem_shiftO, ExactHamData (KAM/Iso/ExactHamiltonian.lean)
LEAN_NOTE: audit I-7 PASS WITH NOTES
NOTE: [pre-extract: dropped reference to bpI:p0:r3bp, which part p7 proves or sets up]

NODE: stepI:p7:eh-shell
KIND: step
TITLE: The real shell
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-shell@L415-L415
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-shell@L415-L415
CONTRACT_ID: stepI:p7:eh-shell
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: real w with (L',G') in K
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: r = |q(w)|_2 lies in [L'^2(1-e'), L'^2(1+e')] subset [r_min, rho_max]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:orbit-identities, bpI:p7:sec-complex#data, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-shell@L415-L415 | (a): L^2(1-e) <= r <= L^2(1+e)
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-shell@L415-L415 | r_min and rho_max
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-shell@L415-L415 | Q or its position component is used directly in this step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-review-I-p67
REVIEWER: sol-delta-I-c
LEAN_STATUS: PROVED
LEAN_REF: real_pos_data (KAM/Iso/ExactHamiltonian.lean)
LEAN_NOTE: audit I-7 PASS WITH NOTES; named eh-shell (KAM.Iso.ExactAux)
NOTE: -

NODE: stepI:p7:eh-delta
KIND: step
TITLE: Choice of $\delta_2$
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-delta@L417-L418
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-delta@L417-L418
CONTRACT_ID: stepI:p7:eh-delta
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K is a nonempty compact subset of C_0, rho_max<1; the section data and shift constants r_min,epsilon_0,mu_2,c_*,C_sh are selected as in exact-ham L394; delta_1 is the complex-domain radius; delta_*=delta_1/2
SOURCE_QUANTIFIERS: After fixed K and the selected shift/complex-domain constants, choose 0<delta_2<=delta_1/2 independent of w,mu; for every w in U(delta_2), choose real w_prime with actions in K as at L415
SOURCE_CONCLUSION: there is 0 < delta_2 <= delta_* = delta_1/2, depending only on K, such that for every w in U(delta_2) there is a real w' = (Re ell, Re g, L', G') with (L',G') in K and Euclidean distance of the position parts q(w), q(w') less than eps_0/2; hence q(w) in O
CONSTANT_SCOPE: delta_2 depends only on K
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:complex-domain, stepI:p7:eh-shell, bpI:p7:shift, bpI:p7:sec-complex#data, bpI:p8:x-topo, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:complex-domain | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-delta@L417-L417 | Q holomorphic on U(delta_1), real on real points, periodic
EDGE: stepI:p7:eh-shell | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-delta@L417-L417 | q' = q(w') has r_min <= ¦q'¦ <= rho_max
EDGE: bpI:p7:shift | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-delta@L417-L417 | eps_0 and the set O
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-delta@L417-L417 | U(delta), K
EDGE: bpI:p8:x-topo | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-delta@L417-L417 | the closure of the bounded fundamental-domain tube is compact
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-delta@L417-L417 | Q and its position component q(w)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: exactDelta, ExactRadiusData, exact_radius_spec, exact_positions_mem_shiftO (KAM/Iso/ExactHamiltonian.lean)
LEAN_NOTE: audit I-7 PASS WITH NOTES; rows eh-delta (selection, output predicate, geometric export)
NOTE: SOURCE_GAP: uniform continuity of the position component of Q on the compact fundamental-domain closure is invoked but not proved or listed as an external. x-topo pays compactness only. The bound concerns position parts, as explicitly specified at L415; it does not assert a momentum bound.

NODE: stepI:p7:eh-hol
KIND: step
TITLE: Holomorphy and bound
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-hol@L420-L420
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-hol@L420-L420
CONTRACT_ID: stepI:p7:eh-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K is a nonempty compact subset of C_0, rho_max<1; the section data and shift constants r_min,epsilon_0,mu_2,c_*,C_sh are selected as in exact-ham L394; delta_1 is the complex-domain radius; delta_2 is the radius selected at L415-416; F_mu(w) is defined by f(q(w),mu)
SOURCE_QUANTIFIERS: For fixed K and chosen delta_2,mu_2,C_sh, define F on U(delta_2) x D(0,mu_2); all w and mu in this domain, with reality at real pairs
SOURCE_CONCLUSION: F_mu(w) = f(q(w),mu) holomorphic with |F| <= C_sh: (i); periodicity of q(.) and reality of f and Q give (ii); (iv): delta_2 > 0 and K subset K_{delta_2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:eh-delta, bpI:p7:shift, bpI:p7:complex-domain, bpI:p7:orbit-maps, bpI:p7:sec-complex#data, bpI:p7:x-hol
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:eh-delta | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-hol@L420-L420 | q(w) in O
EDGE: bpI:p7:shift | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-hol@L420-L420 | holomorphy, bound C_sh and reality of f
EDGE: bpI:p7:complex-domain | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-hol@L420-L420 | holomorphy and periodicity of Q on U(delta_1)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-hol@L420-L420 | reality of Q on real points
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-hol@L420-L420 | U(delta_2) and K subset K_delta2 are the section-defined sets
EDGE: bpI:p7:x-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-hol@L420-L420 | compose the holomorphic f and the position component of Q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: exactRadiusData_of_positions, exact_ham (KAM/Iso/ExactHamiltonian.lean)
LEAN_NOTE: audit I-7 PASS WITH NOTES; named eh-hol/eh-exact builder
NOTE: -

NODE: stepI:p7:eh-exact
KIND: step
TITLE: Exactness
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L422-L424
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L422-L424
CONTRACT_ID: stepI:p7:eh-exact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K is a nonempty compact subset of C_0, rho_max<1; the section data and shift constants r_min,epsilon_0,mu_2,c_*,C_sh are selected as in exact-ham L394; delta_1 is the complex-domain radius; delta_2 is selected at L415-416; w is real in U(delta_2), mu real with |mu|<mu_2
SOURCE_QUANTIFIERS: For every real w in U(delta_2) and every real mu with |mu|<mu_2, after the common constants are chosen
SOURCE_CONCLUSION: (L,G) in C_0, Q(w) collision free and H^R3_mu(Q(w)) = H^R3_0(q,p) + [w(q) - Psi(q,mu)] = -1/(2L^2) - G + mu f(q,mu)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:complex-domain, stepI:p7:eh-delta, bpI:p7:shift, bpI:p7:shift-def, bpI:p7:h0, bpI:p0:restricted#restrictedHamiltonian, bpI:p0:primaries#CollisionFree, bpI:p0:primaries#radius, bpI:p0:primaries#radiusSq, bpI:p7:orbit-maps, bpI:p7:sec-complex#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:complex-domain | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L422-L422 | (L,G) in C_0 for real w in U(delta_1)
EDGE: stepI:p7:eh-delta | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L422-L422 | q(w) is a real point of O
EDGE: bpI:p7:shift | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L422-L422 | (q,mu) in Xi with real positive radicands; mu f = w - Psi
EDGE: bpI:p7:shift-def | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L422-L422 | Xi, Psi, rad(q - a_j) = sqrt(vartheta(...))
EDGE: bpI:p7:h0 | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L424-L424 | H^R3_0 = ... - w(q) and H^K o Q = -1/(2L^2) - G
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L423-L423 | H^R3_mu formula
EDGE: bpI:p0:primaries#CollisionFree | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L422-L422 | collision freedom
EDGE: bpI:p0:primaries#radius | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L422-L422 | rad(q - a_j(mu))
EDGE: bpI:p0:primaries#radiusSq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L422-L422 | radiusSq
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L422-L424 | Q or its position component is used directly in this step
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:eh-exact@L422-L422 | w in U(delta_2), its action carrier and complex-domain radii are the section data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: exact_identity, exactRadiusData_of_positions (KAM/Iso/ExactHamiltonian.lean)
LEAN_NOTE: audit I-7 PASS WITH NOTES; named eh-exact
NOTE: -

NODE: bpI:p7:period-one
KIND: corollary
TITLE: Period-one form: the data of I-HEAD
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:period-one@L427-L441
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:period-one@L442-L448
CONTRACT_ID: bpI:p7:period-one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K, delta_2, mu_2, C_F, F as in Proposition exact-ham; s_0 = delta_2/(2 pi), r_0 = 2 pi delta_2; B subset 2 pi K arbitrary; S the conversion; h~ = h_{(2pi)^2, 1/(2pi)}; real mu with |mu| < mu_2; f~_mu(theta,I) = mu F_mu(S(theta,I)) on T_{s_0} x B_{r_0}
SOURCE_QUANTIFIERS: K first (then delta_2, mu_2, C_F, s_0, r_0), then B, then mu, (theta, I)
SOURCE_CONCLUSION: (a) S(T_{s_0} x B_{r_0}) subset U(delta_2); (b) h~ holomorphic on B_{r_0} with Re I_1 > pi m_L > 0 there, real at real I; (c) f~_mu holomorphic on T_{s_0} x B_{r_0}, 1-periodic in theta, real at real theta and real I in B_{r_0} for real mu, |f~_mu| <= eps := |mu| C_F; (d) H^R3_mu(Q(S(theta,I))) = h~(I) + f~_mu(theta,I) = realHamiltonian h~ f~_mu (theta,I) for real theta and real I in B_{r_0}, with Q o S symplectic; (e) s_0, r_0, mu_2, C_F depend on K only and eps = C_F |mu|; for mu in [0,mu_2), the hypotheses on (h,f,eps) of I-HEAD other than nondegeneracy hold with the smallness parameter eps = mu C_F (the inequality eps < eps_0 is not asserted here); at mu = 0, eps = 0 and f~_0 = 0
CONSTANT_SCOPE: s_0, r_0, mu_2, C_F depend on K only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:exact-ham, bpI:p6:conversion-map, bpI:p6:kep-ham, bpI:p0:realham#realHamiltonian, bpI:p0:domains#complexStrip, bpI:p0:domains#actionNbhd, bpI:p7:sec-complex#data, stepI:p7:po-dom, stepI:p7:po-prop, stepI:p7:po-exact
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:exact-ham | blueprint-I/parts/p7-delaunay.tex#bpI:p7:period-one@L428-L428 | delta_2, mu_2, C_F, F
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p7-delaunay.tex#bpI:p7:period-one@L428-L428 | the conversion S
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p7-delaunay.tex#bpI:p7:period-one@L428-L428 | h~ = h_{(2pi)^2,1/(2pi)}
EDGE: bpI:p0:realham#realHamiltonian | blueprint-I/parts/p7-delaunay.tex#bpI:p7:period-one@L435-L435 | frozen realHamiltonian
EDGE: bpI:p0:domains#complexStrip | blueprint-I/parts/p7-delaunay.tex#bpI:p7:period-one@L430-L430 | T_{s_0} is the frozen complex strip
EDGE: bpI:p0:domains#actionNbhd | blueprint-I/parts/p7-delaunay.tex#bpI:p7:period-one@L430-L430 | B_{r_0} is the frozen action neighbourhood
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#bpI:p7:period-one@L428-L428 | K and 2 pi K
EDGE: stepI:p7:po-dom | blueprint-I/parts/p7-delaunay.tex#bpI:p7:period-one@L443-L443 | proof step
EDGE: stepI:p7:po-prop | blueprint-I/parts/p7-delaunay.tex#bpI:p7:period-one@L445-L445 | proof step
EDGE: stepI:p7:po-exact | blueprint-I/parts/p7-delaunay.tex#bpI:p7:period-one@L447-L447 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-review-I-p67
REVIEWER: sol-delta-I-c
LEAN_STATUS: PROVED
LEAN_REF: tildeF, period_one, delaunay_periodOne_symplectic (KAM/Iso/PeriodOne.lean)
LEAN_NOTE: audit I-8 PASS WITH NOTES
NOTE: -

NODE: stepI:p7:po-dom
KIND: step
TITLE: Domains
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-dom@L443-L443
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-dom@L443-L443
CONTRACT_ID: stepI:p7:po-dom
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: theta in T_{s_0}; I in B_{r_0}
SOURCE_QUANTIFIERS: as in the enclosing result
SOURCE_CONCLUSION: |Im 2 pi theta_i| < delta_2; I/(2 pi) in K_{delta_2}, so S(T_{s_0} x B_{r_0}) subset U(delta_2); Re(I_1/(2 pi)) > m_L/2 > 0, so I_1 != 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:domains#complexStrip, bpI:p0:domains#actionNbhd, bpI:p6:conversion-map, bpI:p7:exact-ham, bpI:p7:sec-complex#data, bpI:p7:complex-domain
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:domains#complexStrip | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-dom@L443-L443 | theta in T_{s_0}
EDGE: bpI:p0:domains#actionNbhd | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-dom@L443-L443 | I in B_{r_0}: within r_0 of some J in B
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-dom@L443-L443 | S, I/(2 pi)
EDGE: bpI:p7:exact-ham | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-dom@L443-L443 | delta_2 and U(delta_2)
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-dom@L443-L443 | K_{delta}, U(delta), m_L
EDGE: bpI:p7:complex-domain | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-dom@L443-L443 | Re L > m_L/2 on K_{delta_1}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b
REVIEWER: sol-review-I-p67
LEAN_STATUS: PROVED
LEAN_REF: period_one (KAM/Iso/PeriodOne.lean)
LEAN_NOTE: audit I-8 PASS WITH NOTES; rows po-dom (Aux lemmas) inside period_one
NOTE: -

NODE: stepI:p7:po-prop
KIND: step
TITLE: Properties
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-prop@L445-L445
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-prop@L445-L445
CONTRACT_ID: stepI:p7:po-prop
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K,delta_2,mu_2,C_F,F are as in exact-ham; s_0=delta_2/(2 pi), r_0=2 pi delta_2; B is an arbitrary subset of 2 pi K; S(theta,I)=(2 pi theta,I/(2 pi)); h_tilde=h_{(2 pi)^2,1/(2 pi)}; real |mu|<mu_2 and f_tilde_mu=mu F_mu o S on the analytic domain
SOURCE_QUANTIFIERS: For fixed K and common analytic constants, every B subset 2 pi K and every real mu with |mu|<mu_2; all (theta,I) in the associated complex domain, with reality at real pairs
SOURCE_CONCLUSION: (b) h~ holomorphic on B_{r_0}, Re I_1 > pi m_L, real at real I; (c) f~_mu holomorphic, 1-periodic in theta, real, bounded by |mu| C_F
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:conversion, stepI:p7:po-dom, bpI:p7:exact-ham, bpI:p6:conversion-map, bpI:p6:kep-ham, bpI:p7:sec-complex#data, bpI:p6:nondeg, bpI:p7:x-hol
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:conversion | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-prop@L445-L445 | (b): h~ = h_{(2pi)^2, 1/(2pi)} holomorphic where I_1 != 0, real at real I
EDGE: stepI:p7:po-dom | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-prop@L445-L445 | S maps the domain into U(delta_2)
EDGE: bpI:p7:exact-ham | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-prop@L445-L445 | (i),(ii): bound, periodicity, reality of F
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-prop@L445-L445 | periodicity: theta -> theta + k becomes (ell,g) -> (ell,g) + 2 pi k
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-prop@L445-L445 | h~ = h_{(2pi)^2,1/(2pi)} is fixed by the Kepler Hamiltonian package
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-prop@L445-L445 | m_L is the section-defined positive minimum used in Re I_1>pi m_L
EDGE: bpI:p6:nondeg | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-prop@L445-L445 | the explicitly cited domain proof argument is reused with nonvanishing already supplied by po-dom; this is not application of the full conditional corollary
EDGE: bpI:p7:x-hol | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-prop@L445-L445 | composition of the holomorphic F_mu with linear S, and multiplication by the fixed scalar mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-g
REVIEWER: sol-delta-I-h
LEAN_STATUS: PROVED
LEAN_REF: period_one (KAM/Iso/PeriodOne.lean)
LEAN_NOTE: audit I-8 PASS WITH NOTES; rows po-prop (Aux lemmas) inside period_one
NOTE: L443 recalls the domain proof argument of Part 6; L441 already supplied Re(I_1/(2 pi))>m_L/2 and nonvanishing on B_{r_0} directly from complex-domain. Together with conversion(b), this proves holomorphy and reality. The source-explicit nondeg edge is retained as reuse of that proof argument, not an application of the full corollary with its infimum-radius premises. For empty B the domain claims are vacuous. No SOURCE_GAP is established here.

NODE: stepI:p7:po-exact
KIND: step
TITLE: Exactness
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-exact@L447-L447
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-exact@L447-L447
CONTRACT_ID: stepI:p7:po-exact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K,delta_2,mu_2,C_F,F are as in exact-ham; s_0=delta_2/(2 pi), r_0=2 pi delta_2; B is an arbitrary subset of 2 pi K; S(theta,I)=(2 pi theta,I/(2 pi)); h_tilde=h_{(2 pi)^2,1/(2 pi)}; real |mu|<mu_2 and f_tilde_mu=mu F_mu o S on the analytic domain; theta real and I real in B_{r_0} for the exact Hamiltonian identity
SOURCE_QUANTIFIERS: For every real mu with |mu|<mu_2, every real theta and real I in B_{r_0}; symplecticity on the corresponding real domain
SOURCE_CONCLUSION: H^R3_mu(Q(S(theta,I))) = h~(I) + f~_mu = realHamiltonian h~ f~_mu; Q o S symplectic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:exact-ham, bpI:p6:conversion, bpI:p6:kep-ham, bpI:p0:realham#realHamiltonian, stepI:p7:po-dom, bpI:p7:symplectic, bpI:p6:conversion-map, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:exact-ham | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-exact@L447-L447 | (iii) at w = S(theta,I)
EDGE: bpI:p6:conversion | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-exact@L447-L447 | (b) h_{1,1}(L,G) = h~(I); (a) symplectic S
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-exact@L447-L447 | h_{1,1}(L,G) = -1/(2L^2) - G
EDGE: bpI:p0:realham#realHamiltonian | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-exact@L447-L447 | realHamiltonian is the real part of the same real number
EDGE: stepI:p7:po-dom | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-exact@L447-L447 | S(theta,I) in U(delta_2)
EDGE: bpI:p7:symplectic | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-exact@L447-L447 | Q symplectic
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-exact@L447-L447 | S
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:po-exact@L447-L447 | Q or its position component is used directly in this step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: period_one, delaunay_periodOne_symplectic (KAM/Iso/PeriodOne.lean)
LEAN_NOTE: audit I-8 PASS WITH NOTES; row po-exact
NOTE: -

NODE: bpI:p7:transfer
KIND: proposition
TITLE: Transfer of Delaunay solutions to the physical problem
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L450-L455
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L456-L462
CONTRACT_ID: bpI:p7:transfer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Corollary period-one; mu in R with |mu| < mu_2; J subset R; z~ : R -> R^2 x R^2 with Sol(realHamiltonian h~ f~_mu, B, J, z~) (Definition hamsol)
SOURCE_QUANTIFIERS: the data of period-one, then mu, J, z~
SOURCE_CONCLUSION: z := Q o S o z~ satisfies RSol_mu(J,z); for t in J with z~(t) = (theta, I): rad(q(t)) = L^2(1 - e cos u) in [a(1-e), a(1+e)], a = L^2 = I_1^2/(2pi)^2, elements of z(t) are (L,G) = I/(2 pi), and H^R3_mu(z(t)) = realHamiltonian h~ f~_mu (z~(t))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:period-one, bpI:p0:hamsol#IsHamiltonianSolutionOn, bpI:p0:restricted#IsRestrictedSolutionOn, bpI:p0:realham#realHamiltonian, bpI:p6:conversion-map, bpI:p7:orbit-maps, stepI:p7:tr-cf, stepI:p7:tr-open, stepI:p7:tr-chain, bpI:p6:kep-ham, bpI:p7:sec-complex#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:period-one | blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L451-L451 | setting of Corollary period-one
EDGE: bpI:p0:hamsol#IsHamiltonianSolutionOn | blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L451-L451 | Sol predicate
EDGE: bpI:p0:restricted#IsRestrictedSolutionOn | blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L451-L451 | RSol_mu
EDGE: bpI:p0:realham#realHamiltonian | blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L451-L451 | realHamiltonian
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L451-L451 | S
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L451-L451 | Q
EDGE: stepI:p7:tr-cf | blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L457-L457 | proof step
EDGE: stepI:p7:tr-open | blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L459-L459 | proof step
EDGE: stepI:p7:tr-chain | blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L461-L461 | proof step
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L451-L452 | the Hamiltonian is expressed using the converted Kepler h~
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#bpI:p7:transfer@L451-L452 | the setting uses K or the common complex-domain data fixed in the section
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-review-I-p67
REVIEWER: sol-delta-I-c
LEAN_STATUS: PROVED
LEAN_REF: transfer, transfer_identities (KAM/Iso/PeriodOne.lean)
LEAN_NOTE: audit I-8 PASS WITH NOTES
NOTE: -

NODE: stepI:p7:tr-cf
KIND: step
TITLE: Collision freedom and real-analyticity
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-cf@L457-L457
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-cf@L457-L457
CONTRACT_ID: stepI:p7:tr-cf
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K,delta_2,mu_2,C_F,F are as in exact-ham; s_0=delta_2/(2 pi), r_0=2 pi delta_2; B is an arbitrary subset of 2 pi K; S(theta,I)=(2 pi theta,I/(2 pi)); h_tilde=h_{(2 pi)^2,1/(2 pi)}; real |mu|<mu_2 and f_tilde_mu=mu F_mu o S on the analytic domain; J subset R and z_tilde:R->R^2 x R^2 satisfies Sol(realHamiltonian h_tilde f_tilde_mu,B,J,z_tilde); z=Q o S o z_tilde; t in J
SOURCE_QUANTIFIERS: For every period-one datum, mu,J,z_tilde satisfying transfer, and every t in J
SOURCE_CONCLUSION: S z~(t) is real with (L,G) in K, lies in U(delta_2); z(t) = Q(S z~(t)) is collision free, i.e. in W_mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:exact-ham, bpI:p7:sec-ham#data, bpI:p6:conversion-map, bpI:p7:sec-complex#data, bpI:p7:orbit-maps, bpI:p0:hamsol#IsHamiltonianSolutionOn
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:exact-ham | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-cf@L457-L457 | (iv) and (iii): U(delta_2) contains the real points over K, collision freedom
EDGE: bpI:p7:sec-ham#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-cf@L457-L457 | W_mu
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-cf@L457-L457 | S
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-cf@L457-L457 | the setting uses K or the common complex-domain data fixed in the section
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-cf@L457-L457 | Q or its position component is used directly in this step
EDGE: bpI:p0:hamsol#IsHamiltonianSolutionOn | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-cf@L457-L457 | the Sol premise supplies I=z_tilde(t)_2 in B for t in J
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.tr_cf (KAM/Iso/TransferStepNodes.lean)
LEAN_NOTE: GAP-I7b (audit PASS WITH NOTES)
NOTE: -

NODE: stepI:p7:tr-open
KIND: step
TITLE: Agreement of Hamiltonians on an open set
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-open@L459-L459
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-open@L459-L459
CONTRACT_ID: stepI:p7:tr-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K,delta_2,mu_2,C_F,F are as in exact-ham; s_0=delta_2/(2 pi), r_0=2 pi delta_2; B is an arbitrary subset of 2 pi K; S(theta,I)=(2 pi theta,I/(2 pi)); h_tilde=h_{(2 pi)^2,1/(2 pi)}; real |mu|<mu_2 and f_tilde_mu=mu F_mu o S on the analytic domain; J subset R and z_tilde:R->R^2 x R^2 satisfies Sol(realHamiltonian h_tilde f_tilde_mu,B,J,z_tilde); z=Q o S o z_tilde; t in J; V is defined to be the real r_0-neighbourhood cylinder of B
SOURCE_QUANTIFIERS: For every period-one datum, mu,J,z_tilde satisfying transfer, and every t in J; define V from B,r_0 and establish agreement on all of V before evaluating derivatives at z_tilde(t)
SOURCE_CONCLUSION: realHamiltonian h~ f~_mu = H^R3_mu o Q o S on V; both sides real-analytic, so real derivatives and Hamiltonian fields coincide at z~(t)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:period-one, bpI:p0:realham#realHamiltonian, bpI:p0:restricted#restrictedHamiltonian, bpI:p7:chart, bpI:p6:kep-ham, bpI:p6:conversion-map, bpI:p7:sec-complex#data, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:period-one | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-open@L459-L459 | (d) exactness on B_{r_0}
EDGE: bpI:p0:realham#realHamiltonian | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-open@L459-L459 | realHamiltonian
EDGE: bpI:p0:restricted#restrictedHamiltonian | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-open@L459-L459 | H^R3_mu
EDGE: bpI:p7:chart | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-open@L459-L459 | Q real-analytic
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-open@L459-L459 | the Hamiltonian is expressed using the converted Kepler h~
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-open@L459-L459 | S converts the curve or the Hamiltonian to conventional variables
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-open@L459-L459 | the setting uses K or the common complex-domain data fixed in the section
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-open@L459-L459 | Q or its position component is used directly in this step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: hamiltonianVectorField_congr, transfer (KAM/Iso/PeriodOne.lean)
LEAN_NOTE: audit I-8 PASS WITH NOTES; row tr-open
NOTE: -

NODE: stepI:p7:tr-chain
KIND: step
TITLE: Chain rule
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461
CONTRACT_ID: stepI:p7:tr-chain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K,delta_2,mu_2,C_F,F are as in exact-ham; s_0=delta_2/(2 pi), r_0=2 pi delta_2; B is an arbitrary subset of 2 pi K; S(theta,I)=(2 pi theta,I/(2 pi)); h_tilde=h_{(2 pi)^2,1/(2 pi)}; real |mu|<mu_2 and f_tilde_mu=mu F_mu o S on the analytic domain; J subset R and z_tilde:R->R^2 x R^2 satisfies Sol(realHamiltonian h_tilde f_tilde_mu,B,J,z_tilde); z=Q o S o z_tilde; t in J
SOURCE_QUANTIFIERS: For every period-one datum, mu,J,z_tilde satisfying transfer, and every t in J; J need not be open or an interval
SOURCE_CONCLUSION: z~'(t) = X_{realHamiltonian h~ f~_mu}(z~(t)) = X_{H o Q o S}(z~(t)); d/dt z = D(Q o S) z~' = X_{H^R3_mu}(z(t)) = V_mu(z(t)); the formulas for rad(q) and the energy
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepI:p7:tr-open, bpI:p0:hamsol#IsHamiltonianSolutionOn, bpI:p7:symplectic, bpI:p6:conversion, bpI:p7:ham-eq, bpI:p7:orbit-identities, bpI:p7:period-one, stepI:p7:tr-cf, bpI:p6:kep-ham, bpI:p6:conversion-map, bpI:p7:sec-complex#data, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: stepI:p7:tr-open | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461 | agreement of the Hamiltonians and fields
EDGE: bpI:p0:hamsol#IsHamiltonianSolutionOn | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461 | Sol gives z~'(t) = X(z~(t))
EDGE: bpI:p7:symplectic | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461 | D Q symplectic, chain rule for Q
EDGE: bpI:p6:conversion | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461 | (a) symplectic S
EDGE: bpI:p7:ham-eq | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461 | X_{H^R3_mu} = V_mu and RSol_mu
EDGE: bpI:p7:orbit-identities | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461 | (a) rad(q)
EDGE: bpI:p7:period-one | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461 | (d) energy
EDGE: stepI:p7:tr-cf | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461 | z(t) in W_mu
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461 | the Hamiltonian is expressed using the converted Kepler h~
EDGE: bpI:p6:conversion-map | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461 | S converts the curve or the Hamiltonian to conventional variables
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461 | the setting uses K or the common complex-domain data fixed in the section
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#stepI:p7:tr-chain@L461-L461 | Q or its position component is used directly in this step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.tr_chain (KAM/Iso/TransferStepNodes.lean)
LEAN_NOTE: GAP-I7b (audit PASS WITH NOTES)
NOTE: -

NODE: bpI:p7:nondeg
KIND: proposition
TITLE: Isoenergetic nondegeneracy of the Delaunay Hamiltonian
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:nondeg@L467-L471
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:nondeg@L472-L475
CONTRACT_ID: bpI:p7:nondeg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K,delta_2,mu_2,C_F,F are as in exact-ham; s_0=delta_2/(2 pi), r_0=2 pi delta_2; B is an arbitrary subset of 2 pi K; S(theta,I)=(2 pi theta,I/(2 pi)); h_tilde=h_{(2 pi)^2,1/(2 pi)}; real |mu|<mu_2 and f_tilde_mu=mu F_mu o S on the analytic domain
SOURCE_QUANTIFIERS: For the period-one data, every real I with I_1>0 has the displayed determinant; in particular every real I in B_{r_0}, for every B subset 2 pi K; conventional variables have every (L,G) with L>0
SOURCE_CONCLUSION: det borderedHessian h~ I = 3/I_1^4 > 0 for every real I in B_{r_0}, indeed for every real I with I_1 > 0; in conventional variables B_{h_{1,1}}(L,G) = K_{1,1}(L) with det = 3/L^4; h~ satisfies the nondegeneracy hypothesis of I-HEAD on all real points of B_{r_0}, for every B subset 2 pi K
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:period-one, bpI:p0:bordered#borderedHessian, bpI:p0:keplerborder#keplerBorder, stepI:p7:nd-dom, stepI:p7:nd-det, bpI:p6:kep-ham, bpI:p7:sec-complex#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:period-one | blueprint-I/parts/p7-delaunay.tex#bpI:p7:nondeg@L468-L468 | the setting: h~, B_{r_0}
EDGE: bpI:p0:bordered#borderedHessian | blueprint-I/parts/p7-delaunay.tex#bpI:p7:nondeg@L468-L468 | borderedHessian
EDGE: bpI:p0:keplerborder#keplerBorder | blueprint-I/parts/p7-delaunay.tex#bpI:p7:nondeg@L468-L468 | K_{1,1}(L)
EDGE: stepI:p7:nd-dom | blueprint-I/parts/p7-delaunay.tex#bpI:p7:nondeg@L473-L473 | proof step
EDGE: stepI:p7:nd-det | blueprint-I/parts/p7-delaunay.tex#bpI:p7:nondeg@L474-L474 | proof step
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p7-delaunay.tex#bpI:p7:nondeg@L468-L469 | h~ = h_{(2pi)^2,1/(2pi)} is fixed by the Kepler Hamiltonian package
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#bpI:p7:nondeg@L468-L469 | the setting uses K or the common complex-domain data fixed in the section
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: nondeg_exact (KAM/Iso/PeriodOne.lean)
LEAN_NOTE: audit I-8 PASS WITH NOTES
NOTE: -

NODE: stepI:p7:nd-dom
KIND: step
TITLE: Reality of the domain
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:nd-dom@L473-L473
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:nd-dom@L473-L473
CONTRACT_ID: stepI:p7:nd-dom
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K,delta_2,mu_2,C_F,F are as in exact-ham; s_0=delta_2/(2 pi), r_0=2 pi delta_2; B is an arbitrary subset of 2 pi K; S(theta,I)=(2 pi theta,I/(2 pi)); h_tilde=h_{(2 pi)^2,1/(2 pi)}; real |mu|<mu_2 and f_tilde_mu=mu F_mu o S on the analytic domain; I is real and lies in B_{r_0}
SOURCE_QUANTIFIERS: For every period-one datum and every real I in B_{r_0}
SOURCE_CONCLUSION: real I in B_{r_0} has I_1 > 0 (Re I_1/(2 pi) > m_L/2 > 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p7:period-one, bpI:p7:sec-complex#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p7:period-one | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nd-dom@L473-L473 | (b): Re I_1 > pi m_L on B_{r_0}
EDGE: bpI:p7:sec-complex#data | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nd-dom@L473-L473 | the setting uses K or the common complex-domain data fixed in the section
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: nondeg_exact (KAM/Iso/PeriodOne.lean)
LEAN_NOTE: audit I-8 PASS WITH NOTES; positive first action on the real tube
NOTE: -

NODE: stepI:p7:nd-det
KIND: step
TITLE: Determinant
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:nd-det@L474-L474
PROOF_SOURCE: blueprint-I/parts/p7-delaunay.tex#stepI:p7:nd-det@L474-L474
CONTRACT_ID: stepI:p7:nd-det
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K,delta_2,mu_2,C_F,F are as in exact-ham; s_0=delta_2/(2 pi), r_0=2 pi delta_2; B is an arbitrary subset of 2 pi K; S(theta,I)=(2 pi theta,I/(2 pi)); h_tilde=h_{(2 pi)^2,1/(2 pi)}; real |mu|<mu_2 and f_tilde_mu=mu F_mu o S on the analytic domain; kappa=Omega=1; I real with I_1>0 for the general determinant formula, specializing to real I in B_{r_0}
SOURCE_QUANTIFIERS: For fixed kappa=Omega=1, every real I with I_1>0; specialize to real I in B_{r_0} using nd-dom; for the conventional matrix every L>0
SOURCE_CONCLUSION: For every real I with I_1>0, det borderedHessian h_tilde I=3/I_1^4>0; using nd-dom the same holds on real I in B_{r_0}; conventionally B_{h_{1,1}}(L,G)=K_{1,1}(L) and det=3/L^4 for L>0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p6:kep-border, bpI:p6:conversion, stepI:p7:nd-dom, bpI:p6:kep-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p6:kep-border | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nd-det@L474-L474 | determinant of the bordered Hessian of h_{1,1}
EDGE: bpI:p6:conversion | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nd-det@L474-L474 | (d) conversion of the bordered Hessian determinant
EDGE: stepI:p7:nd-dom | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nd-det@L474-L474 | I_1 > 0 on real I in B_{r_0}
EDGE: bpI:p6:kep-ham | blueprint-I/parts/p7-delaunay.tex#stepI:p7:nd-det@L474-L474 | h~ = h_{(2pi)^2,1/(2pi)} is fixed by the Kepler Hamiltonian package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-delta-I-c
REVIEWER: sol-delta-I-g
LEAN_STATUS: PROVED
LEAN_REF: nondeg_exact (KAM/Iso/PeriodOne.lean)
LEAN_NOTE: audit I-8 PASS WITH NOTES; determinant 3/I_1^4
NOTE: -

NODE: bpI:p7:sec-complex#data
KIND: definition
TITLE: Data of section A common complex neighbourhood: K, e_pm, m_L, m_G, r_min, rho_max, K_delta, U(delta)
STATEMENT_SOURCE: blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-complex@L327-L337
PROOF_SOURCE: -
CONTRACT_ID: bpI:p7:sec-complex#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K a nonempty compact subset of C_0 (the safe action region)
SOURCE_QUANTIFIERS: K, then delta > 0 (delta <= delta_K for U(delta))
SOURCE_CONCLUSION: defines e_- = min_K e > 0, e_1 = max_K e < 1, e_2 = (1+e_1)/2, m_L = min_K L > 0, m_G = min_K G > 0, r_min = min_K L^2(1-e) > 0, rho_max = max_K L^2(1+e), delta_K = delta_K(e_1) and P(e_1) from Proposition kepler-eq, K_delta = {(L,G) in C^2 : exists (L',G') in K, |(L,G)-(L',G')|_inf < delta} (open), U(delta) = {(ell,g,L,G) in C^4 : |Im ell| < delta, |Im g| < delta, (L,G) in K_delta}
CONSTANT_SCOPE: all quantities depend only on K
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p8:x-topo, bpI:p7:kepler-eq, bpI:p7:orbit-maps
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p8:x-topo | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-complex#data@L329-L329 | minima and maxima of continuous functions on the nonempty compact K exist and are attained, so e_- > 0, e_1 < 1, m_L, m_G, r_min > 0
EDGE: bpI:p7:kepler-eq | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-complex#data@L334-L334 | delta_K(e_1) and P(e_1)
EDGE: bpI:p7:orbit-maps | blueprint-I/parts/p7-delaunay.tex#bpI:p7:sec-complex@L327-L334 | e(L,G) = sqrt(1-G^2/L^2) on the cone C_0 supplies the continuous functions whose extrema define the data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-p7b+sol-review-I-p67
REVIEWER: sol-delta-I-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.SafeAction, KAM.Iso.kEccMin, KAM.Iso.kEccMax, KAM.Iso.kLMin, KAM.Iso.kGMin, KAM.Iso.kRmin, KAM.Iso.kRhoMax, KAM.Iso.UDelta (KAM/Iso/ComplexDomain.lean); KAM.Kepler.keplerE2, KAM.Kepler.keplerDeltaK, KAM.Kepler.keplerTube (KAM/Kepler/KeplerTube.lean); KAM.actionNbhd (KAM/Frozen/Defs/ActionNbhd.lean)
LEAN_NOTE: Every defined object classified: I-6-audit-1.md:47-53 and 'Definition classification' (SafeAction, six extrema, UDelta over frozen actionNbhd), KEP-4-audit-1.md:75,78,80,120-125 (e2, delta_K, P(e1)); K_delta = sealed actionNbhd, openness I-8-audit-1.md:70.
NOTE: section data node (SPEC, Part 7 L325-335)

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
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.R3bp.R3bpParams, KAM.Iso.R3bp.actionRegion, KAM.Iso.R3bp.actionRegionCl (KAM/Iso/R3bp/Region.lean)
LEAN_NOTE: R3bpParams = six verbatim source premises incl. rho_*<1 (field hinner); actionRegion/actionRegionCl; P8-2-audit-1.md:44,48-49 PASS.
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

NODE: K:bp:p0:g3
KIND: external
TITLE: [K] G3: measure of the non-Diophantine set
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:g3@L157-L162
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p0:g3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: tau > n-1; Omega subset R^n bounded
SOURCE_QUANTIFIERS: n,tau,Omega fixed; exists C; for every alpha > 0
SOURCE_CONCLUSION: meas{omega in Omega : omega not in Dio_{alpha,tau}} <= C alpha
CONSTANT_SCOPE: C depends only on n, tau and Omega (via a bound R with Omega subset [-R,R]^n); not on alpha
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p0:g3; shared Lean provider. There: KIND theorem, contract kam.volume_not_diophantine_le v1, frozen anchor KAM.volume_not_diophantine_le (kam.volume_not_diophantine_le.v1); not an anchor of this graph. Cited as \Kref{bp:p0:g3}, \frozen{KAM.volume_not_diophantine_le}.

NODE: K:bp:p1:cauchy-corollaries
KIND: external
TITLE: [K] Cauchy corollaries
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cauchy-corollaries@L617-L621
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:cauchy-corollaries
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f holomorphic and bounded on T_rho; 0<delta<rho; f valued in C^p (first claim) or C^p / C^{pxq} (second claim)
SOURCE_QUANTIFIERS: rho, delta, f, omega
SOURCE_CONCLUSION: ||(Df)^T||_{rho-delta} <= p delta^-1 ||f||_rho; ||d_omega f||_{rho-delta} <= |omega|_1 delta^-1 ||f||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:cauchy-corollaries; shared Lean provider. There: KIND lemma, contract bp:p1:cauchy-corollaries v1. Cited as \Kref{bp:p1:cauchy-corollaries}.

NODE: K:bp:p1:cauchy-open
KIND: external
TITLE: [K] Cauchy estimate on open sets
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cauchy-open@L474-L479
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:cauchy-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f holomorphic on open U in C^m with |f|<=A on U; closed polydisc of radius delta>0 around z lies in U
SOURCE_QUANTIFIERS: U,f,A,delta>0,z; l; c(m,j) depends only on m and j
SOURCE_CONCLUSION: |d_l f(z)|<=A/delta; |D^j f(z)|<=c(m,j) A delta^-j for j=1,2,3 (iterated Frechet derivative, operator norm)
CONSTANT_SCOPE: c(m,j) depends only on m,j
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:cauchy-open; shared Lean provider. There: KIND lemma, contract bp:p1:cauchy-open v1. Cited as \Kref{bp:p1:cauchy-open}.

NODE: K:bp:p1:cauchy-strip
KIND: external
TITLE: [K] Cauchy estimate on strips
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cauchy-strip@L568-L574
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:cauchy-strip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic and bounded on T_rho; 0<delta<rho; u scalar, vector (max norm) or matrix (operator norm) valued
SOURCE_QUANTIFIERS: rho, delta, u; every ell
SOURCE_CONCLUSION: ||d_ell u||_{rho-delta} <= delta^-1 ||u||_rho and ||Du||_{rho-delta} <= n delta^-1 ||u||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:cauchy-strip; shared Lean provider. There: KIND lemma, contract bp:p1:cauchy-strip v1. Cited as \Kref{bp:p1:cauchy-strip}.

NODE: K:bp:p1:cohomological
KIND: external
TITLE: [K] Cohomological equation on strips
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L887-L897
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:cohomological
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega in Dio_{gamma,tau}, gamma>0, tau>=0; g holomorphic, bounded, 1-periodic on T_rho with avg(g)=0; 0<delta<rho; g real on real points (for realness); vector/matrix valued componentwise
SOURCE_QUANTIFIERS: fixed dimension n under the corpus conventions, and tau>=0; a constant c(n,tau) depending only on these; then every gamma>0, rho>0, Diophantine omega, datum g as stated and 0<delta<rho; then the unique zero-average solution u
SOURCE_CONCLUSION: there is a unique u holomorphic and 1-periodic on T_{rho-delta} (no boundedness assumed) with avg(u)=0 and Du(theta) omega=g(theta); u is bounded and ||u||_{rho-delta} <= c(n,tau) gamma^-1 delta^-(tau+n) ||g||_rho; u real on real points if g is
CONSTANT_SCOPE: c(n,tau) depends only on n and tau (not on gamma, rho, delta, omega, g)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:cohomological; shared Lean provider. There: KIND lemma, contract bp:p1:cohomological v1. Cited as \Kref{bp:p1:cohomological}.

NODE: K:bp:p1:ext-banach
KIND: external
TITLE: [K] Banach's fixed point theorem
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-banach@L95-L96
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:ext-banach
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a contraction of a nonempty complete metric space
SOURCE_QUANTIFIERS: the metric space and contraction arbitrary
SOURCE_CONCLUSION: the contraction has a fixed point
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: external input of the track-K graph, node bp:p1:ext-banach (Mathlib-level; not re-proved there either); shared Lean provider. There: KIND external, contract bp:p1:ext-banach v1. Cited as \Kref{bp:p1:ext-banach}.

NODE: K:bp:p1:ext-cramer
KIND: external
TITLE: [K] Cramer's rule
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-cramer@L97-L99
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:ext-cramer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M a square matrix with det M != 0
SOURCE_QUANTIFIERS: M arbitrary
SOURCE_CONCLUSION: M is invertible and M^-1=(det M)^-1 adj M; entries of adj M and det M are polynomials with integer coefficients in the entries of M
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: external input of the track-K graph, node bp:p1:ext-cramer (Mathlib-level; not re-proved there either); shared Lean provider. There: KIND external, contract bp:p1:ext-cramer v1. Cited as \Kref{bp:p1:ext-cramer}.

NODE: K:bp:p1:ext-integral
KIND: external
TITLE: [K] Integrals
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-integral@L82-L86
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:ext-integral
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: continuous function on a compact box; phi in C^1([a,b]); F W-valued with any norm on W; uniformly convergent series of continuous functions on a box; dominated convergence setting
SOURCE_QUANTIFIERS: the objects named in each clause
SOURCE_CONCLUSION: continuous function on a compact box is integrable and Fubini applies; int_a^b phi'=phi(b)-phi(a); |int F|<=int|F|; term-by-term integration of a uniformly convergent series of continuous functions on a box; dominated convergence theorem holds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: external input of the track-K graph, node bp:p1:ext-integral (Mathlib-level; not re-proved there either); shared Lean provider. There: KIND external, contract bp:p1:ext-integral v1. Cited as \Kref{bp:p1:ext-integral}.

NODE: K:bp:p1:ext-mvt
KIND: external
TITLE: [K] Mean value inequality
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-mvt@L75-L78
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:ext-mvt
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: C a convex subset of a real or complex normed space; f differentiable at every point of C; |Df|<=A on C
SOURCE_QUANTIFIERS: C, f, A fixed; then x,y in C
SOURCE_CONCLUSION: |f(y)-f(x)|<=A|y-x|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: external input of the track-K graph, node bp:p1:ext-mvt (Mathlib-level; not re-proved there either); shared Lean provider. There: KIND external, contract bp:p1:ext-mvt v1. Cited as \Kref{bp:p1:ext-mvt}.

NODE: K:bp:p1:hamiltonian-real
KIND: external
TITLE: [K] Real and complex Hamiltonian fields
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:hamiltonian-real@L1073-L1079
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:hamiltonian-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V open in C^n x C^n; h holomorphic on V and real at real points of V; z in V cap (R^n x R^n); H:R^n x R^n->R agrees with Re h near z; (second claim) phi holomorphic; X_H frozen vector field, J=-Omega_0
SOURCE_QUANTIFIERS: for all V, h, z, H; for all holomorphic phi
SOURCE_CONCLUSION: H differentiable at z and X_H(z)=X_h(z); X_phi=J (Dphi)^T with J=[[0,I],[-I,0]]=-Omega_0, equivalently Omega_0 X_phi=(Dphi)^T
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:hamiltonian-real; shared Lean provider. There: KIND lemma, contract bp:p1:hamiltonian-real v1. Cited as \Kref{bp:p1:hamiltonian-real}.

NODE: K:bp:p1:holomorphic-analytic
KIND: external
TITLE: [K] Holomorphic maps are analytic
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L296-L312
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:holomorphic-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U in C^m open; F:U->W holomorphic; (a) z_0 in U, r>0 with P-bar(z_0,r) in U, A=max_{P-bar(z_0,r)}|F|; (b) U_R=U cap R^m, x_0 in U_R; W=C^p and F(U_R) in R^p for the real clause
SOURCE_QUANTIFIERS: F,U,W,m; then z_0,r (A determined); alpha in N^m
SOURCE_CONCLUSION: (a) exist c_alpha in W with |c_alpha|<=A r^-|alpha| and F(z)=sum_alpha c_alpha (z-z_0)^alpha on P(z_0,r), absolutely convergent; F analytic on U; (b) F|U_R real-analytic near each x_0 (power series in x-x_0, absolutely convergent); real coefficients if W=C^p and F(U_R) in R^p
CONSTANT_SCOPE: c_alpha depends on F,z_0,r only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:holomorphic-analytic; shared Lean provider. There: KIND lemma, contract bp:p1:holomorphic-analytic v1. Cited as \Kref{bp:p1:holomorphic-analytic}.

NODE: K:bp:p1:holomorphic-inverse
KIND: external
TITLE: [K] Holomorphic inverse
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-inverse@L404-L407
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:holomorphic-inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A holomorphic matrix-valued function on an open set V with det A != 0 there
SOURCE_QUANTIFIERS: A:V->C^{p x p}, V open
SOURCE_CONCLUSION: A^-1 is holomorphic on V and D(A^-1)=-A^-1 (DA) A^-1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:holomorphic-inverse; shared Lean provider. There: KIND lemma, contract bp:p1:holomorphic-inverse v1. Cited as \Kref{bp:p1:holomorphic-inverse}.

NODE: K:bp:p1:holomorphic-regularity
KIND: external
TITLE: [K] Derivatives of holomorphic maps
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-regularity@L227-L236
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:holomorphic-regularity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U in C^m open; F:U->W holomorphic
SOURCE_QUANTIFIERS: U,F,W,m arbitrary; z in U; v,w in C^m; j>=1
SOURCE_CONCLUSION: DF:U->L(C^m,W) holomorphic; D^jF exists and is holomorphic for every j>=1, F is C^infty; |D^{j+1}F(z)|=|D^j(DF)(z)|=|D(D^jF)(z)|; D^2F(z)[v,w]=D^2F(z)[w,v]; d_i d_j F=d_j d_i F on U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:holomorphic-regularity; shared Lean provider. There: KIND lemma, contract bp:p1:holomorphic-regularity v1. Cited as \Kref{bp:p1:holomorphic-regularity}.

NODE: K:bp:p1:increments-open
KIND: external
TITLE: [K] Increments on open sets
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:increments-open@L425-L428
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:increments-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F holomorphic on open U in C^m; |DF|<=A on U; segment [z,z+w] in U
SOURCE_QUANTIFIERS: U,F,A; z,w
SOURCE_CONCLUSION: |F(z+w)-F(z)|<=A|w|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:increments-open; shared Lean provider. There: KIND lemma, contract bp:p1:increments-open v1. Cited as \Kref{bp:p1:increments-open}.

NODE: K:bp:p1:iteration
KIND: external
TITLE: [K] Quadratic iteration on nested strips
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:iteration@L1009-L1014
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:iteration
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q>0; p>=0; reals y_0,y_1,...>=0 with y_{m+1}<=Q 2^{pm} y_m^2 for all m>=0; Q 2^p y_0<=1/2 (second claim: only q:=Q 2^p y_0<=1)
SOURCE_QUANTIFIERS: for all Q>0, p>=0, sequences (y_m) satisfying the recursion; then for all m>=0
SOURCE_CONCLUSION: y_m<=Q^{-1} 2^{-p(m+1)} 2^{-2^m} for all m>=0 (so y_m->0); under q<=1 only: y_m<=q^{2^m-1} 2^{-pm} y_0 for all m>=0
CONSTANT_SCOPE: none (Q, p, y_0 arbitrary; no constants introduced)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:iteration; shared Lean provider. There: KIND lemma, contract bp:p1:iteration v1. Cited as \Kref{bp:p1:iteration}.

NODE: K:bp:p1:matrix-norms
KIND: external
TITLE: [K] Max-norm matrix facts
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:matrix-norms@L148-L153
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:matrix-norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: norm |M|=max_i sum_j |M_ij|
SOURCE_QUANTIFIERS: M,N matrices of compatible sizes, v vector; M of size m x m' for the transpose bound; M of size 2n x q resp. p x 2n; M_1,M_2 stacked
SOURCE_CONCLUSION: |MN|<=|M||N|; |Mv|<=|M||v|; |M^T|<=m|M| (m x m' matrices); |Omega_0 M|=|M| (2n x q); |M Omega_0|=|M| (p x 2n); |(M_1;M_2)|=max{|M_1|,|M_2|}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:matrix-norms; shared Lean provider. There: KIND lemma, contract bp:p1:matrix-norms v1. Cited as \Kref{bp:p1:matrix-norms}.

NODE: K:bp:p1:neumann
KIND: external
TITLE: [K] Neumann series
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:neumann@L177-L181
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:neumann
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A invertible; |A^-1||Delta|<=1/2; for the pointwise version A(theta), Delta(theta) matrix-valued with sup norms
SOURCE_QUANTIFIERS: A,Delta square matrices of the same size; pointwise version for theta in a set
SOURCE_CONCLUSION: A+Delta invertible, |(A+Delta)^-1|<=2|A^-1|, |(A+Delta)^-1-A^-1|<=2|A^-1|^2|Delta|; same pointwise for matrix-valued functions with sup norms
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:neumann; shared Lean provider. There: KIND lemma, contract bp:p1:neumann v1. Cited as \Kref{bp:p1:neumann}.

NODE: K:bp:p1:real-inverse
KIND: external
TITLE: [K] Real inverses
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:real-inverse@L205-L208
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:real-inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A an invertible real matrix; A(theta) real for real theta and invertible
SOURCE_QUANTIFIERS: A, theta arbitrary
SOURCE_CONCLUSION: A^-1 is real; A(theta)^-1 real for real theta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:real-inverse; shared Lean provider. There: KIND lemma, contract bp:p1:real-inverse v1. Cited as \Kref{bp:p1:real-inverse}.

NODE: K:bp:p1:real-restriction
KIND: external
TITLE: [K] Real restriction
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:real-restriction@L1047-L1051
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:real-restriction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; rho>0; K holomorphic on T_rho and real on reals; for the primary claim, K primary on T_rho (p=2n)
SOURCE_QUANTIFIERS: n>=1, rho>0, p and K as stated; then every x in R^n and m in Z^n
SOURCE_CONCLUSION: k=K|_{R^n} real-analytic with real derivative the restriction of the complex derivative; |Dk(x)|<=|DK(x)| for x in R^n; if K primary, k(x+m)=k(x)+(m,0) for m in Z^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-review-I-imports
REVIEWER: sol-delta-I-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:real-restriction; shared Lean provider. There: KIND lemma, contract bp:p1:real-restriction v1. Cited as \Kref{bp:p1:real-restriction}. Source premises also include conventions blueprint/parts/p1-analysis.tex@L37-L39.

NODE: K:bp:p1:taylor
KIND: external
TITLE: [K] Second-order Taylor bound
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:taylor@L436-L439
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F holomorphic on open U in C^m; |D^2F|<=A on U; segment [z,z+w] in U
SOURCE_QUANTIFIERS: U,F,A; z,w
SOURCE_CONCLUSION: |F(z+w)-F(z)-DF(z)w|<=(A/2)|w|^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:taylor; shared Lean provider. There: KIND lemma, contract bp:p1:taylor v1. Cited as \Kref{bp:p1:taylor}.

NODE: K:bp:p1:uniform-limits
KIND: external
TITLE: [K] Uniform limits
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:uniform-limits@L364-L368
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:uniform-limits
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K_s holomorphic on an open set V; K_s->K pointwise on V; DK_s->Lambda uniformly on V; for the strip clauses: n>=1, r>0, V=T_r, and every K_s primary on T_r, respectively real on reals
SOURCE_QUANTIFIERS: V,K_s,K,Lambda; sequence index s; for the additional strip clauses, n>=1 and r>0
SOURCE_CONCLUSION: K holomorphic on V and DK=Lambda; if V=T_r and all K_s primary (resp. real on reals) then K is primary (resp. real on reals)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-review-I-imports
REVIEWER: sol-delta-I-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:uniform-limits; shared Lean provider. There: KIND lemma, contract bp:p1:uniform-limits v1. Cited as \Kref{bp:p1:uniform-limits}. Source premises also include conventions blueprint/parts/p1-analysis.tex@L37-L39.

NODE: K:bp:p2:admissible
KIND: external
TITLE: [K] Admissible parameterization
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:admissible@L306-L317
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:admissible
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r>0, beta>0, 0<=epsilon<=1; the standing data of Part 2 (B(frak), sigma_K, sigma_B, sigma_T)
SOURCE_QUANTIFIERS: for all r,beta,epsilon, K:C^n->C^n x C^n
SOURCE_CONCLUSION: defines (r,beta,epsilon)-admissible: (A1) K holomorphic, primary and real on reals on T_r; (A2) B_beta(K(theta)) subset B(frak) for all theta in T_r; (A3) |DK|<=sigma_K on T_r; (A4) det G != 0 and |B|<=sigma_B on T_r; (A5) avg T invertible and |avg T^{-1}|<=sigma_T; (A6) |E|<=epsilon on T_r
CONSTANT_SCOPE: none (definition; uses sigma_K,sigma_B,sigma_T of the standing data)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:admissible; shared Lean provider. There: KIND definition, contract bp:p2:admissible v1. Cited as \Kref{bp:p2:A2}, \Kref{bp:p2:A3}, \Kref{bp:p2:A4}, \Kref{bp:p2:A5}, \Kref{bp:p2:A6}.

NODE: K:bp:p2:averages
KIND: external
TITLE: [K] Averages
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:averages@L158-L167
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:averages
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (a) f: R^n->C^{pxq} continuous and 1-periodic; (b) v holomorphic and 1-periodic on T_r (not necessarily bounded), values in C, C^p or C^{pxq}
SOURCE_QUANTIFIERS: for all p,q, r>0, f resp. v; averages over [0,1]^n
SOURCE_CONCLUSION: (a) f integrable on [0,1]^n, avg f linear in f, real if f is, |avg f|<=sup_{[0,1]^n}|f|; (b) avg(d_{theta_l} v)=0 for every l and avg(d_omega v)=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:averages; shared Lean provider. There: KIND corollary, contract bp:p2:averages v1. Cited as \Kref{bp:p2:averages}.

NODE: K:bp:p2:cohomological
KIND: external
TITLE: [K] Cohomological equation in operator norms
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:cohomological@L186-L198
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:cohomological
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<delta<r; Gamma_delta=c_R gamma^{-1} delta^{-kappa}; the standing data of Part 2 (gamma, tau, omega in Dio_{gamma,tau}); (a) g:T_r->C^p holomorphic, 1-periodic, |g|<=H, avg g=0; (b) u:T_r->C^{pxq} holomorphic, 1-periodic, avg u=0, |d_omega u|<=H on T_r
SOURCE_QUANTIFIERS: for all 0<delta<r, p,q, H; g resp. u as stated (outermost: standing data)
SOURCE_CONCLUSION: (a) unique u=Rg holomorphic 1-periodic on T_{r-delta}, avg u=0, d_omega u=g, |u|<=Gamma_delta H, real on reals if g is; (b) |u|<=Gamma_delta H on T_{r-delta}
CONSTANT_SCOPE: c_R depends only on (n,tau); kappa=tau+n; Gamma_delta depends on gamma, delta, n, tau only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:cohomological; shared Lean provider. There: KIND corollary, contract bp:p2:cohomological v1. Cited as \Kref{bp:p2:cohomological}.

NODE: K:bp:p2:constants
KIND: external
TITLE: [K] Exponents and constants
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:constants@L78-L108
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2: n>=2, tau>=n-1, M,sigma_K,sigma_B,sigma_T>0; c(n,tau) from bp:p1:cohomological; for the final definitions mu>0 and 0<rho_inf<rho
SOURCE_QUANTIFIERS: for the data (n,tau,M,sigma_K,sigma_B,sigma_T) in order; then for mu>0 and 0<rho_inf<rho
SOURCE_CONCLUSION: defines, in order: kappa=tau+n; a=2kappa+2; c_R=max{1,c(n,tau)}; m=max{1,M,sigma_K,sigma_B,sigma_T}; Theta=4n m^3; C_X=5n^2 m^5; C_T=2n m^2 C_X; C_Omega=2n(n+1)c_R m; C_sym=m^2 C_Omega; C_red=2n(n+1)m^2; C_xi0=2n m^2(m Theta+c_R C_T); C_xiN=C_xi0+2n c_R m; C_g=C_T C_xiN+2n m^2 Theta; C_xi=c_R C_g+Theta C_xiN; C_DeltaK=2m^2 C_xi; C_lin=C_red C_xi+C_sym C_g; C_E=4m^2 Theta^2 C_lin+m C_DeltaK^2; C_G=6n^2 m; C_B=2m^2 C_G; C_DeltaN=2n m+m C_B; C_DeltaX=2m^3+(m+n Theta)C_DeltaN; C_DeltaT=4n m^2 C_DeltaX+2n C_DeltaN C_X; c_step=2Theta^4 max{C_sym,2m C_DeltaT C_DeltaK}; c_sum=4Theta^2 C_DeltaK max{n,C_B,m^2 C_DeltaT}; all preceding constants >=1; c_*=max{2^{2a}C_E,c_step max{1,2/mu},2c_sum/mu}; delta_0=min{1,(rho-rho_inf)/8} in (0,1]
CONSTANT_SCOPE: kappa,a,c_R,m,Theta,C_* and c_step,c_sum depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); c_* = c_*(n,tau,M,sigma_K,sigma_B,sigma_T,mu); delta_0 = delta_0(rho,rho_inf)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-review-I-imports
REVIEWER: sol-delta-I-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:constants; shared Lean provider. There: KIND definition, contract bp:p2:constants v1. Cited as \Kref{bp:p2:constants}.

NODE: K:bp:p2:exactness
KIND: external
TITLE: [K] Exactness: two vanishing averages
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:exactness@L515-L523
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:exactness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); K holomorphic and primary on T_r with K(T_r) subset B(frak); for eta^N: det G != 0
SOURCE_QUANTIFIERS: for all r>0, K as stated
SOURCE_CONCLUSION: avg Omega_K=0 and avg(L^T Omega_0 E)=0, i.e. avg eta^N=0 when det G != 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:exactness; shared Lean provider. There: KIND lemma, contract bp:p2:exactness v1. Cited as \Kref{bp:p2:exactness}.

NODE: K:bp:p2:frame-basic
KIND: external
TITLE: [K] Regularity and bounds of the frame
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:frame-basic@L382-L398
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:frame-basic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); K holomorphic on T_r satisfying (A2)-(A4) (primary and real not needed); (c) (A6); (d) |omega|<=Theta, 0<delta<=1, delta<r
SOURCE_QUANTIFIERS: for all r>0, K, epsilon, delta as stated
SOURCE_CONCLUSION: (a) L,G,E,A,Omega_K,B,N,P,X_N,T,E_sym,Q,eta holomorphic on T_r, B symmetric, T continuous on R^n so avg T defined; (b) |L|<=m, |L^T|<=2n m, |B|<=m, |N|<=m^2, |N^T|<=2n m^2, |P|<=2m^2, |A|<=m on T_r; (c) |eta^L|<=2n m^2 epsilon, |eta^N|<=2n m epsilon on T_r; (d) |X_N|<=C_X/delta, |T|<=C_T/delta on T_{r-delta}
CONSTANT_SCOPE: m, C_X, C_T depend only on (n,tau,M,sigma_K,sigma_B,sigma_T)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:frame-basic; shared Lean provider. There: KIND lemma, contract bp:p2:frame-basic v1. Cited as \Kref{bp:p2:frame-basic}.

NODE: K:bp:p2:frame-identities
KIND: external
TITLE: [K] Frame identities
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:frame-identities@L441-L463
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:frame-identities
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); K holomorphic on T_r, K(T_r) subset B(frak), det G != 0 on T_r
SOURCE_QUANTIFIERS: for all r>0, K as stated; identities on T_r
SOURCE_CONCLUSION: (a) L^T Omega_0 N=-I_n, N^T Omega_0 L=I_n, N^T Omega_0 N=B Omega_K B; (b) P^T Omega_0 P=Omega_0+E_sym, E_sym=diag(Omega_K, B Omega_K B); (c) d_omega L=AL-DE; (d) d_omega Omega_K=-(DE)^T Omega_0 L-L^T Omega_0 DE; (e) Q(AP-d_omega P)=Lambda+E_red with Lambda=[[0,T],[0,0]], E_red=[[N^T Omega_0 DE,0],[-L^T Omega_0 DE,(DE)^T Omega_0 N]]; (f) QP=I_{2n}-Omega_0 E_sym and QE=-eta
CONSTANT_SCOPE: none (exact identities)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-review-I-imports
REVIEWER: sol-delta-I-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:frame-identities; shared Lean provider. There: KIND lemma, contract bp:p2:frame-identities v1. Cited as \Kref{bp:p2:frame-identities}.

NODE: K:bp:p2:frequency
KIND: external
TITLE: [K] Frequency bound
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:frequency@L357-L365
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:frequency
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); K satisfies (A3),(A4),(A6) on T_r with epsilon<=1 and K(T_r) subset B(frak)
SOURCE_QUANTIFIERS: for all r>0, epsilon in [0,1], K as stated
SOURCE_CONCLUSION: gamma<=|omega|<=2n sigma_K sigma_B (M+epsilon)<=Theta
CONSTANT_SCOPE: gamma, omega from the standing data; Theta=4n m^3 depends only on (n,M,sigma_K,sigma_B,sigma_T)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:frequency; shared Lean provider. There: KIND lemma, contract bp:p2:frequency v1. Cited as \Kref{bp:p2:frequency}.

NODE: K:bp:p2:frozen-agreement
KIND: external
TITLE: [K] Agreement with the frozen definitions
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:frozen-agreement@L295-L304
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:frozen-agreement
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: on the open strip T_r: the objects of bp:p2:objects; det G a unit where inverse is used; T continuous on R^n for avg T
SOURCE_QUANTIFIERS: for all r>0, K as in bp:p2:objects; frozen definitions in their stated arguments
SOURCE_CONCLUSION: the frozen gramMatrix, normalFrame, torsion, invarianceError coincide with G, N, T, E; the frozen matrix inverse is the true inverse where det is a unit; the frozen torsionAverage equals avg T at real points; each use of B,N,T is preceded by det G != 0 and each use of avg T by continuity of T on R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:frozen-agreement; shared Lean provider. There: KIND claim, contract bp:p2:frozen-agreement v1. Cited as \Kref{bp:p2:frozen-agreement}.

NODE: K:bp:p2:hamiltonian
KIND: external
TITLE: [K] The Hamiltonian vector field
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:hamiltonian@L214-L230
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:hamiltonian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing)
SOURCE_QUANTIFIERS: z in B(frak), k in Z^n, beta>0, w with |w|<beta and B_beta(z) subset B(frak); M from the standing data
SOURCE_CONCLUSION: (a) X_h holomorphic, DX_h and D^2X_h exist, |D(DX_h)|=|D^2X_h|<=M; (b) X_h and DX_h are invariant under z->z+(k,0); (c) X_h,DX_h real at real z; (d) Omega_0 X_h=(Dh)^T, Omega_0 DX_h symmetric, DX_h^T Omega_0+Omega_0 DX_h=0; (e) |DX_h(z+w)-DX_h(z)|<=M|w| and |X_h(z+w)-X_h(z)-DX_h(z)w|<=M|w|^2
CONSTANT_SCOPE: constants are M and the standing data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:hamiltonian; shared Lean provider. There: KIND lemma, contract bp:p2:hamiltonian v1. Cited as \Kref{bp:p2:hamiltonian}.

NODE: K:bp:p2:matrix
KIND: external
TITLE: [K] Matrix norms
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:matrix@L122-L139
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:matrix
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standard matrix and vector norms (max norm on vectors, |M|=max_i sum_j |M_ij|, operator norm on bilinear/matrix maps); Omega_0 the canonical 2n x 2n matrix
SOURCE_QUANTIFIERS: for all p,q and all p x q complex matrices M, M_1, M_2, M_ij, vectors v; block matrices conformal; matrices U_1,U_2 with n rows
SOURCE_CONCLUSION: (a) max|M_ij|<=|M|=sup_{|v|<=1}|Mv| and |M^T|<=p|M|; (b) |M_1M_2|<=|M_1||M_2|, |Mv|<=|M||v|; (c) |(M_1 M_2)|<=|M_1|+|M_2|; |[[M_11,M_12],[M_21,M_22]]|<=max{|M_11|+|M_12|,|M_21|+|M_22|}; |diag(M_1,M_2)|=max{|M_1|,|M_2|}; (d) Omega_0^T=-Omega_0=Omega_0^{-1}, Omega_0^2=-I, Omega_0^T Omega_0=I, |Omega_0|=1, Omega_0(U_1;U_2)=(-U_2;U_1)
CONSTANT_SCOPE: none (constants are absolute, no parameters)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-review-I-imports
REVIEWER: sol-delta-I-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:matrix; shared Lean provider. There: KIND corollary, contract bp:p2:matrix v1. Cited as \Kref{bp:p2:matrix}.

NODE: K:bp:p2:objects
KIND: external
TITLE: [K] Objects attached to a parameterization
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:objects@L270-L293
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:objects
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r>0; K:C^n->C^n x C^n holomorphic on T_r with K(T_r) subset B(frak) (data of the standing package); for the second group det G != 0 on T_r; for avg T, T continuous on R^n
SOURCE_QUANTIFIERS: for all r>0, K, theta in T_r; the standing data fixed outermost
SOURCE_CONCLUSION: defines L=DK, G=L^T L, E=X_h o K - L omega, A=DX_h o K, Omega_K=L^T Omega_0 L; and where det G != 0: B=G^{-1}, N=Omega_0 L B, P=(L N), X_N=AN-d_omega N, T=N^T Omega_0 X_N, E_sym=P^T Omega_0 P-Omega_0, Q=-Omega_0 P^T Omega_0, eta=Omega_0 P^T Omega_0 E=(eta^L;eta^N)=(-N^T Omega_0 E; L^T Omega_0 E); avg T=int_{[0,1]^n} T
CONSTANT_SCOPE: none (definitions; depend on K, h, omega only)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:objects; shared Lean provider. There: KIND definition, contract bp:p2:objects v1. Cited as \Kref{bp:p2:objects}.

NODE: K:bp:p2:periodicity
KIND: external
TITLE: [K] Periodicity and realness of the attached objects
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:periodicity@L324-L333
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:periodicity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); K holomorphic and primary on T_r with K(T_r) subset B(frak); for B,N,P,X_N,T,E_sym,eta: det G != 0 on T_r; for realness: K real on reals
SOURCE_QUANTIFIERS: for all r>0, K as stated
SOURCE_CONCLUSION: L,G,E,A,Omega_K,h o K, K^I and f_j=(K^I)^T d_{theta_j}K^theta (j=1..n) are 1-periodic on T_r; if det G != 0 then B,N,P,X_N,T,E_sym,eta are 1-periodic; if also K real on reals, all these objects and avg T are real at real points
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:periodicity; shared Lean provider. There: KIND lemma, contract bp:p2:periodicity v1. Cited as \Kref{bp:p2:periodicity}.

NODE: K:bp:p2:standing
KIND: external
TITLE: [K] Standing data of Part~\ref{bp:p2}
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:standing@L56-L65
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p2:standing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (this is the package of typing data)
SOURCE_QUANTIFIERS: fixed once for all of Part 2 (outermost): n>=2, tau>=n-1, M,sigma_K,sigma_B,sigma_T>0, B(frak) open in C^n x C^n invariant under (theta,I)->(theta+k,I), h, gamma>0, omega
SOURCE_CONCLUSION: defines the standing data: h holomorphic on B(frak), 1-periodic in theta, real at real points; |X_h|,|DX_h|,|D^2X_h| <= M on B(frak) (bilinear operator norm for D^2X_h); gamma>0 and omega in Dio_{gamma,tau}
CONSTANT_SCOPE: M, sigma_K, sigma_B, sigma_T, n, tau, gamma, omega, h, B(frak) are fixed for all of Part 2; nothing depends on later quantities
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p2:standing; shared Lean provider. There: KIND definition, contract bp:p2:standing v1. Cited as \Kref{bp:p2:standing}.

NODE: K:bp:p4:data
KIND: external
TITLE: [K] Shrunken domains and basic constants
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:data@L138-L163
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p4:data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=2, tau>n-1, s0,r0>0; B open bounded nonempty; h holomorphic on B_{r0} and real at real points; fixed witnesses L_h of the inverse frequency inequality on closure B and C_B of the boundary-layer inequality; f and epsilon as in HEAD
SOURCE_QUANTIFIERS: first fix n>=2, tau>n-1, s0,r0>0, B,h,L_h,C_B as in HEAD; then f,epsilon as in HEAD; define the displayed constants and domains from fixed data, independently of f,epsilon; for each I* in R^n define K^0_{I*}
SOURCE_CONCLUSION: defines L_+=max(L_h,1), C_B^+=max(C_B,0), s=min(s0,1), delta_*=min(s,r0)/4, mu=delta_*/2, D=T_{s/2} x B_{r0/2}, D'=T_{3s/4} x B_{3r0/4}, cbar=max{1,c(n,j),c(2n,j):j=1,2,3}, and the unperturbed torus K^0_{I*}(theta)=(theta,iota I*); hbold(theta,I)=h(I)+f(theta,I) on D(s0,r0), realHamiltonian h f=Re hbold at real points
CONSTANT_SCOPE: all constants depend only on n,tau,s0,r0,B,h,L_h,C_B
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-review-I-imports
REVIEWER: sol-delta-I-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p4:data; shared Lean provider. There: KIND definition, contract bp:p4:data v1. Cited as \Kref{bp:p4:data}.

NODE: K:bp:p4:derivative-bounds
KIND: external
TITLE: [K] Derivative bounds
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:derivative-bounds@L183-L195
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p4:derivative-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of HEAD; shrunken domains of Definition data; (d) additionally eps<=1
SOURCE_QUANTIFIERS: H_j=cbar M_h delta_*^{-j}, F_j=cbar delta_*^{-j} (j=1,2,3), M=cbar(M_h+1)delta_*^{-3}; z, I points
SOURCE_CONCLUSION: (a) polydiscs of radius delta_* around D lie in D' and around B_{r0/2} in B_{3r0/4}; (b) |D^j h|<=H_j on B_{r0/2}; (c) |D^j f|<=F_j eps on D, |X_f|<=F_1 eps, |DX_f|<=F_2 eps; (d) if eps<=1, |Dh~|,|X_h~|,|DX_h~|,|D^2 X_h~|<=M on D
CONSTANT_SCOPE: H_j,F_j,M depend only on the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p4:derivative-bounds; shared Lean provider. There: KIND lemma, contract bp:p4:derivative-bounds v1. Cited as \Kref{bp:p4:derivative-bounds}.

NODE: K:bp:p4:freq-map
KIND: external
TITLE: [K] The frequency map
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:freq-map@L225-L237
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p4:freq-map
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: fixed HEAD data of Section sec-data; U={I real : iota I in B_{r0}}, g=frequencyMap h; H_1,H_2 are defined constants, not assumed derivative estimates
SOURCE_QUANTIFIERS: fixed HEAD data; U={I in R^n : iota I in B_{r0}}, g=frequencyMap h; (ii),(iii) for every I in U; (iv) for every real I with iota I in B_{r0/2}; (v) for every pair I,J in B
SOURCE_CONCLUSION: (i) U open and closure B subset U; (ii) for I in U, all partial_i h(iota I) are real and g(I)=(partial_i h(iota I))_i; (iii) g differentiable on U with Dg(I) the real symmetric Hessian there; (iv) for iota I in B_{r0/2}, |g(I)|<=H_1 and |Hessian h(iota I)|<=H_2; (v) g is Lambda_g-Lipschitz on B, Lambda_g=max(H_2,2H_1/delta_*), and |omega|<=W_inf=H_1 for omega in g(B)
CONSTANT_SCOPE: Lambda_g, W_inf depend only on the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p4:freq-map; shared Lean provider. There: KIND lemma, contract bp:p4:freq-map v1. Cited as \Kref{bp:p4:freq-map}.

NODE: K:bp:p4:h-bounded
KIND: external
TITLE: [K] $h$ is bounded on a shrunken neighbourhood
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:h-bounded@L168-L170
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p4:h-bounded
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of HEAD
SOURCE_QUANTIFIERS: M_h
SOURCE_CONCLUSION: M_h:=sup{|h(I)| : I in B_{3r0/4}} is finite
CONSTANT_SCOPE: M_h depends only on the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p4:h-bounded; shared Lean provider. There: KIND lemma, contract bp:p4:h-bounded v1. Cited as \Kref{bp:p4:h-bounded}.

NODE: K:bp:p4:h1
KIND: external
TITLE: [K] The Hamiltonian hypothesis H1
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:h1@L309-L313
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p4:h1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eps<=1; the data of HEAD; D and h~=h+f
SOURCE_QUANTIFIERS: (D,h~)
SOURCE_CONCLUSION: D and h~ satisfy the H1 block of G1 and G2 (D open, Z^n-invariant in theta; h~ holomorphic, periodic, real; four derivative bounds by M) with M of derivative-bounds
CONSTANT_SCOPE: M depends only on the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p4:h1; shared Lean provider. There: KIND lemma, contract bp:p4:h1 v1. Cited as \Kref{bp:p4:h1}.

NODE: K:step:p2:ham-real
KIND: external
TITLE: [K] Realness
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ham-real@L243-L246
PROOF_SOURCE: -
CONTRACT_ID: K:step:p2:ham-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing): h real at real points of B(frak)
SOURCE_QUANTIFIERS: real z in B(frak)
SOURCE_CONCLUSION: Dh, X_h and DX_h are real at real points
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node step:p2:ham-real; shared Lean provider. There: KIND step, contract step:p2:ham-real v1. Cited as \Kref{step:p2:ham-real}.

NODE: K:step:p2:pt-small
KIND: external
TITLE: [K] Consequences of the smallness
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-small@L823-L832
PROOF_SOURCE: -
CONTRACT_ID: K:step:p2:pt-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d<β, 2𝔪C_ΔTd/δ²≤1, δ≤1; definitions of the constants
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: C_ΔT≥max{n,C_G,C_ΔN}; nd/δ≤1/(2𝔪)≤𝔪, 𝔪C_Gd/δ≤1/2, C_ΔNd/δ≤1/(2𝔪)≤𝔪², 𝔪C_ΔTd/δ²≤1/2
CONSTANT_SCOPE: constants of bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node step:p2:pt-small; shared Lean provider. There: KIND step, contract step:p2:pt-small v1. Cited as \Kref{step:p2:pt-small}.

NODE: K:step:p4:db-cauchy
KIND: external
TITLE: [K] Cauchy estimates
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:db-cauchy@L204-L208
PROOF_SOURCE: -
CONTRACT_ID: K:step:p4:db-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed HEAD data and perturbation f,epsilon of bp:p4:data (L138-L163), with h holomorphic on B_{r0} and f holomorphic, periodic, real and |f|<=epsilon on D(s0,r0); shrunken domains, delta_*,cbar from bp:p4:data; M_h defined as sup{|h(I)|:I in B_{3r0/4}}; H_j=cbar M_h delta_*^{-j}, F_j=cbar delta_*^{-j} as in the parent derivative-bounds lemma; neither polydisc containment nor boundedness of h is an additional premise
SOURCE_QUANTIFIERS: HEAD data fixed first; then f,epsilon as in HEAD; j=1,2,3, I in B_{r0/2}, z in D
SOURCE_CONCLUSION: |D^j h(I)|<=H_j; |D^j f(z)|<=F_j epsilon; |D^j hbold(z)|<=cbar(M_h+epsilon)delta_*^{-j}, where hbold(theta,I)=h(I)+f(theta,I); delta_*<=1 gives delta_*^{-j}<=delta_*^{-3}
CONSTANT_SCOPE: delta_*,cbar,M_h,H_j,F_j depend only on the fixed HEAD data (n,tau,s0,r0,B,h,L_h,C_B); no new constant is chosen
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-review-I-imports
REVIEWER: sol-delta-I-e
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node step:p4:db-cauchy; shared Lean provider. There: KIND step, contract step:p4:db-cauchy v1. Cited as \Kref{step:p4:db-cauchy}. Source premises also include parent blueprint/parts/p4-measure.tex@L138-L195.

NODE: K:step:p4:h1-holo
KIND: external
TITLE: [K] Holomorphy, periodicity, reality
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:h1-holo@L321-L327
PROOF_SOURCE: -
CONTRACT_ID: K:step:p4:h1-holo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h holomorphic on B_{r0}, real at real points; f holomorphic, 1-periodic, real on D(s0,r0)
SOURCE_QUANTIFIERS: z in D, k in Z^n
SOURCE_CONCLUSION: h~ holomorphic on D, periodic in theta, real at real points of D
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node step:p4:h1-holo; shared Lean provider. There: KIND step, contract step:p4:h1-holo v1. Cited as \Kref{step:p4:h1-holo}.

NODE: K:step:p4:h1-open
KIND: external
TITLE: [K] Openness and invariance
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:h1-open@L316-L319
PROOF_SOURCE: -
CONTRACT_ID: K:step:p4:h1-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D=T_{s/2} x B_{r0/2}
SOURCE_QUANTIFIERS: k in Z^n
SOURCE_CONCLUSION: D open and Z^n-invariant in theta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node step:p4:h1-open; shared Lean provider. There: KIND step, contract step:p4:h1-open v1. Cited as \Kref{step:p4:h1-open}.

NODE: N:bpN:p3:gen-continuation-periodic
KIND: external
TITLE: [N] Closed sets, periodic fields
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-continuation-periodic@L297-L299
PROOF_SOURCE: -
CONTRACT_ID: N:bpN:p3:gen-continuation-periodic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E = R^n x R^n; U subset R^n open; W = R^n x U; F C^1 on W with F(theta+k,I) = F(theta,I) for k in Z^n; z the maximal solution through x0 in W (Theorem bpN:p3:gen-maximal), maximal interval (T_-,T_+); z(t)_2 in K for t in [t_*,T_+) (some t_* in [0,T_+)) with K subset U compact
SOURCE_QUANTIFIERS: n, U, F, x0, K, t_* fixed
SOURCE_CONCLUSION: T_+ = +infinity; likewise on the left (T_- = -infinity when z(t)_2 stays in a compact subset of U on (T_-,t_*]); the angle components z(t)_1 may be unbounded
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-global-I
REVIEWER: sol-delta-I-global
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED (pending N graph): source result of track N, node bpN:p3:gen-continuation-periodic; shared Lean provider. Cited as \Nref{bpN:p3:gen-continuation-periodic}. Owning-node retention is not certified: docs/graph/N/DEPGRAPH.md is absent. Re-check against its assembled root closure before treating this as a valid retained N import; if excluded, resolve track-I ownership under SPEC.

NODE: N:bpN:p3:gen-maximal
KIND: external
TITLE: [N] Maximal solution
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-maximal@L251-L258
PROOF_SOURCE: -
CONTRACT_ID: N:bpN:p3:gen-maximal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E a finite-dimensional real normed space; F C^1 on the open set W; x0 in W
SOURCE_QUANTIFIERS: F, W, x0 fixed; there exist T_- in [-infinity,0), T_+ in (0,+infinity] and z : R -> E
SOURCE_CONCLUSION: z(0) = x0, IsSolIn F W (T_-,T_+) z, and every solution y with y(0) = x0 on an interval J containing 0 satisfies J subset (T_-,T_+) and y = z on J; the maximal interval and the maximal solution are unique
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-global-I
REVIEWER: sol-delta-I-global
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED (pending N graph): source result of track N, node bpN:p3:gen-maximal; shared Lean provider. Cited as \Nref{bpN:p3:gen-maximal}. Owning-node retention is not certified: docs/graph/N/DEPGRAPH.md is absent. Re-check against its assembled root closure before treating this as a valid retained N import; if excluded, resolve track-I ownership under SPEC.

NODE: N:bpN:p3:gen-sol
KIND: external
TITLE: [N] Solutions in $W$
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-sol@L88-L93
PROOF_SOURCE: -
CONTRACT_ID: N:bpN:p3:gen-sol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F : E -> E (total); W subset E; J subset R; z : R -> E (typing data)
SOURCE_QUANTIFIERS: F, W, J, z
SOURCE_CONCLUSION: defines IsSolIn F W J z: for every t in J, z(t) in W and z has the two-sided derivative F(z(t)) at t (HasDerivAt); not a frozen declaration
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-global-I
REVIEWER: sol-delta-I-global
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED (pending N graph): source result of track N, node bpN:p3:gen-sol; shared Lean provider. Cited as \Nref{bpN:p3:gen-sol}. Owning-node retention is not certified: docs/graph/N/DEPGRAPH.md is absent. Re-check against its assembled root closure before treating this as a valid retained N import; if excluded, resolve track-I ownership under SPEC.

NODE: N:bpN:p3:gen-uniqueness
KIND: external
TITLE: [N] Uniqueness on arbitrary intervals
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-uniqueness@L217-L224
PROOF_SOURCE: -
CONTRACT_ID: N:bpN:p3:gen-uniqueness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E a finite-dimensional real normed space; F C^1 on the open set W; J subset R an interval of any kind (open, closed, half-open, unbounded or a point); t0 in J; y1, y2 : R -> E with IsSolIn F W J y_i (i = 1, 2) and y1(t0) = y2(t0)
SOURCE_QUANTIFIERS: F, W, J, t0, y1, y2 fixed
SOURCE_CONCLUSION: y1 = y2 on J (no confinement, boundedness or smallness of either solution assumed); in particular solutions on intervals J1, J2 that agree at one point of J1 cap J2 agree on J1 cap J2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-global-I
REVIEWER: sol-delta-I-global
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED (pending N graph): source result of track N, node bpN:p3:gen-uniqueness; shared Lean provider. Cited as \Nref{bpN:p3:gen-uniqueness}. Owning-node retention is not certified: docs/graph/N/DEPGRAPH.md is absent. Re-check against its assembled root closure before treating this as a valid retained N import; if excluded, resolve track-I ownership under SPEC.

NODE: N:bpN:p3:ham-energy
KIND: external
TITLE: [N] Energy conservation
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-energy@L388-L393
PROOF_SOURCE: -
CONTRACT_ID: N:bpN:p3:ham-energy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H : P -> R with P = R^n x R^n; J subset R an interval; z : R -> P; for every t in J, H is differentiable at z(t) and z has derivative X_H(z(t)) at t
SOURCE_QUANTIFIERS: H, J, z fixed
SOURCE_CONCLUSION: t -> H(z(t)) is constant on J (no regularity of H beyond the pointwise differentiability, no confinement)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-global-I
REVIEWER: sol-delta-I-global
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED (pending N graph): source result of track N, node bpN:p3:ham-energy; shared Lean provider. Cited as \Nref{bpN:p3:ham-energy}. Owning-node retention is not certified: docs/graph/N/DEPGRAPH.md is absent. Re-check against its assembled root closure before treating this as a valid retained N import; if excluded, resolve track-I ownership under SPEC.

NODE: N:bpN:p3:ham-periodic
KIND: external
TITLE: [N] Periodicity in the angles passes to solutions
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-periodic@L402-L407
PROOF_SOURCE: -
CONTRACT_ID: N:bpN:p3:ham-periodic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W subset P open with W + (k,0) = W for all k in Z^n; H : P -> R with H(theta+k,I) = H(theta,I) for (theta,I) in W, k in Z^n
SOURCE_QUANTIFIERS: W, H fixed; for every k in Z^n, every J subset R and every z : R -> P
SOURCE_CONCLUSION: X_H(theta+k,I) = X_H(theta,I) on W; if IsSolIn X_H W J z then IsSolIn X_H W J (z + (k,0)) and H o (z + (k,0)) = H o z
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-global-I
REVIEWER: sol-delta-I-global
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED (pending N graph): source result of track N, node bpN:p3:ham-periodic; shared Lean provider. Cited as \Nref{bpN:p3:ham-periodic}. Owning-node retention is not certified: docs/graph/N/DEPGRAPH.md is absent. Re-check against its assembled root closure before treating this as a valid retained N import; if excluded, resolve track-I ownership under SPEC.

NODE: N:bpN:p3:ham-reduction
KIND: external
TITLE: [N] Track N and track I Hamiltonian predicates
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:ham-reduction@L416-L427
PROOF_SOURCE: -
CONTRACT_ID: N:bpN:p3:ham-reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H : P -> R; U subset R^n open; W subset P open with R^n x U subset W; H C^2 on W; W_U := R^n x U
SOURCE_QUANTIFIERS: H, U, W fixed; for every J subset R and every z : R -> P
SOURCE_CONCLUSION: IsSolutionOn H U J z <-> IsSolIn X_H W_U J z <-> IsHamiltonianSolutionOn H U J z (the frozen KAM.Nekhoroshev.IsSolutionOn and KAM.Iso.IsHamiltonianSolutionOn); X_H is C^1 on W_U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-global-I
REVIEWER: sol-delta-I-global
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED (pending N graph): source result of track N, node bpN:p3:ham-reduction; shared Lean provider. Cited as \Nref{bpN:p3:ham-reduction}. Owning-node retention is not certified: docs/graph/N/DEPGRAPH.md is absent. Re-check against its assembled root closure before treating this as a valid retained N import; if excluded, resolve track-I ownership under SPEC.

NODE: N:bpN:p3:gen-exit
KIND: external
TITLE: [N] First exit
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-exit@L328-L341
PROOF_SOURCE: -
CONTRACT_ID: N:bpN:p3:gen-exit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: IsSolIn F W J z with J an interval, 0 in J; V subset E open; z(0) in V; A = {t in J : t >= 0, z(t) not in V}
SOURCE_QUANTIFIERS: F, W, J, z, V fixed
SOURCE_CONCLUSION: exactly one holds: (i) A empty and z(t) in V for all t in J, t >= 0; (ii) A nonempty, t* = min A exists, t* > 0, t* in J, z(t) in V on [0,t*), z(t*) in boundary of V = closure(V) minus V; t* equals sup{t in J : t >= 0, z([0,t]) subset V}; the same holds backwards in time
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-global-I
REVIEWER: sol-delta-I-global
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED (pending N graph): source result of track N, node bpN:p3:gen-exit; shared Lean provider. Cited as \Nref{bpN:p3:gen-exit}. Owning-node retention is not certified: docs/graph/N/DEPGRAPH.md is absent. Re-check against its assembled root closure before treating this as a valid retained N import; if excluded, resolve track-I ownership under SPEC.

NODE: N:bpN:p3:gen-symmetry
KIND: external
TITLE: [N] Symmetries
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-symmetry@L101-L110
PROOF_SOURCE: -
CONTRACT_ID: N:bpN:p3:gen-symmetry
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E a finite-dimensional real normed space; F:E->E total, W subset E open, J subset R, z:R->E with IsSolIn F W J z; for (c), v in E with W+v=W and F(x+v)=F(x) for x in W; no C^1 assumption is required for the solution transformations
SOURCE_QUANTIFIERS: F,W,J,z as stated; (a) every c in R; (b) time reversal, with the additional C^1 implication conditional on F being C^1 on W; (c) every v satisfying the translation conditions
SOURCE_CONCLUSION: (a) t -> z(t+c) is a solution on J-c; (b) t -> z(-t) is a solution of -F on -J, and -F is C^1 on W if F is; (c) t -> z(t)+v is a solution of F in W on J
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP+sol-global-I
REVIEWER: sol-delta-I-global
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED (pending N graph): source result of track N, node bpN:p3:gen-symmetry; shared Lean provider. Cited as \Nref{bpN:p3:gen-symmetry}. Owning-node retention is not certified: docs/graph/N/DEPGRAPH.md is absent. Re-check against its assembled root closure before treating this as a valid retained N import; if excluded, resolve track-I ownership under SPEC.

NODE: P:bpP:p0:fixedsol#IsFixedSolution
KIND: external
TITLE: [P] Fixed-Sun solutions: KAM.Planetary.IsFixedSolution
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:fixedsol@L235-L242
PROOF_SOURCE: -
CONTRACT_ID: P:bpP:p0:fixedsol#IsFixedSolution
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: n in N, G, m_0, epsilon in R, m in R^n, Q, V : R -> (R^2)^n
SOURCE_QUANTIFIERS: G, m_0, m, epsilon, Q, V
SOURCE_CONCLUSION: defines IsFixedSol(G,m_0,m,epsilon,Q,V): for all t and i != j: pl(Q_i(t)) > 0, pl(Q_j(t) - Q_i(t)) > 0, Q_i has derivative V_i(t), and V_i has derivative -G m_0 Q_i(t) / pl(Q_i(t))^3 + epsilon sum_{j != i} G m_j (Q_j(t) - Q_i(t)) / pl(Q_j(t) - Q_i(t))^3; the Sun is the constant origin
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED (pending P graph): frozen definition KAM.Planetary.IsFixedSolution, anchor node bpP:p0:fixedsol#IsFixedSolution of the track-P graph; not an anchor of this graph. Cited as \frozen{KAM.Planetary.IsFixedSolution}.

NODE: P:bpP:p0:newton#IsNewtonSolution
KIND: external
TITLE: [P] Newton solutions: KAM.Planetary.IsNewtonSolution
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:newton@L226-L233
PROOF_SOURCE: -
CONTRACT_ID: P:bpP:p0:newton#IsNewtonSolution
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: N in N, G in R, M in R^N, Q, V : R -> (R^2)^N
SOURCE_QUANTIFIERS: G, M, Q, V
SOURCE_CONCLUSION: defines IsNewton(G,M,Q,V): for all t in R and i != j (indices < N): pl(Q_j(t) - Q_i(t)) > 0; Q_i has derivative V_i(t) at t; V_i has derivative sum_{j != i} G M_j (Q_j(t) - Q_i(t)) / pl(Q_j(t) - Q_i(t))^3 at t (HasDerivAt)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-INP
REVIEWER: sol-review-I-imports
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED (pending P graph): frozen definition KAM.Planetary.IsNewtonSolution, anchor node bpP:p0:newton#IsNewtonSolution of the track-P graph; not an anchor of this graph. Cited as \frozen{KAM.Planetary.IsNewtonSolution}.

NODE: bpN:p3:gen-invariant
KIND: definition
TITLE: Invariant sets
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-invariant@L352-L356
PROOF_SOURCE: -
CONTRACT_ID: bpN:p3:gen-invariant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F : E -> E; W subset E; S subset E (typing data)
SOURCE_QUANTIFIERS: F, W, S
SOURCE_CONCLUSION: defines: S is invariant for (F,W) iff for every interval J' and every y with IsSolIn F W J' y, if y(t1) in S for one t1 in J' then y(t) in S for all t in J'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-invariant@L353-L353 | IsSolIn used in the definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-nown
REVIEWER: sol-review-I-nown
LEAN_STATUS: PROVED
LEAN_REF: IsInvariantSet, isInvariantSet_equilibria, isInvariantSet_union (KAM/ODE/Exit.lean)
LEAN_NOTE: audit N3-4/N3-5 PASS WITH NOTES
NOTE: -

NODE: bpN:p3:gen-barrier
KIND: corollary
TITLE: Barrier
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-barrier@L358-L363
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-barrier@L364-L368
CONTRACT_ID: bpN:p3:gen-barrier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E a finite-dimensional real normed space; F C^1 on the open set W; V subset E open; IsSolIn F W J z with J an interval, 0 in J, z(0) in V; G subset E with z(J) subset G; (boundary of V) cap G subset S with S invariant for (F,W) (Definition bpN:p3:gen-invariant) and z(0) not in S
SOURCE_QUANTIFIERS: F, W, V, J, z, G, S fixed
SOURCE_CONCLUSION: z(t) in V for all t in J (both time directions)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:barrier-fwd, stepN:p3:barrier-bwd, N:bpN:p3:gen-sol, bpN:p3:gen-invariant
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:barrier-fwd | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-barrier@L365-L365 | proof step (forward)
EDGE: stepN:p3:barrier-bwd | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-barrier@L367-L367 | proof step (backward)
EDGE: N:bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-barrier@L359-L359 | IsSolIn F W J z
EDGE: bpN:p3:gen-invariant | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:gen-barrier@L360-L360 | S invariant
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-nown
REVIEWER: sol-review-I-nown
LEAN_STATUS: PROVED
LEAN_REF: gen_barrier (KAM/ODE/Exit.lean)
LEAN_NOTE: audit N3-4/N3-5 PASS WITH NOTES
NOTE: -

NODE: stepN:p3:barrier-fwd
KIND: step
TITLE: Barrier, forward in time
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:barrier-fwd@L365-L365
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:barrier-fwd@L365-L365
CONTRACT_ID: stepN:p3:barrier-fwd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hypotheses of bpN:p3:gen-barrier
SOURCE_QUANTIFIERS: z, V, G, S
SOURCE_CONCLUSION: z(t) in V for all t in J with t >= 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: N:bpN:p3:gen-exit, bpN:p3:gen-invariant
ROUTES: -
ROUTE_FOR: -
EDGE: N:bpN:p3:gen-exit | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:barrier-fwd@L365-L365 | Lemma gen-exit(ii): first exit time t* in J with z(t*) in boundary V cap G
EDGE: bpN:p3:gen-invariant | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:barrier-fwd@L365-L365 | invariance of S gives z(0) in S, a contradiction
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-nown
REVIEWER: sol-review-I-nown
LEAN_STATUS: PROVED
LEAN_REF: gen_barrier (KAM/ODE/Exit.lean)
LEAN_NOTE: audit N3-4/N3-5 PASS WITH NOTES; whole-J confinement, forward direction (private barrier_forward)
NOTE: -

NODE: stepN:p3:barrier-bwd
KIND: step
TITLE: Barrier, backward in time
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:barrier-bwd@L367-L367
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:barrier-bwd@L367-L367
CONTRACT_ID: stepN:p3:barrier-bwd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hypotheses of bpN:p3:gen-barrier (source data and assumptions only)
SOURCE_QUANTIFIERS: E, F, W, V, J, z, G, S as in bpN:p3:gen-barrier; for all t in J with t <= 0
SOURCE_CONCLUSION: z(t) in V for all t in J with t <= 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:barrier-fwd, N:bpN:p3:gen-symmetry, bpN:p3:gen-invariant, N:bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:barrier-fwd | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:barrier-bwd@L367-L367 | forward step applied to t -> z(-t)
EDGE: N:bpN:p3:gen-symmetry | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:barrier-bwd@L367-L367 | time reversal: z(-t) solves -F on -J, -F is C^1
EDGE: bpN:p3:gen-invariant | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:barrier-bwd@L367-L367 | S invariant for -F as well (reversal swaps solutions of F and -F)
EDGE: N:bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:barrier-bwd@L367-L367 | IsSolIn for -F on -J
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-nown+sol-review-I-nown
REVIEWER: sol-delta-I-e
LEAN_STATUS: PROVED
LEAN_REF: gen_barrier (KAM/ODE/Exit.lean)
LEAN_NOTE: audit N3-4/N3-5 PASS WITH NOTES; whole-J confinement, backward direction
NOTE: -

NODE: bpN:p3:newton-reduction
KIND: proposition
TITLE: Newtonian predicates
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:newton-reduction@L434-L449
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:newton-reduction@L450-L454
CONTRACT_ID: bpN:p3:newton-reduction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: N >= 2; E_N = (Fin N -> R^2) x (Fin N -> R^2) with max norm; ell = planeLength; W_N = {(q,v) : ell(q_j-q_i) > 0 for every i != j}; F_N(q,v) = (v, (sum_{j != i} (G mass_j / ell(q_j-q_i)^3) (q_j-q_i))_i); for the fixed-Sun variant W_Nprime = W_N cap {(q,v) : ell(q_i) > 0 for every i}, Fprime(q,v) = (v, (-G m0 q_i / ell(q_i)^3 + eps sum_{j != i} (G m_j / ell(q_j-q_i)^3) (q_j-q_i))_i); for the restricted variant W_mu = {z : CollisionFree mu z}, F_mu is the total extension by the same formula of restrictedVectorField mu
SOURCE_QUANTIFIERS: for every N >= 2, G in R and mass : Fin N -> R, and all Q,V : R -> (Fin N -> R^2), set x(t)=(Q(t),V(t)); likewise for every G,m0,eps in R and m : Fin N -> R in the fixed-Sun variant; for every mu in R, arbitrary J subset R and z : R -> R^2 x R^2 in the restricted variant
SOURCE_CONCLUSION: W_N is open, F_N is C^infinity on W_N and IsNewtonSolution G mass Q V <-> IsSolIn F_N W_N R x; likewise IsFixedSolution with (W_N', F'); IsRestrictedSolutionOn mu J z <-> IsSolIn F_mu W_mu J z; in all three cases F is C^infinity on the open set W and the general layer applies
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepN:p3:nr-smooth, stepN:p3:nr-pair, N:bpN:p3:gen-sol, P:bpP:p0:newton#IsNewtonSolution, P:bpP:p0:fixedsol#IsFixedSolution, bpI:p0:restricted#IsRestrictedSolutionOn, bpI:p0:restricted#restrictedVectorField, bpI:p0:primaries#CollisionFree
ROUTES: -
ROUTE_FOR: -
EDGE: stepN:p3:nr-smooth | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:newton-reduction@L451-L451 | proof step: open domain and smoothness
EDGE: stepN:p3:nr-pair | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:newton-reduction@L453-L453 | proof step: derivatives of pairs
EDGE: N:bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:newton-reduction@L441-L441 | IsSolIn F_N W_N R x
EDGE: P:bpP:p0:newton#IsNewtonSolution | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:newton-reduction@L441-L441 | IsNewtonSolution
EDGE: P:bpP:p0:fixedsol#IsFixedSolution | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:newton-reduction@L442-L442 | IsFixedSolution
EDGE: bpI:p0:restricted#IsRestrictedSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:newton-reduction@L445-L445 | IsRestrictedSolutionOn mu J z
EDGE: bpI:p0:restricted#restrictedVectorField | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:newton-reduction@L444-L444 | F_mu is the total extension of restrictedVectorField mu
EDGE: bpI:p0:primaries#CollisionFree | blueprint-N/parts/p3-hamiltonian-ode.tex#bpN:p3:newton-reduction@L444-L444 | W_mu defined by CollisionFree
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-nown+sol-review-I-nown
REVIEWER: sol-delta-I-e
LEAN_STATUS: PROVED
LEAN_REF: newtonDomain, newtonField, fixedDomain, fixedField, restrictedDomain, restrictedField, restrictedField_eq (KAM/ODE/NewtonDefs.lean); newton_reduction, fixed_reduction, restricted_reduction (KAM/ODE/NewtonReduction.lean)
LEAN_NOTE: audit N3-8 PASS WITH NOTES; all three reductions
NOTE: The fields are the displayed formulas, not arbitrary fields called Newtonian. No mass, G or mu positivity assumption, and no interval assumption on J in the restricted equivalence. planeLength and planeSq are the elementary planar formulas recalled at L451; the P solution-predicate imports remain pending the owning P graph.

NODE: stepN:p3:nr-smooth
KIND: step
TITLE: Open domain and smoothness
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-smooth@L451-L451
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-smooth@L451-L451
CONTRACT_ID: stepN:p3:nr-smooth
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data of bpN:p3:newton-reduction
SOURCE_QUANTIFIERS: for every N >= 2, G in R and mass : Fin N -> R; in the fixed-Sun variant also m0,eps in R and m : Fin N -> R; in the restricted variant every mu in R
SOURCE_CONCLUSION: W_N, W_N', W_mu are open and F_N, F', F_mu are C^infinity on them
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpI:p0:primaries#radius, bpI:p0:primaries#radiusSq, bpI:p0:primaries#primary1, bpI:p0:primaries#primary2, bpI:p0:primaries#CollisionFree, bpI:p0:restricted#restrictedVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpI:p0:primaries#radius | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-smooth@L451-L451 | radius = sqrt(radiusSq) in F_mu
EDGE: bpI:p0:primaries#radiusSq | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-smooth@L451-L451 | radiusSq polynomial
EDGE: bpI:p0:primaries#primary1 | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-smooth@L451-L451 | shift by primary_1 mu
EDGE: bpI:p0:primaries#primary2 | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-smooth@L451-L451 | shift by primary_2 mu
EDGE: bpI:p0:primaries#CollisionFree | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-smooth@L451-L451 | openness of W_mu uses its two strict positive-radius inequalities
EDGE: bpI:p0:restricted#restrictedVectorField | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-smooth@L451-L451 | finite sums and products in the explicit formula for F_mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-nown+sol-review-I-nown
REVIEWER: sol-delta-I-e
LEAN_STATUS: PROVED
LEAN_REF: contDiffAt_force, newton_reduction, fixed_reduction, restricted_reduction (KAM/ODE/NewtonReduction.lean)
LEAN_NOTE: audit N3-8 PASS WITH NOTES; rows nr-smooth
NOTE: -

NODE: stepN:p3:nr-pair
KIND: step
TITLE: Derivatives of pairs
STATEMENT_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-pair@L453-L453
PROOF_SOURCE: blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-pair@L453-L453
CONTRACT_ID: stepN:p3:nr-pair
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing and field/domain data of bpN:p3:newton-reduction; x(s)=(Q(s),V(s)); no smoothness result assumed
SOURCE_QUANTIFIERS: all Newtonian and fixed-Sun parameters as in bpN:p3:newton-reduction; all Q,V : R -> (Fin N -> R^2) and t in R; likewise every mu in R and z : R -> R^2 x R^2, pointwise for t in an arbitrary J subset R
SOURCE_CONCLUSION: the three frozen Newtonian clauses at t (positive pair distances, component derivatives Q_i prime = V_i(t), and V_i prime = force_i) hold iff x(t) in W_N AND HasDerivAt x (F_N(x(t))) t; likewise for the fixed-Sun domain W_Nprime and field Fprime; the restricted clause at t is equivalently z(t) in W_mu AND HasDerivAt z (F_mu(z(t))) t. Quantifying these pointwise equivalences gives the IsSolIn equivalences of bpN:p3:newton-reduction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: P:bpP:p0:newton#IsNewtonSolution, P:bpP:p0:fixedsol#IsFixedSolution, bpI:p0:restricted#IsRestrictedSolutionOn, N:bpN:p3:gen-sol
ROUTES: -
ROUTE_FOR: -
EDGE: P:bpP:p0:newton#IsNewtonSolution | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-pair@L453-L453 | blocks of IsNewtonSolution
EDGE: P:bpP:p0:fixedsol#IsFixedSolution | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-pair@L453-L453 | blocks of IsFixedSolution
EDGE: bpI:p0:restricted#IsRestrictedSolutionOn | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-pair@L453-L453 | restricted predicate analogue
EDGE: N:bpN:p3:gen-sol | blueprint-N/parts/p3-hamiltonian-ode.tex#stepN:p3:nr-pair@L453-L453 | IsSolIn: derivative F(z(t)) with membership in W
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-I-nown+sol-review-I-nown
REVIEWER: sol-delta-I-e
LEAN_STATUS: PROVED
LEAN_REF: hasDerivAt_pair_iff, newton_reduction, fixed_reduction, restricted_reduction (KAM/ODE/NewtonReduction.lean)
LEAN_NOTE: audit N3-8 PASS WITH NOTES; row nr-pair
NOTE: L453 identifies the first block with domain membership before bundling the derivative blocks. Its final sentence omits the membership conjunct in words; retain that conjunct as required by the first block and IsSolIn. This is a reported source wording defect, not a new smoothness premise.

<!-- BEGIN PROOF DEPGRAPH GENERATED -->
Regenerated by `proof_depgraph.py`; do not hand-edit.

### Dashboard

* Total nodes: **450**
* Frozen anchors: **34**
* Versioned statement contracts: **450**
* Total edges: **1956**
* Root-closure nodes: **450**
* Dependency leaves in root closure: **92**
* Assumption boundary leaves: **0**
* External boundary leaves: **72**
* Alternative routes: **4**
* Topology review queue: **0**
* Explicit source gaps: **4**
* Coverage items: **672**; excluded: **194**

### Roots

* `bpI:p0:g1` [REVIEWED; frozen] — contract `iso.isoenergetic_kam@1`
* `bpI:p0:head` [REVIEWED; frozen] — contract `iso.all_time_confinement@1`
* `bpI:p0:kepler` [REVIEWED; frozen] — contract `iso.kepler_bordered_det@1`
* `bpI:p0:r3bp` [REVIEWED; frozen] — contract `iso.restricted_near_circular@1`

### Topology review queue

* _(none)_

### Dependency leaves in root closure

* `K:bp:p0:g3` [REVIEWED] — [K] G3: measure of the non-Diophantine set
* `K:bp:p1:cauchy-corollaries` [REVIEWED] — [K] Cauchy corollaries
* `K:bp:p1:cauchy-open` [REVIEWED] — [K] Cauchy estimate on open sets
* `K:bp:p1:cauchy-strip` [REVIEWED] — [K] Cauchy estimate on strips
* `K:bp:p1:cohomological` [REVIEWED] — [K] Cohomological equation on strips
* `K:bp:p1:ext-banach` [REVIEWED] — [K] Banach's fixed point theorem
* `K:bp:p1:ext-cramer` [REVIEWED] — [K] Cramer's rule
* `K:bp:p1:ext-integral` [REVIEWED] — [K] Integrals
* `K:bp:p1:ext-mvt` [REVIEWED] — [K] Mean value inequality
* `K:bp:p1:hamiltonian-real` [REVIEWED] — [K] Real and complex Hamiltonian fields
* `K:bp:p1:holomorphic-analytic` [REVIEWED] — [K] Holomorphic maps are analytic
* `K:bp:p1:holomorphic-inverse` [REVIEWED] — [K] Holomorphic inverse
* `K:bp:p1:holomorphic-regularity` [REVIEWED] — [K] Derivatives of holomorphic maps
* `K:bp:p1:increments-open` [REVIEWED] — [K] Increments on open sets
* `K:bp:p1:iteration` [REVIEWED] — [K] Quadratic iteration on nested strips
* `K:bp:p1:matrix-norms` [REVIEWED] — [K] Max-norm matrix facts
* `K:bp:p1:neumann` [REVIEWED] — [K] Neumann series
* `K:bp:p1:real-inverse` [REVIEWED] — [K] Real inverses
* `K:bp:p1:real-restriction` [REVIEWED] — [K] Real restriction
* `K:bp:p1:taylor` [REVIEWED] — [K] Second-order Taylor bound
* `K:bp:p1:uniform-limits` [REVIEWED] — [K] Uniform limits
* `K:bp:p2:admissible` [REVIEWED] — [K] Admissible parameterization
* `K:bp:p2:averages` [REVIEWED] — [K] Averages
* `K:bp:p2:cohomological` [REVIEWED] — [K] Cohomological equation in operator norms
* `K:bp:p2:constants` [REVIEWED] — [K] Exponents and constants
* `K:bp:p2:exactness` [REVIEWED] — [K] Exactness: two vanishing averages
* `K:bp:p2:frame-basic` [REVIEWED] — [K] Regularity and bounds of the frame
* `K:bp:p2:frame-identities` [REVIEWED] — [K] Frame identities
* `K:bp:p2:frequency` [REVIEWED] — [K] Frequency bound
* `K:bp:p2:frozen-agreement` [REVIEWED] — [K] Agreement with the frozen definitions
* `K:bp:p2:hamiltonian` [REVIEWED] — [K] The Hamiltonian vector field
* `K:bp:p2:matrix` [REVIEWED] — [K] Matrix norms
* `K:bp:p2:objects` [REVIEWED] — [K] Objects attached to a parameterization
* `K:bp:p2:periodicity` [REVIEWED] — [K] Periodicity and realness of the attached objects
* `K:bp:p2:standing` [REVIEWED] — [K] Standing data of Part~\ref{bp:p2}
* `K:bp:p4:data` [REVIEWED] — [K] Shrunken domains and basic constants
* `K:bp:p4:derivative-bounds` [REVIEWED] — [K] Derivative bounds
* `K:bp:p4:freq-map` [REVIEWED] — [K] The frequency map
* `K:bp:p4:h-bounded` [REVIEWED] — [K] $h$ is bounded on a shrunken neighbourhood
* `K:bp:p4:h1` [REVIEWED] — [K] The Hamiltonian hypothesis H1
* `K:step:p2:ham-real` [REVIEWED] — [K] Realness
* `K:step:p2:pt-small` [REVIEWED] — [K] Consequences of the smallness
* `K:step:p4:db-cauchy` [REVIEWED] — [K] Cauchy estimates
* `K:step:p4:h1-holo` [REVIEWED] — [K] Holomorphy, periodicity, reality
* `K:step:p4:h1-open` [REVIEWED] — [K] Openness and invariance
* `N:bpN:p3:gen-continuation-periodic` [REVIEWED] — [N] Closed sets, periodic fields
* `N:bpN:p3:gen-exit` [REVIEWED] — [N] First exit
* `N:bpN:p3:gen-maximal` [REVIEWED] — [N] Maximal solution
* `N:bpN:p3:gen-sol` [REVIEWED] — [N] Solutions in $W$
* `N:bpN:p3:gen-symmetry` [REVIEWED] — [N] Symmetries
* `N:bpN:p3:gen-uniqueness` [REVIEWED] — [N] Uniqueness on arbitrary intervals
* `N:bpN:p3:ham-energy` [REVIEWED] — [N] Energy conservation
* `N:bpN:p3:ham-periodic` [REVIEWED] — [N] Periodicity in the angles passes to solutions
* `N:bpN:p3:ham-reduction` [REVIEWED] — [N] Track N and track I Hamiltonian predicates
* `P:bpP:p0:fixedsol#IsFixedSolution` [REVIEWED] — [P] Fixed-Sun solutions: KAM.Planetary.IsFixedSolution
* `P:bpP:p0:newton#IsNewtonSolution` [REVIEWED] — [P] Newton solutions: KAM.Planetary.IsNewtonSolution
* `bpI:p0:diophantine#IsDiophantine` [REVIEWED] — Diophantine vectors: KAM.IsDiophantine
* `bpI:p0:domains#actionNbhd` [REVIEWED] — Strip, action neighbourhood: KAM.actionNbhd
* `bpI:p0:domains#complexStrip` [REVIEWED] — Strip, action neighbourhood: KAM.complexStrip
* `bpI:p0:extended#energyAverage` [REVIEWED] — Energy average and extended torsion: KAM.Iso.energyAverage
* `bpI:p0:hamiltonian#hamiltonianVectorField` [REVIEWED] — Hamiltonian vector fields: KAM.hamiltonianVectorField
* `bpI:p0:hamiltonian#hamiltonianVectorFieldC` [REVIEWED] — Hamiltonian vector fields: KAM.hamiltonianVectorFieldℂ
* `bpI:p0:keplerborder#keplerBorder` [REVIEWED] — The Kepler bordered matrix: KAM.Iso.keplerBorder
* `bpI:p0:primaries#primary1` [REVIEWED] — Planar Euclidean length, the primaries, collisions: KAM.Iso.primary₁
* `bpI:p0:primaries#primary2` [REVIEWED] — Planar Euclidean length, the primaries, collisions: KAM.Iso.primary₂
* `bpI:p0:primaries#radiusSq` [REVIEWED] — Planar Euclidean length, the primaries, collisions: KAM.Iso.radiusSq
* `bpI:p0:realham#frequencyMap` [REVIEWED] — Real Hamiltonian, frequency map: KAM.frequencyMap
* `bpI:p0:realham#realHamiltonian` [REVIEWED] — Real Hamiltonian, frequency map: KAM.realHamiltonian
* `bpI:p0:stripdata#IsRealOnReals` [REVIEWED] — Torus data on strips: KAM.IsRealOnReals
* `bpI:p0:stripdata#dotC` [REVIEWED] — Torus data on strips: KAM.dotℂ
* `bpI:p0:stripdata#omegaZero` [REVIEWED] — Torus data on strips: KAM.omegaZero
* `bpI:p1:ext-chain` [REVIEWED] — Chain and product rules
* `bpI:p1:ext-neumann` [REVIEWED] — Neumann criterion of radius one
* `bpI:p1:ext-real-direction` [REVIEWED] — Complex derivative in a real direction
* `bpI:p3:ext-compact` [REVIEWED] — Compactness
* `bpI:p3:ext-ift` [REVIEWED] — Inverse function theorem
* `bpI:p3:ext-lebesgue` [REVIEWED] — Lebesgue measure on $\R^2$
* `bpI:p5:ext-top` [REVIEWED] — Topology
* `bpI:p6:conversion-map` [REVIEWED] — Period-one conversion map
* `bpI:p6:kep-ham` [REVIEWED] — The Kepler--rotation Hamiltonian
* `bpI:p7:elements` [REVIEWED] — Kepler region and elements
* `bpI:p7:x-forms` [REVIEWED] — Exterior calculus on open subsets of $\R^m$
* `bpI:p7:x-hol` [REVIEWED] — Holomorphic functions of several variables
* `bpI:p7:x-ift` [REVIEWED] — Inverse function theorem (real-analytic)
* `bpI:p7:x-param` [REVIEWED] — Parameter integrals
* `bpI:p7:x-schwarz` [REVIEWED] — Schwarz lemma (maximum modulus)
* `bpI:p7:x-weier` [REVIEWED] — Weierstrass
* `bpI:p8:x-cont` [REVIEWED] — Monotone functions
* `bpI:p8:x-norm` [REVIEWED] — Triangle inequality
* `bpI:p8:x-topo` [REVIEWED] — Topology of R^k
* `stepI:p7:ke-const` [REVIEWED] — Constants
* `stepI:p7:ke-trig` [REVIEWED] — Trigonometric bounds

### Assumption boundary leaves

* _(none)_

### External boundary leaves

* `K:bp:p0:g3` [REVIEWED] — [K] G3: measure of the non-Diophantine set
* `K:bp:p1:cauchy-corollaries` [REVIEWED] — [K] Cauchy corollaries
* `K:bp:p1:cauchy-open` [REVIEWED] — [K] Cauchy estimate on open sets
* `K:bp:p1:cauchy-strip` [REVIEWED] — [K] Cauchy estimate on strips
* `K:bp:p1:cohomological` [REVIEWED] — [K] Cohomological equation on strips
* `K:bp:p1:ext-banach` [REVIEWED] — [K] Banach's fixed point theorem
* `K:bp:p1:ext-cramer` [REVIEWED] — [K] Cramer's rule
* `K:bp:p1:ext-integral` [REVIEWED] — [K] Integrals
* `K:bp:p1:ext-mvt` [REVIEWED] — [K] Mean value inequality
* `K:bp:p1:hamiltonian-real` [REVIEWED] — [K] Real and complex Hamiltonian fields
* `K:bp:p1:holomorphic-analytic` [REVIEWED] — [K] Holomorphic maps are analytic
* `K:bp:p1:holomorphic-inverse` [REVIEWED] — [K] Holomorphic inverse
* `K:bp:p1:holomorphic-regularity` [REVIEWED] — [K] Derivatives of holomorphic maps
* `K:bp:p1:increments-open` [REVIEWED] — [K] Increments on open sets
* `K:bp:p1:iteration` [REVIEWED] — [K] Quadratic iteration on nested strips
* `K:bp:p1:matrix-norms` [REVIEWED] — [K] Max-norm matrix facts
* `K:bp:p1:neumann` [REVIEWED] — [K] Neumann series
* `K:bp:p1:real-inverse` [REVIEWED] — [K] Real inverses
* `K:bp:p1:real-restriction` [REVIEWED] — [K] Real restriction
* `K:bp:p1:taylor` [REVIEWED] — [K] Second-order Taylor bound
* `K:bp:p1:uniform-limits` [REVIEWED] — [K] Uniform limits
* `K:bp:p2:admissible` [REVIEWED] — [K] Admissible parameterization
* `K:bp:p2:averages` [REVIEWED] — [K] Averages
* `K:bp:p2:cohomological` [REVIEWED] — [K] Cohomological equation in operator norms
* `K:bp:p2:constants` [REVIEWED] — [K] Exponents and constants
* `K:bp:p2:exactness` [REVIEWED] — [K] Exactness: two vanishing averages
* `K:bp:p2:frame-basic` [REVIEWED] — [K] Regularity and bounds of the frame
* `K:bp:p2:frame-identities` [REVIEWED] — [K] Frame identities
* `K:bp:p2:frequency` [REVIEWED] — [K] Frequency bound
* `K:bp:p2:frozen-agreement` [REVIEWED] — [K] Agreement with the frozen definitions
* `K:bp:p2:hamiltonian` [REVIEWED] — [K] The Hamiltonian vector field
* `K:bp:p2:matrix` [REVIEWED] — [K] Matrix norms
* `K:bp:p2:objects` [REVIEWED] — [K] Objects attached to a parameterization
* `K:bp:p2:periodicity` [REVIEWED] — [K] Periodicity and realness of the attached objects
* `K:bp:p2:standing` [REVIEWED] — [K] Standing data of Part~\ref{bp:p2}
* `K:bp:p4:data` [REVIEWED] — [K] Shrunken domains and basic constants
* `K:bp:p4:derivative-bounds` [REVIEWED] — [K] Derivative bounds
* `K:bp:p4:freq-map` [REVIEWED] — [K] The frequency map
* `K:bp:p4:h-bounded` [REVIEWED] — [K] $h$ is bounded on a shrunken neighbourhood
* `K:bp:p4:h1` [REVIEWED] — [K] The Hamiltonian hypothesis H1
* `K:step:p2:ham-real` [REVIEWED] — [K] Realness
* `K:step:p2:pt-small` [REVIEWED] — [K] Consequences of the smallness
* `K:step:p4:db-cauchy` [REVIEWED] — [K] Cauchy estimates
* `K:step:p4:h1-holo` [REVIEWED] — [K] Holomorphy, periodicity, reality
* `K:step:p4:h1-open` [REVIEWED] — [K] Openness and invariance
* `N:bpN:p3:gen-continuation-periodic` [REVIEWED] — [N] Closed sets, periodic fields
* `N:bpN:p3:gen-exit` [REVIEWED] — [N] First exit
* `N:bpN:p3:gen-maximal` [REVIEWED] — [N] Maximal solution
* `N:bpN:p3:gen-sol` [REVIEWED] — [N] Solutions in $W$
* `N:bpN:p3:gen-symmetry` [REVIEWED] — [N] Symmetries
* `N:bpN:p3:gen-uniqueness` [REVIEWED] — [N] Uniqueness on arbitrary intervals
* `N:bpN:p3:ham-energy` [REVIEWED] — [N] Energy conservation
* `N:bpN:p3:ham-periodic` [REVIEWED] — [N] Periodicity in the angles passes to solutions
* `N:bpN:p3:ham-reduction` [REVIEWED] — [N] Track N and track I Hamiltonian predicates
* `P:bpP:p0:fixedsol#IsFixedSolution` [REVIEWED] — [P] Fixed-Sun solutions: KAM.Planetary.IsFixedSolution
* `P:bpP:p0:newton#IsNewtonSolution` [REVIEWED] — [P] Newton solutions: KAM.Planetary.IsNewtonSolution
* `bpI:p1:ext-chain` [REVIEWED] — Chain and product rules
* `bpI:p1:ext-neumann` [REVIEWED] — Neumann criterion of radius one
* `bpI:p1:ext-real-direction` [REVIEWED] — Complex derivative in a real direction
* `bpI:p3:ext-compact` [REVIEWED] — Compactness
* `bpI:p3:ext-ift` [REVIEWED] — Inverse function theorem
* `bpI:p3:ext-lebesgue` [REVIEWED] — Lebesgue measure on $\R^2$
* `bpI:p5:ext-top` [REVIEWED] — Topology
* `bpI:p7:x-forms` [REVIEWED] — Exterior calculus on open subsets of $\R^m$
* `bpI:p7:x-hol` [REVIEWED] — Holomorphic functions of several variables
* `bpI:p7:x-ift` [REVIEWED] — Inverse function theorem (real-analytic)
* `bpI:p7:x-param` [REVIEWED] — Parameter integrals
* `bpI:p7:x-schwarz` [REVIEWED] — Schwarz lemma (maximum modulus)
* `bpI:p7:x-weier` [REVIEWED] — Weierstrass
* `bpI:p8:x-cont` [REVIEWED] — Monotone functions
* `bpI:p8:x-norm` [REVIEWED] — Triangle inequality
* `bpI:p8:x-topo` [REVIEWED] — Topology of R^k

### Uncovered graph nodes

* _(none)_

### Nodes outside every root closure

* _(none)_

### Explicit source gaps

* `stepI:p2:to-frame` [REVIEWED] — Frame
* `stepI:p3:to-torsion#p1-setting` [REVIEWED] — Unproved full Part 1 setting required by the cited shortcut
* `stepI:p7:cd-uc` [REVIEWED] — Uniform continuity
* `stepI:p7:eh-delta` [REVIEWED] — Choice of $\delta_2$
<!-- END PROOF DEPGRAPH GENERATED -->
