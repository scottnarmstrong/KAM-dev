# Proof dependency database — track K

GRAPH_VERSION: 4
ROOTS: bp:p0:head, bp:p0:headq, bp:p0:g1, bp:p0:g2, bp:p0:g3
CORPUS: blueprint/parts/{p0-conventions,p1-analysis,p2-aposteriori,p3-uniqueness,p4-measure}.tex pinned by SHA-256 in docs/graph/K/CORPUS.sha256 (KAM-dev, 2026-10-27)
CONVENTIONS: docs/graph/K/SPEC.md "Conventions to watch": max norm on C^m and induced operator norm; sup norms on strips T_rho; weighted l1 only inside the cohomological equation (D12); 1-periodicity, averages over [0,1]^n; |k.omega| >= gamma |k|_1^{-tau}; d=n, A=0, primary tori, Omega_0; stated constant dependences; G1 uniform in gamma <= gammabar with mu/2 margins; HEAD rate eps^{1/4}
STANDING_ASSUMPTIONS: -
EXTERNAL_POLICY: the eleven Mathlib-level inputs (E1)-(E11) of Part 1 are KIND external nodes bp:p1:ext-*; any other unproved fact is a step node with NOTE SOURCE_GAP
FROZEN_ANCHORS: bp:p0:diophantine#IsDiophantine, bp:p0:domains#complexStrip, bp:p0:domains#actionNbhd, bp:p0:domains#fundamentalDomain, bp:p0:hamiltonian#hamiltonianVectorField, bp:p0:hamiltonian#hamiltonianVectorFieldC, bp:p0:hamiltonian#symplecticForm, bp:p0:hamiltonian#omegaZero, bp:p0:nearlyintegrable#realHamiltonian, bp:p0:nearlyintegrable#frequencyMap, bp:p0:torus#IsInvariantLagrangianTorus, bp:p0:cover#kamCover, bp:p0:stripdata#IsPrimaryOnStrip, bp:p0:stripdata#IsRealOnReals, bp:p0:stripdata#invarianceError, bp:p0:stripdata#dotC, bp:p0:stripdata#gramMatrix, bp:p0:stripdata#normalFrame, bp:p0:stripdata#torsion, bp:p0:stripdata#torsionAverage, bp:p0:head, bp:p0:headq, bp:p0:g1, bp:p0:g2, bp:p0:g3
FROZEN_MANIFEST: manifest/frozen-anchors.json | sha256:8859fe7f8bae7ca904585d0b72a6c23601d848c66febefdc7e5c74adb2300555
WRITER: claude-main-orchestrator
GLOBAL_REVIEWER: sol-global-K
GLOBAL_REVIEW_REF: docs/graph/K/reviews/GLOBAL-review.md and docs/graph/K/reviews/GLOBAL-recheck.md (Codex GPT-6.1-Sol medium, tmux kam-graph-global)

The dependency direction is `NODE -> prerequisite`. Node blocks are assembled from `docs/graph/K/packets/<slice>.nodes.md`; edit those, then re-run `scripts/depgraph_assemble.py`.

## Nodes

NODE: bp:p0:diophantine#IsDiophantine
KIND: definition
TITLE: Diophantine vectors: KAM.IsDiophantine
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:diophantine@L32-L38
PROOF_SOURCE: -
CONTRACT_ID: kam.IsDiophantine
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: gamma, tau real; omega in R^n; k in Z^n, |k|_1 = sum_i |k_i|
SOURCE_QUANTIFIERS: gamma,tau in R, omega in R^n (n fixed), for every k in Z^n \ {0}
SOURCE_CONCLUSION: defines omega in Dio_{gamma,tau} iff gamma/|k|_1^tau <= |k.omega| for every nonzero integer k
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/IsDiophantine.lean
FROZEN_DECL: KAM.IsDiophantine
FROZEN_ANCHOR_ID: kam.IsDiophantine.v1
FROZEN_ABI_SHA256: 24a486c6ccc5648791465ec3577c2e37fd464ecaec8f0dab9c74a5588535e717
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.IsDiophantine (KAM/Frozen/Defs/IsDiophantine.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:domains#complexStrip
KIND: definition
TITLE: Complex neighbourhoods and the fundamental domain: KAM.complexStrip
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:conventions@L19-L20
PROOF_SOURCE: -
CONTRACT_ID: kam.complexStrip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: rho > 0; n fixed
SOURCE_QUANTIFIERS: n, rho > 0
SOURCE_CONCLUSION: defines the complex strip T_rho = {theta in C^n : |Im theta_i| < rho for all i}
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/ComplexStrip.lean
FROZEN_DECL: KAM.complexStrip
FROZEN_ANCHOR_ID: kam.complexStrip.v1
FROZEN_ABI_SHA256: 91cedb11be4f33139d30fcc5103f7ed5370fa5d89a68f9a3aaf0b061ae2920e7
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.complexStrip (KAM/Frozen/Defs/ComplexStrip.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:domains#actionNbhd
KIND: definition
TITLE: Complex neighbourhoods and the fundamental domain: KAM.actionNbhd
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:domains@L40-L45
PROOF_SOURCE: -
CONTRACT_ID: kam.actionNbhd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B subset R^n; r > 0
SOURCE_QUANTIFIERS: B subset R^n, r > 0
SOURCE_CONCLUSION: defines the complex neighbourhood B_r = {I in C^n : exists J in B, |I-J| < r} (max norm)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/ActionNbhd.lean
FROZEN_DECL: KAM.actionNbhd
FROZEN_ANCHOR_ID: kam.actionNbhd.v1
FROZEN_ABI_SHA256: b05e2aeddf393c0b232bd809f64d9d8040e0fdf54248c4f880ab1ad98c040f21
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.actionNbhd (KAM/Frozen/Defs/ActionNbhd.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:domains#fundamentalDomain
KIND: definition
TITLE: Complex neighbourhoods and the fundamental domain: KAM.fundamentalDomain
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:domains@L40-L45
PROOF_SOURCE: -
CONTRACT_ID: kam.fundamentalDomain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B subset R^n
SOURCE_QUANTIFIERS: B subset R^n
SOURCE_CONCLUSION: defines the fundamental domain F_B = [0,1)^n x B of T^n x B, with product Lebesgue measure
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/FundamentalDomain.lean
FROZEN_DECL: KAM.fundamentalDomain
FROZEN_ANCHOR_ID: kam.fundamentalDomain.v1
FROZEN_ABI_SHA256: 810177265bdc6565103c4424a87272ae1769c4479cde418f98ce4b0c917946c2
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.fundamentalDomain (KAM/Frozen/Defs/FundamentalDomain.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:hamiltonian#hamiltonianVectorField
KIND: definition
TITLE: Hamiltonian vector fields, symplectic form: KAM.hamiltonianVectorField
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:hamiltonian@L47-L55
PROOF_SOURCE: -
CONTRACT_ID: kam.hamiltonianVectorField
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H : R^n x R^n -> R
SOURCE_QUANTIFIERS: H real function on R^n x R^n, point z
SOURCE_CONCLUSION: defines X_H(z) = (d_I H(z), -d_theta H(z))
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/HamiltonianVectorField.lean
FROZEN_DECL: KAM.hamiltonianVectorField
FROZEN_ANCHOR_ID: kam.hamiltonianVectorField.v1
FROZEN_ABI_SHA256: 427a145572df4c3e14079cf88feb16d60e1cd92fcd1770faddd36ad706562ca6
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.hamiltonianVectorField (KAM/Frozen/Defs/HamiltonianVectorField.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:hamiltonian#hamiltonianVectorFieldC
KIND: definition
TITLE: Hamiltonian vector fields, symplectic form: KAM.hamiltonianVectorFieldℂ
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:hamiltonian@L47-L55
PROOF_SOURCE: -
CONTRACT_ID: kam.hamiltonianVectorFieldℂ
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h holomorphic on an open subset of C^n x C^n
SOURCE_QUANTIFIERS: h holomorphic on an open subset of C^n x C^n, point z
SOURCE_CONCLUSION: defines X_h by the same formula as X_H with complex derivatives: X_h(z) = (d_I h(z), -d_theta h(z))
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/HamiltonianVectorFieldC.lean
FROZEN_DECL: KAM.hamiltonianVectorFieldℂ
FROZEN_ANCHOR_ID: kam.hamiltonianVectorFieldℂ.v1
FROZEN_ABI_SHA256: 482764b7e8e1691b3c3c182bca9b959f0d657e126c6b21b837ff0516f91e4f0d
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.hamiltonianVectorFieldℂ (KAM/Frozen/Defs/HamiltonianVectorFieldC.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:hamiltonian#symplecticForm
KIND: definition
TITLE: Hamiltonian vector fields, symplectic form: KAM.symplecticForm
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:hamiltonian@L47-L55
PROOF_SOURCE: -
CONTRACT_ID: kam.symplecticForm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data: vectors (a,b),(c,d) in R^n x R^n)
SOURCE_QUANTIFIERS: (a,b),(c,d) in R^n x R^n
SOURCE_CONCLUSION: defines omega_0((a,b),(c,d)) = sum_i (b_i c_i - a_i d_i), i.e. omega_0 = sum_i dI_i ^ dtheta_i
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/SymplecticForm.lean
FROZEN_DECL: KAM.symplecticForm
FROZEN_ANCHOR_ID: kam.symplecticForm.v1
FROZEN_ABI_SHA256: 542b8d8eb08283f5c961a969dd96003cbb23fc447da8ea444498cb92a48f6d75
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.symplecticForm (KAM/Frozen/Defs/SymplecticForm.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:hamiltonian#omegaZero
KIND: definition
TITLE: Hamiltonian vector fields, symplectic form: KAM.omegaZero
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:hamiltonian@L47-L55
PROOF_SOURCE: -
CONTRACT_ID: kam.omegaZero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data: (a,b) in vectors of R^n x R^n or C^n x C^n)
SOURCE_QUANTIFIERS: (a,b) in R^n x R^n (and its complexification)
SOURCE_CONCLUSION: defines Omega_0(a,b) = (-b,a), the matrix [[0,-I],[I,0]] of omega_0
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/OmegaZero.lean
FROZEN_DECL: KAM.omegaZero
FROZEN_ANCHOR_ID: kam.omegaZero.v1
FROZEN_ABI_SHA256: 32a39d2730c3b399c1bb81f1b709931dbdea47635807e8036db3b25116ef457b
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.omegaZero (KAM/Frozen/Defs/OmegaZero.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:nearlyintegrable#realHamiltonian
KIND: definition
TITLE: The integrable part, the perturbation, the frequency map: KAM.realHamiltonian
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:nearlyintegrable@L65-L71
PROOF_SOURCE: -
CONTRACT_ID: kam.realHamiltonian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h : C^n -> C; f : C^n x C^n -> C
SOURCE_QUANTIFIERS: h, f as stated; (theta,I) real points
SOURCE_CONCLUSION: defines the real Hamiltonian H(theta,I) = Re(h(I) + f(theta,I)) at real points
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/RealHamiltonian.lean
FROZEN_DECL: KAM.realHamiltonian
FROZEN_ANCHOR_ID: kam.realHamiltonian.v1
FROZEN_ABI_SHA256: ea510392f643a3fce65df6d4bc826d902d7b2277f67b0c009e3522d5659a0fab
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.realHamiltonian (KAM/Frozen/Defs/RealHamiltonian.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:nearlyintegrable#frequencyMap
KIND: definition
TITLE: The integrable part, the perturbation, the frequency map: KAM.frequencyMap
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:nearlyintegrable@L65-L71
PROOF_SOURCE: -
CONTRACT_ID: kam.frequencyMap
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h : C^n -> C; I real
SOURCE_QUANTIFIERS: h as stated, I real
SOURCE_CONCLUSION: defines the frequency map nabla h(I), the real gradient of I -> Re h(I) at real I
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/FrequencyMap.lean
FROZEN_DECL: KAM.frequencyMap
FROZEN_ANCHOR_ID: kam.frequencyMap.v1
FROZEN_ABI_SHA256: c9326077b299282bff92fdb8a3a849f512167fd4dc8e859bb0fdf1662f525cc5
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.frequencyMap (KAM/Frozen/Defs/FrequencyMap.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:torus#IsInvariantLagrangianTorus
KIND: definition
TITLE: Invariant Lagrangian torus: KAM.IsInvariantLagrangianTorus
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:torus@L73-L81
PROOF_SOURCE: -
CONTRACT_ID: kam.IsInvariantLagrangianTorus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H : R^n x R^n -> R; omega in R^n; K : R^n -> R^n x R^n
SOURCE_QUANTIFIERS: H, omega, K; (i)-(vi) quantified over theta, theta' in R^n, k in Z^n, u,v, t in R as displayed
SOURCE_CONCLUSION: defines K an invariant Lagrangian torus of H with frequency omega: (i) K real-analytic; (ii) K(theta+k)=K(theta)+(k,0); (iii) K(theta')=K(theta)+(k,0) implies theta'=theta+k; (iv) DK(theta) injective; (v) omega_0(DK u, DK v)=0; (vi) d/dt K(theta+t omega) = X_H(K(theta+t omega))
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/IsInvariantLagrangianTorus.lean
FROZEN_DECL: KAM.IsInvariantLagrangianTorus
FROZEN_ANCHOR_ID: kam.IsInvariantLagrangianTorus.v1
FROZEN_ABI_SHA256: 6b48dce61c4419bba274f6bb9fb3d9ae3eb888906c7eb1b5b35e1345d36fb925
DEPS: bp:p0:hamiltonian#symplecticForm, bp:p0:hamiltonian#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:hamiltonian#symplecticForm | blueprint/parts/p0-conventions.tex#bp:p0:torus@L77-L77 | condition (v) uses omega_0
EDGE: bp:p0:hamiltonian#hamiltonianVectorField | blueprint/parts/p0-conventions.tex#bp:p0:torus@L78-L78 | condition (vi) uses X_H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.IsInvariantLagrangianTorus (KAM/Frozen/Defs/IsInvariantLagrangianTorus.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:cover#kamCover
KIND: definition
TITLE: The KAM cover: KAM.kamCover
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:cover@L83-L89
PROOF_SOURCE: -
CONTRACT_ID: kam.kamCover
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h, f, B, r_0, tau, delta given
SOURCE_QUANTIFIERS: h,f,B,r_0,tau,delta; z; then exists K,omega,gamma,I_0
SOURCE_CONCLUSION: defines the KAM cover K(delta): the set of z in K(R^n) such that for some K,omega,gamma,I_0: gamma>0; omega in Dio_{gamma,tau}; K invariant Lagrangian torus of H with frequency omega; every action K(theta)_2 within r_0 of B; I_0 in B and nabla h(I_0)=omega; |K(theta)-(theta,I_0)| <= delta for all theta
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/KamCover.lean
FROZEN_DECL: KAM.kamCover
FROZEN_ANCHOR_ID: kam.kamCover.v1
FROZEN_ABI_SHA256: f9c676f0007ab98884cb96e9c3f8fb979465c5dcf587d8178451fb7846709f62
DEPS: bp:p0:diophantine#IsDiophantine, bp:p0:torus#IsInvariantLagrangianTorus, bp:p0:nearlyintegrable#realHamiltonian, bp:p0:nearlyintegrable#frequencyMap
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p0-conventions.tex#bp:p0:cover@L85-L85 | omega in Dio_{gamma,tau}
EDGE: bp:p0:torus#IsInvariantLagrangianTorus | blueprint/parts/p0-conventions.tex#bp:p0:cover@L85-L86 | K invariant Lagrangian torus of H
EDGE: bp:p0:nearlyintegrable#realHamiltonian | blueprint/parts/p0-conventions.tex#bp:p0:cover@L86-L86 | H is the real Hamiltonian built from h,f
EDGE: bp:p0:nearlyintegrable#frequencyMap | blueprint/parts/p0-conventions.tex#bp:p0:cover@L87-L87 | nabla h(I_0)=omega
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.kamCover (KAM/Frozen/Defs/KamCover.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:stripdata#IsPrimaryOnStrip
KIND: definition
TITLE: Torus data on strips: KAM.IsPrimaryOnStrip
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L91-L101
PROOF_SOURCE: -
CONTRACT_ID: kam.IsPrimaryOnStrip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K : C^n -> C^n x C^n; rho
SOURCE_QUANTIFIERS: K, rho; theta in T_rho, k in Z^n
SOURCE_CONCLUSION: defines K primary on T_rho: K(theta+k)=K(theta)+(k,0) for theta in T_rho, k in Z^n
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/IsPrimaryOnStrip.lean
FROZEN_DECL: KAM.IsPrimaryOnStrip
FROZEN_ANCHOR_ID: kam.IsPrimaryOnStrip.v1
FROZEN_ABI_SHA256: 3e3ec50a4ddc91e4ce8c9cc082a1bfb7387ad08b9dba70baed76847df2f86680
DEPS: bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L92-L92 | strip T_rho used in the definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.IsPrimaryOnStrip (KAM/Frozen/Defs/IsPrimaryOnStrip.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:stripdata#IsRealOnReals
KIND: definition
TITLE: Torus data on strips: KAM.IsRealOnReals
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L91-L101
PROOF_SOURCE: -
CONTRACT_ID: kam.IsRealOnReals
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K : C^n -> C^n x C^n
SOURCE_QUANTIFIERS: K
SOURCE_CONCLUSION: defines K real on reals: K(R^n) subset R^n x R^n
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/IsRealOnReals.lean
FROZEN_DECL: KAM.IsRealOnReals
FROZEN_ANCHOR_ID: kam.IsRealOnReals.v1
FROZEN_ABI_SHA256: 6549c22016139f44ca97ba901aa4927905970838ce283fef53b30c223dfabbb5
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.IsRealOnReals (KAM/Frozen/Defs/IsRealOnReals.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:stripdata#invarianceError
KIND: definition
TITLE: Torus data on strips: KAM.invarianceError
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L91-L101
PROOF_SOURCE: -
CONTRACT_ID: kam.invarianceError
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K : C^n -> C^n x C^n; h holomorphic; omega in R^n
SOURCE_QUANTIFIERS: h, K, omega, theta
SOURCE_CONCLUSION: defines the invariance error E(theta) = X_h(K(theta)) - DK(theta) omega
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/InvarianceError.lean
FROZEN_DECL: KAM.invarianceError
FROZEN_ANCHOR_ID: kam.invarianceError.v1
FROZEN_ABI_SHA256: 775e46d01cc020277055f39825a2dbea7f42d822652ba4c92b95c3159fc0a273
DEPS: bp:p0:hamiltonian#hamiltonianVectorFieldC
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:hamiltonian#hamiltonianVectorFieldC | blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L94-L94 | E uses X_h
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.invarianceError (KAM/Frozen/Defs/InvarianceError.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:stripdata#dotC
KIND: definition
TITLE: Torus data on strips: KAM.dotℂ
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L91-L101
PROOF_SOURCE: -
CONTRACT_ID: kam.dotℂ
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: u,v in C^n x C^n
SOURCE_QUANTIFIERS: n fixed; u,v in C^n x C^n
SOURCE_CONCLUSION: defines dotC(u,v)=sum_i (u_1i v_1i + u_2i v_2i), the bilinear non-conjugated pairing used by the transpose formulas
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/DotC.lean
FROZEN_DECL: KAM.dotℂ
FROZEN_ANCHOR_ID: kam.dotℂ.v1
FROZEN_ABI_SHA256: 6d938a769932067b5668f7e0b3bb92a62331b9be8f6a13b7a625af3b5eed362b
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.dotℂ (KAM/Frozen/Defs/DotC.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:stripdata#gramMatrix
KIND: definition
TITLE: Torus data on strips: KAM.gramMatrix
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L91-L101
PROOF_SOURCE: -
CONTRACT_ID: kam.gramMatrix
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K : C^n -> C^n x C^n; L = DK (a 2n x n matrix)
SOURCE_QUANTIFIERS: K, theta
SOURCE_CONCLUSION: defines the Gram matrix L^T L with L = DK and the bilinear transpose
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/GramMatrix.lean
FROZEN_DECL: KAM.gramMatrix
FROZEN_ANCHOR_ID: kam.gramMatrix.v1
FROZEN_ABI_SHA256: 3990b90567c6199a3443b1021021aab73e8e5b521b377b96f62981c2b57834ef
DEPS: bp:p0:stripdata#dotC
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:stripdata#dotC | blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L95-L95 | Gram matrix uses the bilinear transpose
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.gramMatrix (KAM/Frozen/Defs/GramMatrix.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:stripdata#normalFrame
KIND: definition
TITLE: Torus data on strips: KAM.normalFrame
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L91-L101
PROOF_SOURCE: -
CONTRACT_ID: kam.normalFrame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: K:C^n->C^n x C^n and theta in C^n; L=DK; no invertibility premise
SOURCE_QUANTIFIERS: K, theta
SOURCE_CONCLUSION: defines B=(L^T L)^{-1} using the total matrix inverse and N=Omega_0 L B; invertibility is a later theorem hypothesis, not a premise of this definition
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/NormalFrame.lean
FROZEN_DECL: KAM.normalFrame
FROZEN_ANCHOR_ID: kam.normalFrame.v1
FROZEN_ABI_SHA256: 86b86c14c2624b16a514c56a00d7ae7b1798ef789d9f1556d2a2c2ac8c4af95b
DEPS: bp:p0:stripdata#gramMatrix, bp:p0:hamiltonian#omegaZero
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:stripdata#gramMatrix | blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L96-L96 | B=(L^T L)^{-1} from the Gram matrix
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L96-L96 | N = Omega_0 L B
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.normalFrame (KAM/Frozen/Defs/NormalFrame.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:stripdata#torsion
KIND: definition
TITLE: Torus data on strips: KAM.torsion
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L91-L101
PROOF_SOURCE: -
CONTRACT_ID: kam.torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K, h, omega as above; N the normal frame
SOURCE_QUANTIFIERS: h, K, omega, theta
SOURCE_CONCLUSION: defines X_N = DX_h(K) N - DN[omega] and the torsion T = N^T Omega_0 X_N
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/Torsion.lean
FROZEN_DECL: KAM.torsion
FROZEN_ANCHOR_ID: kam.torsion.v1
FROZEN_ABI_SHA256: 6248d8a94564264c3e8525e65f1a6a645815608c795c7def60f04eea1c61a493
DEPS: bp:p0:stripdata#normalFrame, bp:p0:hamiltonian#hamiltonianVectorFieldC, bp:p0:hamiltonian#omegaZero, bp:p0:stripdata#dotC
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:stripdata#normalFrame | blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L96-L97 | X_N and T use the normal frame N
EDGE: bp:p0:hamiltonian#hamiltonianVectorFieldC | blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L96-L96 | X_N uses DX_h
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L97-L97 | T = N^T Omega_0 X_N
EDGE: bp:p0:stripdata#dotC | blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L97-L97 | N^T ... uses the bilinear transpose
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.torsion (KAM/Frozen/Defs/Torsion.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:stripdata#torsionAverage
KIND: definition
TITLE: Torus data on strips: KAM.torsionAverage
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L91-L101
PROOF_SOURCE: -
CONTRACT_ID: kam.torsionAverage
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K, h, omega as above
SOURCE_QUANTIFIERS: h, K, omega
SOURCE_CONCLUSION: defines the torsion average avg(T) = int_{[0,1]^n} T(theta) dtheta
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/TorsionAverage.lean
FROZEN_DECL: KAM.torsionAverage
FROZEN_ANCHOR_ID: kam.torsionAverage.v1
FROZEN_ABI_SHA256: 40ce1d2056d5a44fae79b3f6a61108242c23a931d7d577028d8a70b9352e655d
DEPS: bp:p0:stripdata#torsion
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:stripdata#torsion | blueprint/parts/p0-conventions.tex#bp:p0:stripdata@L97-L97 | average of T
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.torsionAverage (KAM/Frozen/Defs/TorsionAverage.lean)
LEAN_NOTE: sealed frozen definition (manifest SEALED since D11); formalized, nothing to prove
NOTE: -

NODE: bp:p0:head
KIND: theorem
TITLE: HEAD: positive-measure KAM with rate
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:head@L105-L115
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p0:head@L1202-L1232
CONTRACT_ID: kam.kam_positive_measure
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 2; tau > n-1; s_0, r_0 > 0; B subset R^n open and bounded with meas{I in B : dist(I,B^c) < delta} <= C_B delta for all delta > 0; h holomorphic on B_{r_0}, real on real points, with |I-J| <= L |nabla h(I) - nabla h(J)| on closure of B; f holomorphic on D(s_0,r_0)=T_{s_0} x B_{r_0}, 1-periodic in theta, real on real points; epsilon <= epsilon_0 with |f| <= epsilon on D(s_0,r_0)
SOURCE_QUANTIFIERS: n,tau,s_0,r_0,B,h (with witnesses C_B, L) fixed first; then exists C, epsilon_0 > 0; then for all f, epsilon
SOURCE_CONCLUSION: meas(F_B \ K(C sqrt(epsilon))) <= C epsilon^{1/4}
CONSTANT_SCOPE: C, epsilon_0 depend only on the data n, tau, s_0, r_0, B, h (and the witnesses C_B, L); not on f or epsilon
FROZEN_FILE: KAM/Frozen/Theorems/KamPositiveMeasure.lean
FROZEN_DECL: KAM.kam_positive_measure
FROZEN_ANCHOR_ID: kam.kam_positive_measure.v1
FROZEN_ABI_SHA256: 4c734e37b56b161f141cf03c217a4b47c7014dac1370c1f7863676c39c7c1538
DEPS: step:p4:head-empty, step:p4:head-constants, step:p4:head-negative, step:p4:head-positive, step:p4:head-zero, bp:p0:domains#complexStrip, bp:p0:domains#actionNbhd, bp:p0:domains#fundamentalDomain, bp:p0:cover#kamCover, bp:p0:nearlyintegrable#frequencyMap
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:head-empty | blueprint/parts/p4-measure.tex#bp:p0:head@L1203-L1203 | proof step of this result
EDGE: step:p4:head-constants | blueprint/parts/p4-measure.tex#bp:p0:head@L1206-L1206 | proof step of this result
EDGE: step:p4:head-negative | blueprint/parts/p4-measure.tex#bp:p0:head@L1216-L1216 | proof step of this result
EDGE: step:p4:head-positive | blueprint/parts/p4-measure.tex#bp:p0:head@L1220-L1220 | proof step of this result
EDGE: step:p4:head-zero | blueprint/parts/p4-measure.tex#bp:p0:head@L1228-L1228 | proof step of this result
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p0-conventions.tex#bp:p0:head@L109-L109 | strip T_{s_0} in D(s_0,r_0)
EDGE: bp:p0:domains#actionNbhd | blueprint/parts/p0-conventions.tex#bp:p0:head@L108-L108 | B_{r_0} in the phase domain and in h holomorphic on B_{r_0}
EDGE: bp:p0:domains#fundamentalDomain | blueprint/parts/p0-conventions.tex#bp:p0:head@L112-L112 | F_B in the conclusion
EDGE: bp:p0:cover#kamCover | blueprint/parts/p0-conventions.tex#bp:p0:head@L112-L112 | K(C sqrt eps) in the conclusion
EDGE: bp:p0:nearlyintegrable#frequencyMap | blueprint/parts/p0-conventions.tex#bp:p0:head@L108-L108 | nabla h in the nondegeneracy inequality
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.kam_positive_measure (SEALED: by exact KAM.Provider.kam_positive_measure …; provider via KAM.Provider.exists_gValid + KAM.Head.head_of_gValid)
LEAN_NOTE: SEALED 2026-10-27 (D26): provider package P4-S1 (audit docs/campaign/audits/P4-S1-audit-1.md PASS, exact-type probe) on P4-12 (audit P4-12-audit-1.md PASS); axioms propext/Classical.choice/Quot.sound; leanchecker replay of the frozen module, provider and KAM.Head.Assembly exit 0
NOTE: -

NODE: bp:p0:headq
KIND: theorem
TITLE: HEAD-Q: qualitative form
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:headq@L117-L122
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p0:headq@L1270-L1305
CONTRACT_ID: kam.kam_positive_measure_qualitative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: same data as HEAD (n >= 2; tau > n-1; s_0, r_0 > 0; B open bounded; h holomorphic on B_{r_0}, real on real points, nondegeneracy |I-J| <= L|nabla h(I)-nabla h(J)| on closure of B) but without the boundary-layer condition; f, epsilon as in HEAD with epsilon <= epsilon_0
SOURCE_QUANTIFIERS: n,tau,s_0,r_0,B,h fixed; for every kappa > 0 there exists epsilon_0 > 0; then for all f, epsilon
SOURCE_CONCLUSION: meas(F_B \ K(kappa)) <= kappa meas(F_B)
CONSTANT_SCOPE: epsilon_0 depends on kappa and the data n, tau, s_0, r_0, B, h; not on f or epsilon
FROZEN_FILE: KAM/Frozen/Theorems/KamPositiveMeasureQualitative.lean
FROZEN_DECL: KAM.kam_positive_measure_qualitative
FROZEN_ANCHOR_ID: kam.kam_positive_measure_qualitative.v1
FROZEN_ABI_SHA256: 3cac1e4650a580f08a539ba876442f6608e36106126a0d57948d4e246c090a21
DEPS: step:p4:hq-trivial, step:p4:hq-approx, step:p4:hq-head, step:p4:hq-transfer, step:p4:hq-cover, bp:p0:head, bp:p0:domains#complexStrip, bp:p0:domains#actionNbhd, bp:p0:domains#fundamentalDomain, bp:p0:cover#kamCover, bp:p0:nearlyintegrable#frequencyMap
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:hq-trivial | blueprint/parts/p4-measure.tex#bp:p0:headq@L1271-L1271 | proof step of this result
EDGE: step:p4:hq-approx | blueprint/parts/p4-measure.tex#bp:p0:headq@L1276-L1276 | proof step of this result
EDGE: step:p4:hq-head | blueprint/parts/p4-measure.tex#bp:p0:headq@L1279-L1279 | proof step of this result
EDGE: step:p4:hq-transfer | blueprint/parts/p4-measure.tex#bp:p0:headq@L1289-L1289 | proof step of this result
EDGE: step:p4:hq-cover | blueprint/parts/p4-measure.tex#bp:p0:headq@L1297-L1297 | proof step of this result
EDGE: bp:p0:head | blueprint/parts/p4-measure.tex#step:p4:hq-head@L1280-L1286 | HEAD applied to B-prime; its premises are supplied at L1278-L1282, with perturbation restriction at L1288-L1292
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p0-conventions.tex#bp:p0:headq@L119-L119 | strip T_{s_0} in D(s_0,r_0)
EDGE: bp:p0:domains#actionNbhd | blueprint/parts/p0-conventions.tex#bp:p0:headq@L119-L119 | B_{r_0} in the phase domain and in h holomorphic on B_{r_0}
EDGE: bp:p0:domains#fundamentalDomain | blueprint/parts/p0-conventions.tex#bp:p0:headq@L120-L120 | F_B in the conclusion
EDGE: bp:p0:cover#kamCover | blueprint/parts/p0-conventions.tex#bp:p0:headq@L120-L120 | K(kappa) in the qualitative conclusion
EDGE: bp:p0:nearlyintegrable#frequencyMap | blueprint/parts/p0-conventions.tex#bp:p0:headq@L119-L119 | nabla h in the nondegeneracy inequality
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.kam_positive_measure_qualitative (SEALED: by exact KAM.Provider.kam_positive_measure_qualitative …; provider = KAM.Head.headq_of_head applied to the sealed HEAD)
LEAN_NOTE: SEALED 2026-10-28 (D26): provider package P4-S2 (audit docs/campaign/audits/P4-S2-audit-1.md PASS, exact-type probe) on P4-Q (audit P4-Q-audit-1.md PASS); axioms propext/Classical.choice/Quot.sound; leanchecker replay of the frozen module, provider and KAM.Head.HeadQ exit 0
NOTE: -

NODE: bp:p0:g1
KIND: theorem
TITLE: G1: a-posteriori KAM at fixed frequency
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:g1@L124-L140
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:g1@L1110-L1143
CONTRACT_ID: kam.aposteriori_kam
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 2; tau >= n-1; 0 < rho_inf < rho; M, sigma_K, sigma_B, sigma_T, mu, gammabar > 0; mathfrak B subset C^n x C^n open and invariant under theta -> theta+k; h holomorphic on mathfrak B, 1-periodic in theta, real on real points, |Dh|,|X_h|,|DX_h|,|D^2X_h| <= M on mathfrak B; K holomorphic on T_rho, primary, real on reals, B_mu(K(theta)) subset mathfrak B and |DK| <= sigma_K - mu on T_rho; L^T L invertible with |B| <= sigma_B - mu on T_rho; avg(T) invertible with |avg(T)^{-1}| <= sigma_T - mu; 0 < gamma <= gammabar and omega in Dio_{gamma,tau}; |E| <= e on T_rho; C_1 e/(gamma^4 rho^{4 tau}) < 1
SOURCE_QUANTIFIERS: n,tau,rho_inf,rho,M,sigma_K,sigma_B,sigma_T,mu,gammabar fixed; exists C_1,C_2 > 0; for all mathfrak B,h,K,omega,gamma,e satisfying the hypotheses
SOURCE_CONCLUSION: exists K_inf holomorphic on T_{rho_inf}, primary, real on reals, with E_inf = 0 on T_{rho_inf}, B_{mu/2}(K_inf(theta)) subset mathfrak B, |DK_inf| <= sigma_K - mu/2, and |K_inf - K| <= C_2 e/(gamma^2 rho^{2 tau}) on T_{rho_inf}
CONSTANT_SCOPE: C_1, C_2 > 0 chosen after the fixed data (n,tau,rho_inf,rho,M,sigma_K,sigma_B,sigma_T,mu,gammabar) and before mathfrak B,h,K,omega,gamma,e; independent of these (in particular of gamma below gammabar, and of the torus)
FROZEN_FILE: KAM/Frozen/Theorems/AposterioriKam.lean
FROZEN_DECL: KAM.aposteriori_kam
FROZEN_ANCHOR_ID: kam.aposteriori_kam.v1
FROZEN_ABI_SHA256: 15dbaab5a036f69e52d0659874d64abe6fdd36e0f235973db368792c615ee293
DEPS: bp:p2:g1, bp:p0:diophantine#IsDiophantine, bp:p0:domains#complexStrip, bp:p0:hamiltonian#hamiltonianVectorFieldC, bp:p0:stripdata#IsPrimaryOnStrip, bp:p0:stripdata#IsRealOnReals, bp:p0:stripdata#invarianceError, bp:p0:stripdata#gramMatrix, bp:p0:stripdata#torsionAverage
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:g1 | blueprint/parts/p2-aposteriori.tex#bp:p2:g1@L1132-L1142 | the explicit-constant theorem verifies all seven clauses of the frozen G1 conclusion
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p0-conventions.tex#bp:p0:g1@L132-L132 | omega in Dio_{gamma,tau}
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p0-conventions.tex#bp:p0:g1@L130-L130 | strips T_rho
EDGE: bp:p0:hamiltonian#hamiltonianVectorFieldC | blueprint/parts/p0-conventions.tex#bp:p0:g1@L129-L129 | X_h bounds
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p0-conventions.tex#bp:p0:g1@L130-L130 | K primary
EDGE: bp:p0:stripdata#IsRealOnReals | blueprint/parts/p0-conventions.tex#bp:p0:g1@L130-L130 | K real on reals
EDGE: bp:p0:stripdata#invarianceError | blueprint/parts/p0-conventions.tex#bp:p0:g1@L133-L133 | error E
EDGE: bp:p0:stripdata#gramMatrix | blueprint/parts/p0-conventions.tex#bp:p0:g1@L131-L131 | L^T L and B
EDGE: bp:p0:stripdata#torsionAverage | blueprint/parts/p0-conventions.tex#bp:p0:g1@L131-L131 | avg(T)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.aposteriori_kam (SEALED: by exact KAM.Provider.aposteriori_kam …; provider ⟨_, _, KAM.Apost.g1_explicit …⟩)
LEAN_NOTE: SEALED 2026-10-27 (D26): provider package P2-14, audit docs/campaign/audits/P2-14-audit-1.md PASS WITH NOTES (exact-type probe); axioms propext/Classical.choice/Quot.sound; leanchecker replay of the frozen module, provider, KAM.Apost.G1 and KAM.Apost.Limit exit 0
NOTE: -

NODE: bp:p0:g2
KIND: theorem
TITLE: G2: local uniqueness for flows
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:g2@L142-L155
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p0:g2@L512-L568
CONTRACT_ID: kam.local_uniqueness_flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 2; tau >= n-1; rho > 0; M, sigma_K, sigma_B, sigma_T, mu > 0; mathfrak B open and Z^n-invariant; h holomorphic, periodic, real, |Dh|,|X_h|,|DX_h|,|D^2X_h| <= M; omega in Dio_{gamma,tau} with gamma > 0 (no upper bound, no smallness); K_1 holomorphic on T_rho, primary, real on reals, B_mu(K_1(theta)) subset mathfrak B, |DK_1| <= sigma_K - mu, L^T L invertible with |B| <= sigma_B - mu on T_rho, avg(T) invertible with |avg(T)^{-1}| <= sigma_T - mu, E_1 = 0 on T_rho; K_2 holomorphic on T_rho, primary, real on reals, K_2(T_rho) subset mathfrak B, E_2 = 0; |K_1 - K_2| <= c gamma^2 rho^{2 tau} on T_rho
SOURCE_QUANTIFIERS: n,tau,rho,M,sigma_K,sigma_B,sigma_T,mu fixed; exists c > 0; for all mathfrak B,h,K_1,K_2,omega,gamma satisfying the hypotheses
SOURCE_CONCLUSION: exists phi in R^n with K_2(theta) = K_1(theta+phi) on T_{rho/2}
CONSTANT_SCOPE: c > 0 depends only on n,tau,rho,M,sigma_K,sigma_B,sigma_T,mu; not on gamma, mathfrak B, h, K_1, K_2, omega
FROZEN_FILE: KAM/Frozen/Theorems/LocalUniquenessFlow.lean
FROZEN_DECL: KAM.local_uniqueness_flow
FROZEN_ANCHOR_ID: kam.local_uniqueness_flow.v1
FROZEN_ABI_SHA256: 60351404d1e73fe60603199359120cf75ed2012677c70fc7a56d21e117a0f2e7
DEPS: step:p3:g2-constant, step:p3:g2-smallness, step:p3:g2-phase, step:p3:g2-size, step:p3:g2-iteration, step:p3:g2-conclusion, bp:p0:diophantine#IsDiophantine, bp:p0:domains#complexStrip, bp:p0:hamiltonian#hamiltonianVectorFieldC, bp:p0:stripdata#IsPrimaryOnStrip, bp:p0:stripdata#IsRealOnReals, bp:p0:stripdata#invarianceError, bp:p0:stripdata#gramMatrix, bp:p0:stripdata#torsionAverage
ROUTES: -
ROUTE_FOR: -
EDGE: step:p3:g2-constant | blueprint/parts/p3-uniqueness.tex#bp:p0:g2@L513-L513 | proof step of this result
EDGE: step:p3:g2-smallness | blueprint/parts/p3-uniqueness.tex#bp:p0:g2@L526-L526 | proof step of this result
EDGE: step:p3:g2-phase | blueprint/parts/p3-uniqueness.tex#bp:p0:g2@L535-L535 | proof step of this result
EDGE: step:p3:g2-size | blueprint/parts/p3-uniqueness.tex#bp:p0:g2@L540-L540 | proof step of this result
EDGE: step:p3:g2-iteration | blueprint/parts/p3-uniqueness.tex#bp:p0:g2@L549-L549 | proof step of this result
EDGE: step:p3:g2-conclusion | blueprint/parts/p3-uniqueness.tex#bp:p0:g2@L565-L565 | proof step of this result
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p0-conventions.tex#bp:p0:g2@L145-L145 | omega in Dio_{gamma,tau}
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p0-conventions.tex#bp:p0:g2@L146-L146 | strips T_rho
EDGE: bp:p0:hamiltonian#hamiltonianVectorFieldC | blueprint/parts/p0-conventions.tex#bp:p0:g2@L145-L145 | X_h bounds
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p0-conventions.tex#bp:p0:g2@L146-L146 | K primary
EDGE: bp:p0:stripdata#IsRealOnReals | blueprint/parts/p0-conventions.tex#bp:p0:g2@L146-L146 | K real on reals
EDGE: bp:p0:stripdata#invarianceError | blueprint/parts/p0-conventions.tex#bp:p0:g2@L149-L149 | error E
EDGE: bp:p0:stripdata#gramMatrix | blueprint/parts/p0-conventions.tex#bp:p0:g2@L147-L147 | L^T L and B
EDGE: bp:p0:stripdata#torsionAverage | blueprint/parts/p0-conventions.tex#bp:p0:g2@L148-L148 | avg(T)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.local_uniqueness_flow (SEALED: by exact KAM.Provider.local_uniqueness_flow …; provider ⟨_, KAM.Uniq.g2_explicit …⟩)
LEAN_NOTE: SEALED 2026-10-27 (D26): provider package P3-5, audit docs/campaign/audits/P3-5-audit-1.md PASS (exact-type probe); axioms propext/Classical.choice/Quot.sound; leanchecker replay of the frozen module, provider and KAM.Uniq.G2 exit 0
NOTE: -

NODE: bp:p0:g3
KIND: theorem
TITLE: G3: measure of the non-Diophantine set
STATEMENT_SOURCE: blueprint/parts/p0-conventions.tex#bp:p0:g3@L157-L162
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p0:g3@L104-L128
CONTRACT_ID: kam.volume_not_diophantine_le
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: tau > n-1; Omega subset R^n bounded
SOURCE_QUANTIFIERS: n,tau,Omega fixed; exists C; for every alpha > 0
SOURCE_CONCLUSION: meas{omega in Omega : omega not in Dio_{alpha,tau}} <= C alpha
CONSTANT_SCOPE: C depends only on n, tau and Omega (via a bound R with Omega subset [-R,R]^n); not on alpha
FROZEN_FILE: KAM/Frozen/Theorems/VolumeNotDiophantineLe.lean
FROZEN_DECL: KAM.volume_not_diophantine_le
FROZEN_ANCHOR_ID: kam.volume_not_diophantine_le.v1
FROZEN_ABI_SHA256: 719393036634dc4d232cc3586abd37667f6ec654c42eb21f15aac7eaeb4f374a
DEPS: step:p4:g3-n0, step:p4:g3-cube, step:p4:g3-union, step:p4:g3-sum, bp:p0:diophantine#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:g3-n0 | blueprint/parts/p4-measure.tex#bp:p0:g3@L105-L105 | proof step of this result
EDGE: step:p4:g3-cube | blueprint/parts/p4-measure.tex#bp:p0:g3@L109-L109 | proof step of this result
EDGE: step:p4:g3-union | blueprint/parts/p4-measure.tex#bp:p0:g3@L114-L114 | proof step of this result
EDGE: step:p4:g3-sum | blueprint/parts/p4-measure.tex#bp:p0:g3@L122-L122 | proof step of this result
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p0-conventions.tex#bp:p0:g3@L159-L159 | complement of Dio_{alpha,tau}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p0
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.volume_not_diophantine_le (SEALED via KAM.Provider.volume_not_diophantine_le)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:ext-cauchy
KIND: external
TITLE: Cauchy's formulas in one variable
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-cauchy@L56-L66
PROOF_SOURCE: -
CONTRACT_ID: bp:p1:ext-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi holomorphic on an open subset of C containing the closed disc |zeta-c|<=r, with values in W
SOURCE_QUANTIFIERS: phi, an open set, c, r, W fixed in the statement; then w with |w-c|<r
SOURCE_CONCLUSION: phi(w)=(2 pi i)^-1 oint_{|zeta-c|=r} phi(zeta)/(zeta-w) dzeta for |w-c|<r; phi'(c)=(2 pi i)^-1 oint phi(zeta)/(zeta-c)^2 dzeta; hence |phi'(c)|<=r^-1 max_{|zeta-c|=r}|phi(zeta)|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bp:p1:ext-rectangle
KIND: external
TITLE: Cauchy's theorem for rectangles
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-rectangle@L67-L70
PROOF_SOURCE: -
CONTRACT_ID: bp:p1:ext-rectangle
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi holomorphic (values in W) on an open subset of C containing a closed rectangle R with sides parallel to the axes
SOURCE_QUANTIFIERS: phi, R arbitrary with the stated properties
SOURCE_CONCLUSION: the integral of phi over the boundary of R vanishes
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bp:p1:ext-identity
KIND: external
TITLE: Identity theorem in one variable
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-identity@L71-L74
PROOF_SOURCE: -
CONTRACT_ID: bp:p1:ext-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi holomorphic on a connected open set S in C; phi vanishes on a nonempty open interval of R contained in S
SOURCE_QUANTIFIERS: S, phi, interval arbitrary with the stated properties
SOURCE_CONCLUSION: phi=0 on S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bp:p1:ext-mvt
KIND: external
TITLE: Mean value inequality
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-mvt@L75-L78
PROOF_SOURCE: -
CONTRACT_ID: bp:p1:ext-mvt
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
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bp:p1:ext-schwarz
KIND: external
TITLE: Symmetry of second derivatives
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-schwarz@L79-L81
PROOF_SOURCE: -
CONTRACT_ID: bp:p1:ext-schwarz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f differentiable near z; Df differentiable at z
SOURCE_QUANTIFIERS: f, z arbitrary with the stated properties
SOURCE_CONCLUSION: the bilinear map D^2f(z) is symmetric
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bp:p1:ext-integral
KIND: external
TITLE: Integrals
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-integral@L82-L86
PROOF_SOURCE: -
CONTRACT_ID: bp:p1:ext-integral
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
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bp:p1:ext-fourier
KIND: external
TITLE: Fourier series on the torus
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-fourier@L87-L91
PROOF_SOURCE: -
CONTRACT_ID: bp:p1:ext-fourier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v:R^n->C continuous and 1-periodic; sum_k |hat v_k|<infinity
SOURCE_QUANTIFIERS: v arbitrary with the stated properties; then x in R^n
SOURCE_CONCLUSION: v(x)=sum_k hat v_k chi_k(x) for every x in R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bp:p1:ext-lebesgue
KIND: external
TITLE: Lebesgue outer measure
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-lebesgue@L92-L94
PROOF_SOURCE: -
CONTRACT_ID: bp:p1:ext-lebesgue
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S subset of R^d
SOURCE_QUANTIFIERS: S arbitrary subset of R^d
SOURCE_CONCLUSION: meas S is the infimum of sum_j vol(R_j) over all countable covers of S by closed boxes R_j; meas is monotone and countably subadditive
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bp:p1:ext-banach
KIND: external
TITLE: Banach's fixed point theorem
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-banach@L95-L96
PROOF_SOURCE: -
CONTRACT_ID: bp:p1:ext-banach
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
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bp:p1:ext-cramer
KIND: external
TITLE: Cramer's rule
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-cramer@L97-L99
PROOF_SOURCE: -
CONTRACT_ID: bp:p1:ext-cramer
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
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bp:p1:operator-norms
KIND: lemma
TITLE: Operator norms, blocks, $\Omega_0$
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:operator-norms@L119-L123
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:operator-norms@L125-L146
CONTRACT_ID: bp:p1:operator-norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: max norms of Part 0 on vectors; matrices M; block matrices (A B; C D)
SOURCE_QUANTIFIERS: all matrices and blocks of any compatible sizes
SOURCE_CONCLUSION: operator norm of a matrix = max_i sum_j |M_ij|; block matrix norm <= max{|A|+|B|,|C|+|D|}; |Omega_0|=1, Omega_0^T=-Omega_0, Omega_0^2=-I
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:opn-rowsum, step:p1:opn-blocks, step:p1:opn-omega
EDGE: step:p1:opn-rowsum | blueprint/parts/p1-analysis.tex#bp:p1:operator-norms@L126-L126 | proof step of this result
EDGE: step:p1:opn-blocks | blueprint/parts/p1-analysis.tex#bp:p1:operator-norms@L135-L135 | proof step of this result
EDGE: step:p1:opn-omega | blueprint/parts/p1-analysis.tex#bp:p1:operator-norms@L140-L140 | proof step of this result
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.operator_norms
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:opn-rowsum
KIND: step
TITLE: Row sums
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:opn-rowsum@L126-L133
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:opn-rowsum@L126-L133
CONTRACT_ID: step:p1:opn-rowsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M in C^{p x q}; v in C^q with |v|<=1
SOURCE_QUANTIFIERS: for every row i; i_0 a row of largest sum
SOURCE_CONCLUSION: sup_{|v|<=1}|Mv| = max_i sum_j |M_ij| (operator norm equals the largest row sum, also for linear maps identified with matrices)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.matrix_operator_norm_rowSum
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:opn-blocks
KIND: step
TITLE: Blocks
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:opn-blocks@L135-L138
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:opn-blocks@L135-L138
CONTRACT_ID: step:p1:opn-blocks
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: block matrix (A B; C D) of compatible sizes; induced operator norms for max norms
SOURCE_QUANTIFIERS: rows of the upper and lower block rows
SOURCE_CONCLUSION: upper block-row sums <= |A|+|B|, lower <= |C|+|D|, so block norm <= max{|A|+|B|,|C|+|D|}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:opn-rowsum
EDGE: step:p1:opn-rowsum | blueprint/parts/p1-analysis.tex#step:p1:opn-blocks@L136-L136 | norm as largest row sum
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.matrix_operator_norm_blocks
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:opn-omega
KIND: step
TITLE: The matrix $\Omega_0$
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:opn-omega@L140-L145
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:opn-omega@L140-L145
CONTRACT_ID: step:p1:opn-omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Omega_0(a,b)=(-b,a) as defined in Part 0; induced operator norm for max norms
SOURCE_QUANTIFIERS: a,b in C^n
SOURCE_CONCLUSION: Omega_0^2=-I, Omega_0^T=-Omega_0, every row has one nonzero entry +-1, so |Omega_0|=1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:hamiltonian#omegaZero, step:p1:opn-rowsum
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p1-analysis.tex#step:p1:opn-omega@L141-L141 | Omega_0(a,b)=(-b,a) definition
EDGE: step:p1:opn-rowsum | blueprint/parts/p1-analysis.tex#step:p1:opn-omega@L145-L145 | norm equals largest row sum
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.matrix_operator_norm_omegaZero
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:matrix-norms
KIND: lemma
TITLE: Max-norm matrix facts
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:matrix-norms@L148-L153
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:matrix-norms@L155-L175
CONTRACT_ID: bp:p1:matrix-norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: norm |M|=max_i sum_j |M_ij|
SOURCE_QUANTIFIERS: M,N matrices of compatible sizes, v vector; M of size m x m' for the transpose bound; M of size 2n x q resp. p x 2n; M_1,M_2 stacked
SOURCE_CONCLUSION: |MN|<=|M||N|; |Mv|<=|M||v|; |M^T|<=m|M| (m x m' matrices); |Omega_0 M|=|M| (2n x q); |M Omega_0|=|M| (p x 2n); |(M_1;M_2)|=max{|M_1|,|M_2|}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:mn-products, step:p1:mn-transpose, step:p1:mn-signed
EDGE: step:p1:mn-products | blueprint/parts/p1-analysis.tex#bp:p1:matrix-norms@L156-L156 | proof step of this result
EDGE: step:p1:mn-transpose | blueprint/parts/p1-analysis.tex#bp:p1:matrix-norms@L162-L162 | proof step of this result
EDGE: step:p1:mn-signed | blueprint/parts/p1-analysis.tex#bp:p1:matrix-norms@L167-L167 | proof step of this result
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.matrix_norms
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:mn-products
KIND: step
TITLE: Products
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:mn-products@L156-L160
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:mn-products@L156-L160
CONTRACT_ID: step:p1:mn-products
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: matrices M,N and vector v of compatible sizes; induced operator norms for max norms
SOURCE_QUANTIFIERS: all compatible M,N,v
SOURCE_CONCLUSION: |Mv|<=|M||v| and |MN|<=|M||N|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:operator-norms
EDGE: bp:p1:operator-norms | blueprint/parts/p1-analysis.tex#step:p1:mn-products@L157-L157 | cited at this line (step; \ref{bp:p1:operator-norms})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.matrix_norm_products
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:mn-transpose
KIND: step
TITLE: Transposes
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:mn-transpose@L162-L165
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:mn-transpose@L162-L165
CONTRACT_ID: step:p1:mn-transpose
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M an m x m' matrix
SOURCE_QUANTIFIERS: row j of M^T
SOURCE_CONCLUSION: |M_ij|<=|M| and |M^T|<=m|M|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.matrix_norm_transpose
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:mn-signed
KIND: step
TITLE: $\Omega_0$ and stacked blocks
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:mn-signed@L167-L174
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:mn-signed@L167-L174
CONTRACT_ID: step:p1:mn-signed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Omega_0(a,b)=(-b,a) (Part 0): signed permutation matrix
SOURCE_QUANTIFIERS: M of sizes 2n x q, p x 2n; M_1,M_2 stacked
SOURCE_CONCLUSION: |Omega_0 M|=|M Omega_0|=|M| and |(M_1;M_2)|=max{|M_1|,|M_2|}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:hamiltonian#omegaZero
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p1-analysis.tex#step:p1:mn-signed@L168-L168 | Omega_0(a,b)=(-b,a) definition
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.matrix_norm_signed
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:neumann
KIND: lemma
TITLE: Neumann series
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:neumann@L177-L181
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:neumann@L183-L203
CONTRACT_ID: bp:p1:neumann
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A invertible; |A^-1||Delta|<=1/2; for the pointwise version A(theta), Delta(theta) matrix-valued with sup norms
SOURCE_QUANTIFIERS: A,Delta square matrices of the same size; pointwise version for theta in a set
SOURCE_CONCLUSION: A+Delta invertible, |(A+Delta)^-1|<=2|A^-1|, |(A+Delta)^-1-A^-1|<=2|A^-1|^2|Delta|; same pointwise for matrix-valued functions with sup norms
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:neu-series, step:p1:neu-inverse, step:p1:neu-difference, step:p1:neu-pointwise
EDGE: step:p1:neu-series | blueprint/parts/p1-analysis.tex#bp:p1:neumann@L184-L184 | proof step of this result
EDGE: step:p1:neu-inverse | blueprint/parts/p1-analysis.tex#bp:p1:neumann@L191-L191 | proof step of this result
EDGE: step:p1:neu-difference | blueprint/parts/p1-analysis.tex#bp:p1:neumann@L195-L195 | proof step of this result
EDGE: step:p1:neu-pointwise | blueprint/parts/p1-analysis.tex#bp:p1:neumann@L199-L199 | proof step of this result
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: matrix_isUnit_add_of_inv_norm_mul_le_half, matrix_norm_inv_add_le, matrix_norm_inv_add_sub_inv_le, matrix_neumann_uniform (KAM/Matrix/Neumann.lean:104,110,116,124); ring level isUn
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:neu-series
KIND: step
TITLE: The Neumann series
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:neu-series@L184-L189
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:neu-series@L184-L189
CONTRACT_ID: step:p1:neu-series
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A invertible square matrix; Delta of the same size; |A^{-1}| |Delta|<=1/2; max-norm operator norms; X denotes A^{-1}Delta
SOURCE_QUANTIFIERS: square matrices
SOURCE_CONCLUSION: |X^j|<=2^-j, S=sum_j (-X)^j converges absolutely, |S|<=2, S(I+X)=(I+X)S=I
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:matrix-norms, bp:p1:operator-norms
EDGE: bp:p1:matrix-norms | blueprint/parts/p1-analysis.tex#step:p1:neu-series@L185-L185 | cited at this line (step; \ref{bp:p1:matrix-norms})
EDGE: bp:p1:operator-norms | blueprint/parts/p1-analysis.tex#step:p1:neu-series@L188-L188 | cited at this line (step; \ref{bp:p1:operator-norms})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: BYPASSED
LEAN_REF: none: invertibility of I + X comes from Mathlib's isUnit_one_sub_of_norm_lt_one (used at Neumann.lean:39); S = Σ(-X)^j, ‖S‖ ≤ 2, S(I+X) = I are never stated
LEAN_NOTE: route substitution (D27): parent proved by Zohar's route; docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md)
NOTE: -

NODE: step:p1:neu-inverse
KIND: step
TITLE: The inverse of $A+\Delta$
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:neu-inverse@L191-L193
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:neu-inverse@L191-L193
CONTRACT_ID: step:p1:neu-inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A invertible square matrix; Delta of the same size; |A^{-1}| |Delta|<=1/2; max-norm operator norms; X=A^{-1}Delta; S=sum_{j>=0}(-X)^j
SOURCE_QUANTIFIERS: A,Delta as in lemma
SOURCE_CONCLUSION: A+Delta invertible with inverse S A^-1 and |(A+Delta)^-1|<=2|A^-1|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:neu-series, bp:p1:matrix-norms
EDGE: step:p1:neu-series | blueprint/parts/p1-analysis.tex#step:p1:neu-inverse@L192-L192 | S is the inverse of I+X with norm at most 2
EDGE: bp:p1:matrix-norms | blueprint/parts/p1-analysis.tex#step:p1:neu-inverse@L193-L193 | submultiplicativity
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: isUnit_add_of_inverse_norm_mul_le_half (:33), norm_inverse_add_le (:51)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:neu-difference
KIND: step
TITLE: The difference
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:neu-difference@L195-L197
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:neu-difference@L195-L197
CONTRACT_ID: step:p1:neu-difference
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A invertible square matrix; Delta of the same size; |A^{-1}| |Delta|<=1/2; max-norm operator norms
SOURCE_QUANTIFIERS: as in lemma
SOURCE_CONCLUSION: (A+Delta)^-1-A^-1=-(A+Delta)^-1 Delta A^-1 and |.|<=2|A^-1|^2|Delta|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:neu-inverse, bp:p1:matrix-norms
EDGE: step:p1:neu-inverse | blueprint/parts/p1-analysis.tex#step:p1:neu-difference@L196-L196 | inverse and its bound
EDGE: bp:p1:matrix-norms | blueprint/parts/p1-analysis.tex#step:p1:neu-difference@L197-L197 | submultiplicativity
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: inverse_sub_inverse_add (:45), norm_inverse_add_sub_inverse_le (:67)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:neu-pointwise
KIND: step
TITLE: Matrix-valued functions
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:neu-pointwise@L199-L202
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:neu-pointwise@L199-L202
CONTRACT_ID: step:p1:neu-pointwise
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A(theta) invertible, Delta(theta) for theta in S'; sup|A^-1| sup|Delta|<=1/2
SOURCE_QUANTIFIERS: theta in a set S'
SOURCE_CONCLUSION: hypothesis and conclusions hold at every theta, and pass to the suprema over S'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:neu-inverse, step:p1:neu-difference
EDGE: step:p1:neu-inverse | blueprint/parts/p1-analysis.tex#step:p1:neu-pointwise@L202-L202 | conclusions applied at each theta
EDGE: step:p1:neu-difference | blueprint/parts/p1-analysis.tex#step:p1:neu-pointwise@L202-L202 | conclusions applied at each theta
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: matrix_neumann_uniform (:124); adapter neumann_pointwise
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:real-inverse
KIND: lemma
TITLE: Real inverses
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:real-inverse@L205-L208
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:real-inverse@L210-L216
CONTRACT_ID: bp:p1:real-inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A an invertible real matrix; A(theta) real for real theta and invertible
SOURCE_QUANTIFIERS: A, theta arbitrary
SOURCE_CONCLUSION: A^-1 is real; A(theta)^-1 real for real theta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:ri-adjugate
EDGE: step:p1:ri-adjugate | blueprint/parts/p1-analysis.tex#bp:p1:real-inverse@L211-L211 | proof step of this result
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.real_inverse
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:ri-adjugate
KIND: step
TITLE: Adjugate
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ri-adjugate@L211-L215
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ri-adjugate@L211-L215
CONTRACT_ID: step:p1:ri-adjugate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A real invertible square matrix; for the pointwise clause A(theta) real at real theta and invertible
SOURCE_QUANTIFIERS: A real invertible
SOURCE_CONCLUSION: A^-1=(det A)^-1 adj A is real; the pointwise claim is the same at each real theta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-cramer
EDGE: bp:p1:ext-cramer | blueprint/parts/p1-analysis.tex#step:p1:ri-adjugate@L214-L214 | cited at this line (step; \ref{bp:p1:ext-cramer})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.real_inverse_adjugate
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:holomorphic-regularity
KIND: lemma
TITLE: Derivatives of holomorphic maps
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-regularity@L227-L236
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-regularity@L238-L294
CONTRACT_ID: bp:p1:holomorphic-regularity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U in C^m open; F:U->W holomorphic
SOURCE_QUANTIFIERS: U,F,W,m arbitrary; z in U; v,w in C^m; j>=1
SOURCE_CONCLUSION: DF:U->L(C^m,W) holomorphic; D^jF exists and is holomorphic for every j>=1, F is C^infty; |D^{j+1}F(z)|=|D^j(DF)(z)|=|D(D^jF)(z)|; D^2F(z)[v,w]=D^2F(z)[w,v]; d_i d_j F=d_j d_i F on U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:hreg-line, step:p1:hreg-integral, step:p1:hreg-differentiate, step:p1:hreg-full, step:p1:hreg-orders, step:p1:hreg-symmetry
EDGE: step:p1:hreg-line | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-regularity@L239-L239 | proof step of this result
EDGE: step:p1:hreg-integral | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-regularity@L247-L247 | proof step of this result
EDGE: step:p1:hreg-differentiate | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-regularity@L256-L256 | proof step of this result
EDGE: step:p1:hreg-full | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-regularity@L274-L274 | proof step of this result
EDGE: step:p1:hreg-orders | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-regularity@L281-L281 | proof step of this result
EDGE: step:p1:hreg-symmetry | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-regularity@L290-L290 | proof step of this result
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: differentiableOn_fderiv_of_isOpen (KAM/Strip/Regularity.lean:178), ..._pi (:120), contDiffOn_infty_of_differentiableOn (:163), contDiffOn_nat_of_differentiableOn (:173)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:hreg-line
KIND: step
TITLE: Cauchy's estimate along lines
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hreg-line@L239-L245
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hreg-line@L239-L245
CONTRACT_ID: step:p1:hreg-line
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; F:U->W holomorphic; x in U; r>0; closed P(x,r) subset U; |F|<=A there; |v|=1
SOURCE_QUANTIFIERS: x,r,A,v arbitrary with those properties
SOURCE_CONCLUSION: |DF(x)v|<=A/r for |v|=1 and hence |DF(x)|<=A/r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-cauchy
EDGE: bp:p1:ext-cauchy | blueprint/parts/p1-analysis.tex#step:p1:hreg-line@L243-L243 | cited at this line (step; \ref{bp:p1:ext-cauchy})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: norm_fderiv_le_of_closedBall_bound (Cauchy.lean:53; the blueprint cites it)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:hreg-integral
KIND: step
TITLE: A Cauchy integral for the derivative
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hreg-integral@L247-L254
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hreg-integral@L247-L254
CONTRACT_ID: step:p1:hreg-integral
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; F:U->W holomorphic; z_0 in U; r>0 with closed P(z_0,3r) subset U; A=max there; |v|=1; x in P(z_0,r)
SOURCE_QUANTIFIERS: z_0,r,A fixed; v, x then arbitrary
SOURCE_CONCLUSION: DF(x)v=(2 pi i)^-1 oint_{|zeta|=r} F(x+zeta v)/zeta^2 dzeta for x in P(z_0,r)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-cauchy
EDGE: bp:p1:ext-cauchy | blueprint/parts/p1-analysis.tex#step:p1:hreg-integral@L251-L251 | cited at this line (step; \ref{bp:p1:ext-cauchy})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: BYPASSED
LEAN_REF: none: the Cauchy integral for DF(x)v is used inside the proof of the next declaration (Mathlib deriv_eq_smul_circleIntegral)
LEAN_NOTE: route substitution (D27): parent proved by Zohar's route; docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md)
NOTE: -

NODE: step:p1:hreg-differentiate
KIND: step
TITLE: Differentiation under the integral
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hreg-differentiate@L256-L272
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hreg-differentiate@L256-L272
CONTRACT_ID: step:p1:hreg-differentiate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; F:U->W holomorphic; z_0 in U; r>0 with closed P(z_0,3r) subset U; A=max there; |v|=1; x in P(z_0,r); |h|<r-|x-z_0|
SOURCE_QUANTIFIERS: z_0,r,A,v fixed; x; then h
SOURCE_CONCLUSION: x->DF(x)v is complex differentiable at x in P(z_0,r) with derivative h->(2 pi i)^-1 oint DF(x+zeta v)h zeta^-2 dzeta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:hreg-line, step:p1:hreg-integral, bp:p1:ext-mvt, bp:p1:ext-integral
EDGE: step:p1:hreg-line | blueprint/parts/p1-analysis.tex#step:p1:hreg-differentiate@L258-L258 | line-estimate bound on DF(y)
EDGE: step:p1:hreg-integral | blueprint/parts/p1-analysis.tex#step:p1:hreg-differentiate@L269-L269 | Cauchy integral for DF(x)v
EDGE: bp:p1:ext-mvt | blueprint/parts/p1-analysis.tex#step:p1:hreg-differentiate@L263-L263 | bound on R(h,zeta)
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:hreg-differentiate@L265-L265 | dominated convergence
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: differentiableAt_fderiv_apply_of_bounded (Regularity.lean:47; the blueprint cites it)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:hreg-full
KIND: step
TITLE: The full derivative
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hreg-full@L274-L279
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hreg-full@L274-L279
CONTRACT_ID: step:p1:hreg-full
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; F:U->W holomorphic; z_0 in U; r>0 with closed P(z_0,3r) subset U
SOURCE_QUANTIFIERS: z_0 in U arbitrary
SOURCE_CONCLUSION: DF is holomorphic on P(z_0,r), hence on U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:hreg-differentiate
EDGE: step:p1:hreg-differentiate | blueprint/parts/p1-analysis.tex#step:p1:hreg-full@L275-L275 | cited at this line (step; \ref{step:p1:hreg-differentiate})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: differentiableOn_fderiv_of_isOpen_pi (:120), differentiableOn_fderiv_of_isOpen (:178)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:hreg-orders
KIND: step
TITLE: All orders
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hreg-orders@L281-L288
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hreg-orders@L281-L288
CONTRACT_ID: step:p1:hreg-orders
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; F:U->W holomorphic
SOURCE_QUANTIFIERS: j>=1; F, DF as the maps
SOURCE_CONCLUSION: every D^jF exists and is holomorphic, F is C^infty, and the norm identities |D^{j+1}F|=|D^j(DF)|=|D(D^jF)|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:hreg-full
EDGE: step:p1:hreg-full | blueprint/parts/p1-analysis.tex#step:p1:hreg-orders@L284-L284 | DF holomorphic, applied inductively to D^jF
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: contDiffOn_infty_of_differentiableOn (:163)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:hreg-symmetry
KIND: step
TITLE: Symmetry
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hreg-symmetry@L290-L293
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hreg-symmetry@L290-L293
CONTRACT_ID: step:p1:hreg-symmetry
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; F:U->W holomorphic
SOURCE_QUANTIFIERS: z in U; v,w
SOURCE_CONCLUSION: D^2F(z) symmetric; d_i d_j F=d_j d_i F
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:hreg-full, bp:p1:ext-schwarz
EDGE: step:p1:hreg-full | blueprint/parts/p1-analysis.tex#step:p1:hreg-symmetry@L291-L291 | DF differentiable
EDGE: bp:p1:ext-schwarz | blueprint/parts/p1-analysis.tex#step:p1:hreg-symmetry@L292-L292 | symmetry of D^2F(z)
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: -
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:holomorphic-analytic
KIND: lemma
TITLE: Holomorphic maps are analytic
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L296-L312
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L314-L362
CONTRACT_ID: bp:p1:holomorphic-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U in C^m open; F:U->W holomorphic; (a) z_0 in U, r>0 with P-bar(z_0,r) in U, A=max_{P-bar(z_0,r)}|F|; (b) U_R=U cap R^m, x_0 in U_R; W=C^p and F(U_R) in R^p for the real clause
SOURCE_QUANTIFIERS: F,U,W,m; then z_0,r (A determined); alpha in N^m
SOURCE_CONCLUSION: (a) exist c_alpha in W with |c_alpha|<=A r^-|alpha| and F(z)=sum_alpha c_alpha (z-z_0)^alpha on P(z_0,r), absolutely convergent; F analytic on U; (b) F|U_R real-analytic near each x_0 (power series in x-x_0, absolutely convergent); real coefficients if W=C^p and F(U_R) in R^p
CONSTANT_SCOPE: c_alpha depends on F,z_0,r only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:han-margin, step:p1:han-cauchy, step:p1:han-series, step:p1:han-bounds, step:p1:han-real
EDGE: step:p1:han-margin | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L315-L315 | proof step of this result
EDGE: step:p1:han-cauchy | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L319-L319 | proof step of this result
EDGE: step:p1:han-series | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L333-L333 | proof step of this result
EDGE: step:p1:han-bounds | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L345-L345 | proof step of this result
EDGE: step:p1:han-real | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L352-L352 | proof step of this result
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.holomorphic_analytic (+ KAM.holomorphic_analytic_real; engine KAM.analyticOnNhd_of_differentiableOn)
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:han-margin
KIND: step
TITLE: A larger polydisc
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:han-margin@L315-L317
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:han-margin@L315-L317
CONTRACT_ID: step:p1:han-margin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P-bar(z_0,r) in U compact, U open, F continuous
SOURCE_QUANTIFIERS: z_0,r as in (a)
SOURCE_CONCLUSION: exists r_1>r with P-bar(z_0,r_1) in U; A is finite
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.han_margin
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:han-cauchy
KIND: step
TITLE: Iterated Cauchy formula
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:han-cauchy@L319-L331
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:han-cauchy@L319-L331
CONTRACT_ID: step:p1:han-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; F:U->W holomorphic; z_0 in U; r>0 with closed P(z_0,r) subset U; A=max there; r_1 is the larger radius constructed in the margin step; w in P(z_0,r); C_j the coordinate circles of radius r
SOURCE_QUANTIFIERS: w in P(z_0,r); circles C_j around z_{0,j}
SOURCE_CONCLUSION: F(w)=(2 pi i)^-m oint_{C_1}...oint_{C_m} F(zeta)/prod(zeta_j-w_j) dzeta, as an integral over the torus C_1x...xC_m
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:han-margin, bp:p1:ext-cauchy, bp:p1:ext-integral
EDGE: step:p1:han-margin | blueprint/parts/p1-analysis.tex#step:p1:han-cauchy@L323-L323 | r_1>r so integrand holomorphic on larger disc
EDGE: bp:p1:ext-cauchy | blueprint/parts/p1-analysis.tex#step:p1:han-cauchy@L324-L324 | first Cauchy formula in each variable
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:han-cauchy@L331-L331 | Fubini
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.han_cauchy (torus form)
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:han-series
KIND: step
TITLE: Geometric expansion
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:han-series@L333-L343
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:han-series@L333-L343
CONTRACT_ID: step:p1:han-series
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; F:U->W holomorphic; z_0 in U; r>0 with closed P(z_0,r) subset U; A=max there; w in P(z_0,r); t=|w-z_0|/r; c_alpha denotes the displayed contour integral
SOURCE_QUANTIFIERS: w in P(z_0,r); zeta on the torus
SOURCE_CONCLUSION: F(w)=sum_alpha c_alpha (w-z_0)^alpha with c_alpha=(2 pi i)^-m oint...oint F(zeta)/prod(zeta_j-z_{0,j})^{alpha_j+1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:han-cauchy, bp:p1:ext-integral
EDGE: step:p1:han-cauchy | blueprint/parts/p1-analysis.tex#step:p1:han-series@L334-L334 | iterated Cauchy formula expanded
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:han-series@L338-L338 | term-by-term integration
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: BYPASSED
LEAN_REF: KAM.exists_powerSeries_coeff (expansion only)
LEAN_NOTE: route substitution (D27): the Lean proof expands by higher Cauchy estimates and Taylor along lines; the contour-integral identification of the coefficients is not formalized and no proved consumer uses it (I-STRIP-5 audits 1-2)
NOTE: -

NODE: step:p1:han-bounds
KIND: step
TITLE: Coefficient bounds
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:han-bounds@L345-L350
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:han-bounds@L345-L350
CONTRACT_ID: step:p1:han-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; F:U->W holomorphic; z_0 in U; r>0 with closed P(z_0,r) subset U; A=max there; c_alpha denotes the contour integral constructed in the previous step; w in P(z_0,r)
SOURCE_QUANTIFIERS: alpha in N^m; w in P(z_0,r)
SOURCE_CONCLUSION: |c_alpha|<=A r^-|alpha|; sum |c_alpha||(w-z_0)^alpha|<=A(1-t)^-m; part (a) holds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:han-series, bp:p1:ext-integral
EDGE: step:p1:han-series | blueprint/parts/p1-analysis.tex#step:p1:han-bounds@L346-L346 | coefficient formula
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:han-bounds@L346-L346 | integral estimate by length times sup
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.holomorphic_series (coefficient bounds, summability, tsum bound A(1-t)^(-m))
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27); the coefficients are the Lean expansion's, not identified with contour integrals (step han-series BYPASSED, D27)
NOTE: -

NODE: step:p1:han-real
KIND: step
TITLE: Real points
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:han-real@L352-L361
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:han-real@L352-L361
CONTRACT_ID: step:p1:han-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; F:U->W holomorphic; x_0 in U cap R^m; r>0 with closed P(x_0,r) subset U; additionally W=C^p and F real on U cap R^m for the real-coefficient clause
SOURCE_QUANTIFIERS: real x with |x-x_0|<r; W=C^p with F real on U_R for the second clause
SOURCE_CONCLUSION: F|U_R is a real power series in x-x_0, absolutely convergent near x_0; with real F, F(x)=sum (Re c_alpha)(x-x_0)^alpha, |Re c_alpha|<=|c_alpha|; this is (b)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:han-bounds
EDGE: step:p1:han-bounds | blueprint/parts/p1-analysis.tex#step:p1:han-real@L353-L353 | part (a) established
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.holomorphic_series_real, KAM.holomorphic_analytic_real
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:uniform-limits
KIND: lemma
TITLE: Uniform limits
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:uniform-limits@L364-L368
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:uniform-limits@L370-L402
CONTRACT_ID: bp:p1:uniform-limits
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K_s holomorphic on an open set V; K_s->K pointwise; DK_s->Lambda uniformly on V; for V=T_r, every K_s primary on T_r, respectively real on reals
SOURCE_QUANTIFIERS: V,K_s,K,Lambda; sequence index s
SOURCE_CONCLUSION: K holomorphic on V and DK=Lambda; if V=T_r and all K_s primary (resp. real on reals) then K is primary (resp. real on reals)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:ul-differences, step:p1:ul-limit, step:p1:ul-derivative, step:p1:ul-primary
EDGE: step:p1:ul-differences | blueprint/parts/p1-analysis.tex#bp:p1:uniform-limits@L374-L374 | proof step of this result
EDGE: step:p1:ul-limit | blueprint/parts/p1-analysis.tex#bp:p1:uniform-limits@L381-L381 | proof step of this result
EDGE: step:p1:ul-derivative | blueprint/parts/p1-analysis.tex#bp:p1:uniform-limits@L388-L388 | proof step of this result
EDGE: step:p1:ul-primary | blueprint/parts/p1-analysis.tex#bp:p1:uniform-limits@L396-L396 | proof step of this result
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.uniform_limits (+ KAM.uniform_limits_isPrimaryOnStrip, KAM.uniform_limits_isRealOnReals)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:ul-differences
KIND: step
TITLE: Linearization error of the differences
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ul-differences@L374-L379
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ul-differences@L374-L379
CONTRACT_ID: step:p1:ul-differences
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V subset C^m open; W finite-dimensional complex normed; K_s:V->W holomorphic; K_s->K pointwise; DK_s->Lambda uniformly on V; eta_s=sup_V |DK_s-Lambda| for sufficiently large s; x in V; P(x,r) subset V
SOURCE_QUANTIFIERS: x,r fixed; indices s,t; y in P(x,r)
SOURCE_CONCLUSION: |phi_st(y)-phi_st(x)|<=2(eta_s+eta_t)|y-x| for phi_st(y)=K_s(y)-K_t(y)-(DK_s(x)-DK_t(x))(y-x)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-mvt
EDGE: bp:p1:ext-mvt | blueprint/parts/p1-analysis.tex#step:p1:ul-differences@L378-L378 | cited at this line (step; \ref{bp:p1:ext-mvt})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: Mathlib hasFDerivAt_of_tendstoUniformlyOn (used by KAM.uniform_limits; cited by the blueprint)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:ul-limit
KIND: step
TITLE: Passage to the limit
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ul-limit@L381-L386
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ul-limit@L381-L386
CONTRACT_ID: step:p1:ul-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V subset C^m open; W finite-dimensional complex normed; K_s:V->W holomorphic; K_s->K pointwise; DK_s->Lambda uniformly on V; eta_s=sup_V |DK_s-Lambda| for sufficiently large s; x in V; P(x,r) subset V
SOURCE_QUANTIFIERS: x,r,s fixed; y in P(x,r); t->infinity
SOURCE_CONCLUSION: |K_s(y)-K(y)-(K_s(x)-K(x))-(DK_s(x)-Lambda(x))(y-x)|<=2 eta_s|y-x|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:ul-differences
EDGE: step:p1:ul-differences | blueprint/parts/p1-analysis.tex#step:p1:ul-limit@L382-L382 | difference estimate passed to limit
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: Mathlib hasFDerivAt_of_tendstoUniformlyOn (used by KAM.uniform_limits; cited by the blueprint)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:ul-derivative
KIND: step
TITLE: Differentiability of the limit
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ul-derivative@L388-L394
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ul-derivative@L388-L394
CONTRACT_ID: step:p1:ul-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V subset C^m open; W finite-dimensional complex normed; K_s:V->W holomorphic; K_s->K pointwise; DK_s->Lambda uniformly on V; eta_s=sup_V |DK_s-Lambda| for sufficiently large s; x in V; P(x,r) subset V; epsilon>0
SOURCE_QUANTIFIERS: eps>0, then s, then r'<=r
SOURCE_CONCLUSION: |K(y)-K(x)-Lambda(x)(y-x)|<=eps|y-x| for |y-x|<r'; Lambda(x) complex linear; K complex differentiable at x with DK(x)=Lambda(x)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:ul-limit
EDGE: step:p1:ul-limit | blueprint/parts/p1-analysis.tex#step:p1:ul-derivative@L391-L391 | cited at this line (step; \ref{step:p1:ul-limit})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: Mathlib hasFDerivAt_of_tendstoUniformlyOn (used by KAM.uniform_limits; cited by the blueprint)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:ul-primary
KIND: step
TITLE: Periodicity and realness
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ul-primary@L396-L401
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ul-primary@L396-L401
CONTRACT_ID: step:p1:ul-primary
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V=T_r, W=C^n x C^n; every K_s primary on T_r (resp. 1-periodic, resp. real on reals)
SOURCE_QUANTIFIERS: theta in T_r, k in Z^n; x in R^n
SOURCE_CONCLUSION: K(theta+k)=K(theta)+(k,0), K is 1-periodic where each K_s is, and K(R^n) in R^n x R^n since the latter is closed
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:stripdata#IsPrimaryOnStrip, bp:p0:stripdata#IsRealOnReals, bp:p0:domains#complexStrip
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p1-analysis.tex#step:p1:ul-primary@L397-L397 | primary on T_r
EDGE: bp:p0:stripdata#IsRealOnReals | blueprint/parts/p1-analysis.tex#step:p1:ul-primary@L400-L400 | real on reals
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#step:p1:ul-primary@L397-L397 | strip T_r
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.uniform_limits_isPrimaryOnStrip, KAM.uniform_limits_isRealOnReals
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:holomorphic-inverse
KIND: lemma
TITLE: Holomorphic inverse
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-inverse@L404-L407
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-inverse@L409-L423
CONTRACT_ID: bp:p1:holomorphic-inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A holomorphic matrix-valued function on an open set V with det A != 0 there
SOURCE_QUANTIFIERS: A:V->C^{p x p}, V open
SOURCE_CONCLUSION: A^-1 is holomorphic on V and D(A^-1)=-A^-1 (DA) A^-1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:hi-holomorphic, step:p1:hi-derivative
EDGE: step:p1:hi-holomorphic | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-inverse@L412-L412 | proof step of this result
EDGE: step:p1:hi-derivative | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-inverse@L418-L418 | proof step of this result
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.holomorphic_inverse
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:hi-holomorphic
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hi-holomorphic@L412-L416
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hi-holomorphic@L412-L416
CONTRACT_ID: step:p1:hi-holomorphic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V open; A:V->C^{p x p} holomorphic; det A nonzero on V
SOURCE_QUANTIFIERS: on V
SOURCE_CONCLUSION: A^-1=(det A)^-1 adj A is holomorphic on V
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-cramer
EDGE: bp:p1:ext-cramer | blueprint/parts/p1-analysis.tex#step:p1:hi-holomorphic@L413-L413 | cited at this line (step; \ref{bp:p1:ext-cramer})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.holomorphic_inverse_differentiableOn
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:hi-derivative
KIND: step
TITLE: Derivative
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hi-derivative@L418-L422
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hi-derivative@L418-L422
CONTRACT_ID: step:p1:hi-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V open; A:V->C^{p x p} holomorphic; det A nonzero on V
SOURCE_QUANTIFIERS: z in V; direction v
SOURCE_CONCLUSION: D(A^-1)(z)v=-A(z)^-1 (DA(z)v) A(z)^-1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:hi-holomorphic
EDGE: step:p1:hi-holomorphic | blueprint/parts/p1-analysis.tex#step:p1:hi-derivative@L419-L419 | A^-1 differentiable so product rule applies
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.fderiv_matrix_inv_apply
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-MAT-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:increments-open
KIND: lemma
TITLE: Increments on open sets
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:increments-open@L425-L428
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:increments-open@L430-L434
CONTRACT_ID: bp:p1:increments-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F holomorphic on open U in C^m; |DF|<=A on U; segment [z,z+w] in U
SOURCE_QUANTIFIERS: U,F,A; z,w
SOURCE_CONCLUSION: |F(z+w)-F(z)|<=A|w|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:io-mvt
EDGE: step:p1:io-mvt | blueprint/parts/p1-analysis.tex#bp:p1:increments-open@L431-L431 | proof step of this result
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.increments_open
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:io-mvt
KIND: step
TITLE: Mean value inequality
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:io-mvt@L431-L433
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:io-mvt@L431-L433
CONTRACT_ID: step:p1:io-mvt
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; F:U->W holomorphic; |DF|<=A on U; [z,z+w] subset U
SOURCE_QUANTIFIERS: z,w
SOURCE_CONCLUSION: |F(z+w)-F(z)|<=A|w|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-mvt
EDGE: bp:p1:ext-mvt | blueprint/parts/p1-analysis.tex#step:p1:io-mvt@L433-L433 | cited at this line (step; \ref{bp:p1:ext-mvt})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.increments_open
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:taylor
KIND: lemma
TITLE: Second-order Taylor bound
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:taylor@L436-L439
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:taylor@L441-L452
CONTRACT_ID: bp:p1:taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F holomorphic on open U in C^m; |D^2F|<=A on U; segment [z,z+w] in U
SOURCE_QUANTIFIERS: U,F,A; z,w
SOURCE_CONCLUSION: |F(z+w)-F(z)-DF(z)w|<=(A/2)|w|^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:tay-lipschitz, step:p1:tay-integrate
EDGE: step:p1:tay-lipschitz | blueprint/parts/p1-analysis.tex#bp:p1:taylor@L442-L442 | proof step of this result
EDGE: step:p1:tay-integrate | blueprint/parts/p1-analysis.tex#bp:p1:taylor@L447-L447 | proof step of this result
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.taylor (+ KAM.taylor_iteratedFDeriv)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1C-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:tay-lipschitz
KIND: step
TITLE: The derivative along the segment
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:tay-lipschitz@L442-L445
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:tay-lipschitz@L442-L445
CONTRACT_ID: step:p1:tay-lipschitz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; F:U->W holomorphic; |D^2F|<=A on U; [z,z+w] subset U
SOURCE_QUANTIFIERS: t in [0,1]
SOURCE_CONCLUSION: |DF(z+tw)-DF(z)|<=A t|w|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-regularity, bp:p1:increments-open
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p1-analysis.tex#step:p1:tay-lipschitz@L443-L443 | cited at this line (step; \ref{bp:p1:holomorphic-regularity})
EDGE: bp:p1:increments-open | blueprint/parts/p1-analysis.tex#step:p1:tay-lipschitz@L444-L444 | cited at this line (step; \ref{bp:p1:increments-open})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.taylor_lipschitz
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1C-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:tay-integrate
KIND: step
TITLE: Integration
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:tay-integrate@L447-L451
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:tay-integrate@L447-L451
CONTRACT_ID: step:p1:tay-integrate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; F:U->W holomorphic; |D^2F|<=A on U; [z,z+w] subset U; g(t)=F(z+tw)-F(z)-t DF(z)w
SOURCE_QUANTIFIERS: z,w fixed; t in [0,1]
SOURCE_CONCLUSION: |g(1)|<=int_0^1 A t|w|^2 dt = (A/2)|w|^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:tay-lipschitz, bp:p1:holomorphic-regularity, bp:p1:ext-integral
EDGE: step:p1:tay-lipschitz | blueprint/parts/p1-analysis.tex#step:p1:tay-integrate@L450-L450 | bound on g'
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p1-analysis.tex#step:p1:tay-integrate@L449-L449 | DF continuous so g is C^1
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:tay-integrate@L450-L450 | fundamental theorem of calculus and norm of an integral
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.taylor_integrate (Mathlib boundary-comparison route)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1C-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:cauchy-open
KIND: lemma
TITLE: Cauchy estimate on open sets
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cauchy-open@L474-L479
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cauchy-open@L481-L508
CONTRACT_ID: bp:p1:cauchy-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f holomorphic on open U in C^m with |f|<=A on U; closed polydisc of radius delta>0 around z lies in U
SOURCE_QUANTIFIERS: U,f,A,delta>0,z; l; c(m,j) depends only on m and j
SOURCE_CONCLUSION: |d_l f(z)|<=A/delta; |D^j f(z)|<=c(m,j) A delta^-j for j=1,2,3 (iterated Frechet derivative, operator norm)
CONSTANT_SCOPE: c(m,j) depends only on m,j
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:co-first, step:p1:co-second, step:p1:co-third, step:p1:co-constants
EDGE: step:p1:co-first | blueprint/parts/p1-analysis.tex#bp:p1:cauchy-open@L484-L484 | proof step of this result
EDGE: step:p1:co-second | blueprint/parts/p1-analysis.tex#bp:p1:cauchy-open@L490-L490 | proof step of this result
EDGE: step:p1:co-third | blueprint/parts/p1-analysis.tex#bp:p1:cauchy-open@L499-L499 | proof step of this result
EDGE: step:p1:co-constants | blueprint/parts/p1-analysis.tex#bp:p1:cauchy-open@L506-L506 | proof step of this result
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: norm_coordinate_fderiv_le_of_closedBall (KAM/Strip/Cauchy.lean:87), norm_fderiv_le_of_closedBall (:80), norm_iteratedFDeriv_two_le_of_closedBall (KAM/Strip/HigherCauchy.lean:45), n
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:co-first
KIND: step
TITLE: First derivatives
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:co-first@L484-L488
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:co-first@L484-L488
CONTRACT_ID: step:p1:co-first
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; f:U->W holomorphic; delta>0; closed P(z,delta) subset U; |f|<=A on closed P(z,delta)
SOURCE_QUANTIFIERS: l
SOURCE_CONCLUSION: |Df(z)|<=A/delta and |d_l f(z)|<=A/delta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:hreg-line
EDGE: step:p1:hreg-line | blueprint/parts/p1-analysis.tex#step:p1:co-first@L485-L485 | line estimate with x=z, r=delta
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: norm_fderiv_le_of_closedBall (Cauchy.lean:80), norm_coordinate_fderiv_le_of_closedBall (:87)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:co-second
KIND: step
TITLE: Second derivatives
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:co-second@L490-L497
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:co-second@L490-L497
CONTRACT_ID: step:p1:co-second
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; f:U->W holomorphic; delta>0; closed P(z,delta) subset U; |f|<=A on closed P(z,delta)
SOURCE_QUANTIFIERS: y in P-bar(z,delta/2)
SOURCE_CONCLUSION: |Df(y)|<=2A/delta on P-bar(z,delta/2) and |D^2f(z)|<=4A/delta^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:co-first, bp:p1:holomorphic-regularity
EDGE: step:p1:co-first | blueprint/parts/p1-analysis.tex#step:p1:co-second@L493-L493 | cited at this line (step; \ref{step:p1:co-first})
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p1-analysis.tex#step:p1:co-second@L494-L494 | cited at this line (step; \ref{bp:p1:holomorphic-regularity})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: norm_iteratedFDeriv_two_le_of_closedBall (HigherCauchy.lean:45; uses norm_fderiv_le_on_half_closedBall :31)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:co-third
KIND: step
TITLE: Third derivatives
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:co-third@L499-L504
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:co-third@L499-L504
CONTRACT_ID: step:p1:co-third
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; f:U->W holomorphic; delta>0; closed P(z,delta) subset U; |f|<=A on closed P(z,delta)
SOURCE_QUANTIFIERS: z, radius delta/2
SOURCE_CONCLUSION: |D^2(Df)(z)|<=32A/delta^3 and |D^3f(z)|<=32A/delta^3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:co-second, bp:p1:holomorphic-regularity
EDGE: step:p1:co-second | blueprint/parts/p1-analysis.tex#step:p1:co-third@L500-L500 | cited at this line (step; \ref{step:p1:co-second})
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p1-analysis.tex#step:p1:co-third@L503-L503 | cited at this line (step; \ref{bp:p1:holomorphic-regularity})
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: norm_iteratedFDeriv_three_le_of_closedBall (:60)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:co-constants
KIND: step
TITLE: Constants
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:co-constants@L506-L507
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:co-constants@L506-L507
CONTRACT_ID: step:p1:co-constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^m open; W finite-dimensional complex normed; f:U->W holomorphic; delta>0; closed P(z,delta) subset U; |f|<=A on closed P(z,delta)
SOURCE_QUANTIFIERS: j=1,2,3
SOURCE_CONCLUSION: the lemma holds with c(m,1)=1, c(m,2)=4, c(m,3)=32, independent of m
CONSTANT_SCOPE: constants are absolute (independent of m)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:co-first, step:p1:co-second, step:p1:co-third
EDGE: step:p1:co-first | blueprint/parts/p1-analysis.tex#step:p1:co-constants@L507-L507 | c(m,1)=1
EDGE: step:p1:co-second | blueprint/parts/p1-analysis.tex#step:p1:co-constants@L507-L507 | c(m,2)=4
EDGE: step:p1:co-third | blueprint/parts/p1-analysis.tex#step:p1:co-constants@L507-L507 | c(m,3)=32
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1a+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: the numerals 1, 4, 32 in the statements above
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:ext-measure
KIND: external
TITLE: (E11) Lebesgue measure on products and boxes
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:ext-measure@L100-L109
PROOF_SOURCE: -
CONTRACT_ID: bp:p1:ext-measure
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: finite dimensions d1, d2 >= 0; A, B, E measurable; E_1 subset E_2 subset ... measurable; a box prod_i [a_i,b_i]
SOURCE_QUANTIFIERS: for all measurable A, B, E and increasing measurable sequences E_j, and all boxes
SOURCE_CONCLUSION: Lebesgue measure on R^{d1} x R^{d2} = R^{d1+d2} is the product measure: meas(A x B) = meas A meas B and meas E = int meas(E_x) dx (Tonelli); meas(union E_j) = lim meas E_j; closed and open boxes with the same corners have measure prod (b_i - a_i), so box boundaries are null
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-main-orchestrator
REVIEWER: sol-review-d4
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: added to the blueprint's external inputs to repair global-review finding F1 (measure-theory facts used in Parts 1 and 4); Mathlib counterparts cited at the item

NODE: bp:p1:periodic-bounded
KIND: lemma
TITLE: Periodic functions are bounded on smaller strips
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:periodic-bounded@L517-L519
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:periodic-bounded@L521-L529
CONTRACT_ID: bp:p1:periodic-bounded
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic and 1-periodic on T_rho, values in W
SOURCE_QUANTIFIERS: rho>0; every holomorphic 1-periodic u:T_rho -> W; every real rho'<rho, including rho'<=0
SOURCE_CONCLUSION: u is bounded on T_rho'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:pb-compact, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:pb-compact | blueprint/parts/p1-analysis.tex#bp:p1:periodic-bounded@L522-L522 | proof step of this result
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:periodic-bounded@L517-L517 | strip T_rho used by name
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.periodic_bounded
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:pb-compact
KIND: step
TITLE: A compact fundamental set
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:pb-compact@L522-L528
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:pb-compact@L522-L528
CONTRACT_ID: step:p1:pb-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic and 1-periodic on T_rho; rho'<rho
SOURCE_QUANTIFIERS: rho>0, u fixed; every real rho'<rho
SOURCE_CONCLUSION: if rho'<=0 then T_rho' is empty; if 0<rho'<rho then the compact fundamental set S at L512 is contained in T_rho and sup_{T_rho'} |u| <= max_S |u|; hence boundedness in both cases
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.periodic_bounded
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:strip-identity
KIND: lemma
TITLE: Identity theorem on strips
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L531-L534
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L536-L546
CONTRACT_ID: bp:p1:strip-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r>0; v holomorphic on T_r with values in W; v(x)=0 for all real x
SOURCE_QUANTIFIERS: r>0 ; v
SOURCE_CONCLUSION: v=0 on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:si-induction, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:si-induction | blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L537-L537 | proof step of this result
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L532-L532 | strip T_r used by name
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.strip_identity
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:si-induction
KIND: step
TITLE: One coordinate at a time
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:si-induction@L537-L545
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:si-induction@L537-L545
CONTRACT_ID: step:p1:si-induction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v holomorphic on T_r, vanishing on R^n
SOURCE_QUANTIFIERS: j from 1 to n; theta in T_r with theta_{j+1..n} real
SOURCE_CONCLUSION: claim (S_n): v=0 on T_r, by induction on (S_j)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-identity
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-identity | blueprint/parts/p1-analysis.tex#step:p1:si-induction@L544-L544 | one-variable identity theorem applied to coordinates of phi
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.strip_identity
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:increments
KIND: lemma
TITLE: Increments
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:increments@L551-L555
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:increments@L557-L566
CONTRACT_ID: bp:p1:increments
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic on T_rho; 0<delta<rho; theta, theta+v in T_{rho-delta}; (second claim) u bounded on T_rho
SOURCE_QUANTIFIERS: rho, delta, u; theta, v
SOURCE_CONCLUSION: |u(theta+v)-u(theta)| <= ||Du||_{rho-delta}|v|; if u bounded, this is <= n delta^-1 ||u||_rho |v|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:inc-mvt, step:p1:inc-cauchy, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:inc-mvt | blueprint/parts/p1-analysis.tex#bp:p1:increments@L558-L558 | proof step of this result
EDGE: step:p1:inc-cauchy | blueprint/parts/p1-analysis.tex#bp:p1:increments@L563-L563 | proof step of this result
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:increments@L552-L552 | strip T_rho used by name
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.increments
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1C-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:inc-mvt
KIND: step
TITLE: Mean value inequality
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:inc-mvt@L558-L561
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:inc-mvt@L558-L561
CONTRACT_ID: step:p1:inc-mvt
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic on T_rho; 0<delta<rho; theta, theta+v in T_{rho-delta} (convex)
SOURCE_QUANTIFIERS: theta, v
SOURCE_CONCLUSION: |u(theta+v)-u(theta)| <= ||Du||_{rho-delta}|v|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-mvt | blueprint/parts/p1-analysis.tex#step:p1:inc-mvt@L560-L560 | mean value inequality on the segment
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.increments_mvt
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1C-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:inc-cauchy
KIND: step
TITLE: With the Cauchy estimate
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:inc-cauchy@L563-L565
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:inc-cauchy@L563-L565
CONTRACT_ID: step:p1:inc-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u bounded holomorphic on T_rho; 0<delta<rho
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: ||Du||_{rho-delta} <= n delta^-1 ||u||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cauchy-strip
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cauchy-strip | blueprint/parts/p1-analysis.tex#step:p1:inc-cauchy@L564-L564 | Cauchy estimate on strips
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.increments_cauchy
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1C-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:cauchy-strip
KIND: lemma
TITLE: Cauchy estimate on strips
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cauchy-strip@L568-L574
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cauchy-strip@L576-L597
CONTRACT_ID: bp:p1:cauchy-strip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic and bounded on T_rho; 0<delta<rho; u scalar, vector (max norm) or matrix (operator norm) valued
SOURCE_QUANTIFIERS: rho, delta, u; every ell
SOURCE_CONCLUSION: ||d_ell u||_{rho-delta} <= delta^-1 ||u||_rho and ||Du||_{rho-delta} <= n delta^-1 ||u||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:cs-coordinate, step:p1:cs-full, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:cs-coordinate | blueprint/parts/p1-analysis.tex#bp:p1:cauchy-strip@L579-L579 | proof step of this result
EDGE: step:p1:cs-full | blueprint/parts/p1-analysis.tex#bp:p1:cauchy-strip@L589-L589 | proof step of this result
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:cauchy-strip@L569-L569 | strip T_rho used by name
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: norm_coordinate_fderiv_le_of_mem_complexStrip (KAM/Strip/Cauchy.lean:126), norm_fderiv_le_of_mem_complexStrip (:117)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:cs-coordinate
KIND: step
TITLE: One coordinate
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:cs-coordinate@L579-L587
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:cs-coordinate@L579-L587
CONTRACT_ID: step:p1:cs-coordinate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic bounded on T_rho, 0<delta<rho, theta in T_{rho-delta}, 1<=ell<=n
SOURCE_QUANTIFIERS: theta, ell
SOURCE_CONCLUSION: |d_ell u(theta)| <= delta^-1 ||u||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-cauchy | blueprint/parts/p1-analysis.tex#step:p1:cs-coordinate@L584-L584 | one-variable Cauchy estimate on the circle of radius delta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: norm_coordinate_fderiv_le_of_mem_complexStrip (Cauchy.lean:126; the blueprint cites it)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:cs-full
KIND: step
TITLE: The full derivative
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:cs-full@L589-L596
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:cs-full@L589-L596
CONTRACT_ID: step:p1:cs-full
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: coordinate bound of the previous step; theta in T_{rho-delta}
SOURCE_QUANTIFIERS: v in C^n
SOURCE_CONCLUSION: |Du(theta)| <= n delta^-1 ||u||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:cs-coordinate, bp:p1:operator-norms
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:cs-coordinate | blueprint/parts/p1-analysis.tex#step:p1:cs-full@L590-L590 | previous step: bound on each d_ell u
EDGE: bp:p1:operator-norms | blueprint/parts/p1-analysis.tex#step:p1:cs-full@L595-L595 | operator norm equals row-sum norm of the Jacobian
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: norm_fderiv_le_of_mem_complexStrip (:117)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:cauchy-corollaries
KIND: lemma
TITLE: Cauchy corollaries
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cauchy-corollaries@L617-L621
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cauchy-corollaries@L623-L637
CONTRACT_ID: bp:p1:cauchy-corollaries
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f holomorphic and bounded on T_rho; 0<delta<rho; f valued in C^p (first claim) or C^p / C^{pxq} (second claim)
SOURCE_QUANTIFIERS: rho, delta, f, omega
SOURCE_CONCLUSION: ||(Df)^T||_{rho-delta} <= p delta^-1 ||f||_rho; ||d_omega f||_{rho-delta} <= |omega|_1 delta^-1 ||f||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:cc-transpose, step:p1:cc-omega, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:cc-transpose | blueprint/parts/p1-analysis.tex#bp:p1:cauchy-corollaries@L626-L626 | proof step of this result
EDGE: step:p1:cc-omega | blueprint/parts/p1-analysis.tex#bp:p1:cauchy-corollaries@L633-L633 | proof step of this result
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:cauchy-corollaries@L618-L618 | strip T_rho used by name
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: none (the coordinate bound at Cauchy.lean:126 is the input)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:cc-transpose
KIND: step
TITLE: Transposed derivative
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:cc-transpose@L626-L631
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:cc-transpose@L626-L631
CONTRACT_ID: step:p1:cc-transpose
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f holomorphic bounded on T_rho with values in C^p; theta in T_{rho-delta}
SOURCE_QUANTIFIERS: theta
SOURCE_CONCLUSION: row sums of (Df(theta))^T are <= p delta^-1 ||f||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:cs-coordinate
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:cs-coordinate | blueprint/parts/p1-analysis.tex#step:p1:cc-transpose@L630-L630 | coordinate Cauchy bound for d_ell f
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: none in Zohar's files
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:cc-omega
KIND: step
TITLE: Derivative along $\omega$
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:cc-omega@L633-L636
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:cc-omega@L633-L636
CONTRACT_ID: step:p1:cc-omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f holomorphic bounded on T_rho with values in any W; theta in T_{rho-delta}
SOURCE_QUANTIFIERS: theta
SOURCE_CONCLUSION: |d_omega f(theta)| <= |omega|_1 delta^-1 ||f||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:cs-coordinate
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:cs-coordinate | blueprint/parts/p1-analysis.tex#step:p1:cc-omega@L634-L634 | coordinate Cauchy bound for d_ell f
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: none in Zohar's files
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:averages-real
KIND: lemma
TITLE: Averages of functions on the real torus
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:averages-real@L646-L649
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:averages-real@L651-L663
CONTRACT_ID: bp:p1:averages-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v:R^n->C continuous, 1-periodic, differentiable with continuous derivative
SOURCE_QUANTIFIERS: v; ell; omega
SOURCE_CONCLUSION: <d_ell v>=0 and <Dv omega>=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:ar-one, step:p1:ar-fubini
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:ar-one | blueprint/parts/p1-analysis.tex#bp:p1:averages-real@L652-L652 | proof step of this result
EDGE: step:p1:ar-fubini | blueprint/parts/p1-analysis.tex#bp:p1:averages-real@L658-L658 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: torusAverage_coordinate_eq_zero (KAM/Strip/Averages.lean:108), torusAverage_direction_eq_zero (:126), torusAverage_fderiv_eq_zero (:142)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:ar-one
KIND: step
TITLE: One variable
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ar-one@L652-L656
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ar-one@L652-L656
CONTRACT_ID: step:p1:ar-one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v as in the lemma; ell and the other coordinates x' fixed
SOURCE_QUANTIFIERS: x' in [0,1]^(n-1)
SOURCE_CONCLUSION: integral over [0,1] of d_ell v in x_ell is 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:ar-one@L655-L655 | fundamental theorem of calculus on [0,1]
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: BYPASSED
LEAN_REF: inlined as hline in the private torusAverage_coordinate_succ_eq_zero (:68)
LEAN_NOTE: route substitution (D27): parent proved by Zohar's route; docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md)
NOTE: -

NODE: step:p1:ar-fubini
KIND: step
TITLE: Fubini
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ar-fubini@L658-L662
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:ar-fubini@L658-L662
CONTRACT_ID: step:p1:ar-fubini
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d_ell v continuous on [0,1]^n; previous step
SOURCE_QUANTIFIERS: ell
SOURCE_CONCLUSION: <d_ell v>=0 and <Dv omega>=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-integral, step:p1:ar-one
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:ar-fubini@L659-L659 | Fubini
EDGE: step:p1:ar-one | blueprint/parts/p1-analysis.tex#step:p1:ar-fubini@L660-L660 | inner integral vanishes
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: torusAverage_coordinate_eq_zero (:108) (Fubini by measurePreserving_piFinSuccAbove in :68), torusAverage_direction_eq_zero (:126)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:averages
KIND: lemma
TITLE: Averages
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:averages@L665-L669
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:averages@L671-L684
CONTRACT_ID: bp:p1:averages
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v holomorphic, bounded and 1-periodic on T_rho; scalar, C^p or C^{pxq} valued
SOURCE_QUANTIFIERS: rho, v; ell; omega
SOURCE_CONCLUSION: <d_theta_ell v>=0, <Dv omega>=0, |avg(v)| <= ||v||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:av-derivatives, step:p1:av-bound, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:av-derivatives | blueprint/parts/p1-analysis.tex#bp:p1:averages@L672-L672 | proof step of this result
EDGE: step:p1:av-bound | blueprint/parts/p1-analysis.tex#bp:p1:averages@L679-L679 | proof step of this result
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:averages@L666-L666 | strip T_rho used by name
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: torusAverage_complex_coordinate_eq_zero (KAM/Strip/Averages.lean:172), torusAverage_complex_direction_eq_zero (:199), norm_torusAverage_le_of_strip_bound (:220)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:av-derivatives
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:av-derivatives@L672-L677
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:av-derivatives@L672-L677
CONTRACT_ID: step:p1:av-derivatives
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v holomorphic 1-periodic on T_rho
SOURCE_QUANTIFIERS: ell; omega
SOURCE_CONCLUSION: <d_ell v>=0 and <Dv omega>=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-regularity, bp:p1:averages-real
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p1-analysis.tex#step:p1:av-derivatives@L674-L674 | d_ell v holomorphic hence continuous
EDGE: bp:p1:averages-real | blueprint/parts/p1-analysis.tex#step:p1:av-derivatives@L676-L676 | averages of derivatives on the real torus
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: :172, :199 (and :160)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:av-bound
KIND: step
TITLE: The bound
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:av-bound@L679-L683
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:av-bound@L679-L683
CONTRACT_ID: step:p1:av-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v bounded on T_rho; [0,1]^n has measure 1
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: |avg(v)| <= sup over R^n of |v| <= ||v||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:av-bound@L680-L680 | norm of an integral is at most integral of the norm
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: :220
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:averages-matrix
KIND: lemma
TITLE: Averages of matrix-valued functions
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:averages-matrix@L686-L689
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:averages-matrix@L691-L699
CONTRACT_ID: bp:p1:averages-matrix
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M continuous, 1-periodic and matrix valued on R^n; (second claim) M is C^1
SOURCE_QUANTIFIERS: M; omega
SOURCE_CONCLUSION: |avg(M)| <= sup over R^n of |M|; and <d_omega M>=0 if M is C^1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:am-bound, step:p1:am-derivative
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:am-bound | blueprint/parts/p1-analysis.tex#bp:p1:averages-matrix@L692-L692 | proof step of this result
EDGE: step:p1:am-derivative | blueprint/parts/p1-analysis.tex#bp:p1:averages-matrix@L696-L696 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: norm_torusAverage_le (KAM/Strip/Averages.lean:43), torusAverage_fderiv_eq_zero (:142)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:am-bound
KIND: step
TITLE: The bound
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:am-bound@L692-L694
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:am-bound@L692-L694
CONTRACT_ID: step:p1:am-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M continuous 1-periodic matrix valued
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: |avg(M)| <= sup |M| (operator norm)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:am-bound@L693-L693 | norm of an integral is at most integral of the norm
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: norm_torusAverage_le (:43)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:am-derivative
KIND: step
TITLE: Derivative along $\omega$
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:am-derivative@L696-L698
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:am-derivative@L696-L698
CONTRACT_ID: step:p1:am-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M is C^1, 1-periodic
SOURCE_QUANTIFIERS: omega
SOURCE_CONCLUSION: <d_omega M>=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:averages-real
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:averages-real | blueprint/parts/p1-analysis.tex#step:p1:am-derivative@L698-L698 | applied to each entry
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: torusAverage_fderiv_eq_zero (:142)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:periodic-average
KIND: lemma
TITLE: Translation invariance of averages
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:periodic-average@L701-L703
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:periodic-average@L705-L717
CONTRACT_ID: bp:p1:periodic-average
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v continuous and 1-periodic on R^n
SOURCE_QUANTIFIERS: v; a in R^n
SOURCE_CONCLUSION: avg(v(.+a)) = avg(v)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:pa-one, step:p1:pa-induction
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:pa-one | blueprint/parts/p1-analysis.tex#bp:p1:periodic-average@L706-L706 | proof step of this result
EDGE: step:p1:pa-induction | blueprint/parts/p1-analysis.tex#bp:p1:periodic-average@L711-L711 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.periodic_average
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:pa-one
KIND: step
TITLE: One variable
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:pa-one@L706-L709
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:pa-one@L706-L709
CONTRACT_ID: step:p1:pa-one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: psi:R->C continuous 1-periodic
SOURCE_QUANTIFIERS: b in R
SOURCE_CONCLUSION: integral over [0,1] of psi(x+b) dx equals integral of psi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:pa-one@L708-L708 | differentiation of the integral in its limits
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: Function.Periodic.intervalIntegral_add_eq (in KAM.torusAverage_add_single)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:pa-induction
KIND: step
TITLE: One coordinate at a time
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:pa-induction@L711-L716
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:pa-induction@L711-L716
CONTRACT_ID: step:p1:pa-induction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v continuous 1-periodic; a^(j)=(a_1..a_j,0..0)
SOURCE_QUANTIFIERS: 1<=j<=n
SOURCE_CONCLUSION: avg(v(.+a^(j))) = avg(v(.+a^(j-1))), hence avg(v(.+a))=avg(v)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-integral, step:p1:pa-one
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:pa-induction@L713-L713 | Fubini
EDGE: step:p1:pa-one | blueprint/parts/p1-analysis.tex#step:p1:pa-induction@L714-L714 | one-variable shift invariance
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.periodic_average
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:exp-sums
KIND: lemma
TITLE: Exponential sums over $\Z^n$
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:exp-sums@L727-L734
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:exp-sums@L736-L755
CONTRACT_ID: bp:p1:exp-sums
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; (a) y>=0, a>0, tau>=0; (b) x>0; (c) x>0
SOURCE_QUANTIFIERS: n; y, a, tau, x
SOURCE_CONCLUSION: (a) y^tau e^{-ay} <= (tau/(ea))^tau; (b) sum over Z^n of e^{-x|k|_1} = coth(x/2)^n and coth(x/2) <= 1+2/x; (c) sum over k!=0 of e^{-x|k|_1} <= (8n/x)^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:es-power, step:p1:es-product, step:p1:es-nonzero
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:es-power | blueprint/parts/p1-analysis.tex#bp:p1:exp-sums@L737-L737 | proof step of this result
EDGE: step:p1:es-product | blueprint/parts/p1-analysis.tex#bp:p1:exp-sums@L742-L742 | proof step of this result
EDGE: step:p1:es-nonzero | blueprint/parts/p1-analysis.tex#bp:p1:exp-sums@L747-L747 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Fourier.exp_sums
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:es-power
KIND: step
TITLE: The power times the exponential
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:es-power@L737-L740
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:es-power@L737-L740
CONTRACT_ID: step:p1:es-power
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: y>=0, a>0, tau>=0
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: (a) y^tau e^{-ay} <= (tau/(ea))^tau
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Fourier.rpow_mul_exp_neg_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:es-product
KIND: step
TITLE: Product structure
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:es-product@L742-L745
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:es-product@L742-L745
CONTRACT_ID: step:p1:es-product
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: x>0
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: (b) sum over Z^n of e^{-x|k|_1} = coth(x/2)^n and coth(x/2) <= 1+2/x
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Fourier.hasSum_exp_neg_modeSize, cosh_div_sinh_half_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:es-nonzero
KIND: step
TITLE: Nonzero modes
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:es-nonzero@L747-L754
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:es-nonzero@L747-L754
CONTRACT_ID: step:p1:es-nonzero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: x>0; parts (a) and (b)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: (c) sum over k!=0 of e^{-x|k|_1} <= (8n/x)^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:es-product, step:p1:es-power
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:es-product | blueprint/parts/p1-analysis.tex#step:p1:es-nonzero@L748-L748 | part (b) with x/2
EDGE: step:p1:es-power | blueprint/parts/p1-analysis.tex#step:p1:es-nonzero@L753-L753 | part (a) for x^n e^{-x/2}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Fourier.tsum_exp_neg_modeSize_ne_zero_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:fourier-basic
KIND: lemma
TITLE: Fourier coefficients of periodic functions
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L757-L768
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L770-L784
CONTRACT_ID: bp:p1:fourier-basic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v C-valued (componentwise for vector/matrix); (a) v continuous, 1-periodic, C^1; (b) v continuous, 1-periodic, sum |hat v_k| finite; (c) r>0, v holomorphic and 1-periodic on T_r, not necessarily bounded, all hat v_k=0
SOURCE_QUANTIFIERS: v; k in Z^n; ell; omega in C^n; r
SOURCE_CONCLUSION: (a) hat(d_ell v)_k = 2 pi i k_ell hat v_k and hat(d_omega v)_k = 2 pi i (k.omega) hat v_k; (b) v(x)=sum hat v_k chi_k(x) for all x, so v=0 if all hat v_k=0; (c) v=0 on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:fb-derivative, step:p1:fb-series, step:p1:fb-holomorphic, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:fb-derivative | blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L771-L771 | proof step of this result
EDGE: step:p1:fb-series | blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L778-L778 | proof step of this result
EDGE: step:p1:fb-holomorphic | blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L781-L781 | proof step of this result
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L765-L765 | strip T_r used by name
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: (a) KAM.torusCoeff_fderiv_real, torusCoeff_fderiv_coordinate_real (FourierDerivative); (b),(c) KAM.hasSum_torusCoeff_mul_character, eq_zero_of_torusCoeff_eq_zero, eq_zero_of_torusCoeff_holomorphic (FourierBasic; scalar, componentwise per the blueprint)
LEAN_NOTE: Zohar Komargodski's Part 1 Fourier layer; retro audit docs/campaign/audits/I-STRIP-2-audit-1.md (PASS for these nodes; part (a) via I-STRIP-3b-audit-1.md)
NOTE: -

NODE: step:p1:fb-derivative
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:fb-derivative@L771-L776
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:fb-derivative@L771-L776
CONTRACT_ID: step:p1:fb-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: part (a): v continuous, 1-periodic, C^1; w=v chi_{-k}
SOURCE_QUANTIFIERS: k; ell
SOURCE_CONCLUSION: hat(d_ell v)_k = 2 pi i k_ell hat v_k; same for d_omega
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:averages-real
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:averages-real | blueprint/parts/p1-analysis.tex#step:p1:fb-derivative@L773-L773 | <d_ell w>=0 for w=v chi_{-k}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.torusCoeff_fderiv_coordinate_real, KAM.torusCoeff_fderiv_real (KAM/Strip/FourierDerivative.lean:83,152); holomorphic form KAM.torusCoeff_fderiv (KAM/Strip/Cohomological.lean:66)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p1:fb-series
KIND: step
TITLE: Fourier series
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:fb-series@L778-L779
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:fb-series@L778-L779
CONTRACT_ID: step:p1:fb-series
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: part (b): v continuous, 1-periodic, summable coefficients
SOURCE_QUANTIFIERS: x in R^n
SOURCE_CONCLUSION: v(x)=sum hat v_k chi_k(x); v=0 if all coefficients vanish
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-fourier
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-fourier | blueprint/parts/p1-analysis.tex#step:p1:fb-series@L779-L779 | Fourier series of a continuous periodic function with summable coefficients
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.hasSum_torusCoeff_mul_character, KAM.eq_zero_of_torusCoeff_eq_zero
LEAN_NOTE: Zohar Komargodski's Part 1 Fourier layer; retro audit docs/campaign/audits/I-STRIP-2-audit-1.md (PASS for these nodes; part (a) via I-STRIP-3b-audit-1.md)
NOTE: -

NODE: step:p1:fb-holomorphic
KIND: step
TITLE: Holomorphic functions
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:fb-holomorphic@L781-L783
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:fb-holomorphic@L781-L783
CONTRACT_ID: step:p1:fb-holomorphic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: part (c): v holomorphic 1-periodic on T_r with vanishing coefficients; part (b)
SOURCE_QUANTIFIERS: r
SOURCE_CONCLUSION: v=0 on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:fb-series, bp:p1:strip-identity
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:fb-series | blueprint/parts/p1-analysis.tex#step:p1:fb-holomorphic@L783-L783 | part (b): v=0 on R^n
EDGE: bp:p1:strip-identity | blueprint/parts/p1-analysis.tex#step:p1:fb-holomorphic@L783-L783 | identity theorem on strips
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.eq_zero_of_torusCoeff_holomorphic
LEAN_NOTE: Zohar Komargodski's Part 1 Fourier layer; retro audit docs/campaign/audits/I-STRIP-2-audit-1.md (PASS for these nodes; part (a) via I-STRIP-3b-audit-1.md)
NOTE: -

NODE: bp:p1:decay
KIND: lemma
TITLE: Coefficient decay
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:decay@L786-L789
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:decay@L791-L819
CONTRACT_ID: bp:p1:decay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic, bounded and 1-periodic on T_rho
SOURCE_QUANTIFIERS: rho, u; k in Z^n; rho' with 0<=rho'<rho
SOURCE_CONCLUSION: |hat u_k| <= e^{-2 pi |k|_1 rho'} ||u||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:dec-shift, step:p1:dec-bound, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:dec-shift | blueprint/parts/p1-analysis.tex#bp:p1:decay@L800-L800 | proof step of this result
EDGE: step:p1:dec-bound | blueprint/parts/p1-analysis.tex#bp:p1:decay@L813-L813 | proof step of this result
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:decay@L787-L787 | strip T_rho used by name
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: norm_torusCoeff_le_of_lt (KAM/Strip/Fourier.lean:229); boundary radius norm_torusCoeff_le (:291)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:dec-shift
KIND: step
TITLE: Shifting one variable
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:dec-shift@L800-L811
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:dec-shift@L800-L811
CONTRACT_ID: step:p1:dec-shift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic 1-periodic on T_rho, k, rho'<rho, t_j=-rho' sgn(k_j); I_j integrals
SOURCE_QUANTIFIERS: 1<=j<=n; x_l for l!=j
SOURCE_CONCLUSION: I_{j-1}=I_j for 1<=j<=n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-rectangle, bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-rectangle | blueprint/parts/p1-analysis.tex#step:p1:dec-shift@L806-L806 | Cauchy theorem on the rectangle
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:dec-shift@L811-L811 | Fubini over the remaining coordinates
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: BYPASSED
LEAN_REF: torusAverage_imag_shift (:114): the average of a periodic holomorphic g is unchanged when the torus moves to ℝⁿ + i t,
LEAN_NOTE: route substitution (D27): parent proved by Zohar's route; docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md)
NOTE: -

NODE: step:p1:dec-bound
KIND: step
TITLE: The bound
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:dec-bound@L813-L818
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:dec-bound@L813-L818
CONTRACT_ID: step:p1:dec-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I_n=hat u_k via the shifts; |u|<=||u||_rho
SOURCE_QUANTIFIERS: k; rho'
SOURCE_CONCLUSION: |hat u_k| = |I_n| <= e^{-2 pi rho' |k|_1} ||u||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:dec-shift, bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:dec-shift | blueprint/parts/p1-analysis.tex#step:p1:dec-bound@L818-L818 | hat u_k = I_0 = ... = I_n
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:dec-bound@L814-L818 | norm of the integral over a box of volume one bounds I_n by the displayed uniform integrand bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: last part of norm_torusCoeff_le_of_lt (:229), with norm_character (:68), norm_character_le (:82); W-valued: inside decay (Bridges) via the scalar bound and duality
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:summation
KIND: lemma
TITLE: Summation
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:summation@L824-L831
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:summation@L833-L875
CONTRACT_ID: bp:p1:summation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (forward) sum_k |a_k| e^{2 pi |k|_1 rho} finite; (converse) u as in decay, 0<delta<rho
SOURCE_QUANTIFIERS: rho, a_k, u, delta
SOURCE_CONCLUSION: u=sum a_k e^{2 pi i k.theta} holomorphic and 1-periodic on T_rho, hat u_k=a_k, ||u||_rho <= sum |a_k| e^{2 pi |k|_1 rho}; conversely sum |hat u_k| e^{2 pi |k|_1(rho-delta)} <= coth(pi delta)^n ||u||_rho and u equals its Fourier series on T_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:sum-bound, step:p1:sum-holo, step:p1:sum-coeff, step:p1:sum-converse, step:p1:sum-representation, bp:p1:decay, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:sum-bound | blueprint/parts/p1-analysis.tex#bp:p1:summation@L836-L836 | proof step of this result
EDGE: step:p1:sum-holo | blueprint/parts/p1-analysis.tex#bp:p1:summation@L841-L841 | proof step of this result
EDGE: step:p1:sum-coeff | blueprint/parts/p1-analysis.tex#bp:p1:summation@L853-L853 | proof step of this result
EDGE: step:p1:sum-converse | blueprint/parts/p1-analysis.tex#bp:p1:summation@L861-L861 | proof step of this result
EDGE: step:p1:sum-representation | blueprint/parts/p1-analysis.tex#bp:p1:summation@L869-L869 | proof step of this result
EDGE: bp:p1:decay | blueprint/parts/p1-analysis.tex#bp:p1:summation@L828-L828 | converse part is stated for u as in the decay lemma
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:summation@L825-L825 | strip T_rho used by name
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.summation_forward_vec, KAM.summation_converse_vec (FourierSeriesVector; W-valued) + scalar KAM.differentiableOn_fourierSum, torusCoeff_fourierSum, summableWeighted_torusCoeff, eq_fourierSum_torusCoeff (Zohar)
LEAN_NOTE: scalar layer by Zohar Komargodski (retro audit docs/campaign/audits/I-STRIP-2-audit-1.md); W-valued statements and uniform convergence by package I-STRIP-2b (audit docs/campaign/audits/I-STRIP-2b-audit-1.md PASS WITH NOTES, closes F1/F2); kernel replay passed (2026-10-28)
NOTE: -

NODE: step:p1:sum-bound
KIND: step
TITLE: Convergence and the bound
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:sum-bound@L836-L839
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:sum-bound@L836-L839
CONTRACT_ID: step:p1:sum-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M=sum |a_k| e^{2 pi |k|_1 rho} finite; S_N partial sums
SOURCE_QUANTIFIERS: theta in T_rho
SOURCE_CONCLUSION: series converges absolutely and uniformly on T_rho, |u|<=M, u 1-periodic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.norm_fourierSumVec_le, fourierSumVec_add_single, summable_character_smul, tendstoUniformlyOn_fourierSumVec(_cutoff); scalar tendstoUniformlyOn_fourierSum(_cutoff)
LEAN_NOTE: scalar layer by Zohar Komargodski (retro audit docs/campaign/audits/I-STRIP-2-audit-1.md); W-valued statements and uniform convergence by package I-STRIP-2b (audit docs/campaign/audits/I-STRIP-2b-audit-1.md PASS WITH NOTES, closes F1/F2); kernel replay passed (2026-10-28)
NOTE: -

NODE: step:p1:sum-holo
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:sum-holo@L841-L851
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:sum-holo@L841-L851
CONTRACT_ID: step:p1:sum-holo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M finite; u the uniform limit of S_N on T_rho
SOURCE_QUANTIFIERS: epsilon in (0,rho)
SOURCE_CONCLUSION: u holomorphic on T_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:exp-sums, bp:p1:uniform-limits, step:p1:sum-bound
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:exp-sums | blueprint/parts/p1-analysis.tex#step:p1:sum-holo@L843-L843 | part (a) with tau=1 bounds D chi_k terms
EDGE: bp:p1:uniform-limits | blueprint/parts/p1-analysis.tex#step:p1:sum-holo@L849-L849 | uniform limit of holomorphic functions with uniformly convergent derivatives
EDGE: step:p1:sum-bound | blueprint/parts/p1-analysis.tex#step:p1:sum-holo@L849-L849 | S_N converges to u uniformly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.differentiableOn_fourierSumVec (scalar: KAM.differentiableOn_fourierSum)
LEAN_NOTE: scalar layer by Zohar Komargodski (retro audit docs/campaign/audits/I-STRIP-2-audit-1.md); W-valued statements and uniform convergence by package I-STRIP-2b (audit docs/campaign/audits/I-STRIP-2b-audit-1.md PASS WITH NOTES, closes F1/F2); kernel replay passed (2026-10-28)
NOTE: -

NODE: step:p1:sum-coeff
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:sum-coeff@L853-L859
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:sum-coeff@L853-L859
CONTRACT_ID: step:p1:sum-coeff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: series converges uniformly on [0,1]^n
SOURCE_QUANTIFIERS: k
SOURCE_CONCLUSION: hat u_k = a_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-integral, step:p1:sum-bound
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-integral | blueprint/parts/p1-analysis.tex#step:p1:sum-coeff@L854-L854 | term-by-term integration
EDGE: step:p1:sum-bound | blueprint/parts/p1-analysis.tex#step:p1:sum-coeff@L854-L854 | uniform convergence of the series
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.torusCoeffW_fourierSumVec (scalar: KAM.torusCoeff_fourierSum)
LEAN_NOTE: scalar layer by Zohar Komargodski (retro audit docs/campaign/audits/I-STRIP-2-audit-1.md); W-valued statements and uniform convergence by package I-STRIP-2b (audit docs/campaign/audits/I-STRIP-2b-audit-1.md PASS WITH NOTES, closes F1/F2); kernel replay passed (2026-10-28)
NOTE: -

NODE: step:p1:sum-converse
KIND: step
TITLE: The converse estimate
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:sum-converse@L861-L867
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:sum-converse@L861-L867
CONTRACT_ID: step:p1:sum-converse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic, bounded and 1-periodic on T_rho; 0<delta<rho (the boundary-radius decay is a dependency, not an extra premise)
SOURCE_QUANTIFIERS: delta
SOURCE_CONCLUSION: sum |hat u_k| e^{2 pi |k|_1 (rho-delta)} <= coth(pi delta)^n ||u||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:decay#boundary-radius, bp:p1:exp-sums
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:exp-sums | blueprint/parts/p1-analysis.tex#step:p1:sum-converse@L863-L863 | part (b) with x=2 pi delta
EDGE: bp:p1:decay#boundary-radius | blueprint/parts/p1-analysis.tex#step:p1:sum-converse@L862-L863 | the boundary-radius decay statement of L809-L810
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.summableWeighted_torusCoeffW (scalar: KAM.summableWeighted_torusCoeff)
LEAN_NOTE: scalar layer by Zohar Komargodski (retro audit docs/campaign/audits/I-STRIP-2-audit-1.md); W-valued statements and uniform convergence by package I-STRIP-2b (audit docs/campaign/audits/I-STRIP-2b-audit-1.md PASS WITH NOTES, closes F1/F2); kernel replay passed (2026-10-28)
NOTE: -

NODE: step:p1:sum-representation
KIND: step
TITLE: Fourier representation
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:sum-representation@L869-L874
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:sum-representation@L869-L874
CONTRACT_ID: step:p1:sum-representation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u as in decay; converse estimate; first part of the lemma
SOURCE_QUANTIFIERS: theta in T_rho; delta with max|Im theta_j|<rho-delta
SOURCE_CONCLUSION: u equals sum hat u_k chi_k at theta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:sum-converse, step:p1:sum-bound, step:p1:sum-holo, step:p1:sum-coeff, bp:p1:fourier-basic
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:sum-converse | blueprint/parts/p1-analysis.tex#step:p1:sum-representation@L871-L871 | summability of weighted coefficients
EDGE: step:p1:sum-bound | blueprint/parts/p1-analysis.tex#step:p1:sum-representation@L871-L871 | first part of the lemma: boundedness and periodicity
EDGE: step:p1:sum-holo | blueprint/parts/p1-analysis.tex#step:p1:sum-representation@L871-L871 | first part of the lemma: holomorphy
EDGE: step:p1:sum-coeff | blueprint/parts/p1-analysis.tex#step:p1:sum-representation@L872-L872 | first part of the lemma: hat v_k = hat u_k
EDGE: bp:p1:fourier-basic | blueprint/parts/p1-analysis.tex#step:p1:sum-representation@L874-L874 | part (c): vanishing coefficients imply zero
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.eq_fourierSumVec_torusCoeffW (scalar: KAM.eq_fourierSum_torusCoeff)
LEAN_NOTE: scalar layer by Zohar Komargodski (retro audit docs/campaign/audits/I-STRIP-2-audit-1.md); W-valued statements and uniform convergence by package I-STRIP-2b (audit docs/campaign/audits/I-STRIP-2b-audit-1.md PASS WITH NOTES, closes F1/F2); kernel replay passed (2026-10-28)
NOTE: -

NODE: bp:p1:cohomological
KIND: lemma
TITLE: Cohomological equation on strips
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L887-L897
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L899-L969
CONTRACT_ID: bp:p1:cohomological
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega in Dio_{gamma,tau}, gamma>0, tau>=0; g holomorphic, bounded, 1-periodic on T_rho with avg(g)=0; 0<delta<rho; g real on real points (for realness); vector/matrix valued componentwise
SOURCE_QUANTIFIERS: fixed dimension n under the corpus conventions, and tau>=0; a constant c(n,tau) depending only on these; then every gamma>0, rho>0, Diophantine omega, datum g as stated and 0<delta<rho; then the unique zero-average solution u
SOURCE_CONCLUSION: there is a unique u holomorphic and 1-periodic on T_{rho-delta} (no boundedness assumed) with avg(u)=0 and Du(theta) omega=g(theta); u is bounded and ||u||_{rho-delta} <= c(n,tau) gamma^-1 delta^-(tau+n) ||g||_rho; u real on real points if g is
CONSTANT_SCOPE: c(n,tau) depends only on n and tau (not on gamma, rho, delta, omega, g)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:coh-data, step:p1:coh-coefficients, step:p1:coh-weighted, step:p1:coh-existence, step:p1:coh-equation, step:p1:coh-unique, step:p1:coh-real, step:p1:coh-vector, bp:p0:diophantine#IsDiophantine, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:coh-data | blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L906-L906 | proof step of this result
EDGE: step:p1:coh-coefficients | blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L910-L910 | proof step of this result
EDGE: step:p1:coh-weighted | blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L917-L917 | proof step of this result
EDGE: step:p1:coh-existence | blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L934-L934 | proof step of this result
EDGE: step:p1:coh-equation | blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L939-L939 | proof step of this result
EDGE: step:p1:coh-unique | blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L946-L946 | proof step of this result
EDGE: step:p1:coh-real | blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L955-L955 | proof step of this result
EDGE: step:p1:coh-vector | blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L962-L962 | proof step of this result
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L888-L888 | omega in Dio_{gamma,tau}
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:cohomological@L888-L888 | strip T_rho used by name
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.cohomological (Zohar's KAM/Strip/Cohomological.lean + node assembly)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:coh-data
KIND: step
TITLE: Coefficients of the datum
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-data@L906-L908
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-data@L906-L908
CONTRACT_ID: step:p1:coh-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g scalar holomorphic bounded 1-periodic on T_rho, avg(g)=0
SOURCE_QUANTIFIERS: k in Z^n
SOURCE_CONCLUSION: hat g_0=0 and |hat g_k| <= e^{-2 pi |k|_1 rho}||g||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:decay#boundary-radius
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:decay#boundary-radius | blueprint/parts/p1-analysis.tex#step:p1:coh-data@L907-L908 | the boundary-radius decay statement of L809-L810
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.torusCoeff_zero (KAM/Strip/Cohomological.lean:52) with zero average; KAM.norm_torusCoeff_le (KAM/Strip/Fourier.lean:291)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md (parent KAM.cohomological); decay input audited in docs/campaign/audits/I-ZMAP-audit-1.md, I-ZMAP-audit-2.md; kernel replay passed with the package
NOTE: -

NODE: step:p1:coh-coefficients
KIND: step
TITLE: The coefficient solution
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-coefficients@L910-L915
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-coefficients@L910-L915
CONTRACT_ID: step:p1:coh-coefficients
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: gamma>0, tau>=0, omega Diophantine (gamma,tau); datum g as in the enclosing lemma with hat g_0=0 from step:p1:coh-data
SOURCE_QUANTIFIERS: define a_0=0 and a_k=hat g_k/(2 pi i k.omega) for every k!=0; coefficient identity for every k in Z^n; inverse-divisor estimate for every k!=0
SOURCE_CONCLUSION: a_0=0, a_k=hat g_k/(2 pi i k.omega) satisfy 2 pi i (k.omega) a_k=hat g_k and |a_k| <= (2 pi gamma)^-1 |k|_1^tau |hat g_k|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:diophantine#IsDiophantine, step:p1:coh-data
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p1-analysis.tex#step:p1:coh-coefficients@L911-L911 | k.omega >= gamma k_1^-tau
EDGE: step:p1:coh-data | blueprint/parts/p1-analysis.tex#step:p1:coh-coefficients@L912-L913 | the all-mode coefficient identity uses hat g_0=0 at k=0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Diophantine.solve, solve_zero_mode, directionalCoeff_solve, norm_solve_le (KAM/Diophantine/Cohomological.lean:50,~78,82,104); KAM.sum_mul_eq_flowMultiplier (KAM/Strip/Cohomological.lean:121)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md (consumer KAM.cohomological; Diophantine solver itself not separately audited); kernel replay passed with the package
NOTE: -

NODE: step:p1:coh-weighted
KIND: step
TITLE: Weighted estimate
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-weighted@L917-L932
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-weighted@L917-L932
CONTRACT_ID: step:p1:coh-weighted
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: coefficient bounds of coh-data and coh-coefficients; s=2 pi(rho-delta/2)
SOURCE_QUANTIFIERS: delta in (0,rho)
SOURCE_CONCLUSION: sum |a_k| e^{2 pi |k|_1 (rho-delta)} <= c(n,tau) gamma^-1 delta^-(tau+n) ||g||_rho with c(n,tau)=(2 pi)^-1 (tau/(e pi))^tau (8n/pi)^n
CONSTANT_SCOPE: c(n,tau) depends only on n and tau
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:coh-data, step:p1:coh-coefficients, bp:p1:exp-sums
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:coh-data | blueprint/parts/p1-analysis.tex#step:p1:coh-weighted@L918-L918 | decay of hat g_k
EDGE: step:p1:coh-coefficients | blueprint/parts/p1-analysis.tex#step:p1:coh-weighted@L927-L927 | bound on a_k
EDGE: bp:p1:exp-sums | blueprint/parts/p1-analysis.tex#step:p1:coh-weighted@L918-L918 | parts (c) and (a)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.weightedNorm_torusCoeff_le_of_avg_zero, KAM.summableWeighted_solve_torusCoeff (KAM/Strip/Cohomological.lean:134,183)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md (parent KAM.cohomological); kernel replay passed with the package
NOTE: -

NODE: step:p1:coh-existence
KIND: step
TITLE: Existence
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-existence@L934-L937
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-existence@L934-L937
CONTRACT_ID: step:p1:coh-existence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: weighted estimate; a_k
SOURCE_QUANTIFIERS: delta in (0,rho)
SOURCE_CONCLUSION: u=sum a_k chi_k is holomorphic, 1-periodic, bounded on T_{rho-delta}, hat u_k=a_k, avg(u)=0, norm bound
CONSTANT_SCOPE: c(n,tau) as stated
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:summation, step:p1:coh-weighted, step:p1:coh-coefficients
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:summation | blueprint/parts/p1-analysis.tex#step:p1:coh-existence@L935-L935 | summation at radius rho-delta
EDGE: step:p1:coh-weighted | blueprint/parts/p1-analysis.tex#step:p1:coh-existence@L937-L937 | weighted sum of a_k
EDGE: step:p1:coh-coefficients | blueprint/parts/p1-analysis.tex#step:p1:coh-existence@L936-L936 | a_0=0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.differentiableOn_cohSolution, cohSolution_add_single, torusCoeff_cohSolution, torusAverage_cohSolution, norm_cohSolution_le (KAM/Strip/Cohomological.lean:222-250); packaged in KAM.cohomological (KAM/Strip/CohomologicalNodes.lean:57)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p1:coh-equation
KIND: step
TITLE: The equation
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-equation@L939-L944
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-equation@L939-L944
CONTRACT_ID: step:p1:coh-equation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u=sum a_k chi_k on T_rho-delta
SOURCE_QUANTIFIERS: theta in T_{rho-delta}
SOURCE_CONCLUSION: Du omega=g on T_{rho-delta}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-regularity, bp:p1:fourier-basic, step:p1:coh-existence, step:p1:coh-coefficients
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p1-analysis.tex#step:p1:coh-equation@L940-L940 | Du omega - g holomorphic
EDGE: bp:p1:fourier-basic | blueprint/parts/p1-analysis.tex#step:p1:coh-equation@L942-L942 | (a) coefficients of derivative, (c) vanishing coefficients
EDGE: step:p1:coh-existence | blueprint/parts/p1-analysis.tex#step:p1:coh-equation@L943-L943 | hat u_k=a_k
EDGE: step:p1:coh-coefficients | blueprint/parts/p1-analysis.tex#step:p1:coh-equation@L943-L943 | 2 pi i (k.omega) a_k=hat g_k
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.fderiv_cohSolution (KAM/Strip/Cohomological.lean:257); KAM.cohomological (KAM/Strip/CohomologicalNodes.lean:57)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p1:coh-unique
KIND: step
TITLE: Uniqueness
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-unique@L946-L953
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-unique@L946-L953
CONTRACT_ID: step:p1:coh-unique
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u~ holomorphic and 1-periodic on T_{rho-delta}, avg(u~)=0, Du~ omega=g (no bound)
SOURCE_QUANTIFIERS: u~
SOURCE_CONCLUSION: u~=u; for g=0 only u=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:fourier-basic, step:p1:coh-coefficients, step:p1:coh-existence
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:fourier-basic | blueprint/parts/p1-analysis.tex#step:p1:coh-unique@L949-L949 | (a) and (c)
EDGE: step:p1:coh-coefficients | blueprint/parts/p1-analysis.tex#step:p1:coh-unique@L950-L950 | hat u~_k=a_k
EDGE: step:p1:coh-existence | blueprint/parts/p1-analysis.tex#step:p1:coh-unique@L950-L950 | compare with the constructed u
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.eq_cohSolution (KAM/Strip/Cohomological.lean:302); KAM.cohomological (last conjunct)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p1:coh-real
KIND: step
TITLE: Realness
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-real@L955-L960
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-real@L955-L960
CONTRACT_ID: step:p1:coh-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g real on R^n
SOURCE_QUANTIFIERS: x in R^n
SOURCE_CONCLUSION: u real on R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:coh-coefficients, step:p1:coh-existence
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:coh-coefficients | blueprint/parts/p1-analysis.tex#step:p1:coh-real@L957-L957 | a_k formula and conjugate symmetry
EDGE: step:p1:coh-existence | blueprint/parts/p1-analysis.tex#step:p1:coh-real@L959-L959 | series representation of u
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.cohSolution_im_eq_zero (KAM/Strip/Cohomological.lean:385); KAM.cohomological
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p1:coh-vector
KIND: step
TITLE: Vector- and matrix-valued data
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-vector@L962-L968
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coh-vector@L962-L968
CONTRACT_ID: step:p1:coh-vector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: scalar case (existence, bound, equation, uniqueness, realness)
SOURCE_QUANTIFIERS: components i (and entries ij)
SOURCE_CONCLUSION: C^p-valued g: unique u with the same constant, norm = max of component norms; matrix entries componentwise
CONSTANT_SCOPE: c(n,tau) same as scalar
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:coh-existence, step:p1:coh-equation, step:p1:coh-unique, step:p1:coh-real
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:coh-existence | blueprint/parts/p1-analysis.tex#step:p1:coh-vector@L963-L963 | scalar existence and bound per component
EDGE: step:p1:coh-equation | blueprint/parts/p1-analysis.tex#step:p1:coh-vector@L963-L963 | scalar equation per component
EDGE: step:p1:coh-unique | blueprint/parts/p1-analysis.tex#step:p1:coh-vector@L964-L964 | scalar uniqueness per component
EDGE: step:p1:coh-real | blueprint/parts/p1-analysis.tex#step:p1:coh-vector@L963-L963 | scalar realness per component
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.cohSolutionPi family (cohSolutionPi, differentiableOn_cohSolutionPi, norm_cohSolutionPi_le, eq_cohSolutionPi, ... KAM/Strip/Cohomological.lean:399-500); KAM.cohomological second conjunct (CohomologicalNodes.lean)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: bp:p1:cohomological-operator
KIND: lemma
TITLE: Cohomological equation in operator norms, a-priori bound
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cohomological-operator@L971-L974
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:cohomological-operator@L976-L1004
CONTRACT_ID: bp:p1:cohomological-operator
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the cohomological lemma; g:T_rho->C^{pxq} holomorphic bounded 1-periodic, avg(g)=0, operator norm; (second claim) u holomorphic periodic with avg(u)=0
SOURCE_QUANTIFIERS: gamma, tau, rho, omega, delta, g, u
SOURCE_CONCLUSION: the cohomological lemma holds for matrix g with the operator norm, and every holomorphic periodic u with avg(u)=0 solving the equation satisfies the same bound
CONSTANT_SCOPE: c(n,tau) as in bp:p1:cohomological
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:coo-entries, step:p1:coo-vectors, step:p1:coo-norm, step:p1:coo-apriori, bp:p1:cohomological
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:coo-entries | blueprint/parts/p1-analysis.tex#bp:p1:cohomological-operator@L980-L980 | proof step of this result
EDGE: step:p1:coo-vectors | blueprint/parts/p1-analysis.tex#bp:p1:cohomological-operator@L985-L985 | proof step of this result
EDGE: step:p1:coo-norm | blueprint/parts/p1-analysis.tex#bp:p1:cohomological-operator@L992-L992 | proof step of this result
EDGE: step:p1:coo-apriori | blueprint/parts/p1-analysis.tex#bp:p1:cohomological-operator@L997-L997 | proof step of this result
EDGE: bp:p1:cohomological | blueprint/parts/p1-analysis.tex#bp:p1:cohomological-operator@L972-L972 | the lemma extended to the operator norm
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.cohomological_operator, KAM.cohomological_apriori_operator, KAM.cohSolutionMat
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:coo-entries
KIND: step
TITLE: The entrywise solution
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coo-entries@L980-L983
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coo-entries@L980-L983
CONTRACT_ID: step:p1:coo-entries
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g matrix valued; cohomological lemma applied entrywise
SOURCE_QUANTIFIERS: entries
SOURCE_CONCLUSION: unique entrywise solution u on T_{rho-delta} with avg(u)=0, Du omega=g; every zero-average periodic solution equals u
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cohomological
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cohomological | blueprint/parts/p1-analysis.tex#step:p1:coo-entries@L981-L981 | applied to each entry
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.cohSolutionMat, differentiableOn_cohSolutionMat, torusAverage_cohSolutionMat, fderiv_cohSolutionMat, eq_cohSolutionMat (KAM/Strip/CohomologicalOperator.lean:192-265); KAM.cohomological_operator (CohomologicalNodes.lean:119)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p1:coo-vectors
KIND: step
TITLE: Testing against vectors
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coo-vectors@L985-L990
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coo-vectors@L985-L990
CONTRACT_ID: step:p1:coo-vectors
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v in C^q, |v|<=1; u from coo-entries
SOURCE_QUANTIFIERS: v; theta in T_{rho-delta}
SOURCE_CONCLUSION: |u(theta)v| <= Gamma ||g||_rho, Gamma=c(n,tau) gamma^-1 delta^-(tau+n)
CONSTANT_SCOPE: Gamma depends on n, tau, gamma, delta
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:matrix-norms, step:p1:coo-entries, bp:p1:cohomological
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:matrix-norms | blueprint/parts/p1-analysis.tex#step:p1:coo-vectors@L987-L987 | g v <= g v
EDGE: step:p1:coo-entries | blueprint/parts/p1-analysis.tex#step:p1:coo-vectors@L988-L988 | uv solves the equation with data gv; uniqueness
EDGE: bp:p1:cohomological | blueprint/parts/p1-analysis.tex#step:p1:coo-vectors@L989-L989 | uniqueness and bound for C^p-valued data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.norm_cohSolutionMat_le (KAM/Strip/CohomologicalOperator.lean:286); helper KAM.mulVec_transfer (:89)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p1:coo-norm
KIND: step
TITLE: Operator norm
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coo-norm@L992-L995
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coo-norm@L992-L995
CONTRACT_ID: step:p1:coo-norm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: vector bound of previous step; u from coo-entries
SOURCE_QUANTIFIERS: theta in T_{rho-delta}
SOURCE_CONCLUSION: |u(theta)| <= Gamma ||g||_rho, for every zero-average periodic solution
CONSTANT_SCOPE: Gamma as above
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:operator-norms, step:p1:coo-vectors, step:p1:coo-entries
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:operator-norms | blueprint/parts/p1-analysis.tex#step:p1:coo-norm@L993-L993 | operator norm as sup over v<=1
EDGE: step:p1:coo-vectors | blueprint/parts/p1-analysis.tex#step:p1:coo-norm@L993-L993 | bound on u(theta)v
EDGE: step:p1:coo-entries | blueprint/parts/p1-analysis.tex#step:p1:coo-norm@L994-L994 | every solution equals u
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.norm_cohSolutionMat_le, KAM.eq_cohSolutionMat (KAM/Strip/CohomologicalOperator.lean:265,286); KAM.cohomological_operator
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p1:coo-apriori
KIND: step
TITLE: A-priori form
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coo-apriori@L997-L1003
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:coo-apriori@L997-L1003
CONTRACT_ID: step:p1:coo-apriori
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic 1-periodic on T_rho, C^p or C^{pxq} valued, avg(u)=0, ||Du omega||_rho <= H < infinity
SOURCE_QUANTIFIERS: H; delta in (0,rho)
SOURCE_CONCLUSION: ||u||_{rho-delta} <= Gamma H
CONSTANT_SCOPE: Gamma as above
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-regularity, bp:p1:averages-real, step:p1:coo-entries, step:p1:coo-norm
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p1-analysis.tex#step:p1:coo-apriori@L1000-L1000 | g=Du omega holomorphic
EDGE: bp:p1:averages-real | blueprint/parts/p1-analysis.tex#step:p1:coo-apriori@L1001-L1001 | avg(g)=0 from entries of the real restriction
EDGE: step:p1:coo-entries | blueprint/parts/p1-analysis.tex#step:p1:coo-apriori@L1002-L1002 | u restricted is a solution in the class
EDGE: step:p1:coo-norm | blueprint/parts/p1-analysis.tex#step:p1:coo-apriori@L1003-L1003 | bound for every zero-average periodic solution
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1b
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.cohomological_apriori, cohomological_apriori_pi, cohomological_apriori_operator (KAM/Strip/CohomologicalOperator.lean:119,144,165); second conjunct of KAM.cohomological_operator
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: bp:p1:decay#boundary-radius
KIND: step
TITLE: Coefficient decay at the boundary radius
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:decay#boundary-radius@L821-L822
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:decay#boundary-radius@L821-L822
CONTRACT_ID: bp:p1:decay#boundary-radius
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic, bounded and 1-periodic on T_rho; rho>0
SOURCE_QUANTIFIERS: every k in Z^n
SOURCE_CONCLUSION: |hat u_k| <= exp(-2 pi |k|_1 rho) ||u||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:decay
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:decay | blueprint/parts/p1-analysis.tex#bp:p1:decay#boundary-radius@L821-L822 | let rho' increase to rho in the coefficient estimate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: norm_torusCoeff_le (:291); W-valued: decay_boundary_radius (Bridges)
LEAN_NOTE: Zohar's lemmas + I-ZMAP adapters (KAM/Strip/Bridges.lean, KAM/Matrix/Bridges.lean); audits docs/campaign/audits/I-ZMAP-audit-1.md and -audit-2.md (map: docs/campaign/audits/I-ZMAP-map.md); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:iteration
KIND: lemma
TITLE: Quadratic iteration on nested strips
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:iteration@L1009-L1014
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:iteration@L1016-L1030
CONTRACT_ID: bp:p1:iteration
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q>0; p>=0; reals y_0,y_1,...>=0 with y_{m+1}<=Q 2^{pm} y_m^2 for all m>=0; Q 2^p y_0<=1/2 (second claim: only q:=Q 2^p y_0<=1)
SOURCE_QUANTIFIERS: for all Q>0, p>=0, sequences (y_m) satisfying the recursion; then for all m>=0
SOURCE_CONCLUSION: y_m<=Q^{-1} 2^{-p(m+1)} 2^{-2^m} for all m>=0 (so y_m->0); under q<=1 only: y_m<=q^{2^m-1} 2^{-pm} y_0 for all m>=0
CONSTANT_SCOPE: none (Q, p, y_0 arbitrary; no constants introduced)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:it-super, step:p1:it-linear
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:it-super | blueprint/parts/p1-analysis.tex#bp:p1:iteration@L1017-L1022 | proof step of this result
EDGE: step:p1:it-linear | blueprint/parts/p1-analysis.tex#bp:p1:iteration@L1024-L1029 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.quadratic_iteration
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:it-super
KIND: step
TITLE: Super-exponential decay
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:it-super@L1017-L1022
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:it-super@L1017-L1022
CONTRACT_ID: step:p1:it-super
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: real sequence (y_m) with y_m>=0 for every m>=0; Q>0; p>=0; y_{m+1}<=Q 2^{pm} y_m^2; Q 2^p y_0<=1/2
SOURCE_QUANTIFIERS: x_m:=Q 2^{p(m+1)} y_m, induction on m>=0
SOURCE_CONCLUSION: x_m<=2^{-2^m}, i.e. y_m<=Q^{-1} 2^{-p(m+1)} 2^{-2^m}, and y_m->0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.quadratic_iteration_super
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:it-linear
KIND: step
TITLE: The form linear in $y_0$
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:it-linear@L1024-L1029
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:it-linear@L1024-L1029
CONTRACT_ID: step:p1:it-linear
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: real sequence (y_m) with y_m>=0 for every m>=0; Q>0; p>=0; y_{m+1}<=Q 2^{pm} y_m^2; q=Q 2^p y_0<=1
SOURCE_QUANTIFIERS: induction on m>=0
SOURCE_CONCLUSION: y_m<=q^{2^m-1} 2^{-pm} y_0 for all m>=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.quadratic_iteration_linear
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P1B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:real-restriction-consequences
KIND: claim
TITLE: Real restrictions of linear and primary maps
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:real-restriction-consequences@L1039-L1045
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:real-restriction-consequences@L1039-L1045
CONTRACT_ID: bp:p1:real-restriction-consequences
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: l:C^n->C^p C-linear with l(R^n) in R^p, l_R its restriction; K:T_rho->C^n x C^n primary on T_rho and real on reals, k its restriction to R^n
SOURCE_QUANTIFIERS: for all such l, K, rho; x in R^n, m in Z^n
SOURCE_CONCLUSION: |l_R|<=|l| (operator norms of max norms); k(x+m)=k(x)+(m,0) for x in R^n, m in Z^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:stripdata#IsPrimaryOnStrip, bp:p0:stripdata#IsRealOnReals, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.real_restriction_consequences
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: Self-contained remark; proof is inline (real h with |h|<=1 are a subset of complex ones; primarity identity at the real point x).
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p1-analysis.tex#bp:p1:real-restriction-consequences@L1043-L1044 | unfold primarity at the real point x
EDGE: bp:p0:stripdata#IsRealOnReals | blueprint/parts/p1-analysis.tex#bp:p1:real-restriction-consequences@L1043-L1044 | the restriction takes real values
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p1-analysis.tex#bp:p1:real-restriction-consequences@L1043-L1044 | real x belongs to the positive-width strip

NODE: bp:p1:real-restriction
KIND: lemma
TITLE: Real restriction
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:real-restriction@L1047-L1051
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:real-restriction@L1053-L1071
CONTRACT_ID: bp:p1:real-restriction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K holomorphic on T_rho and real on reals; for the primary claim, K primary on T_rho (p=2n)
SOURCE_QUANTIFIERS: K, rho, p (=2n in applications); x in R^n; m in Z^n
SOURCE_CONCLUSION: k=K|_{R^n} real-analytic with real derivative the restriction of the complex derivative; |Dk(x)|<=|DK(x)| for x in R^n; if K primary, k(x+m)=k(x)+(m,0) for m in Z^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:rr-analytic, step:p1:rr-derivative, step:p1:rr-consequences
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:rr-analytic | blueprint/parts/p1-analysis.tex#bp:p1:real-restriction@L1057-L1059 | proof step of this result
EDGE: step:p1:rr-derivative | blueprint/parts/p1-analysis.tex#bp:p1:real-restriction@L1061-L1065 | proof step of this result
EDGE: step:p1:rr-consequences | blueprint/parts/p1-analysis.tex#bp:p1:real-restriction@L1067-L1070 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.real_restriction
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:rr-analytic
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:rr-analytic@L1057-L1059
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:rr-analytic@L1057-L1059
CONTRACT_ID: step:p1:rr-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K:T_rho->C^p holomorphic with K(R^n) in R^p; T_rho open, T_rho cap R^n=R^n
SOURCE_QUANTIFIERS: k=K|_{R^n}
SOURCE_CONCLUSION: k is real-analytic on R^n as a map into R^p
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:holomorphic-analytic | blueprint/parts/p1-analysis.tex#step:p1:rr-analytic@L1058-L1059 | part (b) with U=T_rho, m=n, W=C^p gives real analyticity of the restriction
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.analyticOnNhd_realRestriction
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:rr-derivative
KIND: step
TITLE: The derivative
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:rr-derivative@L1061-L1065
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:rr-derivative@L1061-L1065
CONTRACT_ID: step:p1:rr-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K holomorphic on T_rho, K(R^n) in R^p; x in R^n
SOURCE_QUANTIFIERS: real h->0
SOURCE_CONCLUSION: k differentiable at x and Dk(x)h=DK(x)h for h in R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.realRestriction_fderiv
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:rr-consequences
KIND: step
TITLE: Norm and primarity
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:rr-consequences@L1067-L1070
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:rr-consequences@L1067-L1070
CONTRACT_ID: step:p1:rr-consequences
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K:T_rho->C^p holomorphic and real on reals; k its real restriction; x in R^n; K primary when the primarity clause is claimed
SOURCE_QUANTIFIERS: x in R^n
SOURCE_CONCLUSION: |Dk(x)|<=|DK(x)|; for primary K (p=2n), k(x+m)=k(x)+(m,0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:rr-derivative, bp:p1:real-restriction-consequences
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:rr-derivative | blueprint/parts/p1-analysis.tex#step:p1:rr-consequences@L1068-L1069 | previous step: Dk(x) is the restriction of DK(x)
EDGE: bp:p1:real-restriction-consequences | blueprint/parts/p1-analysis.tex#step:p1:rr-consequences@L1069-L1070 | remark gives the norm bound and the primary identity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.norm_fderiv_realRestriction_le, KAM.realRestriction_add_int
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:hamiltonian-real
KIND: lemma
TITLE: Real and complex Hamiltonian fields
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:hamiltonian-real@L1073-L1079
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:hamiltonian-real@L1081-L1108
CONTRACT_ID: bp:p1:hamiltonian-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V open in C^n x C^n; h holomorphic on V and real at real points of V; z in V cap (R^n x R^n); H:R^n x R^n->R agrees with Re h near z; (second claim) phi holomorphic; X_H frozen vector field, J=-Omega_0
SOURCE_QUANTIFIERS: for all V, h, z, H; for all holomorphic phi
SOURCE_CONCLUSION: H differentiable at z and X_H(z)=X_h(z); X_phi=J (Dphi)^T with J=[[0,I],[-I,0]]=-Omega_0, equivalently Omega_0 X_phi=(Dphi)^T
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:hr-derivative, step:p1:hr-components, step:p1:hr-matrix, bp:p0:hamiltonian#hamiltonianVectorField, bp:p0:hamiltonian#hamiltonianVectorFieldC, bp:p0:hamiltonian#omegaZero
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:hr-derivative | blueprint/parts/p1-analysis.tex#bp:p1:hamiltonian-real@L1085-L1091 | proof step of this result
EDGE: step:p1:hr-components | blueprint/parts/p1-analysis.tex#bp:p1:hamiltonian-real@L1093-L1099 | proof step of this result
EDGE: step:p1:hr-matrix | blueprint/parts/p1-analysis.tex#bp:p1:hamiltonian-real@L1101-L1107 | proof step of this result
EDGE: bp:p0:hamiltonian#hamiltonianVectorField | blueprint/parts/p1-analysis.tex#bp:p1:hamiltonian-real@L1075-L1076 | X_H in the statement is the frozen real vector field
EDGE: bp:p0:hamiltonian#hamiltonianVectorFieldC | blueprint/parts/p1-analysis.tex#bp:p1:hamiltonian-real@L1075-L1076 | X_h, X_varphi in the statement is the frozen complex vector field
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p1-analysis.tex#bp:p1:hamiltonian-real@L1077-L1078 | Omega_0 in the statement
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.hamiltonian_real
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:hr-derivative
KIND: step
TITLE: The real derivative
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hr-derivative@L1085-L1091
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hr-derivative@L1085-L1091
CONTRACT_ID: step:p1:hr-derivative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V subset C^n x C^n open; h holomorphic on V and real at real points; z in V cap R^{2n}; H:R^{2n}->R agrees with Re h near z
SOURCE_QUANTIFIERS: e in R^n x R^n
SOURCE_CONCLUSION: H differentiable at z with DH(z)e=Dh(z)e (real number)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.hamiltonian_real_fderiv
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:hr-components
KIND: step
TITLE: Components
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hr-components@L1093-L1099
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hr-components@L1093-L1099
CONTRACT_ID: step:p1:hr-components
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: V subset C^n x C^n open; h holomorphic on V and real at real points; z in V cap R^{2n}; H:R^{2n}->R agrees with Re h near z
SOURCE_QUANTIFIERS: z, i=1..n
SOURCE_CONCLUSION: X_H(z)=X_h(z)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:hr-derivative, bp:p0:hamiltonian#hamiltonianVectorField, bp:p0:hamiltonian#hamiltonianVectorFieldC
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:hr-derivative | blueprint/parts/p1-analysis.tex#step:p1:hr-components@L1099-L1099 | previous step with e=(0,e_i) and e=(e_i,0)
EDGE: bp:p0:hamiltonian#hamiltonianVectorField | blueprint/parts/p1-analysis.tex#step:p1:hr-components@L1094-L1096 | component formula for X_H by the frozen definition
EDGE: bp:p0:hamiltonian#hamiltonianVectorFieldC | blueprint/parts/p1-analysis.tex#step:p1:hr-components@L1094-L1097 | component formula for X_h by the frozen definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.hamiltonianVectorField_eq_of_real
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:hr-matrix
KIND: step
TITLE: Matrix form
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hr-matrix@L1101-L1107
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:hr-matrix@L1101-L1107
CONTRACT_ID: step:p1:hr-matrix
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi holomorphic; frozen formula X_phi=(d_I phi,-d_theta phi)
SOURCE_QUANTIFIERS: phi holomorphic
SOURCE_CONCLUSION: X_phi=J(Dphi)^T with J=-Omega_0=Omega_0^{-1}; equivalently Omega_0 X_phi=(Dphi)^T; J as a map L(C^{2n},C)->C^{2n}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:hamiltonian#hamiltonianVectorFieldC, bp:p0:hamiltonian#omegaZero, bp:p1:operator-norms
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:hamiltonian#hamiltonianVectorFieldC | blueprint/parts/p1-analysis.tex#step:p1:hr-matrix@L1103-L1104 | frozen formula for X_phi
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p1-analysis.tex#step:p1:hr-matrix@L1105-L1105 | Omega_0 identified with -J
EDGE: bp:p1:operator-norms | blueprint/parts/p1-analysis.tex#step:p1:hr-matrix@L1105-L1106 | Omega_0^2=-I gives J=-Omega_0=Omega_0^{-1}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.hamiltonianVectorFieldℂ_eq_neg_omegaZero, KAM.omegaZero_hamiltonianVectorFieldℂ
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/I-STRIP-5-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:lip-image-product
KIND: claim
TITLE: Products
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:lip-image-product@L1118-L1122
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:lip-image-product@L1118-L1122
CONTRACT_ID: bp:p1:lip-image-product
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: R^n x R^n identified with R^{2n}
SOURCE_QUANTIFIERS: n
SOURCE_CONCLUSION: the identification is an isometry for the max norm of the two components and carries the product of Lebesgue measures to Lebesgue measure on R^{2n}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-measure
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-measure | blueprint/parts/p1-analysis.tex#bp:p1:lip-image-product@L1121-L1121 | product of Lebesgue measures is Lebesgue measure on R^2n, cited as (E11)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+claude-main-orchestrator
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.lip_image_product
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: the identification is (E11); repaired F1

NODE: bp:p1:lip-image
KIND: lemma
TITLE: Lipschitz images and preimages
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:lip-image@L1124-L1129
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:lip-image@L1131-L1166
CONTRACT_ID: bp:p1:lip-image
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S subset R^d; F:S->R^d with |F(x)-F(y)|<=Lambda|x-y|; Phi:A->R^d injective with Lipschitz inverse Phi^{-1}:Phi(A)->A; R^d with max norm
SOURCE_QUANTIFIERS: for all d, S, F, Lambda; for all A, Phi, N
SOURCE_CONCLUSION: outer measure meas F(S)<=Lambda^d meas S; meas N=0 implies meas Phi^{-1}(N)=0; both hold on R^n x R^n with the max norm of the components and the product Lebesgue measure
CONSTANT_SCOPE: Lambda is the Lipschitz constant of F (arbitrary)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:li-cubes, step:p1:li-image, step:p1:li-sum, step:p1:li-preimage, step:p1:li-product
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:li-cubes | blueprint/parts/p1-analysis.tex#bp:p1:lip-image@L1135-L1142 | proof step of this result
EDGE: step:p1:li-image | blueprint/parts/p1-analysis.tex#bp:p1:lip-image@L1144-L1148 | proof step of this result
EDGE: step:p1:li-sum | blueprint/parts/p1-analysis.tex#bp:p1:lip-image@L1150-L1155 | proof step of this result
EDGE: step:p1:li-preimage | blueprint/parts/p1-analysis.tex#bp:p1:lip-image@L1157-L1161 | proof step of this result
EDGE: step:p1:li-product | blueprint/parts/p1-analysis.tex#bp:p1:lip-image@L1163-L1165 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.lip_image (+ KAM.lip_image_prod, KAM.lip_preimage_null, KAM.lip_preimage_null_prod)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27); proved by the blueprint's stated alternative route (Mathlib hausdorffMeasure_pi_real + LipschitzOnWith.hausdorffMeasure_image_le), so steps li-cubes and li-image are bypassed
NOTE: -

NODE: step:p1:li-cubes
KIND: step
TITLE: Covers by cubes
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:li-cubes@L1135-L1142
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:li-cubes@L1135-L1142
CONTRACT_ID: step:p1:li-cubes
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S subset R^d; epsilon>0; R^d carries Lebesgue outer measure
SOURCE_QUANTIFIERS: eps>0
SOURCE_CONCLUSION: countably many closed cubes Q_j cover S with sum vol(Q_j)<=meas S+eps
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-lebesgue
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-lebesgue | blueprint/parts/p1-analysis.tex#step:p1:li-cubes@L1137-L1138 | definition of outer measure by closed box covers gives boxes R_j
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: not formalized as a separate declaration; its parent bp:p1:lip-image is PROVED by the blueprint's alternative Mathlib route (docs/campaign/audits/I-LIP-audit-1.md, note N1)
NOTE: -

NODE: step:p1:li-image
KIND: step
TITLE: Image of one cube
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:li-image@L1144-L1148
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:li-image@L1144-L1148
CONTRACT_ID: step:p1:li-image
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F:S->R^d Lambda-Lipschitz on S; Q closed cube of side ell
SOURCE_QUANTIFIERS: Q
SOURCE_CONCLUSION: meas F(S cap Q)<=Lambda^d ell^d = Lambda^d vol(Q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-lebesgue
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: not formalized as a separate declaration; its parent bp:p1:lip-image is PROVED by the blueprint's alternative Mathlib route (docs/campaign/audits/I-LIP-audit-1.md, note N1)
NOTE: -
EDGE: bp:p1:ext-lebesgue | blueprint/parts/p1-analysis.tex#step:p1:li-image@L1146-L1148 | image lies in a cube; outer measure is bounded by its box volume

NODE: step:p1:li-sum
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:li-sum@L1150-L1155
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:li-sum@L1150-L1155
CONTRACT_ID: step:p1:li-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S subset R^d; F:S->R^d Lambda-Lipschitz in the max norm; epsilon>0
SOURCE_QUANTIFIERS: eps>0
SOURCE_CONCLUSION: meas F(S)<=Lambda^d meas S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:li-cubes, step:p1:li-image, bp:p1:ext-lebesgue
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:li-cubes | blueprint/parts/p1-analysis.tex#step:p1:li-sum@L1151-L1152 | cube cover
EDGE: step:p1:li-image | blueprint/parts/p1-analysis.tex#step:p1:li-sum@L1151-L1152 | image of one cube
EDGE: bp:p1:ext-lebesgue | blueprint/parts/p1-analysis.tex#step:p1:li-sum@L1151-L1151 | countable subadditivity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.lip_image
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:li-preimage
KIND: step
TITLE: Preimages of null sets
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:li-preimage@L1157-L1161
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:li-preimage@L1157-L1161
CONTRACT_ID: step:p1:li-preimage
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Phi:A->R^d injective with Lambda-Lipschitz inverse; meas N=0
SOURCE_QUANTIFIERS: N
SOURCE_CONCLUSION: meas Phi^{-1}(N)=0
CONSTANT_SCOPE: Lambda is the Lipschitz constant of the inverse
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:li-sum, bp:p1:ext-lebesgue
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:li-sum | blueprint/parts/p1-analysis.tex#step:p1:li-preimage@L1160-L1161 | Lipschitz image estimate applied to Phi^{-1} on Phi(A)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.lip_preimage_null
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -
EDGE: bp:p1:ext-lebesgue | blueprint/parts/p1-analysis.tex#step:p1:li-preimage@L1159-L1161 | N cap Phi(A) subset N, so its outer measure is zero

NODE: step:p1:li-product
KIND: step
TITLE: Products
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:li-product@L1163-L1165
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:li-product@L1163-L1165
CONTRACT_ID: step:p1:li-product
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: S subset R^n x R^n; F:S->R^n x R^n Lambda-Lipschitz in the max norm; for the preimage claim Phi:A->R^n x R^n injective with Lipschitz inverse and N of outer measure zero; product Lebesgue measure
SOURCE_QUANTIFIERS: n; d=2n
SOURCE_CONCLUSION: both claims hold on R^n x R^n with max norm and product Lebesgue measure
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:lip-image-product, step:p1:li-sum, step:p1:li-preimage
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:lip-image-product | blueprint/parts/p1-analysis.tex#step:p1:li-product@L1164-L1164 | identification of R^n x R^n with R^{2n}
EDGE: step:p1:li-sum | blueprint/parts/p1-analysis.tex#step:p1:li-product@L1164-L1165 | case d=2n of the image estimate
EDGE: step:p1:li-preimage | blueprint/parts/p1-analysis.tex#step:p1:li-product@L1164-L1165 | case d=2n of the preimage claim
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.lip_image_prod, KAM.lip_preimage_null_prod
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p1:mcshane
KIND: lemma
TITLE: McShane extension
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:mcshane@L1168-L1171
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:mcshane@L1173-L1194
CONTRACT_ID: bp:p1:mcshane
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X metric space; S subset X; Lambda>=0; phi:S->R^d Lambda-Lipschitz (max norm); optionally |phi|<=beta on S; beta >= 0 (for the clamped extension)
SOURCE_QUANTIFIERS: for all X, S, Lambda, phi, beta
SOURCE_CONCLUSION: phi extends to a Lambda-Lipschitz map on X; the extension can be chosen with |Phi|<=beta on X
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:mc-component, step:p1:mc-components, step:p1:mc-clamp
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:mc-component | blueprint/parts/p1-analysis.tex#bp:p1:mcshane@L1177-L1183 | proof step of this result
EDGE: step:p1:mc-components | blueprint/parts/p1-analysis.tex#bp:p1:mcshane@L1185-L1188 | proof step of this result
EDGE: step:p1:mc-clamp | blueprint/parts/p1-analysis.tex#bp:p1:mcshane@L1190-L1193 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+claude-main-orchestrator
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.mcshane (+ KAM.mcshane_prod)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:mc-component
KIND: step
TITLE: One component
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:mc-component@L1177-L1183
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:mc-component@L1177-L1183
CONTRACT_ID: step:p1:mc-component
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: phi_j:S->R Lambda-Lipschitz
SOURCE_QUANTIFIERS: component j
SOURCE_CONCLUSION: U_j(x)=inf_{y in S}(phi_j(y)+Lambda dist(x,y)) is finite, Lambda-Lipschitz and equals phi_j on S (S empty: extension 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.mcshane_component
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:mc-components
KIND: step
TITLE: All components
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:mc-components@L1185-L1188
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:mc-components@L1185-L1188
CONTRACT_ID: step:p1:mc-components
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X metric space; S subset X; Lambda>=0; phi:S->R^d Lambda-Lipschitz in max norm; U_j is the scalar extension constructed in the preceding step
SOURCE_QUANTIFIERS: max norm on R^d
SOURCE_CONCLUSION: U=(U_j) is a Lambda-Lipschitz extension of phi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:mc-component
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:mc-component | blueprint/parts/p1-analysis.tex#step:p1:mc-components@L1185-L1187 | componentwise extensions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.mcshane_components
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:mc-clamp
KIND: step
TITLE: Clamping
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:mc-clamp@L1190-L1193
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:mc-clamp@L1190-L1193
CONTRACT_ID: step:p1:mc-clamp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X metric space; S subset X; Lambda>=0; phi:S->R^d Lambda-Lipschitz in max norm; |phi|<=beta on S; U is the preceding constructed extension; beta >= 0 (for the clamped extension)
SOURCE_QUANTIFIERS: clamping Phi_j=max(-beta,min(beta,U_j))
SOURCE_CONCLUSION: Phi is a Lambda-Lipschitz extension of phi with |Phi|<=beta on X
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:mc-components
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:mc-components | blueprint/parts/p1-analysis.tex#step:p1:mc-clamp@L1191-L1192 | clamp the extension U
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1+claude-main-orchestrator
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.mcshane_clamp
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: repaired F1: the statement now assumes beta >= 0 (blueprint fix)

NODE: bp:p1:lipeo-fixed
KIND: claim
TITLE: Bijections fixing a set
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:lipeo-fixed@L1196-L1201
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:lipeo-fixed@L1196-L1201
CONTRACT_ID: bp:p1:lipeo-fixed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi a bijection of R^d with Psi(x)=x for x in Z' subset R^d
SOURCE_QUANTIFIERS: Psi, Z'
SOURCE_CONCLUSION: Psi maps R^d minus Z' onto itself
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.lipeo_fixed
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: Self-contained remark; proof is inline (injectivity argument).

NODE: bp:p1:lipeo
KIND: lemma
TITLE: Lipeomorphisms
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:lipeo@L1203-L1207
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:lipeo@L1209-L1225
CONTRACT_ID: bp:p1:lipeo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G:R^d->R^d lambda-Lipschitz with lambda<1; Psi=id+G; (second claim) G=0 on Z'
SOURCE_QUANTIFIERS: for all d, lambda<1, G, Z'
SOURCE_CONCLUSION: Psi is a bijection of R^d with (1-lambda)|x-y|<=|Psi(x)-Psi(y)|<=(1+lambda)|x-y|; if G=0 on Z' then Psi maps R^d minus Z' onto itself
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p1:lipeo-bounds, step:p1:lipeo-onto, step:p1:lipeo-zero
ROUTES: -
ROUTE_FOR: -
EDGE: step:p1:lipeo-bounds | blueprint/parts/p1-analysis.tex#bp:p1:lipeo@L1212-L1215 | proof step of this result
EDGE: step:p1:lipeo-onto | blueprint/parts/p1-analysis.tex#bp:p1:lipeo@L1217-L1220 | proof step of this result
EDGE: step:p1:lipeo-zero | blueprint/parts/p1-analysis.tex#bp:p1:lipeo@L1222-L1224 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.lipeo (via KAM.lipeo_complete; constants KAM.lipeo_half)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:lipeo-bounds
KIND: step
TITLE: Bi-Lipschitz bounds
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:lipeo-bounds@L1212-L1215
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:lipeo-bounds@L1212-L1215
CONTRACT_ID: step:p1:lipeo-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G lambda-Lipschitz, lambda<1
SOURCE_QUANTIFIERS: x,y in R^d
SOURCE_CONCLUSION: (1-lambda)|x-y|<=|Psi(x)-Psi(y)|<=(1+lambda)|x-y|; Psi injective with (1-lambda)^{-1}-Lipschitz inverse on the image
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.lipeo_bounds
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:lipeo-onto
KIND: step
TITLE: Surjectivity
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:lipeo-onto@L1217-L1220
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:lipeo-onto@L1217-L1220
CONTRACT_ID: step:p1:lipeo-onto
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G lambda-Lipschitz, lambda<1; R^d complete
SOURCE_QUANTIFIERS: y in R^d
SOURCE_CONCLUSION: Psi surjective, hence a bijection of R^d with (1-lambda)^{-1}-Lipschitz inverse
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-banach, step:p1:lipeo-bounds
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-banach | blueprint/parts/p1-analysis.tex#step:p1:lipeo-onto@L1218-L1219 | fixed point of the contraction x->y-G(x)
EDGE: step:p1:lipeo-bounds | blueprint/parts/p1-analysis.tex#step:p1:lipeo-onto@L1219-L1220 | injectivity and Lipschitz inverse from the lower bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.lipeo_onto
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p1:lipeo-zero
KIND: step
TITLE: The set where $G$ vanishes
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:lipeo-zero@L1222-L1224
PROOF_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:lipeo-zero@L1222-L1224
CONTRACT_ID: step:p1:lipeo-zero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G:R^d->R^d lambda-Lipschitz with lambda<1; Psi=id+G; G=0 on Z-prime subset R^d
SOURCE_QUANTIFIERS: Z'
SOURCE_CONCLUSION: Psi maps R^d minus Z' onto itself
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:lipeo-fixed, step:p1:lipeo-onto
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:lipeo-fixed | blueprint/parts/p1-analysis.tex#step:p1:lipeo-zero@L1223-L1224 | bijection fixing Z' pointwise preserves the complement
EDGE: step:p1:lipeo-onto | blueprint/parts/p1-analysis.tex#step:p1:lipeo-zero@L1223-L1223 | Psi is a bijection of R^d
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p1c+sol-review-r1
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.lipeo_zero
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-LIP-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:standing
KIND: definition
TITLE: Standing data of Part~\ref{bp:p2}
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:standing@L56-L65
PROOF_SOURCE: -
CONTRACT_ID: bp:p2:standing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (this is the package of typing data)
SOURCE_QUANTIFIERS: fixed once for all of Part 2 (outermost): n>=2, tau>=n-1, M,sigma_K,sigma_B,sigma_T>0, B(frak) open in C^n x C^n invariant under (theta,I)->(theta+k,I), h, gamma>0, omega
SOURCE_CONCLUSION: defines the standing data: h holomorphic on B(frak), 1-periodic in theta, real at real points; |X_h|,|DX_h|,|D^2X_h| <= M on B(frak) (bilinear operator norm for D^2X_h); gamma>0 and omega in Dio_{gamma,tau}
CONSTANT_SCOPE: M, sigma_K, sigma_B, sigma_T, n, tau, gamma, omega, h, B(frak) are fixed for all of Part 2; nothing depends on later quantities
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:hamiltonian#hamiltonianVectorFieldC, bp:p0:diophantine#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:hamiltonian#hamiltonianVectorFieldC | blueprint/parts/p2-aposteriori.tex#bp:p2:standing@L62-L62 | X_h in the bounds is the Hamiltonian vector field
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p2-aposteriori.tex#bp:p2:standing@L64-L64 | omega in Dio_{gamma,tau}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Params, KAM.Apost.Standing
LEAN_NOTE: definitions/standing data per the audited Part 2/3 design; prover evidence + independent audit docs/campaign/audits/P2-1b-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:constants
KIND: definition
TITLE: Exponents and constants
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:constants@L78-L108
PROOF_SOURCE: -
CONTRACT_ID: bp:p2:constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: tau>=0, n>=1 (here n>=2, tau>=n-1); c(n,tau) the constant of the cohomological lemma; M,sigma_K,sigma_B,sigma_T>0; mu>0 and 0<rho_inf<rho for c_* and delta_0
SOURCE_QUANTIFIERS: for the data (n,tau,M,sigma_K,sigma_B,sigma_T) in order; then for mu>0 and 0<rho_inf<rho
SOURCE_CONCLUSION: defines kappa=tau+n, a=2kappa+2, c_R, m(frak), Theta=4n m^3, the constants C_X,C_T,C_Omega,C_sym,C_red,C_xi0,C_xiN,C_g,C_xi,C_DeltaK,C_lin,C_E,C_G,C_B,C_DeltaN,C_DeltaX,C_DeltaT,c_step,c_sum, and c_*, delta_0; the constants defined through L97 are >=1 (L99); c_* and delta_0 are defined subsequently, with delta_0=min{1,(rho-rho_inf)/8} in (0,1]
CONSTANT_SCOPE: kappa,a,c_R,m,Theta,C_* and c_step,c_sum depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); c_* = c_*(n,tau,M,sigma_K,sigma_B,sigma_T,mu); delta_0 = delta_0(rho,rho_inf)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cohomological, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cohomological | blueprint/parts/p2-aposteriori.tex#bp:p2:constants@L79-L79 | c(n,tau) is the constant of the cohomological lemma
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:constants@L99-L99 | the constants are functions of the standing parameters n,tau,M,sigma_K,sigma_B,sigma_T
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.{kappa … delta0}, KAM.Apost.constants_spec
LEAN_NOTE: definitions/standing data per the audited Part 2/3 design; prover evidence + independent audit docs/campaign/audits/P2-1b-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:matrix
KIND: corollary
TITLE: Matrix norms
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:matrix@L122-L139
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:matrix@L141-L156
CONTRACT_ID: bp:p2:matrix
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standard matrix and vector norms (max norm on vectors, |M|=max_i sum_j |M_ij|, operator norm on bilinear/matrix maps); Omega_0 the canonical 2n x 2n matrix
SOURCE_QUANTIFIERS: for all p,q and all p x q complex matrices M, M_1, M_2, M_ij, vectors v; block matrices conformal; matrices U_1,U_2 with n rows
SOURCE_CONCLUSION: (a) max|M_ij|<=|M|=sup_{|v|<=1}|Mv| and |M^T|<=p|M|; (b) |M_1M_2|<=|M_1||M_2|, |Mv|<=|M||v|; (c) block bounds and |diag(M_1,M_2)|=max{|M_1|,|M_2|}; (d) Omega_0^T=-Omega_0=Omega_0^{-1}, Omega_0^2=-I, Omega_0^T Omega_0=I, |Omega_0|=1, Omega_0(U_1;U_2)=(-U_2;U_1)
CONSTANT_SCOPE: none (constants are absolute, no parameters)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:matrix-op, step:p2:matrix-transpose, step:p2:matrix-blocks, bp:p0:hamiltonian#omegaZero
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:matrix-op | blueprint/parts/p2-aposteriori.tex#bp:p2:matrix@L142-L142 | proof step of this result
EDGE: step:p2:matrix-transpose | blueprint/parts/p2-aposteriori.tex#bp:p2:matrix@L146-L146 | proof step of this result
EDGE: step:p2:matrix-blocks | blueprint/parts/p2-aposteriori.tex#bp:p2:matrix@L149-L149 | proof step of this result
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p2-aposteriori.tex#bp:p2:matrix@L134-L134 | Omega_0 in (d)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.matrix_facts
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:matrix-op
KIND: step
TITLE: Operator norm
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:matrix-op@L142-L144
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:matrix-op@L142-L144
CONTRACT_ID: step:p2:matrix-op
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M a p x q matrix
SOURCE_QUANTIFIERS: for all p x q matrices M
SOURCE_CONCLUSION: |M|=max_i sum_j|M_ij|=sup_{|v|<=1}|Mv| and |M_ij|<=|M|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:operator-norms
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:operator-norms | blueprint/parts/p2-aposteriori.tex#step:p2:matrix-op@L143-L143 | operator norm as row sum and sup
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.isGreatest_norm_mulVec, KAM.norm_entry_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:matrix-transpose
KIND: step
TITLE: Transpose and products
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:matrix-transpose@L146-L147
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:matrix-transpose@L146-L147
CONTRACT_ID: step:p2:matrix-transpose
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: M, M_1, M_2 matrices of compatible sizes
SOURCE_QUANTIFIERS: for all such matrices
SOURCE_CONCLUSION: |M^T|<=p|M| and |M_1M_2|<=|M_1||M_2|, |Mv|<=|M||v|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:matrix-norms
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:matrix-norms | blueprint/parts/p2-aposteriori.tex#step:p2:matrix-transpose@L147-L147 | transpose bound and product bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.norm_transpose_le_card_mul, Matrix.linfty_opNorm_mul
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:matrix-blocks
KIND: step
TITLE: Blocks and $\Omega_0$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:matrix-blocks@L149-L155
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:matrix-blocks@L149-L155
CONTRACT_ID: step:p2:matrix-blocks
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: block matrices M_1,M_2,M_ij; matrices U_1,U_2 with n rows
SOURCE_QUANTIFIERS: for all such block matrices
SOURCE_CONCLUSION: block bounds in (c), |diag(M_1,M_2)|=max{|M_1|,|M_2|}, and the identities of (d) for Omega_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:operator-norms, bp:p1:matrix-norms
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:operator-norms | blueprint/parts/p2-aposteriori.tex#step:p2:matrix-blocks@L150-L150 | block bounds, Omega_0^T=-Omega_0, Omega_0^2=-I, ~Omega_0~=1
EDGE: bp:p1:matrix-norms | blueprint/parts/p2-aposteriori.tex#step:p2:matrix-blocks@L151-L151 | stacked-block identity for diag(M_1,M_2)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Tools.{norm_fromCols_le_add, norm_fromBlocks_diagonal, omegaZeroMatrix_transpose_mul_self, omegaZeroMatrix_inv, omegaZeroMatrix_mul_fromRows}
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:averages
KIND: corollary
TITLE: Averages
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:averages@L158-L167
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:averages@L169-L180
CONTRACT_ID: bp:p2:averages
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (a) f: R^n->C^{pxq} continuous and 1-periodic; (b) v holomorphic and 1-periodic on T_r (not necessarily bounded), values in C, C^p or C^{pxq}
SOURCE_QUANTIFIERS: for all p,q, r>0, f resp. v; averages over [0,1]^n
SOURCE_CONCLUSION: (a) f integrable on [0,1]^n, avg f linear in f, real if f is, |avg f|<=sup_{[0,1]^n}|f|; (b) avg(d_{theta_l} v)=0 for every l and avg(d_omega v)=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:avg-bound, step:p2:avg-deriv, bp:p0:domains#complexStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:avg-bound | blueprint/parts/p2-aposteriori.tex#bp:p2:averages@L170-L170 | proof step of (a)
EDGE: step:p2:avg-deriv | blueprint/parts/p2-aposteriori.tex#bp:p2:averages@L175-L175 | proof step of (b)
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p2-aposteriori.tex#bp:p2:averages@L163-L163 | T_r in (b)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.averages
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:avg-bound
KIND: step
TITLE: Integrability and the bound
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:avg-bound@L170-L173
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:avg-bound@L170-L173
CONTRACT_ID: step:p2:avg-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f continuous 1-periodic on R^n with values in matrices
SOURCE_QUANTIFIERS: for all such f
SOURCE_CONCLUSION: f integrable, avg f linear and real for real f, |avg f|<=sup|f|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-integral, bp:p1:averages-matrix
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-integral | blueprint/parts/p2-aposteriori.tex#step:p2:avg-bound@L171-L171 | continuous functions are integrable on a compact box
EDGE: bp:p1:averages-matrix | blueprint/parts/p2-aposteriori.tex#step:p2:avg-bound@L172-L172 | ~avg f~<=sup_{R^n}~f~
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Tools.{torusAverage_basic, torusAverage_vector_apply, im_integral_eq_zero}
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:avg-deriv
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:avg-deriv@L175-L179
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:avg-deriv@L175-L179
CONTRACT_ID: step:p2:avg-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v holomorphic and 1-periodic on T_r, r>0; values scalar, vector or matrix (no additional C^1 premise)
SOURCE_QUANTIFIERS: for all such v and l
SOURCE_CONCLUSION: avg(d_{theta_l} v)=0 and avg(d_omega v)=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: step:p2:avg-deriv#real-route, step:p2:avg-deriv#bounded-route
ROUTE_FOR: -
EDGE: step:p2:avg-deriv#real-route | blueprint/parts/p2-aposteriori.tex#step:p2:avg-deriv@L176-L178 | direct restriction to the real torus
EDGE: step:p2:avg-deriv#bounded-route | blueprint/parts/p2-aposteriori.tex#step:p2:avg-deriv@L178-L179 | explicit parenthetical alternative on T_{r/2}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Tools.torusAverage_fderiv_apply_eq_zero
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: The two proofs at L176-L179 are alternatives, not a conjunction. The C^1 property in the first route is derived from holomorphy.

NODE: bp:p2:cohomological
KIND: corollary
TITLE: Cohomological equation in operator norms
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:cohomological@L186-L198
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:cohomological@L200-L212
CONTRACT_ID: bp:p2:cohomological
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<delta<r; Gamma_delta=c_R gamma^{-1} delta^{-kappa}; the standing data of Part 2 (gamma, tau, omega in Dio_{gamma,tau}); (a) g:T_r->C^p holomorphic, 1-periodic, |g|<=H, avg g=0; (b) u:T_r->C^{pxq} holomorphic, 1-periodic, avg u=0, |d_omega u|<=H on T_r
SOURCE_QUANTIFIERS: for all 0<delta<r, p,q, H; g resp. u as stated (outermost: standing data)
SOURCE_CONCLUSION: (a) unique u=Rg holomorphic 1-periodic on T_{r-delta}, avg u=0, d_omega u=g, |u|<=Gamma_delta H, real on reals if g is; (b) |u|<=Gamma_delta H on T_{r-delta}
CONSTANT_SCOPE: c_R depends only on (n,tau); kappa=tau+n; Gamma_delta depends on gamma, delta, n, tau only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:coh-components, step:p2:coh-apriori, bp:p2:constants, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:coh-components | blueprint/parts/p2-aposteriori.tex#bp:p2:cohomological@L201-L201 | proof step of (a)
EDGE: step:p2:coh-apriori | blueprint/parts/p2-aposteriori.tex#bp:p2:cohomological@L207-L207 | proof step of (b)
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:cohomological@L187-L187 | c_R and kappa in Gamma_delta
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:cohomological@L187-L187 | gamma, tau, omega of the package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.cohomological
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-STRIP-3b-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:coh-components
KIND: step
TITLE: Componentwise solution
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:coh-components@L201-L205
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:coh-components@L201-L205
CONTRACT_ID: step:p2:coh-components
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g:T_r->C^p holomorphic, 1-periodic, |g|<=H, avg g=0; 0<delta<r
SOURCE_QUANTIFIERS: for each component g_i; delta fixed
SOURCE_CONCLUSION: unique componentwise solution u, |u|<=Gamma_delta H, real if g real; uniqueness of u
CONSTANT_SCOPE: c(n,tau)<=c_R
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cohomological, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cohomological | blueprint/parts/p2-aposteriori.tex#step:p2:coh-components@L202-L202 | solve each component
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:coh-components@L204-L204 | c(n,tau)<=c_R and Gamma_delta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.cohomological (KAM/Apost/Tools.lean:322), first conjunct; via KAM.cohomological
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md (supersedes the "blocked" rows of docs/campaign/audits/P2-3-audit-1.md); kernel replay passed with the package
NOTE: -

NODE: step:p2:coh-apriori
KIND: step
TITLE: The a-priori bound
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:coh-apriori@L207-L211
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:coh-apriori@L207-L211
CONTRACT_ID: step:p2:coh-apriori
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the local standing data of Part 2 (bp:p2:standing, L56-L65); u:T_r->C^{pxq} holomorphic 1-periodic, avg u=0, |d_omega u|<=H on T_r
SOURCE_QUANTIFIERS: standing data fixed first; for all such u; 0<delta<r
SOURCE_CONCLUSION: |u|<=Gamma_delta H on T_{r-delta}
CONSTANT_SCOPE: c(n,tau)<=c_R
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:averages, bp:p1:cohomological-operator, bp:p2:constants, bp:p1:holomorphic-regularity, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:averages | blueprint/parts/p2-aposteriori.tex#step:p2:coh-apriori@L209-L209 | avg d_omega u=0
EDGE: bp:p1:cohomological-operator | blueprint/parts/p2-aposteriori.tex#step:p2:coh-apriori@L210-L210 | a-priori bound for periodic solutions of Du omega=g
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:coh-apriori@L211-L211 | c(n,tau)<=c_R, Gamma_delta
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p2-aposteriori.tex#step:p2:coh-apriori@L208-L208 | g=d_omega u is holomorphic since derivatives of holomorphic maps are holomorphic
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:coh-apriori@L208-L211 | the local package supplies gamma>0 and Diophantine omega with tau>=n-1>=0 for the cohomological application
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a+sol-review-r4
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.cohomological (KAM/Apost/Tools.lean:322), second conjunct; via KAM.cohomological_apriori_operator
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/I-STRIP-3b-audit-1.md (supersedes "PARTIAL/blocked" row of docs/campaign/audits/P2-3-audit-1.md); kernel replay passed with the package
NOTE: -

NODE: bp:p2:hamiltonian
KIND: lemma
TITLE: The Hamiltonian vector field
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:hamiltonian@L214-L230
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:hamiltonian@L232-L258
CONTRACT_ID: bp:p2:hamiltonian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing)
SOURCE_QUANTIFIERS: z in B(frak), k in Z^n, beta>0, w with |w|<beta and B_beta(z) subset B(frak); M from the standing data
SOURCE_CONCLUSION: (a) X_h holomorphic, DX_h and D^2X_h exist, |D(DX_h)|=|D^2X_h|<=M; (b) X_h and DX_h are invariant under z->z+(k,0); (c) X_h,DX_h real at real z; (d) Omega_0 X_h=(Dh)^T, Omega_0 DX_h symmetric, DX_h^T Omega_0+Omega_0 DX_h=0; (e) |DX_h(z+w)-DX_h(z)|<=M|w| and |X_h(z+w)-X_h(z)-DX_h(z)w|<=M|w|^2
CONSTANT_SCOPE: constants are M and the standing data only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:ham-regular, step:p2:ham-periodic, step:p2:ham-real, step:p2:ham-symplectic, step:p2:ham-mvt, bp:p2:standing, bp:p0:hamiltonian#hamiltonianVectorFieldC, bp:p0:hamiltonian#omegaZero
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:ham-regular | blueprint/parts/p2-aposteriori.tex#bp:p2:hamiltonian@L233-L233 | proof step (a)
EDGE: step:p2:ham-periodic | blueprint/parts/p2-aposteriori.tex#bp:p2:hamiltonian@L238-L238 | proof step (b)
EDGE: step:p2:ham-real | blueprint/parts/p2-aposteriori.tex#bp:p2:hamiltonian@L243-L243 | proof step (c)
EDGE: step:p2:ham-symplectic | blueprint/parts/p2-aposteriori.tex#bp:p2:hamiltonian@L248-L248 | proof step (d)
EDGE: step:p2:ham-mvt | blueprint/parts/p2-aposteriori.tex#bp:p2:hamiltonian@L253-L253 | proof step (e)
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:hamiltonian@L215-L215 | the lemma is stated under the standing assumption
EDGE: bp:p0:hamiltonian#hamiltonianVectorFieldC | blueprint/parts/p2-aposteriori.tex#bp:p2:hamiltonian@L217-L217 | X_h
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p2-aposteriori.tex#bp:p2:hamiltonian@L221-L221 | Omega_0 in (d)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.hamiltonian
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-4-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ham-regular
KIND: step
TITLE: Regularity
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ham-regular@L233-L236
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ham-regular@L233-L236
CONTRACT_ID: step:p2:ham-regular
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing): h holomorphic on B(frak)
SOURCE_QUANTIFIERS: z in B(frak)
SOURCE_CONCLUSION: Dh and all derivatives holomorphic; X_h holomorphic on B(frak); |D(DX_h)|=|D^2X_h|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-regularity, bp:p0:hamiltonian#hamiltonianVectorFieldC, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p2-aposteriori.tex#step:p2:ham-regular@L234-L234 | derivatives of holomorphic h are holomorphic
EDGE: bp:p0:hamiltonian#hamiltonianVectorFieldC | blueprint/parts/p2-aposteriori.tex#step:p2:ham-regular@L235-L235 | X_h=(d_I h,-d_theta h) by definition
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:ham-regular@L234-L234 | h holomorphic on B(frak)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.differentiableOn_fderiv_h, differentiableOn_ham, differentiableOn_fderiv_ham, norm_fderiv_fderiv_eq, ham_regularity (KAM/Apost/Hamiltonian.lean:140-165)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-4-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p2:ham-periodic
KIND: step
TITLE: Periodicity
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ham-periodic@L238-L241
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ham-periodic@L238-L241
CONTRACT_ID: step:p2:ham-periodic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing): B(frak) invariant under t_k=(theta,I)->(theta+k,I), h o t_k=h
SOURCE_QUANTIFIERS: k in Z^n, z in B(frak)
SOURCE_CONCLUSION: X_h o t_k=X_h and DX_h o t_k=DX_h
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:ham-periodic@L239-L239 | invariance of B(frak) and periodicity of h
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.fderiv_h_translate, ham_translate, fderiv_ham_translate, ham_periodic (KAM/Apost/Hamiltonian.lean:178-203)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-4-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p2:ham-real
KIND: step
TITLE: Realness
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ham-real@L243-L246
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ham-real@L243-L246
CONTRACT_ID: step:p2:ham-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing): h real at real points of B(frak)
SOURCE_QUANTIFIERS: real z in B(frak)
SOURCE_CONCLUSION: Dh, X_h and DX_h are real at real points
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:ham-real@L244-L244 | h real at real points
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.im_fderiv_real_direction, im_ham_eq_zero, im_sqMat_ham, ham_real (KAM/Apost/Hamiltonian.lean:75,212,244,258)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-4-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p2:ham-symplectic
KIND: step
TITLE: Symplectic identity
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ham-symplectic@L248-L251
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ham-symplectic@L248-L251
CONTRACT_ID: step:p2:ham-symplectic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h holomorphic on B(frak); Omega_0^T=-Omega_0
SOURCE_QUANTIFIERS: z in B(frak)
SOURCE_CONCLUSION: Omega_0 X_h=(Dh)^T, Omega_0 DX_h=D^2h symmetric, DX_h^T Omega_0=-Omega_0 DX_h
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:hamiltonian-real, bp:p1:holomorphic-regularity, bp:p2:matrix
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:hamiltonian-real | blueprint/parts/p2-aposteriori.tex#step:p2:ham-symplectic@L249-L249 | Omega_0 X_h=(Dh)^T
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p2-aposteriori.tex#step:p2:ham-symplectic@L250-L250 | symmetry of the Hessian
EDGE: bp:p2:matrix | blueprint/parts/p2-aposteriori.tex#step:p2:ham-symplectic@L251-L251 | Omega_0^T=-Omega_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.sumVec_omegaZero_ham, fderiv_fderiv_comm, omegaZeroMatrix_mul_sqMat_apply, ham_symplectic (KAM/Apost/Hamiltonian.lean:269-329)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-4-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p2:ham-mvt
KIND: step
TITLE: Mean value estimates
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ham-mvt@L253-L257
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ham-mvt@L253-L257
CONTRACT_ID: step:p2:ham-mvt
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); B_beta(z) subset B(frak), |w|<beta; (a): |D(DX_h)|<=M
SOURCE_QUANTIFIERS: z in B(frak), w with |w|<beta
SOURCE_CONCLUSION: |DX_h(z+w)-DX_h(z)|<=M|w| and |X_h(z+w)-X_h(z)-DX_h(z)w|<=(M/2)|w|^2<=M|w|^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:increments-open, bp:p1:taylor, step:p2:ham-regular, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:increments-open | blueprint/parts/p2-aposteriori.tex#step:p2:ham-mvt@L255-L255 | mean value estimate on the convex ball
EDGE: bp:p1:taylor | blueprint/parts/p2-aposteriori.tex#step:p2:ham-mvt@L256-L256 | second order Taylor bound with A=M
EDGE: step:p2:ham-regular | blueprint/parts/p2-aposteriori.tex#step:p2:ham-mvt@L256-L256 | ~D(DX_h)~<=M by (a)
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:ham-mvt@L256-L256 | bounds by M
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.ham_mvt (KAM/Apost/Hamiltonian.lean:351)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-4-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: bp:p2:objects
KIND: definition
TITLE: Objects attached to a parameterization
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:objects@L270-L293
PROOF_SOURCE: -
CONTRACT_ID: bp:p2:objects
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r>0; K:C^n->C^n x C^n holomorphic on T_r with K(T_r) subset B(frak) (data of the standing package); for the second group det G != 0 on T_r; for avg T, T continuous on R^n
SOURCE_QUANTIFIERS: for all r>0, K, theta in T_r; the standing data fixed outermost
SOURCE_CONCLUSION: defines L=DK, G=L^T L, E=X_h o K - L omega, A=DX_h o K, Omega_K=L^T Omega_0 L; and where det G != 0: B=G^{-1}, N=Omega_0 L B, P=(L N), X_N=AN-d_omega N, T=N^T Omega_0 X_N, E_sym=P^T Omega_0 P-Omega_0, Q=-Omega_0 P^T Omega_0, eta=Omega_0 P^T Omega_0 E=(eta^L;eta^N)=(-N^T Omega_0 E; L^T Omega_0 E); avg T=int_{[0,1]^n} T
CONSTANT_SCOPE: none (definitions; depend on K, h, omega only)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:standing, bp:p0:domains#complexStrip, bp:p0:hamiltonian#hamiltonianVectorFieldC, bp:p0:hamiltonian#omegaZero
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:objects@L271-L271 | B(frak), h, omega of the package
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p2-aposteriori.tex#bp:p2:objects@L271-L271 | T_r
EDGE: bp:p0:hamiltonian#hamiltonianVectorFieldC | blueprint/parts/p2-aposteriori.tex#bp:p2:objects@L275-L275 | X_h
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p2-aposteriori.tex#bp:p2:objects@L276-L276 | Omega_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Torus.{tangentMat, linMat, lagrangeMat, normalMat, frameMat, normalFieldMat, symDefect, reducer, eta, etaL, etaN, errDerivMat, triangularMat, redDefect}, KAM.Torus.eta_eq_sumElim
LEAN_NOTE: definitions per the audited Part 2/3 design (+ carrier KAM/Torus/Basic.lean, KAM/Matrix/Calculus.lean); audits docs/campaign/audits/P2-1a-audit-1.md and -audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:frozen-agreement
KIND: claim
TITLE: Agreement with the frozen definitions
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:frozen-agreement@L295-L304
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:frozen-agreement@L295-L304
CONTRACT_ID: bp:p2:frozen-agreement
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: on the open strip T_r: the objects of bp:p2:objects; det G a unit where inverse is used; T continuous on R^n for avg T
SOURCE_QUANTIFIERS: for all r>0, K as in bp:p2:objects; frozen definitions in their stated arguments
SOURCE_CONCLUSION: the frozen gramMatrix, normalFrame, torsion, invarianceError coincide with G, N, T, E; the frozen matrix inverse is the true inverse where det is a unit; the frozen torsionAverage equals avg T at real points; each use of B,N,T is preceded by det G != 0 and each use of avg T by continuity of T on R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:objects, bp:p0:stripdata#gramMatrix, bp:p0:stripdata#normalFrame, bp:p0:stripdata#torsion, bp:p0:stripdata#invarianceError, bp:p0:stripdata#torsionAverage
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#bp:p2:frozen-agreement@L296-L296 | G,N,T,E,avg T compared with the frozen definitions
EDGE: bp:p0:stripdata#gramMatrix | blueprint/parts/p2-aposteriori.tex#bp:p2:frozen-agreement@L296-L296 | frozen G
EDGE: bp:p0:stripdata#normalFrame | blueprint/parts/p2-aposteriori.tex#bp:p2:frozen-agreement@L297-L297 | frozen N
EDGE: bp:p0:stripdata#torsion | blueprint/parts/p2-aposteriori.tex#bp:p2:frozen-agreement@L298-L298 | frozen T
EDGE: bp:p0:stripdata#invarianceError | blueprint/parts/p2-aposteriori.tex#bp:p2:frozen-agreement@L299-L299 | frozen E
EDGE: bp:p0:stripdata#torsionAverage | blueprint/parts/p2-aposteriori.tex#bp:p2:frozen-agreement@L300-L300 | frozen avg T
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Torus.frozen_agreement (items: gramMatrix_eq_tangentMat_transpose_mul, sumVec_normalFrame, sumVec_invarianceError, torsion_eq_mat, gramMatrix_mul_inv, inv_gramMatrix_mul, torsionAverage_eq_avg)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-2-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: a bridge claim between the frozen definitions and the Part 2 objects; kept because Part 2 conclusion step nodes consume it; the reference to bp:p0:totality (excluded in K-p0 as an administrative note) is a pointer, so the former edge was dropped

NODE: bp:p2:admissible
KIND: definition
TITLE: Admissible parameterization
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:admissible@L306-L317
PROOF_SOURCE: -
CONTRACT_ID: bp:p2:admissible
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r>0, beta>0, 0<=epsilon<=1; the standing data of Part 2 (B(frak), sigma_K, sigma_B, sigma_T)
SOURCE_QUANTIFIERS: for all r,beta,epsilon, K:C^n->C^n x C^n
SOURCE_CONCLUSION: defines (r,beta,epsilon)-admissible: (A1) K holomorphic, primary and real on reals on T_r; (A2) B_beta(K(theta)) subset B(frak) for all theta in T_r; (A3) |DK|<=sigma_K on T_r; (A4) det G != 0 and |B|<=sigma_B on T_r; (A5) avg T invertible and |avg T^{-1}|<=sigma_T; (A6) |E|<=epsilon on T_r
CONSTANT_SCOPE: none (definition; uses sigma_K,sigma_B,sigma_T of the standing data)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:standing, bp:p2:objects, bp:p0:stripdata#IsPrimaryOnStrip, bp:p0:stripdata#IsRealOnReals, bp:p0:stripdata#torsionAverage
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:admissible@L311-L311 | B(frak) and sigma_K,sigma_B,sigma_T
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#bp:p2:admissible@L313-L313 | G, B, E, T, avg T
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p2-aposteriori.tex#bp:p2:admissible@L310-L310 | primary on T_r
EDGE: bp:p0:stripdata#IsRealOnReals | blueprint/parts/p2-aposteriori.tex#bp:p2:admissible@L310-L310 | real on reals
EDGE: bp:p0:stripdata#torsionAverage | blueprint/parts/p2-aposteriori.tex#bp:p2:admissible@L314-L314 | avg T
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Admissible
LEAN_NOTE: definitions/standing data per the audited Part 2/3 design; prover evidence + independent audit docs/campaign/audits/P2-1b-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:periodicity
KIND: lemma
TITLE: Periodicity and realness of the attached objects
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:periodicity@L324-L333
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:periodicity@L335-L355
CONTRACT_ID: bp:p2:periodicity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); K holomorphic and primary on T_r with K(T_r) subset B(frak); for B,N,P,X_N,T,E_sym,eta: det G != 0 on T_r; for realness: K real on reals
SOURCE_QUANTIFIERS: for all r>0, K as stated
SOURCE_CONCLUSION: L,G,E,A,Omega_K,h o K, K^I and f_j=(K^I)^T d_{theta_j}K^theta (j=1..n) are 1-periodic on T_r; if det G != 0 then B,N,P,X_N,T,E_sym,eta are 1-periodic; if also K real on reals, all these objects and avg T are real at real points
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:per-dk, step:p2:per-compose, step:p2:per-real, bp:p2:standing, bp:p2:objects, bp:p0:stripdata#IsPrimaryOnStrip, bp:p0:stripdata#IsRealOnReals
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:per-dk | blueprint/parts/p2-aposteriori.tex#bp:p2:periodicity@L336-L336 | proof step
EDGE: step:p2:per-compose | blueprint/parts/p2-aposteriori.tex#bp:p2:periodicity@L342-L342 | proof step
EDGE: step:p2:per-real | blueprint/parts/p2-aposteriori.tex#bp:p2:periodicity@L348-L348 | proof step
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:periodicity@L325-L325 | h periodic on B(frak)
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#bp:p2:periodicity@L325-L325 | the objects L,G,E,A,...
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p2-aposteriori.tex#bp:p2:periodicity@L325-L325 | primary K
EDGE: bp:p0:stripdata#IsRealOnReals | blueprint/parts/p2-aposteriori.tex#bp:p2:periodicity@L329-L329 | real on reals
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.periodicity
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-4-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:per-dk
KIND: step
TITLE: Periodicity of $DK$ and $K^I$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:per-dk@L336-L340
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:per-dk@L336-L340
CONTRACT_ID: step:p2:per-dk
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K holomorphic and primary on T_r, i.e. K(theta+k)=K(theta)+(k,0) on T_r
SOURCE_QUANTIFIERS: k in Z^n, theta in T_r
SOURCE_CONCLUSION: K^I, DK and D^2K are 1-periodic on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:stripdata#IsPrimaryOnStrip
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p2-aposteriori.tex#step:p2:per-dk@L337-L337 | primary identity K(theta+k)=K(theta)+(k,0)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.isPeriodicOn_fderiv_of_shift, periodic_fderiv_K, periodic_K_snd (KAM/Apost/Periodicity.lean:61,99,135)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-4-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p2:per-compose
KIND: step
TITLE: Periodicity of the composed objects
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:per-compose@L342-L346
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:per-compose@L342-L346
CONTRACT_ID: step:p2:per-compose
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2; K holomorphic and primary on T_r with K(T_r) subset B(frak); DK and K^I periodic by step:p2:per-dk; det G!=0 on T_r for expressions involving B,N,P,X_N,T,E_sym,eta
SOURCE_QUANTIFIERS: k in Z^n, theta in T_r
SOURCE_CONCLUSION: X_h o K, DX_h o K, h o K and the listed composed objects are periodic; inverse-dependent objects in the second list are asserted periodic only when det G!=0, as in the enclosing lemma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:hamiltonian, bp:p2:standing, step:p2:per-dk, bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:hamiltonian | blueprint/parts/p2-aposteriori.tex#step:p2:per-compose@L343-L343 | periodicity of X_h, DX_h under (k,0)
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:per-compose@L343-L343 | h periodic
EDGE: step:p2:per-dk | blueprint/parts/p2-aposteriori.tex#step:p2:per-compose@L343-L343 | K(theta+k)=K(theta)+(k,0), periodic L and K^I
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:per-compose@L344-L344 | the objects are algebraic expressions in L, X_h o K, A, K^I
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.ham_translate_single, periodic_tangentMat ... periodic_eta (KAM/Apost/Periodicity.lean:88-192)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-4-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p2:per-real
KIND: step
TITLE: Realness
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:per-real@L348-L354
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:per-real@L348-L354
CONTRACT_ID: step:p2:per-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2; K holomorphic and primary on T_r, K(T_r) subset B(frak), K real on reals; det G!=0 on T_r for the inverse-dependent second group and avg T
SOURCE_QUANTIFIERS: real x
SOURCE_CONCLUSION: all listed objects are real at real points and avg T is real
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:hamiltonian, bp:p1:real-inverse, bp:p2:averages, bp:p0:stripdata#IsRealOnReals, bp:p2:objects, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:hamiltonian | blueprint/parts/p2-aposteriori.tex#step:p2:per-real@L350-L350 | X_h, DX_h real at real points
EDGE: bp:p1:real-inverse | blueprint/parts/p2-aposteriori.tex#step:p2:per-real@L352-L352 | inverse of real invertible matrix is real
EDGE: bp:p2:averages | blueprint/parts/p2-aposteriori.tex#step:p2:per-real@L354-L354 | avg of real function is real
EDGE: bp:p0:stripdata#IsRealOnReals | blueprint/parts/p2-aposteriori.tex#step:p2:per-real@L349-L349 | K real on reals
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:per-real@L353-L353 | definitions of the objects
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:per-real@L350-L354 | the local package supplies h real at real points and real omega used by the reality argument
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a+sol-review-r4
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.im_sumVec_fderiv_real, hasRealEntries_* , hasRealVec_eta, im_action_dot, im_torsionAverage (KAM/Apost/Periodicity.lean:281-438)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-4-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: bp:p2:frequency
KIND: lemma
TITLE: Frequency bound
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:frequency@L357-L365
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:frequency@L367-L380
CONTRACT_ID: bp:p2:frequency
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); K satisfies (A3),(A4),(A6) on T_r with epsilon<=1 and K(T_r) subset B(frak)
SOURCE_QUANTIFIERS: for all r>0, epsilon in [0,1], K as stated
SOURCE_CONCLUSION: gamma<=|omega|<=2n sigma_K sigma_B (M+epsilon)<=Theta
CONSTANT_SCOPE: gamma, omega from the standing data; Theta=4n m^3 depends only on (n,M,sigma_K,sigma_B,sigma_T)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:freq-solve, step:p2:freq-upper, step:p2:freq-lower, bp:p2:admissible, bp:p2:standing, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:freq-solve | blueprint/parts/p2-aposteriori.tex#bp:p2:frequency@L368-L368 | proof step
EDGE: step:p2:freq-upper | blueprint/parts/p2-aposteriori.tex#bp:p2:frequency@L372-L372 | proof step
EDGE: step:p2:freq-lower | blueprint/parts/p2-aposteriori.tex#bp:p2:frequency@L377-L377 | proof step
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#bp:p2:frequency@L358-L358 | (A3),(A4),(A6)
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:frequency@L361-L361 | M, gamma, omega
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:frequency@L361-L361 | Theta and m
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.frequency
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:freq-solve
KIND: step
TITLE: Solving for $\omega$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:freq-solve@L368-L370
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:freq-solve@L368-L370
CONTRACT_ID: step:p2:freq-solve
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K satisfies (A4): det G != 0 on T_r; E=X_h(K)-L omega, B L^T L=I_n
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: omega=B(theta)L(theta)^T(X_h(K(theta))-E(theta))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:freq-solve@L369-L369 | definitions of E and B=G^{-1}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.FrameAux.ofReal_eq_inv_mul_transpose_mulVec
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:freq-upper
KIND: step
TITLE: Upper bound
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:freq-upper@L372-L375
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:freq-upper@L372-L375
CONTRACT_ID: step:p2:freq-upper
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); (A3),(A4),(A6), epsilon<=1; omega formula of the previous step
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: |omega|<=2n sigma_K sigma_B (M+epsilon)<=Theta
CONSTANT_SCOPE: m, Theta of bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:freq-solve, bp:p2:matrix, bp:p2:admissible, bp:p2:standing, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:freq-solve | blueprint/parts/p2-aposteriori.tex#step:p2:freq-upper@L374-L374 | formula for omega
EDGE: bp:p2:matrix | blueprint/parts/p2-aposteriori.tex#step:p2:freq-upper@L373-L373 | ~L^T~<=2n~L~ and product bound
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#step:p2:freq-upper@L373-L373 | ~DK~<=sigma_K, ~B~<=sigma_B, ~E~<=epsilon
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:freq-upper@L374-L374 | ~X_h~<=M
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:freq-upper@L375-L375 | m and Theta, M+epsilon<=2m
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.FrameAux.norm_le_of_pointwise, two_mul_le_Theta
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:freq-lower
KIND: step
TITLE: Lower bound
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:freq-lower@L377-L379
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:freq-lower@L377-L379
CONTRACT_ID: step:p2:freq-lower
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing): omega in Dio_{gamma,tau}
SOURCE_QUANTIFIERS: k=e_1
SOURCE_CONCLUSION: gamma<=|omega_1|<=|omega|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:diophantine#IsDiophantine, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p2-aposteriori.tex#step:p2:freq-lower@L378-L378 | Diophantine inequality at k=e_1
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:freq-lower@L378-L378 | omega in Dio_{gamma,tau}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.FrameAux.le_norm_of_dio
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:frame-basic
KIND: lemma
TITLE: Regularity and bounds of the frame
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:frame-basic@L382-L398
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:frame-basic@L400-L425
CONTRACT_ID: bp:p2:frame-basic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); K holomorphic on T_r satisfying (A2)-(A4) (primary and real not needed); (c) (A6); (d) |omega|<=Theta, 0<delta<=1, delta<r
SOURCE_QUANTIFIERS: for all r>0, K, epsilon, delta as stated
SOURCE_CONCLUSION: (a) L,G,E,A,Omega_K,B,N,P,X_N,T,E_sym,Q,eta holomorphic on T_r, B symmetric, T continuous on R^n so avg T defined; (b) |L|<=m, |L^T|<=2n m, |B|<=m, |N|<=m^2, |N^T|<=2n m^2, |P|<=2m^2, |A|<=m on T_r; (c) |eta^L|<=2n m^2 epsilon, |eta^N|<=2n m epsilon on T_r; (d) |X_N|<=C_X/delta, |T|<=C_T/delta on T_{r-delta}
CONSTANT_SCOPE: m, C_X, C_T depend only on (n,tau,M,sigma_K,sigma_B,sigma_T)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:fb-holo, step:p2:fb-bounds, step:p2:fb-eta, step:p2:fb-torsion, bp:p2:admissible, bp:p2:objects, bp:p2:constants, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:fb-holo | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-basic@L401-L401 | proof step (a)
EDGE: step:p2:fb-bounds | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-basic@L408-L408 | proof step (b)
EDGE: step:p2:fb-eta | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-basic@L414-L414 | proof step (c)
EDGE: step:p2:fb-torsion | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-basic@L418-L418 | proof step (d)
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-basic@L383-L383 | (A2)-(A4)
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-basic@L386-L386 | the objects
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-basic@L388-L388 | m, Theta, C_X, C_T
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-basic@L383-L384 | local Part 2 package is assumed by this result; h, omega and the ambient domain retain the enclosing standing data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.frame_basic
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:fb-holo
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fb-holo@L401-L406
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fb-holo@L401-L406
CONTRACT_ID: step:p2:fb-holo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the local standing data of Part 2 (bp:p2:standing, L56-L65); K holomorphic on T_r with (A2)-(A4), as stated in frame-basic at L383-L384; primary and real are not required
SOURCE_QUANTIFIERS: standing data fixed first; theta in T_r
SOURCE_CONCLUSION: all listed objects holomorphic on T_r; B symmetric; T continuous on R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:hamiltonian, bp:p2:admissible, bp:p1:holomorphic-inverse, bp:p2:objects, bp:p1:holomorphic-regularity, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:hamiltonian | blueprint/parts/p2-aposteriori.tex#step:p2:fb-holo@L402-L402 | X_h, DX_h holomorphic on B(frak)
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#step:p2:fb-holo@L403-L403 | (A4): det G != 0
EDGE: bp:p1:holomorphic-inverse | blueprint/parts/p2-aposteriori.tex#step:p2:fb-holo@L404-L404 | inverse of a holomorphic invertible matrix is holomorphic
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:fb-holo@L404-L404 | definitions of N,P,X_N,T,E_sym,Q,eta
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p2-aposteriori.tex#step:p2:fb-holo@L402-L405 | DK and d_omega N are holomorphic derivatives; K is holomorphic by hypothesis
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:fb-holo@L402-L405 | the local package supplies the open ambient domain and holomorphic h for the Hamiltonian regularity application
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.FrameAux.differentiableOn_*
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:fb-bounds
KIND: step
TITLE: Frame bounds
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fb-bounds@L408-L412
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fb-bounds@L408-L412
CONTRACT_ID: step:p2:fb-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); (A3),(A4) on T_r
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: |L|<=m,|L^T|<=2n m,|N|<=m^2,|N^T|<=2n m^2,|P|<=2m^2,|A|<=M<=m
CONSTANT_SCOPE: m=max{1,M,sigma_K,sigma_B,sigma_T}
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:admissible, bp:p2:matrix, bp:p2:standing, bp:p2:objects, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#step:p2:fb-bounds@L409-L409 | (A3),(A4)
EDGE: bp:p2:matrix | blueprint/parts/p2-aposteriori.tex#step:p2:fb-bounds@L409-L409 | ~Omega_0~=1, transpose and product bounds
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:fb-bounds@L412-L412 | ~DX_h~<=M
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:fb-bounds@L410-L410 | N,P definitions
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:fb-bounds@L409-L409 | m
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.FrameAux.norm_*_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:fb-eta
KIND: step
TITLE: Bounds on $\eta$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fb-eta@L414-L416
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fb-eta@L414-L416
CONTRACT_ID: step:p2:fb-eta
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (A6): |E|<=epsilon; bounds of the previous step; eta^L=-N^T Omega_0 E, eta^N=L^T Omega_0 E
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: |eta^L|<=2n m^2 epsilon and |eta^N|<=2n m epsilon
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:objects, step:p2:fb-bounds, bp:p2:matrix, bp:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:fb-eta@L415-L415 | eta^L,eta^N formulas
EDGE: step:p2:fb-bounds | blueprint/parts/p2-aposteriori.tex#step:p2:fb-eta@L415-L415 | ~N^T~,~L^T~
EDGE: bp:p2:matrix | blueprint/parts/p2-aposteriori.tex#step:p2:fb-eta@L415-L415 | ~Omega_0~=1 and product bound
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#step:p2:fb-eta@L415-L415 | (A6)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.FrameAux.norm_etaL_le, norm_etaN_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:fb-torsion
KIND: step
TITLE: Torsion bound
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fb-torsion@L418-L424
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fb-torsion@L418-L424
CONTRACT_ID: step:p2:fb-torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |N|<=m^2 on T_r; |omega|<=Theta; 0<delta<=1, delta<r; N holomorphic
SOURCE_QUANTIFIERS: theta in T_{r-delta}
SOURCE_CONCLUSION: |d_omega N|<=4n^2 m^5/delta, |X_N|<=C_X/delta, |T|<=C_T/delta
CONSTANT_SCOPE: C_X=5n^2 m^5, C_T=2n m^2 C_X
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cauchy-corollaries, step:p2:fb-bounds, step:p2:fb-holo, bp:p2:matrix, bp:p2:objects, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cauchy-corollaries | blueprint/parts/p2-aposteriori.tex#step:p2:fb-torsion@L419-L419 | Cauchy estimate for d_omega N
EDGE: step:p2:fb-bounds | blueprint/parts/p2-aposteriori.tex#step:p2:fb-torsion@L419-L419 | ~N~<=m^2, ~A~<=m, ~N^T~<=2n m^2
EDGE: step:p2:fb-holo | blueprint/parts/p2-aposteriori.tex#step:p2:fb-torsion@L419-L419 | N holomorphic
EDGE: bp:p2:matrix | blueprint/parts/p2-aposteriori.tex#step:p2:fb-torsion@L422-L422 | product bounds
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:fb-torsion@L422-L422 | X_N and T definitions
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:fb-torsion@L423-L423 | Theta, C_X, C_T
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.FrameAux.norm_normalFieldMat_le, norm_torsion_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:frame-identities
KIND: lemma
TITLE: Frame identities
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:frame-identities@L441-L463
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:frame-identities@L465-L513
CONTRACT_ID: bp:p2:frame-identities
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); K holomorphic on T_r, K(T_r) subset B(frak), det G != 0 on T_r
SOURCE_QUANTIFIERS: for all r>0, K as stated; identities on T_r
SOURCE_CONCLUSION: (a) L^T Omega_0 N=-I_n, N^T Omega_0 L=I_n, N^T Omega_0 N=B Omega_K B; (b) P^T Omega_0 P=Omega_0+E_sym, E_sym=diag(Omega_K, B Omega_K B); (c) d_omega L=AL-DE; (d) d_omega Omega_K=-(DE)^T Omega_0 L-L^T Omega_0 DE; (e) Q(AP-d_omega P)=Lambda+E_red with Lambda=[[0,T],[0,0]], E_red as stated; (f) QP=I_{2n}-Omega_0 E_sym and QE=-eta
CONSTANT_SCOPE: none (exact identities)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:fi-products, step:p2:fi-sym, step:p2:fi-dl, step:p2:fi-domegak, step:p2:fi-blocks, step:p2:fi-22, step:p2:fi-q, bp:p2:objects, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:fi-products | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-identities@L466-L466 | proof step (a)
EDGE: step:p2:fi-sym | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-identities@L471-L471 | proof step (b)
EDGE: step:p2:fi-dl | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-identities@L477-L477 | proof step (c)
EDGE: step:p2:fi-domegak | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-identities@L483-L483 | proof step (d)
EDGE: step:p2:fi-blocks | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-identities@L489-L489 | proof step (e) first part
EDGE: step:p2:fi-22 | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-identities@L499-L499 | proof step (e) second part
EDGE: step:p2:fi-q | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-identities@L509-L509 | proof step (f)
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-identities@L441-L441 | the objects
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:frame-identities@L442-L442 | A=DX_h o K, B(frak)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.frame_identities
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-6-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:fi-products
KIND: step
TITLE: Products with $\Omega_0$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-products@L466-L469
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-products@L466-L469
CONTRACT_ID: step:p2:fi-products
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Omega_0^2=-I, Omega_0^T=-Omega_0, B^T=B, L^T L=G=B^{-1}
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: (a): L^T Omega_0 N=-I_n, N^T Omega_0 L=I_n, N^T Omega_0 N=B Omega_K B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:matrix, bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:matrix | blueprint/parts/p2-aposteriori.tex#step:p2:fi-products@L467-L467 | Omega_0^2=-I, Omega_0^T=-Omega_0
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:fi-products@L467-L467 | definitions of N,B,G,Omega_K
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Identities.fi_LtON, fi_NtOL, fi_NtON
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-6-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:fi-sym
KIND: step
TITLE: Symplecticity defect
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-sym@L471-L475
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-sym@L471-L475
CONTRACT_ID: step:p2:fi-sym
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (a)
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: (b): P^T Omega_0 P=Omega_0+diag(Omega_K, B Omega_K B)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:fi-products, bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:fi-products | blueprint/parts/p2-aposteriori.tex#step:p2:fi-sym@L473-L473 | (a) gives the blocks
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:fi-sym@L472-L472 | definitions of P, E_sym
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Identities.fi_PtOP, fi_symDefect
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-6-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:fi-dl
KIND: step
TITLE: Derivative of the frame along $\omega$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-dl@L477-L481
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-dl@L477-L481
CONTRACT_ID: step:p2:fi-dl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K holomorphic on T_r; L omega = X_h o K - E
SOURCE_QUANTIFIERS: theta in T_r, j
SOURCE_CONCLUSION: (c): d_omega L=AL-DE
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-regularity, bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p2-aposteriori.tex#step:p2:fi-dl@L478-L478 | mixed partials commute
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:fi-dl@L479-L479 | definitions of L, E, A
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Identities.fi_dL
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-6-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:fi-domegak
KIND: step
TITLE: Derivative of $\Omega_K$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-domegak@L483-L487
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-domegak@L483-L487
CONTRACT_ID: step:p2:fi-domegak
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); (c); DX_h^T Omega_0+Omega_0 DX_h=0 at K(theta) in B(frak)
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: (d): d_omega Omega_K=-(DE)^T Omega_0 L-L^T Omega_0 DE
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:fi-dl, bp:p2:hamiltonian, bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:fi-dl | blueprint/parts/p2-aposteriori.tex#step:p2:fi-domegak@L484-L484 | (c)
EDGE: bp:p2:hamiltonian | blueprint/parts/p2-aposteriori.tex#step:p2:fi-domegak@L487-L487 | (d): A^T Omega_0+Omega_0 A=0
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:fi-domegak@L485-L485 | definition of Omega_K
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Identities.fi_dLagrange
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-6-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:fi-blocks
KIND: step
TITLE: Block form of the reduced field
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-blocks@L489-L497
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-blocks@L489-L497
CONTRACT_ID: step:p2:fi-blocks
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (c); Omega_0 block form; X_L=AL-d_omega L, X_N=AN-d_omega N
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: Q(AP-d_omega P) has the block form with X_L=DE and N^T Omega_0 X_N=T
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:matrix, step:p2:fi-dl, bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:matrix | blueprint/parts/p2-aposteriori.tex#step:p2:fi-blocks@L491-L491 | Omega_0(U_1;U_2)=(-U_2;U_1)
EDGE: step:p2:fi-dl | blueprint/parts/p2-aposteriori.tex#step:p2:fi-blocks@L497-L497 | X_L=DE by (c)
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:fi-blocks@L490-L490 | definitions of X_N, Q, T
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Identities.fi_reduced
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-6-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:fi-22
KIND: step
TITLE: The $(2,2)$ block
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-22@L499-L507
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-22@L499-L507
CONTRACT_ID: step:p2:fi-22
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); (a),(c); L^T Omega_0 N=-I_n constant
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: L^T Omega_0 X_N=-(DE)^T Omega_0 N; hence (e)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:fi-products, step:p2:fi-dl, bp:p2:hamiltonian, step:p2:fi-blocks, bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:fi-products | blueprint/parts/p2-aposteriori.tex#step:p2:fi-22@L500-L500 | (a): L^T Omega_0 N=-I_n
EDGE: step:p2:fi-dl | blueprint/parts/p2-aposteriori.tex#step:p2:fi-22@L501-L501 | (c)
EDGE: bp:p2:hamiltonian | blueprint/parts/p2-aposteriori.tex#step:p2:fi-22@L502-L502 | (d): Omega_0 A+A^T Omega_0=0
EDGE: step:p2:fi-blocks | blueprint/parts/p2-aposteriori.tex#step:p2:fi-22@L507-L507 | block form of the reduced field
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:fi-22@L500-L500 | definition of X_N
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Identities.fi_dLtON, fi_LtOXN
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-6-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:fi-q
KIND: step
TITLE: The products with $Q$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-q@L509-L512
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:fi-q@L509-L512
CONTRACT_ID: step:p2:fi-q
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (b); definition of eta; Q=-Omega_0 P^T Omega_0
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: (f): QP=I_{2n}-Omega_0 E_sym and QE=-eta, with the block form of eta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:fi-sym, bp:p2:objects, bp:p2:matrix
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:fi-sym | blueprint/parts/p2-aposteriori.tex#step:p2:fi-q@L510-L510 | (b)
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:fi-q@L510-L510 | definitions of Q and eta
EDGE: bp:p2:matrix | blueprint/parts/p2-aposteriori.tex#step:p2:fi-q@L512-L512 | Omega_0(U_1;U_2)=(-U_2;U_1)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Identities.fi_QP, fi_QE
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-6-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:exactness
KIND: lemma
TITLE: Exactness: two vanishing averages
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:exactness@L515-L523
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:exactness@L525-L547
CONTRACT_ID: bp:p2:exactness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); K holomorphic and primary on T_r with K(T_r) subset B(frak); for eta^N: det G != 0
SOURCE_QUANTIFIERS: for all r>0, K as stated
SOURCE_CONCLUSION: avg Omega_K=0 and avg(L^T Omega_0 E)=0, i.e. avg eta^N=0 when det G != 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:ex-curl, step:p2:ex-avg-omega, step:p2:ex-gradient, step:p2:ex-avg-eta, bp:p0:stripdata#IsPrimaryOnStrip, bp:p2:objects, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:ex-curl | blueprint/parts/p2-aposteriori.tex#bp:p2:exactness@L526-L526 | proof step
EDGE: step:p2:ex-avg-omega | blueprint/parts/p2-aposteriori.tex#bp:p2:exactness@L534-L534 | proof step
EDGE: step:p2:ex-gradient | blueprint/parts/p2-aposteriori.tex#bp:p2:exactness@L538-L538 | proof step
EDGE: step:p2:ex-avg-eta | blueprint/parts/p2-aposteriori.tex#bp:p2:exactness@L543-L543 | proof step
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p2-aposteriori.tex#bp:p2:exactness@L516-L516 | primary K
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#bp:p2:exactness@L518-L518 | Omega_K, eta^N
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:exactness@L516-L516 | local Part 2 package is assumed by this result; h, omega and the ambient domain retain the enclosing standing data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.exactness
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ex-curl
KIND: step
TITLE: $\Omega_K$ is a curl of periodic functions
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ex-curl@L526-L532
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ex-curl@L526-L532
CONTRACT_ID: step:p2:ex-curl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K=(K^theta,K^I) holomorphic and primary on T_r
SOURCE_QUANTIFIERS: i,j
SOURCE_CONCLUSION: (Omega_K)_{ij}=d_{theta_i} f_j - d_{theta_j} f_i with f_j=(K^I)^T d_{theta_j}K^theta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-regularity, bp:p2:objects, bp:p0:hamiltonian#omegaZero
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p2-aposteriori.tex#step:p2:ex-curl@L531-L531 | symmetry of second derivatives
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:ex-curl@L527-L527 | definition of Omega_K
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p2-aposteriori.tex#step:p2:ex-curl@L527-L527 | formula for u^T Omega_0 v
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Exactness.curl_actionForm
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ex-avg-omega
KIND: step
TITLE: Average of $\Omega_K$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ex-avg-omega@L534-L536
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ex-avg-omega@L534-L536
CONTRACT_ID: step:p2:ex-avg-omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f_j holomorphic and 1-periodic on T_r
SOURCE_QUANTIFIERS: i,j
SOURCE_CONCLUSION: avg Omega_K=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:periodicity, bp:p2:averages, step:p2:ex-curl
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:periodicity | blueprint/parts/p2-aposteriori.tex#step:p2:ex-avg-omega@L535-L535 | f_j holomorphic and periodic
EDGE: bp:p2:averages | blueprint/parts/p2-aposteriori.tex#step:p2:ex-avg-omega@L536-L536 | average of a derivative vanishes
EDGE: step:p2:ex-curl | blueprint/parts/p2-aposteriori.tex#step:p2:ex-avg-omega@L536-L536 | Omega_K as a curl of the f_j
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Exactness.avg_lagrangeMat
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ex-gradient
KIND: step
TITLE: The gradient identity
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ex-gradient@L538-L541
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ex-gradient@L538-L541
CONTRACT_ID: step:p2:ex-gradient
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); K holomorphic on T_r, K(T_r) subset B(frak)
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: L^T Omega_0 E=(D(h o K))^T-Omega_K omega
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:hamiltonian, bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:hamiltonian | blueprint/parts/p2-aposteriori.tex#step:p2:ex-gradient@L539-L539 | (d): Omega_0 X_h=(Dh)^T
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:ex-gradient@L541-L541 | definitions of E, Omega_K
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Exactness.etaN_apply
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ex-avg-eta
KIND: step
TITLE: Average of $L^\top\Omega_0E$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ex-avg-eta@L543-L546
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ex-avg-eta@L543-L546
CONTRACT_ID: step:p2:ex-avg-eta
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h o K holomorphic and periodic on T_r; avg Omega_K=0; gradient identity
SOURCE_QUANTIFIERS: theta in T_r
SOURCE_CONCLUSION: avg(L^T Omega_0 E)=0; when det G!=0 on T_r, eta^N is defined by bp:p2:objects and eta^N=L^T Omega_0 E, hence avg eta^N=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:periodicity, bp:p2:averages, step:p2:ex-gradient, step:p2:ex-avg-omega, bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:periodicity | blueprint/parts/p2-aposteriori.tex#step:p2:ex-avg-eta@L544-L544 | h o K holomorphic and periodic
EDGE: bp:p2:averages | blueprint/parts/p2-aposteriori.tex#step:p2:ex-avg-eta@L545-L545 | partial derivatives have zero average
EDGE: step:p2:ex-gradient | blueprint/parts/p2-aposteriori.tex#step:p2:ex-avg-eta@L546-L546 | gradient identity
EDGE: step:p2:ex-avg-omega | blueprint/parts/p2-aposteriori.tex#step:p2:ex-avg-eta@L545-L545 | avg Omega_K=0
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:ex-avg-eta@L546-L546 | eta^N=L^T Omega_0 E
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Exactness.avg_etaN
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:geometry
KIND: lemma
TITLE: Approximate Lagrangian property, symplecticity and reducibility
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:geometry@L549-L563
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:geometry@L565-L596
CONTRACT_ID: bp:p2:geometry
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the standing data of Part 2 (bp:p2:standing); K (r,beta,epsilon)-admissible with epsilon<=1; 0<delta<=1, 2delta<r
SOURCE_QUANTIFIERS: for all r,beta,epsilon,delta, K as stated
SOURCE_CONCLUSION: on T_{r-delta}: |DE|<=n epsilon/delta, |(DE)^T|<=2n epsilon/delta, |d_omega Omega_K|<=2n(n+1) m epsilon/delta, |E_red|<=C_red epsilon/delta; on T_{r-2delta}: |Omega_K|<=C_Omega epsilon/(gamma delta^{kappa+1}), |E_sym|<=C_sym epsilon/(gamma delta^{kappa+1})
CONSTANT_SCOPE: C_red, C_Omega, C_sym, kappa, m depend only on (n,tau,M,sigma_K,sigma_B,sigma_T); gamma from the standing data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:geo-de, step:p2:geo-domegak, step:p2:geo-ered, step:p2:geo-omegak, step:p2:geo-esym, bp:p2:admissible, bp:p2:constants, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:geo-de | blueprint/parts/p2-aposteriori.tex#bp:p2:geometry@L566-L566 | proof step
EDGE: step:p2:geo-domegak | blueprint/parts/p2-aposteriori.tex#bp:p2:geometry@L571-L571 | proof step
EDGE: step:p2:geo-ered | blueprint/parts/p2-aposteriori.tex#bp:p2:geometry@L576-L576 | proof step
EDGE: step:p2:geo-omegak | blueprint/parts/p2-aposteriori.tex#bp:p2:geometry@L582-L582 | proof step
EDGE: step:p2:geo-esym | blueprint/parts/p2-aposteriori.tex#bp:p2:geometry@L589-L589 | proof step
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#bp:p2:geometry@L550-L550 | hypothesis: admissible K
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:geometry@L554-L554 | m, kappa, C_red, C_Omega, C_sym
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:geometry@L550-L550 | standing data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.geometry
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/P2-7-audit-1.md and P2-7-audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:geo-de
KIND: step
TITLE: Derivatives of the error
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:geo-de@L566-L569
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:geo-de@L566-L569
CONTRACT_ID: step:p2:geo-de
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E holomorphic on T_r, |E|<=epsilon, 2n components; 0<delta<=1
SOURCE_QUANTIFIERS: theta in T_{r-delta}
SOURCE_CONCLUSION: |DE|<=n epsilon/delta and |(DE)^T|<=2n epsilon/delta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cauchy-strip, bp:p1:cauchy-corollaries, bp:p2:admissible, bp:p2:frame-basic
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cauchy-strip | blueprint/parts/p2-aposteriori.tex#step:p2:geo-de@L568-L568 | Cauchy bound for DE
EDGE: bp:p1:cauchy-corollaries | blueprint/parts/p2-aposteriori.tex#step:p2:geo-de@L568-L568 | bound for the transpose, p=2n
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#step:p2:geo-de@L567-L567 | (A6)
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:geo-de@L567-L567 | E holomorphic (a)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Geometry.geo_de
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:geo-domegak
KIND: step
TITLE: Bound on $\partial_\omega\Omega_K$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:geo-domegak@L571-L574
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:geo-domegak@L571-L574
CONTRACT_ID: step:p2:geo-domegak
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (d) and (b) of frame lemmas; bounds on DE, (DE)^T
SOURCE_QUANTIFIERS: theta in T_{r-delta}
SOURCE_CONCLUSION: |d_omega Omega_K|<=2n(n+1) m epsilon/delta
CONSTANT_SCOPE: m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frame-identities, bp:p2:frame-basic, step:p2:geo-de
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frame-identities | blueprint/parts/p2-aposteriori.tex#step:p2:geo-domegak@L572-L572 | (d)
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:geo-domegak@L572-L572 | (b): ~L~,~L^T~
EDGE: step:p2:geo-de | blueprint/parts/p2-aposteriori.tex#step:p2:geo-domegak@L573-L573 | ~DE~,~(DE)^T~
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Geometry.geo_domegak
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:geo-ered
KIND: step
TITLE: Bound on $E_{\mathrm{red}}$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:geo-ered@L576-L580
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:geo-ered@L576-L580
CONTRACT_ID: step:p2:geo-ered
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (e) of frame identities; bounds on DE, N, L
SOURCE_QUANTIFIERS: theta in T_{r-delta}
SOURCE_CONCLUSION: |E_red|<=C_red epsilon/delta
CONSTANT_SCOPE: C_red=2n(n+1)m^2
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frame-identities, bp:p2:matrix, bp:p2:frame-basic, step:p2:geo-de, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frame-identities | blueprint/parts/p2-aposteriori.tex#step:p2:geo-ered@L577-L577 | (e): block form of E_red
EDGE: bp:p2:matrix | blueprint/parts/p2-aposteriori.tex#step:p2:geo-ered@L577-L577 | block bound (c)
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:geo-ered@L578-L578 | (b): ~N^T~,~L^T~,~N~
EDGE: step:p2:geo-de | blueprint/parts/p2-aposteriori.tex#step:p2:geo-ered@L578-L578 | ~DE~,~(DE)^T~
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:geo-ered@L580-L580 | C_red
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Geometry.geo_ered
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:geo-omegak
KIND: step
TITLE: The Lagrangian defect by the cohomological equation
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:geo-omegak@L582-L587
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:geo-omegak@L582-L587
CONTRACT_ID: step:p2:geo-omegak
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Omega_K holomorphic and periodic on T_{r-delta}; avg Omega_K=0; |d_omega Omega_K|<=2n(n+1) m epsilon/delta on T_{r-delta}; delta<r-delta
SOURCE_QUANTIFIERS: theta in T_{r-2delta}
SOURCE_CONCLUSION: |Omega_K|<=C_Omega epsilon/(gamma delta^{kappa+1}) on T_{r-2delta}
CONSTANT_SCOPE: C_Omega=2n(n+1) c_R m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:exactness, bp:p2:cohomological, bp:p2:periodicity, bp:p2:frame-basic, bp:p2:admissible, step:p2:geo-domegak, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:exactness | blueprint/parts/p2-aposteriori.tex#step:p2:geo-omegak@L583-L583 | avg Omega_K=0
EDGE: bp:p2:cohomological | blueprint/parts/p2-aposteriori.tex#step:p2:geo-omegak@L585-L585 | (b): a-priori bound
EDGE: bp:p2:periodicity | blueprint/parts/p2-aposteriori.tex#step:p2:geo-omegak@L583-L583 | Omega_K periodic
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:geo-omegak@L583-L583 | Omega_K holomorphic
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#step:p2:geo-omegak@L583-L583 | K primary (A1)
EDGE: step:p2:geo-domegak | blueprint/parts/p2-aposteriori.tex#step:p2:geo-omegak@L584-L584 | bound on d_omega Omega_K
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:geo-omegak@L587-L587 | c_R, kappa, C_Omega
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.geometry (item (b) of KAM.Apost.cohomological on T_{r-δ}); Geometry.geo_omegak_inputs, geo_omegak_arith
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/P2-7-audit-1.md and P2-7-audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:geo-esym
KIND: step
TITLE: The symplecticity defect
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:geo-esym@L589-L595
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:geo-esym@L589-L595
CONTRACT_ID: step:p2:geo-esym
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (b) of frame identities; |B|<=m; bound on Omega_K
SOURCE_QUANTIFIERS: theta in T_{r-2delta}
SOURCE_CONCLUSION: |E_sym|<=C_sym epsilon/(gamma delta^{kappa+1})
CONSTANT_SCOPE: C_sym=m^2 C_Omega
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frame-identities, bp:p2:matrix, bp:p2:frame-basic, step:p2:geo-omegak, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frame-identities | blueprint/parts/p2-aposteriori.tex#step:p2:geo-esym@L590-L590 | (b): E_sym=diag(Omega_K,B Omega_K B)
EDGE: bp:p2:matrix | blueprint/parts/p2-aposteriori.tex#step:p2:geo-esym@L590-L590 | block norm of diag
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:geo-esym@L592-L592 | ~B~<=m
EDGE: step:p2:geo-omegak | blueprint/parts/p2-aposteriori.tex#step:p2:geo-esym@L595-L595 | bound on Omega_K
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:geo-esym@L595-L595 | C_sym
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2a
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Geometry.geo_esym_le, geo_esym_arith
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/P2-7-audit-1.md and P2-7-audit-2.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:avg-deriv#real-route
KIND: route
TITLE: Derivatives of the restriction to the real torus
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:avg-deriv#real-route@L176-L178
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:avg-deriv#real-route@L176-L178
CONTRACT_ID: step:p2:avg-deriv#real-route
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v holomorphic and 1-periodic on T_r; r>0
SOURCE_QUANTIFIERS: each component and every ell, omega
SOURCE_CONCLUSION: avg(d_ell v)=0 and avg(d_omega v)=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-regularity, bp:p1:averages-real
ROUTES: -
ROUTE_FOR: step:p2:avg-deriv
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p2-aposteriori.tex#step:p2:avg-deriv#real-route@L176-L177 | the real restriction has continuous first derivatives obtained by real difference quotients
EDGE: bp:p1:averages-real | blueprint/parts/p2-aposteriori.tex#step:p2:avg-deriv#real-route@L178-L178 | apply to the periodic C^1 restriction entrywise
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Tools.torusAverage_fderiv_apply_eq_zero (KAM/Apost/Tools.lean:158); scalar predecessors KAM.torusAverage_complex_direction_eq_zero, KAM.torusAverage_complex_coordinate_eq_zero, KAM.continuous_fderiv_real_of_holomorphic (KAM/Strip/Averages.lean)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-3-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p2:avg-deriv#bounded-route
KIND: route
TITLE: Alternative through a bounded smaller strip
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:avg-deriv#bounded-route@L178-L179
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:avg-deriv#bounded-route@L178-L179
CONTRACT_ID: step:p2:avg-deriv#bounded-route
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v holomorphic and 1-periodic on T_r; r>0
SOURCE_QUANTIFIERS: each component and every ell, omega
SOURCE_CONCLUSION: avg(d_ell v)=0 and avg(d_omega v)=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:periodic-bounded, bp:p1:averages
ROUTES: -
ROUTE_FOR: step:p2:avg-deriv
EDGE: bp:p1:periodic-bounded | blueprint/parts/p2-aposteriori.tex#step:p2:avg-deriv#bounded-route@L178-L179 | v is bounded on T_{r/2} since 0<r/2<r
EDGE: bp:p1:averages | blueprint/parts/p2-aposteriori.tex#step:p2:avg-deriv#bounded-route@L179-L179 | apply to the holomorphic bounded periodic restriction on T_{r/2}, which contains R^n
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-r2
REVIEWER: sol-review-r4
LEAN_STATUS: BYPASSED
LEAN_REF: none (alternative route not used)
LEAN_NOTE: route substitution (D27): Audit row marks it BYPASSED (alternative): the proof does not shrink the strip or use periodic_bounded; the parent step is proved via the real route. (docs/campaign/audits/P2-3-audit-1.md)
NOTE: -

NODE: bp:p2:triangular
KIND: lemma
TITLE: The triangular system
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:triangular@L616-L644
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:triangular@L646-L668
CONTRACT_ID: bp:p2:triangular
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: δ>0, 2δ<r; η^L,η^N:T_r→C^n holomorphic, 1-periodic, |η^L|≤H_L, |η^N|≤H_N on T_r, average of η^N is 0; T:T_r→C^{n×n} holomorphic, 1-periodic, |T|≤H_T on T_{r−δ}, avg T invertible with |avg T^{-1}|≤σ; Γ_δ=c_Rγ^{-1}δ^{-ϰ}; R from Cor. bp:p2:cohomological(a) (uses ω,γ,τ of the standing data of Part 2); u^N:=Rη^N, ξ^N_0:=avgT^{-1}(avg η^L+avg(Tu^N)), ξ^N:=ξ^N_0−u^N, g^L:=Tξ^N−η^L, ξ^L:=Rg^L, ξ:=(ξ^L,ξ^N)
SOURCE_QUANTIFIERS: standing data (n,τ,ω,γ) fixed; for all r,δ with 0<δ, 2δ<r, all H_L,H_N,H_T,σ (reals bounding as stated), all η^L,η^N,T
SOURCE_CONCLUSION: (a) avg g^L=0 so ξ^L defined; ξ^N,g^L holomorphic periodic on T_{r−δ}, ξ on T_{r−2δ}; (b) ∂_ωξ^N=−η^N on T_{r−δ}, ∂_ωξ^L=g^L on T_{r−2δ}, i.e. Λξ−∂_ωξ=η on T_{r−2δ} with Λ=[[0,T],[0,0]]; (c) |ξ^N_0|≤σ(H_L+H_TΓ_δH_N), |ξ^N|≤|ξ^N_0|+Γ_δH_N and |g^L|≤H_T sup|ξ^N|+H_L on T_{r−δ}, |ξ^L|≤Γ_δ sup|g^L| on T_{r−2δ}; (d) if η^L,η^N,T real on reals then ξ^N_0, ξ, g^L real
CONSTANT_SCOPE: Γ_δ uses c_R,ϰ of bp:p2:constants (dependence on n,τ only); H_L,H_N,H_T,σ are free parameters (bounds), no other constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:tri-first, step:p2:tri-xi0, step:p2:tri-second, step:p2:tri-form, step:p2:tri-real, bp:p2:cohomological, bp:p2:constants, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:tri-first | blueprint/parts/p2-aposteriori.tex#bp:p2:triangular@L647-L647 | proof step of this result
EDGE: step:p2:tri-xi0 | blueprint/parts/p2-aposteriori.tex#bp:p2:triangular@L652-L652 | proof step of this result
EDGE: step:p2:tri-second | blueprint/parts/p2-aposteriori.tex#bp:p2:triangular@L657-L657 | proof step of this result
EDGE: step:p2:tri-form | blueprint/parts/p2-aposteriori.tex#bp:p2:triangular@L662-L662 | proof step of this result
EDGE: step:p2:tri-real | blueprint/parts/p2-aposteriori.tex#bp:p2:triangular@L665-L665 | proof step of this result
EDGE: bp:p2:cohomological | blueprint/parts/p2-aposteriori.tex#bp:p2:triangular@L628-L628 | R is the solution operator of the cohomological corollary
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:triangular@L617-L617 | Γ_δ, c_R, ϰ defined in the constants
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:triangular@L617-L617 | Part 2 standing data remain in force; the result uses this local package, restricted to its frequency/parameter components where appropriate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-r3
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.triangular (defs triU, triXi0, triXiN, triGL, triXiL)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-8a-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:tri-first
KIND: step
TITLE: First cohomological equation
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:tri-first@L647-L650
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:tri-first@L647-L650
CONTRACT_ID: step:p2:tri-first
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data; η^N holomorphic periodic with |η^N|≤H_N on T_r, avg η^N=0; u^N=Rη^N
SOURCE_QUANTIFIERS: δ, T_r, T_{r−δ} as in the lemma
SOURCE_CONCLUSION: u^N holomorphic, periodic, real if η^N is, avg u^N=0, ∂_ωu^N=η^N, |u^N|≤Γ_δH_N on T_{r−δ}; hence ∂_ωξ^N=−η^N and |ξ^N|≤|ξ^N_0|+Γ_δH_N
CONSTANT_SCOPE: Γ_δ=c_Rγ^{-1}δ^{-ϰ} (constants of bp:p2:constants)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:cohomological
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:cohomological | blueprint/parts/p2-aposteriori.tex#step:p2:tri-first@L648-L648 | cohomological corollary (a) solves ∂_ωu^N=η^N with the loss-δ bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.cohomological (KAM/Apost/Tools.lean:322) applied inline in KAM.Apost.triangular (KAM/Apost/Triangular.lean:270, lines 307-315); KAM.Apost.Triangular.triXiN_differentiableOn, triXiN_periodic, fderiv_triXiN, norm_triXiN_le (:175-193)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-8a-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p2:tri-xi0
KIND: step
TITLE: The torsion average fixes $\xi^N_0$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:tri-xi0@L652-L655
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:tri-xi0@L652-L655
CONTRACT_ID: step:p2:tri-xi0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T continuous on R^n; |T|≤H_T on T_{r−δ}; |u^N|≤Γ_δH_N (previous step); avg T invertible, |avg T^{-1}|≤σ
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: |avg(Tu^N)|≤H_TΓ_δH_N, |avg η^L|≤H_L, so |ξ^N_0|≤σ(H_L+H_TΓ_δH_N); and avg g^L=avgT ξ^N_0−avg(Tu^N)−avg η^L=0
CONSTANT_SCOPE: none beyond the lemma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:averages, step:p2:tri-first
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:averages | blueprint/parts/p2-aposteriori.tex#step:p2:tri-xi0@L654-L654 | average of a bounded function is bounded by the same bound
EDGE: step:p2:tri-first | blueprint/parts/p2-aposteriori.tex#step:p2:tri-xi0@L653-L653 | the bound u^N≤Γ_δH_N and u^N periodic holomorphic
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Triangular.norm_triXi0_le, avg_mulVec_triXi0, avg_triGL_eq_zero (KAM/Apost/Triangular.lean:131,152,157); KAM.Apost.triangular
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-8a-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p2:tri-second
KIND: step
TITLE: Second cohomological equation
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:tri-second@L657-L660
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:tri-second@L657-L660
CONTRACT_ID: step:p2:tri-second
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g^L=Tξ^N−η^L holomorphic periodic on T_{r−δ}, |g^L|≤H_T sup|ξ^N|+H_L, avg g^L=0 (previous step); δ<r−δ
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: ξ^L=Rg^L on T_{r−2δ} with ∂_ωξ^L=g^L and |ξ^L|≤Γ_δ sup|g^L|
CONSTANT_SCOPE: Γ_δ as in the lemma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:cohomological, step:p2:tri-xi0, step:p2:tri-first
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:cohomological | blueprint/parts/p2-aposteriori.tex#step:p2:tri-second@L659-L659 | cohomological corollary applied on T_{r−δ} with loss δ
EDGE: step:p2:tri-xi0 | blueprint/parts/p2-aposteriori.tex#step:p2:tri-second@L658-L658 | g^L has zero average
EDGE: step:p2:tri-first | blueprint/parts/p2-aposteriori.tex#step:p2:tri-second@L658-L658 | ξ^N bound used for the bound of g^L
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.triangular (KAM/Apost/Triangular.lean:270, lines 328-340) with KAM.Apost.cohomological; helpers triGL_differentiableOn, triGL_periodic, norm_triGL_le (:201-212)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-8a-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p2:tri-form
KIND: step
TITLE: Triangular form
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:tri-form@L662-L663
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:tri-form@L662-L663
CONTRACT_ID: step:p2:tri-form
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ∂_ωξ^N=−η^N, ∂_ωξ^L=g^L=Tξ^N−η^L
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: Λξ−∂_ωξ=(Tξ^N−∂_ωξ^L, −∂_ωξ^N)=(η^L,η^N)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:tri-first, step:p2:tri-second
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:tri-first | blueprint/parts/p2-aposteriori.tex#step:p2:tri-form@L663-L663 | first equation ∂_ωξ^N=−η^N
EDGE: step:p2:tri-second | blueprint/parts/p2-aposteriori.tex#step:p2:tri-form@L663-L663 | second equation ∂_ωξ^L=g^L
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Triangular.fderiv_triXiN (KAM/Apost/Triangular.lean:185); KAM.Apost.triangular (component equations, line 333) with triGL (:56)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-8a-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p2:tri-real
KIND: step
TITLE: Realness
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:tri-real@L665-L667
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:tri-real@L665-L667
CONTRACT_ID: step:p2:tri-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: data η^L,η^N,T real on reals
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: avg T, avg η^L, avg(Tu^N) real, so ξ^N_0 real; with realness of R, ξ^N, g^L, ξ real
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:cohomological, step:p2:tri-xi0
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:cohomological | blueprint/parts/p2-aposteriori.tex#step:p2:tri-real@L667-L667 | R preserves realness
EDGE: step:p2:tri-xi0 | blueprint/parts/p2-aposteriori.tex#step:p2:tri-real@L666-L666 | definition of ξ^N_0 and the average bounds
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Triangular.triXi0_im_eq_zero, isRealVec_triXiN, isRealVec_triGL (KAM/Apost/Triangular.lean:228,253,259); KAM.Apost.triangular (last conjunct)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-8a-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: bp:p2:correction
KIND: lemma
TITLE: Size of the correction
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L670-L682
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L684-L721
CONTRACT_ID: bp:p2:correction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K is (r,β,ε)-admissible (bp:p2:admissible: A1–A6 with σ_K,σ_B,σ_T); 0<δ≤1, 2δ<r; η^L,η^N,T the objects of K (bp:p2:objects); ξ, ΔK:=Pξ on T_{r−2δ} from the triangular lemma; standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}
SOURCE_QUANTIFIERS: standing data fixed; for all r>0,β>0,ε≥0 (as in admissibility), 0<δ≤1 with 2δ<r, all admissible K
SOURCE_CONCLUSION: ξ and ΔK holomorphic, 1-periodic, real on reals; |ξ^N|≤C_{ξN}ε/(γδ^{ϰ+1}), |g^L|≤C_gε/(γδ^{ϰ+2}) on T_{r−δ}; |ξ|≤C_ξε/(γ²δ^a), |ΔK|≤C_{ΔK}ε/(γ²δ^a), |∂_ωξ|≤C_gε/(γδ^{ϰ+2}) on T_{r−2δ}
CONSTANT_SCOPE: C_{ξN},C_g,C_ξ,C_{ΔK},ϰ,a are the constants of bp:p2:constants: depend only on (n,τ,M,σ_K,σ_B,σ_T); not on r,β,ε,δ,γ,K
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:cor-data, step:p2:cor-absorb, step:p2:cor-xin, step:p2:cor-xi, step:p2:cor-dxi, step:p2:cor-reg, bp:p2:triangular, bp:p2:admissible, bp:p2:constants, bp:p2:objects, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:cor-data | blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L685-L685 | proof step of this result
EDGE: step:p2:cor-absorb | blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L691-L691 | proof step of this result
EDGE: step:p2:cor-xin | blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L696-L696 | proof step of this result
EDGE: step:p2:cor-xi | blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L704-L704 | proof step of this result
EDGE: step:p2:cor-dxi | blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L711-L711 | proof step of this result
EDGE: step:p2:cor-reg | blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L718-L718 | proof step of this result
EDGE: bp:p2:triangular | blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L672-L672 | the correction is built from the triangular system
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L671-L671 | hypothesis class of K
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L675-L675 | constants C_{ξN},C_g,C_ξ,C_{ΔK}
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L672-L672 | η, T, P of K
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:correction@L671-L671 | Part 2 standing data remain in force; the result uses this local package, restricted to its frequency/parameter components where appropriate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-r3
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.correction_spec (defs KAM.Apost.xi, KAM.Apost.correction)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-8b-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:cor-data
KIND: step
TITLE: The data of the triangular system
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:cor-data@L685-L689
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:cor-data@L685-L689
CONTRACT_ID: step:p2:cor-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K is (r,β,ε)-admissible (bp:p2:admissible: A1–A6 with σ_K,σ_B,σ_T); 0<δ≤1; standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: |ω|≤Θ, γ≤Θ; η^L,η^N,T holomorphic periodic real; H_L=2n𝔪²ε, H_N=2n𝔪ε, H_T=C_T/δ; avg η^N=0; σ=σ_T≤𝔪
CONSTANT_SCOPE: Θ,𝔪,C_T from bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frequency, bp:p2:periodicity, bp:p2:frame-basic, bp:p2:exactness, bp:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frequency | blueprint/parts/p2-aposteriori.tex#step:p2:cor-data@L686-L686 | ω≤Θ and γ≤Θ
EDGE: bp:p2:periodicity | blueprint/parts/p2-aposteriori.tex#step:p2:cor-data@L687-L687 | periodicity and realness of η,T
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:cor-data@L687-L687 | bounds on η and T (parts c,d) and holomorphy
EDGE: bp:p2:exactness | blueprint/parts/p2-aposteriori.tex#step:p2:cor-data@L687-L687 | avg η^N=0
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#step:p2:cor-data@L689-L689 | σ_T bound from A5
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.correction_spec (data preamble: frequency, frame_basic, periodicity, exactness)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-8b-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:cor-absorb
KIND: step
TITLE: Absorbing powers of $\gamma\delta$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:cor-absorb@L691-L694
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:cor-absorb@L691-L694
CONTRACT_ID: step:p2:cor-absorb
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: γ≤Θ (previous step), δ≤1
SOURCE_QUANTIFIERS: i,j≥0
SOURCE_CONCLUSION: γδ^j≤Θ; ε≤Θε/(γδ^j); ε/(γδ^j)≤Θε/(γ²δ^{j+i})
CONSTANT_SCOPE: Θ from bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:cor-data
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:cor-data | blueprint/parts/p2-aposteriori.tex#step:p2:cor-absorb@L692-L692 | γ≤Θ established there
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Correction.xiN_absorb
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-8b-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:cor-xin
KIND: step
TITLE: Bounds on $\xi^N$ and $g^L$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:cor-xin@L696-L702
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:cor-xin@L696-L702
CONTRACT_ID: step:p2:cor-xin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: triangular lemma (c) with the data H_L,H_N,H_T,σ of the data step; absorption inequalities
SOURCE_QUANTIFIERS: on T_{r−δ}
SOURCE_CONCLUSION: |ξ^N_0|≤C_{ξ0}ε/(γδ^{ϰ+1}); |ξ^N|≤C_{ξN}ε/(γδ^{ϰ+1}); |g^L|≤C_gε/(γδ^{ϰ+2})
CONSTANT_SCOPE: C_{ξ0},C_{ξN},C_g from bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:triangular, step:p2:cor-data, step:p2:cor-absorb, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:triangular | blueprint/parts/p2-aposteriori.tex#step:p2:cor-xin@L697-L697 | bounds (c) on ξ^N_0, ξ^N, g^L
EDGE: step:p2:cor-data | blueprint/parts/p2-aposteriori.tex#step:p2:cor-xin@L697-L697 | values of H_L,H_N,H_T,σ
EDGE: step:p2:cor-absorb | blueprint/parts/p2-aposteriori.tex#step:p2:cor-xin@L702-L702 | absorbing powers of γδ
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:cor-xin@L699-L699 | explicit constants C_{ξ0},C_{ξN},C_g
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Correction.xiN_arith
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-8b-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:cor-xi
KIND: step
TITLE: Bounds on $\xi$ and $\Delta K$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:cor-xi@L704-L709
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:cor-xi@L704-L709
CONTRACT_ID: step:p2:cor-xi
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: bounds on ξ^N and g^L on T_{r−δ}; triangular lemma (c); |P|≤2𝔪²
SOURCE_QUANTIFIERS: on T_{r−2δ}
SOURCE_CONCLUSION: |ξ|≤C_ξε/(γ²δ^a); |ΔK|≤2𝔪²C_ξε/(γ²δ^a)
CONSTANT_SCOPE: C_ξ=c_RC_g+ΘC_{ξN}, C_{ΔK}=2𝔪²C_ξ
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:triangular, step:p2:cor-xin, step:p2:cor-absorb, bp:p2:frame-basic, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:triangular | blueprint/parts/p2-aposteriori.tex#step:p2:cor-xi@L705-L705 | ξ^L≤Γ_δ supg^L from (c)
EDGE: step:p2:cor-xin | blueprint/parts/p2-aposteriori.tex#step:p2:cor-xi@L705-L705 | bounds on g^L and ξ^N
EDGE: step:p2:cor-absorb | blueprint/parts/p2-aposteriori.tex#step:p2:cor-xi@L707-L707 | absorbing powers of γδ
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:cor-xi@L708-L708 | P≤2𝔪²
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:cor-xi@L708-L708 | C_ξ, C_{ΔK}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Correction.xi0_arith, gL_arith, xiL_arith, xi_arith
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-8b-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:cor-dxi
KIND: step
TITLE: Bound on $\partial_\omega\xi$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:cor-dxi@L711-L716
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:cor-dxi@L711-L716
CONTRACT_ID: step:p2:cor-dxi
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ∂_ωξ=(g^L,−η^N); |η^N|≤2n𝔪ε
SOURCE_QUANTIFIERS: on T_{r−2δ}
SOURCE_CONCLUSION: |∂_ωξ|≤C_gε/(γδ^{ϰ+2})
CONSTANT_SCOPE: C_g from bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:triangular, step:p2:cor-absorb, step:p2:cor-xin, step:p2:cor-data
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:triangular | blueprint/parts/p2-aposteriori.tex#step:p2:cor-dxi@L712-L712 | ∂_ωξ=(g^L,−η^N)
EDGE: step:p2:cor-absorb | blueprint/parts/p2-aposteriori.tex#step:p2:cor-dxi@L712-L712 | absorbing powers of γδ
EDGE: step:p2:cor-xin | blueprint/parts/p2-aposteriori.tex#step:p2:cor-dxi@L712-L712 | bound on g^L
EDGE: step:p2:cor-data | blueprint/parts/p2-aposteriori.tex#step:p2:cor-dxi@L712-L712 | η^N≤2n𝔪ε
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Correction.dxi_arith, fderiv_sumElim_apply
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-8b-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:cor-reg
KIND: step
TITLE: Regularity of the correction
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:cor-reg@L718-L720
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:cor-reg@L718-L720
CONTRACT_ID: step:p2:cor-reg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: P and ξ holomorphic periodic real
SOURCE_QUANTIFIERS: on T_{r−2δ}
SOURCE_CONCLUSION: ΔK=Pξ holomorphic, periodic, real on reals
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:periodicity, bp:p2:frame-basic, bp:p2:triangular
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:periodicity | blueprint/parts/p2-aposteriori.tex#step:p2:cor-reg@L719-L719 | P periodic real
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:cor-reg@L720-L720 | P holomorphic
EDGE: bp:p2:triangular | blueprint/parts/p2-aposteriori.tex#step:p2:cor-reg@L720-L720 | ξ holomorphic periodic real
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.Correction.diffOn_correction, periodic_correction, isRealOnReals_correction, norm_correction_le, dK_arith
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-8b-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:newton-error
KIND: lemma
TITLE: The new invariance error
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L723-L740
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L742-L785
CONTRACT_ID: bp:p2:newton-error
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of bp:p2:correction (K admissible, 0<δ≤1, 2δ<r); C_{ΔK}ε/(γ²δ^a)<β; C_sym ε/(γδ^{ϰ+1})≤1/2; K̄:=K+ΔK on T_{r−2δ}, K̄:=K elsewhere; S:=I_{2n}−Ω_0E_sym; standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}
SOURCE_QUANTIFIERS: as in bp:p2:correction; for all admissible K, r,β,ε,δ satisfying the two inequalities
SOURCE_CONCLUSION: K̄(T_{r−2δ})⊂𝔅; S invertible with |S^{-1}|≤2 on T_{r−2δ}; Ē=PS^{-1}E_lin+Δ²X with E_lin:=E_redξ+Ω_0E_sym∂_ωξ, Δ²X:=X_h(K̄)−X_h(K)−AΔK on T_{r−2δ}; consequently |Ē|≤C_Eε²/(γ⁴δ^{2a}) on T_{r−2δ}
CONSTANT_SCOPE: C_E,C_ΔK,C_sym,ϰ,a from bp:p2:constants: depend only on (n,τ,M,σ_K,σ_B,σ_T)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:ne-invert, step:p2:ne-domain, step:p2:ne-expand, step:p2:ne-reduce, step:p2:ne-lin, step:p2:ne-quad, step:p2:ne-total, bp:p2:correction, bp:p2:constants, bp:p2:objects, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:ne-invert | blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L743-L743 | proof step of this result
EDGE: step:p2:ne-domain | blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L749-L749 | proof step of this result
EDGE: step:p2:ne-expand | blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L754-L754 | proof step of this result
EDGE: step:p2:ne-reduce | blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L759-L759 | proof step of this result
EDGE: step:p2:ne-lin | blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L765-L765 | proof step of this result
EDGE: step:p2:ne-quad | blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L772-L772 | proof step of this result
EDGE: step:p2:ne-total | blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L776-L776 | proof step of this result
EDGE: bp:p2:correction | blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L724-L724 | setting and ΔK of the correction lemma
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L727-L727 | constants C_ΔK,C_sym,C_E
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L730-L730 | E_sym, E, A, P of K
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:newton-error@L724-L724 | Part 2 standing data remain in force; the result uses this local package, restricted to its frequency/parameter components where appropriate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-r3
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.newton_error (defs newtonMap, sMat, linError, quadRemainder)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-9-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ne-invert
KIND: step
TITLE: Invertibility of $S$ and of $Q$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-invert@L743-L747
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-invert@L743-L747
CONTRACT_ID: step:p2:ne-invert
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |Ω_0E_sym|≤1/2 on T_{r−2δ}; QP=S
SOURCE_QUANTIFIERS: on T_{r−2δ}
SOURCE_CONCLUSION: S invertible with |S^{-1}|≤2; Q invertible with Q^{-1}=PS^{-1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:geometry, bp:p1:neumann, bp:p2:frame-identities
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:geometry | blueprint/parts/p2-aposteriori.tex#step:p2:ne-invert@L744-L744 | Ω_0E_sym≤1/2
EDGE: bp:p1:neumann | blueprint/parts/p2-aposteriori.tex#step:p2:ne-invert@L745-L745 | Neumann inversion of I−(small)
EDGE: bp:p2:frame-identities | blueprint/parts/p2-aposteriori.tex#step:p2:ne-invert@L746-L746 | QP=S
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.NewtonError.sMat_spec
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-9-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ne-domain
KIND: step
TITLE: The corrected torus stays in the domain
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-domain@L749-L752
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-domain@L749-L752
CONTRACT_ID: step:p2:ne-domain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |ΔK(θ)|<β on T_{r−2δ} (smallness assumption and the correction bound); A2
SOURCE_QUANTIFIERS: θ∈T_{r−2δ}
SOURCE_CONCLUSION: K̄(θ)∈B_β(K(θ))⊂𝔅 and the segment [K(θ),K̄(θ)] lies in the ball
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:admissible, bp:p2:correction
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#step:p2:ne-domain@L751-L751 | A2: the β-ball around K lies in 𝔅
EDGE: bp:p2:correction | blueprint/parts/p2-aposteriori.tex#step:p2:ne-domain@L750-L750 | ΔK≤C_ΔKε/(γ²δ^a)<β
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.NewtonError.newtonMap_mem
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-9-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ne-expand
KIND: step
TITLE: Expansion of the new error
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-expand@L754-L757
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-expand@L754-L757
CONTRACT_ID: step:p2:ne-expand
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of bp:p2:correction (K admissible, 0<δ≤1, 2δ<r); C_{ΔK}ε/(γ²δ^a)<β; C_sym ε/(γδ^{ϰ+1})≤1/2; K̄:=K+ΔK on T_{r−2δ}, K̄:=K elsewhere; S:=I_{2n}−Ω_0E_sym; standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}
SOURCE_QUANTIFIERS: on T_{r−2δ}
SOURCE_CONCLUSION: Ē=E+AΔK−∂_ωΔK+Δ²X and AΔK−∂_ωΔK=(AP−∂_ωP)ξ−P∂_ωξ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:objects, bp:p2:correction, bp:p2:frame-basic, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#step:p2:ne-expand@L756-L756 | definitions of E and A
EDGE: bp:p2:correction | blueprint/parts/p2-aposteriori.tex#step:p2:ne-expand@L755-L757 | K and Delta K are holomorphic on the working strip, allowing differentiation of Kbar=K+Delta K and Delta K=P xi
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:ne-expand@L755-L757 | the inherited local package supplies the holomorphic Hamiltonian and ambient domain for the frame/correction application
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.NewtonError.sumVec_invarianceError_newtonMap
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-9-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:ne-expand@L755-L757 | admissibility supplies holomorphic K and A2-A4, so part (a) gives holomorphic P for differentiating Delta K=P xi

NODE: step:p2:ne-reduce
KIND: step
TITLE: Reduction by $Q$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-reduce@L759-L763
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-reduce@L759-L763
CONTRACT_ID: step:p2:ne-reduce
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: frame identities (e),(f); triangular system Λξ−∂_ωξ=η; step ne-expand
SOURCE_QUANTIFIERS: on T_{r−2δ}
SOURCE_CONCLUSION: Q(E+AΔK−∂_ωΔK)=E_lin; hence Ē=PS^{-1}E_lin+Δ²X
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frame-identities, bp:p2:triangular, step:p2:ne-expand, step:p2:ne-invert
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frame-identities | blueprint/parts/p2-aposteriori.tex#step:p2:ne-reduce@L760-L760 | identities for Q(AP−∂_ωP) and QP=S
EDGE: bp:p2:triangular | blueprint/parts/p2-aposteriori.tex#step:p2:ne-reduce@L763-L763 | Λξ−∂_ωξ=η
EDGE: step:p2:ne-expand | blueprint/parts/p2-aposteriori.tex#step:p2:ne-reduce@L761-L761 | expansion of Ē
EDGE: step:p2:ne-invert | blueprint/parts/p2-aposteriori.tex#step:p2:ne-reduce@L763-L763 | Q^{-1}=PS^{-1}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.NewtonError.alg_core, xi_equation
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-9-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ne-lin
KIND: step
TITLE: Estimate of the linear part
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-lin@L765-L770
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-lin@L765-L770
CONTRACT_ID: step:p2:ne-lin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: correction bounds for ξ,∂_ωξ; reducibility and symplecticity bounds of bp:p2:geometry; 2ϰ+3=a+1
SOURCE_QUANTIFIERS: on T_{r−2δ}
SOURCE_CONCLUSION: |E_red ξ|≤C_redC_ξε²/(γ²δ^{a+1}), |Ω_0E_sym∂_ωξ|≤C_symC_gε²/(γ²δ^{2ϰ+3}); |E_lin|≤C_linε²/(γ²δ^{a+1})
CONSTANT_SCOPE: C_red,C_sym,C_lin from bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:geometry, bp:p2:correction
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:geometry | blueprint/parts/p2-aposteriori.tex#step:p2:ne-lin@L766-L766 | bounds on E_red, E_sym
EDGE: bp:p2:correction | blueprint/parts/p2-aposteriori.tex#step:p2:ne-lin@L766-L766 | bounds on ξ and ∂_ωξ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.NewtonError.norm_linError_le, lin_arith
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-9-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ne-quad
KIND: step
TITLE: Estimate of the quadratic part
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-quad@L772-L774
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-quad@L772-L774
CONTRACT_ID: step:p2:ne-quad
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lemma ham (e) with z=K(θ), w=ΔK(θ); segment in 𝔅 (ne-domain)
SOURCE_QUANTIFIERS: on T_{r−2δ}
SOURCE_CONCLUSION: |Δ²X|≤M|ΔK|²≤𝔪C_ΔK²ε²/(γ⁴δ^{2a})
CONSTANT_SCOPE: M≤𝔪; C_ΔK from bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:hamiltonian, bp:p2:correction, step:p2:ne-domain
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:hamiltonian | blueprint/parts/p2-aposteriori.tex#step:p2:ne-quad@L773-L773 | second-order Taylor remainder of X_h
EDGE: bp:p2:correction | blueprint/parts/p2-aposteriori.tex#step:p2:ne-quad@L774-L774 | ΔK bound
EDGE: step:p2:ne-domain | blueprint/parts/p2-aposteriori.tex#step:p2:ne-quad@L773-L773 | segment [K,K̄] in 𝔅
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.NewtonError.norm_quadRemainder_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-9-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ne-total
KIND: step
TITLE: The quadratic estimate
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-total@L776-L784
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ne-total@L776-L784
CONTRACT_ID: step:p2:ne-total
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |P|≤2𝔪², |S^{-1}|≤2, E_lin and Δ²X bounds, γ²δ^{a−1}≤Θ²
SOURCE_QUANTIFIERS: on T_{r−2δ}
SOURCE_CONCLUSION: |Ē|≤|P||S^{-1}||E_lin|+|Δ²X|≤C_Eε²/(γ⁴δ^{2a})
CONSTANT_SCOPE: C_E=4𝔪²Θ²C_lin+𝔪C_ΔK²
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frequency, step:p2:ne-reduce, step:p2:ne-invert, bp:p2:frame-basic, step:p2:ne-lin, step:p2:ne-quad
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frequency | blueprint/parts/p2-aposteriori.tex#step:p2:ne-total@L783-L783 | γ≤Θ
EDGE: step:p2:ne-reduce | blueprint/parts/p2-aposteriori.tex#step:p2:ne-total@L779-L779 | formula Ē=PS^{-1}E_lin+Δ²X
EDGE: step:p2:ne-invert | blueprint/parts/p2-aposteriori.tex#step:p2:ne-total@L777-L777 | S^{-1}≤2
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:ne-total@L777-L777 | P≤2𝔪²
EDGE: step:p2:ne-lin | blueprint/parts/p2-aposteriori.tex#step:p2:ne-total@L779-L779 | bound on E_lin
EDGE: step:p2:ne-quad | blueprint/parts/p2-aposteriori.tex#step:p2:ne-total@L779-L779 | bound on Δ²X
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.NewtonError.total_arith
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-9-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:perturbation
KIND: lemma
TITLE: Perturbation of the frame and the torsion
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L798-L820
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L822-L879
CONTRACT_ID: bp:p2:perturbation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r>0, 0<δ≤1, 2δ<r; |ω|≤Θ; K holomorphic on T_r with B_β(K(θ))⊂𝔅, |DK|≤σ_K, det G≠0, |B|≤σ_B on T_r, avg T invertible with |avg T^{-1}|≤σ_T; K̃ holomorphic on T_r with |K̃−K|≤d on T_r; d<β and 2𝔪C_{ΔT}d/δ²≤1; standing data of Part 2 (via 𝔅,h,M)
SOURCE_QUANTIFIERS: standing data fixed; for all r,δ,β>0,d≥0, all ω with |ω|≤Θ, all such K,K̃
SOURCE_CONCLUSION: (a) B_{β−d}(K̃(θ))⊂𝔅 on T_r; (b) |DK̃−DK|≤nd/δ on T_{r−δ}; (c) det G̃≠0, |B̃|≤2𝔪, |B̃−B|≤C_Bd/δ on T_{r−δ}; (d) |Ñ−N|≤C_{ΔN}d/δ, |Ñ|≤2𝔪² on T_{r−δ}; (e) |T̃−T|≤C_{ΔT}d/δ² on T_{r−2δ}; (f) T̃ continuous on R^n, avg T̃ invertible, |avgT̃^{-1}−avgT^{-1}|≤2𝔪²C_{ΔT}d/δ²
CONSTANT_SCOPE: C_B,C_ΔN,C_ΔT,Θ,𝔪 from bp:p2:constants: depend only on (n,τ,M,σ_K,σ_B,σ_T); not on r,δ,β,d,K,K̃
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:pt-small, step:p2:pt-domain, step:p2:pt-dl, step:p2:pt-gram, step:p2:pt-binv, step:p2:pt-n, step:p2:pt-xn, step:p2:pt-torsion, step:p2:pt-twist, bp:p2:constants, bp:p2:objects, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:pt-small | blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L823-L823 | proof step of this result
EDGE: step:p2:pt-domain | blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L834-L834 | proof step of this result
EDGE: step:p2:pt-dl | blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L839-L839 | proof step of this result
EDGE: step:p2:pt-gram | blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L844-L844 | proof step of this result
EDGE: step:p2:pt-binv | blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L848-L848 | proof step of this result
EDGE: step:p2:pt-n | blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L853-L853 | proof step of this result
EDGE: step:p2:pt-xn | blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L859-L859 | proof step of this result
EDGE: step:p2:pt-torsion | blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L866-L866 | proof step of this result
EDGE: step:p2:pt-twist | blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L873-L873 | proof step of this result
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L804-L804 | constants C_B,C_ΔN,C_ΔT
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L801-L801 | G,B,N,T of a parameterization
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:perturbation@L799-L799 | Part 2 standing data remain in force; the result uses this local package, restricted to its frequency/parameter components where appropriate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-r3
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.perturbation
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-10-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:pt-small
KIND: step
TITLE: Consequences of the smallness
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-small@L823-L832
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-small@L823-L832
CONTRACT_ID: step:p2:pt-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d<β, 2𝔪C_ΔTd/δ²≤1, δ≤1; definitions of the constants
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: C_ΔT≥max{n,C_G,C_ΔN}; nd/δ≤1/(2𝔪)≤𝔪, 𝔪C_Gd/δ≤1/2, C_ΔNd/δ≤1/(2𝔪)≤𝔪², 𝔪C_ΔTd/δ²≤1/2
CONSTANT_SCOPE: constants of bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:pt-small@L824-L824 | explicit definitions of C_ΔT,C_ΔN,C_B,C_G,C_X
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.perturbation_small, pt_xn_sum_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-10-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:pt-domain
KIND: step
TITLE: Domain
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-domain@L834-L837
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-domain@L834-L837
CONTRACT_ID: step:p2:pt-domain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |z−K̃(θ)|<β−d; A2-type ball inclusion for K; |ω|≤Θ
SOURCE_QUANTIFIERS: θ∈T_r
SOURCE_CONCLUSION: B_{β−d}(K̃(θ))⊂𝔅; segment [K,K̃]⊂B_β(K); |Ã−A|≤Md≤𝔪d on T_r
CONSTANT_SCOPE: M≤𝔪
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:hamiltonian
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:hamiltonian | blueprint/parts/p2-aposteriori.tex#step:p2:pt-domain@L837-L837 | Lipschitz bound on DX_h along the segment
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.PerturbationAux.ball_subset_of_close
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-10-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:pt-dl
KIND: step
TITLE: Tangent frame
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-dl@L839-L842
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-dl@L839-L842
CONTRACT_ID: step:p2:pt-dl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K̃−K holomorphic on T_r with |K̃−K|≤d; |L|≤𝔪
SOURCE_QUANTIFIERS: on T_{r−δ}
SOURCE_CONCLUSION: |L̃−L|≤nd/δ, |(L̃−L)^T|≤2nd/δ; |L̃|≤2𝔪, |L̃^T|≤4n𝔪
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cauchy-strip, bp:p1:cauchy-corollaries, step:p2:pt-small
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cauchy-strip | blueprint/parts/p2-aposteriori.tex#step:p2:pt-dl@L840-L840 | Cauchy estimate for the derivative on a strip
EDGE: bp:p1:cauchy-corollaries | blueprint/parts/p2-aposteriori.tex#step:p2:pt-dl@L840-L840 | Cauchy corollaries: transposes (p=2n)
EDGE: step:p2:pt-small | blueprint/parts/p2-aposteriori.tex#step:p2:pt-dl@L841-L841 | nd/δ≤𝔪 used to get L̃≤2𝔪
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: PerturbationAux.norm_fderiv_sub_le, norm_transpose_tangentMat_sub_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-10-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:pt-gram
KIND: step
TITLE: Gram matrix
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-gram@L844-L846
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-gram@L844-L846
CONTRACT_ID: step:p2:pt-gram
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: L̃−L bounds, |L̃^T|≤4n𝔪, |L|≤𝔪
SOURCE_QUANTIFIERS: on T_{r−δ}
SOURCE_CONCLUSION: G̃−G=L̃^T(L̃−L)+(L̃−L)^TL and |G̃−G|≤C_Gd/δ
CONSTANT_SCOPE: C_G=6n²𝔪
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:pt-dl, bp:p2:frame-basic
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:pt-dl | blueprint/parts/p2-aposteriori.tex#step:p2:pt-gram@L845-L845 | bounds on L̃−L, L̃^T
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:pt-gram@L845-L845 | L≤𝔪
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: PerturbationAux.norm_gram_sub_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-10-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:pt-binv
KIND: step
TITLE: Gram inverse (invertibility before use)
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-binv@L848-L851
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-binv@L848-L851
CONTRACT_ID: step:p2:pt-binv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |B||G̃−G|≤𝔪C_Gd/δ≤1/2 on T_{r−δ}
SOURCE_QUANTIFIERS: on T_{r−δ}
SOURCE_CONCLUSION: G̃ invertible; |B̃|≤2|B|≤2𝔪; |B̃−B|≤2𝔪²C_Gd/δ=C_Bd/δ (part (c))
CONSTANT_SCOPE: C_B=2𝔪²C_G
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:neumann, step:p2:pt-gram, step:p2:pt-small
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:neumann | blueprint/parts/p2-aposteriori.tex#step:p2:pt-binv@L850-L850 | Neumann perturbation of the inverse
EDGE: step:p2:pt-gram | blueprint/parts/p2-aposteriori.tex#step:p2:pt-binv@L849-L849 | bound on G̃−G
EDGE: step:p2:pt-small | blueprint/parts/p2-aposteriori.tex#step:p2:pt-binv@L849-L849 | smallness 𝔪C_Gd/δ≤1/2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: PerturbationAux.gram_inverse_perturb
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-10-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:pt-n
KIND: step
TITLE: Normal frame
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-n@L853-L857
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-n@L853-L857
CONTRACT_ID: step:p2:pt-n
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Ñ=Ω_0L̃B̃; bounds on L̃−L, B̃−B, |L|≤𝔪
SOURCE_QUANTIFIERS: on T_{r−δ}
SOURCE_CONCLUSION: Ñ−N=Ω_0((L̃−L)B̃+L(B̃−B)); |Ñ−N|≤C_ΔNd/δ, |Ñ|≤2𝔪², |Ñ^T|≤4n𝔪², |(Ñ−N)^T|≤2nC_ΔNd/δ
CONSTANT_SCOPE: C_ΔN=2n𝔪+𝔪C_B
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:pt-dl, step:p2:pt-binv, step:p2:pt-small, bp:p2:frame-basic
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:pt-dl | blueprint/parts/p2-aposteriori.tex#step:p2:pt-n@L854-L854 | bound on L̃−L
EDGE: step:p2:pt-binv | blueprint/parts/p2-aposteriori.tex#step:p2:pt-n@L854-L854 | bounds on B̃, B̃−B
EDGE: step:p2:pt-small | blueprint/parts/p2-aposteriori.tex#step:p2:pt-n@L855-L855 | C_ΔNd/δ≤𝔪²
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:pt-n@L855-L855 | N≤𝔪²
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: PerturbationAux.norm_normalMat_sub_le, norm_normalMat_le_two
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-10-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:pt-xn
KIND: step
TITLE: Displacement of the normal frame
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-xn@L859-L864
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-xn@L859-L864
CONTRACT_ID: step:p2:pt-xn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X̃_Ñ−X_N=(Ã−A)Ñ+A(Ñ−N)−∂_ω(Ñ−N); |ω|≤Θ; Ñ−N bound on T_{r−δ}
SOURCE_QUANTIFIERS: on T_{r−2δ}
SOURCE_CONCLUSION: |X̃_Ñ−X_N|≤C_ΔXd/δ²
CONSTANT_SCOPE: C_ΔX=2𝔪³+(𝔪+nΘ)C_ΔN
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:pt-domain, step:p2:pt-n, bp:p1:cauchy-corollaries, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:pt-domain | blueprint/parts/p2-aposteriori.tex#step:p2:pt-xn@L860-L860 | Ã−A≤𝔪d
EDGE: step:p2:pt-n | blueprint/parts/p2-aposteriori.tex#step:p2:pt-xn@L860-L860 | bounds on Ñ, Ñ−N
EDGE: bp:p1:cauchy-corollaries | blueprint/parts/p2-aposteriori.tex#step:p2:pt-xn@L862-L862 | Cauchy bound on ∂_ω(Ñ−N) with ω_1≤nΘ
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:pt-xn@L864-L864 | definition of C_ΔX
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: PerturbationAux.normalFieldMat_sub, norm_normalField_sub_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-10-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:pt-torsion
KIND: step
TITLE: Torsion
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-torsion@L866-L871
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-torsion@L866-L871
CONTRACT_ID: step:p2:pt-torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T̃−T=Ñ^TΩ_0(X̃_Ñ−X_N)+(Ñ−N)^TΩ_0X_N; |X_N|≤C_X/δ on T_{r−δ} (bp:p2:frame-basic(d))
SOURCE_QUANTIFIERS: on T_{r−2δ}
SOURCE_CONCLUSION: |T̃−T|≤C_ΔTd/δ²
CONSTANT_SCOPE: C_ΔT=4n𝔪²C_ΔX+2nC_ΔNC_X
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frame-basic, step:p2:pt-xn, step:p2:pt-n, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frame-basic | blueprint/parts/p2-aposteriori.tex#step:p2:pt-torsion@L868-L868 | X_N≤C_X/δ
EDGE: step:p2:pt-xn | blueprint/parts/p2-aposteriori.tex#step:p2:pt-torsion@L870-L870 | bound on X̃_Ñ−X_N
EDGE: step:p2:pt-n | blueprint/parts/p2-aposteriori.tex#step:p2:pt-torsion@L870-L870 | bounds on Ñ^T,(Ñ−N)^T
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:pt-torsion@L870-L870 | definition of C_ΔT
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: PerturbationAux.norm_torsion_combo_le, norm_torsion_sub_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-10-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:pt-twist
KIND: step
TITLE: Twist (integrability and invertibility before use)
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-twist@L873-L878
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:pt-twist@L873-L878
CONTRACT_ID: step:p2:pt-twist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r>0, 0<δ≤1, 2δ<r; |ω|≤Θ; K holomorphic on T_r with B_β(K(θ))⊂𝔅, |DK|≤σ_K, det G≠0, |B|≤σ_B on T_r, avg T invertible with |avg T^{-1}|≤σ_T; K̃ holomorphic on T_r with |K̃−K|≤d on T_r; d<β and 2𝔪C_{ΔT}d/δ²≤1; standing data of Part 2 (via 𝔅,h,M)
SOURCE_QUANTIFIERS: as in the lemma
SOURCE_CONCLUSION: T̃ continuous on R^n, avg T̃ defined; avg T̃ invertible with |avgT̃^{-1}−avgT^{-1}|≤2𝔪²C_ΔTd/δ²
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:neumann, step:p2:pt-torsion, step:p2:pt-binv, step:p2:pt-small, bp:p1:holomorphic-inverse, bp:p1:holomorphic-regularity, bp:p2:standing, bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:neumann | blueprint/parts/p2-aposteriori.tex#step:p2:pt-twist@L878-L878 | Neumann inversion of avg T̃
EDGE: step:p2:pt-torsion | blueprint/parts/p2-aposteriori.tex#step:p2:pt-twist@L875-L876 | bound T̃−T≤C_ΔTd/δ²
EDGE: step:p2:pt-binv | blueprint/parts/p2-aposteriori.tex#step:p2:pt-twist@L874-L874 | Ñ holomorphic via det G̃≠0 (part c)
EDGE: step:p2:pt-small | blueprint/parts/p2-aposteriori.tex#step:p2:pt-twist@L878-L878 | 𝔪C_ΔTd/δ²≤1/2
EDGE: bp:p1:holomorphic-inverse | blueprint/parts/p2-aposteriori.tex#step:p2:pt-twist@L874-L876 | the holomorphic new Gram matrix has nonzero determinant by (c), so its inverse and the new normal frame are holomorphic
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p2-aposteriori.tex#step:p2:pt-twist@L874-L876 | the directional derivative of the new holomorphic normal frame is holomorphic, giving holomorphy and continuity of the new torsion
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:pt-twist@L874-L878 | the inherited local package supplies holomorphic h on the open ambient domain when forming the new torsion
EDGE: bp:p1:ext-integral | blueprint/parts/p2-aposteriori.tex#step:p2:pt-twist@L876-L876 | ¦avg(tilde T)-avg(T)¦ <= sup over [0,1]^n of ¦tilde T - T¦ by the norm-of-integral bound; no periodicity needed
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-d2+claude-main-orchestrator
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: PerturbationAux.norm_torsionAverage_sub_le, twist_neumann
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-10-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:step
KIND: proposition
TITLE: The KAM step
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:step@L884-L904
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:step@L906-L930
CONTRACT_ID: bp:p2:step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r>0, 0<δ≤1, 4δ<r, β>0, 0≤ε≤1; K is (r,β,ε)-admissible; 𝔠_step ε/(γ⁴δ^{2a})≤min{1,β}; K̄ the map of bp:p2:newton-error; d:=C_ΔKε/(γ²δ^a); standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}
SOURCE_QUANTIFIERS: standing data fixed; for all r,δ,β,ε as stated and all admissible K
SOURCE_CONCLUSION: (a) K̄ holomorphic, primary on T_{r−2δ}, real on reals; (b) |K̄−K|≤d≤β/2 on T_{r−2δ} and B_{β−d}(K̄(θ))⊂𝔅 for θ∈T_{r−2δ}; (c) |Ē|≤C_Eε²/(γ⁴δ^{2a}) on T_{r−2δ}; (d) |DK̄−DK|≤nd/δ on T_{r−3δ}; (e) det Ḡ≠0 and |B̄−B|≤C_Bd/δ on T_{r−3δ}; (f) avg T̄ invertible and |avgT̄^{-1}−avgT^{-1}|≤2𝔪²C_ΔTd/δ²
CONSTANT_SCOPE: 𝔠_step,C_ΔK,C_E,C_B,C_ΔT,a from bp:p2:constants: depend only on (n,τ,M,σ_K,σ_B,σ_T); not on r,δ,β,ε,γ,K
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:st-small, step:p2:st-error, step:p2:st-ball, step:p2:st-perturb, bp:p2:newton-error, bp:p2:admissible, bp:p2:constants, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:st-small | blueprint/parts/p2-aposteriori.tex#bp:p2:step@L907-L907 | proof step of this result
EDGE: step:p2:st-error | blueprint/parts/p2-aposteriori.tex#bp:p2:step@L916-L916 | proof step of this result
EDGE: step:p2:st-ball | blueprint/parts/p2-aposteriori.tex#bp:p2:step@L922-L922 | proof step of this result
EDGE: step:p2:st-perturb | blueprint/parts/p2-aposteriori.tex#bp:p2:step@L925-L925 | proof step of this result
EDGE: bp:p2:newton-error | blueprint/parts/p2-aposteriori.tex#bp:p2:step@L890-L890 | K̄ is the map defined there
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#bp:p2:step@L886-L886 | hypothesis class of K
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:step@L888-L888 | 𝔠_step, C_ΔK
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:step@L885-L885 | Part 2 standing data remain in force; the result uses this local package, restricted to its frequency/parameter components where appropriate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-r3
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.step
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-12-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:st-small
KIND: step
TITLE: The smallness conditions used
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:st-small@L907-L914
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:st-small@L907-L914
CONTRACT_ID: step:p2:st-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing and admissibility; 𝔠_step ε/(γ⁴δ^{2a})≤min{1,β}; Θ≥1; ϰ+1≤2a, a+2≤2a
SOURCE_QUANTIFIERS: as in the proposition
SOURCE_CONCLUSION: C_sym ε/(γδ^{ϰ+1})≤1/2; d≤β/2; 2𝔪C_ΔTd/δ²≤1/2
CONSTANT_SCOPE: Θ,𝔠_step from bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frequency, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frequency | blueprint/parts/p2-aposteriori.tex#step:p2:st-small@L908-L908 | γ≤Θ
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:st-small@L909-L909 | definition of 𝔠_step as a max of the three constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.step (step_small)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-12-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:st-error
KIND: step
TITLE: Correction and new error
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:st-error@L916-L920
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:st-error@L916-L920
CONTRACT_ID: step:p2:st-error
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 2δ<r; the smallness step; d<β
SOURCE_QUANTIFIERS: on T_{r−2δ}
SOURCE_CONCLUSION: correction and new-error lemmas apply, giving (a), the bound |K̄−K|≤d in (b), and (c)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:correction, bp:p2:newton-error, step:p2:st-small
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:correction | blueprint/parts/p2-aposteriori.tex#step:p2:st-error@L917-L917 | size of ΔK, periodicity and realness
EDGE: bp:p2:newton-error | blueprint/parts/p2-aposteriori.tex#step:p2:st-error@L917-L917 | bound on Ē and K̄(T)⊂𝔅
EDGE: step:p2:st-small | blueprint/parts/p2-aposteriori.tex#step:p2:st-error@L918-L918 | hypotheses of the new-error lemma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.step (item (c) via newton_error)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-12-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:st-ball
KIND: step
TITLE: Ball margin
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:st-ball@L922-L923
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:st-ball@L922-L923
CONTRACT_ID: step:p2:st-ball
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r>0, 0<δ≤1, 4δ<r, β>0, 0≤ε≤1; K is (r,β,ε)-admissible; 𝔠_step ε/(γ⁴δ^{2a})≤min{1,β}; K̄ the map of bp:p2:newton-error; d:=C_ΔKε/(γ²δ^a); standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}
SOURCE_QUANTIFIERS: for all theta in T_{r-2delta} and all z with |z-Kbar(theta)|<beta-d
SOURCE_CONCLUSION: B_{β−d}(K̄(θ))⊂𝔅
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:admissible, step:p2:st-error, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#step:p2:st-ball@L923-L923 | A2: β-ball around K lies in 𝔅
EDGE: step:p2:st-error | blueprint/parts/p2-aposteriori.tex#step:p2:st-ball@L923-L923 | the preceding correction bound gives abs(Kbar-K)<=d in the triangle inequality
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:st-ball@L923-L923 | the inherited local ambient-domain package is fixed for admissibility and the A2 ball inclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.step (item (b), perturbation margin)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-12-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:st-perturb
KIND: step
TITLE: Perturbation on the strip $T_{r-2\delta}$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:st-perturb@L925-L929
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:st-perturb@L925-L929
CONTRACT_ID: step:p2:st-perturb
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K satisfies the hypotheses of the perturbation lemma on T_{r−2δ}; K̃:=K̄ with |K̄−K|≤d<β, 2𝔪C_ΔTd/δ²≤1; 2δ<r−2δ
SOURCE_QUANTIFIERS: on T_{r−2δ}, then T_{r−3δ}
SOURCE_CONCLUSION: (d), (e) on T_{r−3δ} and (f)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:perturbation, bp:p2:admissible, bp:p2:frequency, step:p2:st-small, step:p2:st-error
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:perturbation | blueprint/parts/p2-aposteriori.tex#step:p2:st-perturb@L926-L926 | frame/torsion perturbation
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#step:p2:st-perturb@L926-L926 | A2–A5 supply the lemma hypotheses
EDGE: bp:p2:frequency | blueprint/parts/p2-aposteriori.tex#step:p2:st-perturb@L927-L927 | ω≤Θ
EDGE: step:p2:st-small | blueprint/parts/p2-aposteriori.tex#step:p2:st-perturb@L929-L929 | d<β and 2𝔪C_ΔTd/δ²≤1
EDGE: step:p2:st-error | blueprint/parts/p2-aposteriori.tex#step:p2:st-perturb@L927-L927 | K̄ holomorphic with K̄−K≤d
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.step (perturbation on T_{r-2δ})
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-12-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:schedule
KIND: definition
TITLE: Schedule of the iteration
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:schedule@L935-L947
PROOF_SOURCE: -
CONTRACT_ID: bp:p2:schedule
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<ρ_∞<ρ, γ>0, e≥0; δ_0 from bp:p2:constants
SOURCE_QUANTIFIERS: for given ρ_∞<ρ, γ, e
SOURCE_CONCLUSION: defines δ_s:=2^{-s}δ_0, r_s:=ρ−8δ_0(1−2^{-s}), ε_0:=e, ε_{s+1}:=C_Eε_s²/(γ⁴δ_s^{2a}), d_s:=C_ΔKε_s/(γ²δ_s^a); with r_0=ρ, r_{s+1}=r_s−4δ_s, ρ_∞≤ρ−8δ_0<r_s, δ_s≤1, 4δ_s<r_s
CONSTANT_SCOPE: δ_0=δ_0(ρ,ρ_∞); C_E,C_ΔK,a from bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:schedule@L937-L937 | δ_0, C_E, C_ΔK, a
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.schedule (defs deltaSeq, rSeq, epsSeq, dSeq)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:error-decay
KIND: lemma
TITLE: Decay of the errors
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:error-decay@L952-L957
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:error-decay@L959-L969
CONTRACT_ID: bp:p2:error-decay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: schedule (bp:p2:schedule); q:=2^{2a}C_E e/(γ⁴δ_0^{2a})≤1
SOURCE_QUANTIFIERS: all s≥0; 0≤j≤2a; 0≤j≤2a−1 for the sums
SOURCE_CONCLUSION: ε_s≤q^{2^s−1}2^{-2as}e≤2^{-2as}e; ε_s/δ_s^j≤2^{-(2a−j)s}e/δ_0^j≤e/δ_0^j for 0≤j≤2a; Σ_sε_s/δ_s^j≤2e/δ_0^j for 0≤j≤2a−1
CONSTANT_SCOPE: a,C_E from bp:p2:constants (n,τ,M,σ_*); δ_0=δ_0(ρ,ρ_∞); none depends on s
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:ed-errors, step:p2:ed-sums, bp:p2:schedule
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:ed-errors | blueprint/parts/p2-aposteriori.tex#bp:p2:error-decay@L960-L960 | proof step of this result
EDGE: step:p2:ed-sums | blueprint/parts/p2-aposteriori.tex#bp:p2:error-decay@L966-L966 | proof step of this result
EDGE: bp:p2:schedule | blueprint/parts/p2-aposteriori.tex#bp:p2:error-decay@L953-L953 | ε_s,δ_s of the schedule
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.error_decay
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ed-errors
KIND: step
TITLE: The errors of the schedule
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ed-errors@L960-L964
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ed-errors@L960-L964
CONTRACT_ID: step:p2:ed-errors
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: schedule recursion ε_{s+1}=C_Eε_s²/(γ⁴δ_s^{2a}), δ_s^{-2a}=2^{2as}δ_0^{-2a}; q≤1
SOURCE_QUANTIFIERS: all s≥0
SOURCE_CONCLUSION: ε_{s+1}=Q′2^{2as}ε_s² with Q′=C_E/(γ⁴δ_0^{2a}); ε_s≤q^{2^s−1}2^{-2as}e≤2^{-2as}e
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:schedule, bp:p1:iteration
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:schedule | blueprint/parts/p2-aposteriori.tex#step:p2:ed-errors@L961-L961 | recursion for ε_s
EDGE: bp:p1:iteration | blueprint/parts/p2-aposteriori.tex#step:p2:ed-errors@L963-L963 | quadratic iteration bound linear in y_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.epsSeq_le_q_pow
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:ed-sums
KIND: step
TITLE: Sums
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ed-sums@L966-L968
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:ed-sums@L966-L968
CONTRACT_ID: step:p2:ed-sums
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ε_s≤2^{-2as}e; δ_s=2^{-s}δ_0
SOURCE_QUANTIFIERS: 0≤j≤2a−1
SOURCE_CONCLUSION: ε_sδ_s^{-j}≤2^{-(2a−j)s}e/δ_0^j and Σ_sε_s/δ_s^j≤2e/δ_0^j (geometric series ≤2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:ed-errors
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:ed-errors | blueprint/parts/p2-aposteriori.tex#step:p2:ed-sums@L967-L967 | bound ε_s≤2^{-2as}e
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.error_decay_sum
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:iteration
KIND: proposition
TITLE: The induction
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:iteration@L971-L991
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:iteration@L993-L1030
CONTRACT_ID: bp:p2:iteration
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<ρ_∞<ρ, μ>0; K holomorphic, primary, real on reals on T_ρ; B_μ(K(θ))⊂𝔅; |DK|≤σ_K−μ; det G≠0, |B|≤σ_B−μ; avg T invertible with |avgT^{-1}|≤σ_T−μ; |E|≤e on T_ρ; e≤1 and 𝔠_* e/(γ⁴δ_0^{2a})≤1; standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}
SOURCE_QUANTIFIERS: standing data fixed; for all ρ_∞<ρ, μ>0, e, γ, ω and K as stated; then there exist K_s (s≥0), K_0=K, with D_s:=Σ_{j<s}d_j
SOURCE_CONCLUSION: for every s≥0: (i) K_s is (r_s,μ−D_s,ε_s)-admissible and ε_s≤e≤1; (ii) D_s≤μ/4 and |K_s−K|≤D_s on T_{r_s}; (iii) |DK_s|≤σ_K−μ+Σ_{j<s}nd_j/δ_j≤σ_K−μ/2 on T_{r_s}; (iv) |B_s|≤σ_B−μ+Σ_{j<s}C_Bd_j/δ_j≤σ_B−μ/2; (v) |avgT_s^{-1}|≤σ_T−μ+Σ_{j<s}2𝔪²C_ΔTd_j/δ_j²≤σ_T−μ/2; (vi) |K_{s+1}−K_s|≤d_s and |DK_{s+1}−DK_s|≤nd_s/δ_s on T_{r_{s+1}}
CONSTANT_SCOPE: 𝔠_*=𝔠_*(n,τ,M,σ_K,σ_B,σ_T,μ), δ_0=δ_0(ρ,ρ_∞), 𝔠_step,C_*,a from bp:p2:constants; r_s,δ_s,ε_s,d_s from bp:p2:schedule (depend on ρ,ρ_∞,γ,e)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:it-sums, step:p2:it-stepsmall, step:p2:it-base, step:p2:it-step, bp:p2:admissible, bp:p2:schedule, bp:p2:constants, bp:p2:objects, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:it-sums | blueprint/parts/p2-aposteriori.tex#bp:p2:iteration@L994-L994 | proof step of this result
EDGE: step:p2:it-stepsmall | blueprint/parts/p2-aposteriori.tex#bp:p2:iteration@L1009-L1009 | proof step of this result
EDGE: step:p2:it-base | blueprint/parts/p2-aposteriori.tex#bp:p2:iteration@L1017-L1017 | proof step of this result
EDGE: step:p2:it-step | blueprint/parts/p2-aposteriori.tex#bp:p2:iteration@L1021-L1021 | proof step of this result
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#bp:p2:iteration@L982-L982 | admissibility of K_s
EDGE: bp:p2:schedule | blueprint/parts/p2-aposteriori.tex#bp:p2:iteration@L979-L979 | r_s,δ_s,ε_s,d_s
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:iteration@L977-L977 | 𝔠_*, δ_0
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#bp:p2:iteration@L974-L974 | G,B,T,E of K
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:iteration@L972-L972 | Part 2 standing data remain in force; the result uses this local package, restricted to its frequency/parameter components where appropriate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-r3
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.iteration (def KAM.Apost.kamSeq)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-13-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:it-sums
KIND: step
TITLE: Summed bounds
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:it-sums@L994-L1007
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:it-sums@L994-L1007
CONTRACT_ID: step:p2:it-sums
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: γ≤Θ; 𝔠_*≥2^{2a}C_E, 𝔠_*≥2𝔠_sum/μ; a≥3; e≤1
SOURCE_QUANTIFIERS: j=a,a+1,a+2≤2a−1
SOURCE_CONCLUSION: Σd_j≤μ/4, Σnd_j/δ_j≤μ/4, ΣC_Bd_j/δ_j≤μ/4, Σ2𝔪²C_ΔTd_j/δ_j²≤μ/2; giving the right-hand inequalities in (ii)–(v)
CONSTANT_SCOPE: 𝔠_sum,𝔠_*,Θ,C_* from bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frequency, bp:p2:error-decay, bp:p2:constants, bp:p2:schedule
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frequency | blueprint/parts/p2-aposteriori.tex#step:p2:it-sums@L995-L995 | γ≤Θ
EDGE: bp:p2:error-decay | blueprint/parts/p2-aposteriori.tex#step:p2:it-sums@L997-L997 | Σ_sε_s/δ_s^j≤2e/δ_0^j
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:it-sums@L996-L996 | 𝔠_*,𝔠_sum,a≥3
EDGE: bp:p2:schedule | blueprint/parts/p2-aposteriori.tex#step:p2:it-sums@L1001-L1001 | d_j of the schedule
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.sums_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-13-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:it-stepsmall
KIND: step
TITLE: Step smallness at every stage
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:it-stepsmall@L1009-L1015
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:it-stepsmall@L1009-L1015
CONTRACT_ID: step:p2:it-stepsmall
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<ρ_∞<ρ, μ>0; K holomorphic, primary, real on reals on T_ρ; B_μ(K(θ))⊂𝔅; |DK|≤σ_K−μ; det G≠0, |B|≤σ_B−μ; avg T invertible with |avgT^{-1}|≤σ_T−μ; |E|≤e on T_ρ; e≤1 and 𝔠_* e/(γ⁴δ_0^{2a})≤1; standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}; at stage s, induction condition (ii) is assumed when comparing mu/2 with mu-D_s, as explicitly at L1012
SOURCE_QUANTIFIERS: all s
SOURCE_CONCLUSION: 𝔠_stepε_s/(γ⁴δ_s^{2a})≤min{1,μ/2}≤min{1,μ−D_s}: smallness hypothesis of bp:p2:step holds for (r_s,δ_s,μ−D_s,ε_s)
CONSTANT_SCOPE: 𝔠_*,𝔠_step from bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:error-decay, bp:p2:schedule, bp:p2:constants, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:error-decay | blueprint/parts/p2-aposteriori.tex#step:p2:it-stepsmall@L1010-L1010 | ε_s≤e and ε_s/δ_s^{2a}≤e/δ_0^{2a}
EDGE: bp:p2:schedule | blueprint/parts/p2-aposteriori.tex#step:p2:it-stepsmall@L1010-L1010 | ε_s,δ_s notation
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:it-stepsmall@L1012-L1012 | 𝔠_*≥𝔠_step max{1,2/μ}
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:it-stepsmall@L1010-L1015 | the inherited local package fixes gamma>0 and the parameters entering the decay and step-smallness comparison
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.stepsmall_seq
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-13-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:it-base
KIND: step
TITLE: Base case
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:it-base@L1017-L1019
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:it-base@L1017-L1019
CONTRACT_ID: step:p2:it-base
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K_0=K with the hypotheses H2–H4 of the proposition
SOURCE_QUANTIFIERS: s=0
SOURCE_CONCLUSION: K_0 is (ρ,μ,e)-admissible; (ii)–(v) hold with empty sums
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:admissible
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#step:p2:it-base@L1018-L1018 | A1–A6 for K_0 from the hypotheses with margins σ−μ≤σ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.stage_zero
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-13-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:it-step
KIND: step
TITLE: Inductive step
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:it-step@L1021-L1029
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:it-step@L1021-L1029
CONTRACT_ID: step:p2:it-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (i)–(v) at s; summed bounds; smallness at stage s; 4δ_s<r_s, δ_s≤1
SOURCE_QUANTIFIERS: induction step s→s+1
SOURCE_CONCLUSION: K_{s+1}:=K̄_s satisfies (vi) and (i)–(v) at s+1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:step, bp:p2:admissible, step:p2:it-stepsmall, step:p2:it-sums, bp:p2:schedule
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:step | blueprint/parts/p2-aposteriori.tex#step:p2:it-step@L1022-L1022 | the KAM step produces K̄_s and its bounds
EDGE: bp:p2:admissible | blueprint/parts/p2-aposteriori.tex#step:p2:it-step@L1029-L1029 | A1,A3–A5 for K_{s+1}
EDGE: step:p2:it-stepsmall | blueprint/parts/p2-aposteriori.tex#step:p2:it-step@L1022-L1022 | smallness hypothesis of the step
EDGE: step:p2:it-sums | blueprint/parts/p2-aposteriori.tex#step:p2:it-step@L1028-L1028 | right-hand inequalities (ii)–(v)
EDGE: bp:p2:schedule | blueprint/parts/p2-aposteriori.tex#step:p2:it-step@L1023-L1023 | r_{s+1}=r_s−4δ_s
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.stage_succ
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-13-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:limit
KIND: proposition
TITLE: The limit torus
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1032-L1052
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1054-L1090
CONTRACT_ID: bp:p2:limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: setting of bp:p2:iteration (0<ρ_∞<ρ, μ, K, e, γ, ω with the iteration hypotheses); K_∞:=lim K_s on T_{ρ_∞}, K_∞:=K elsewhere; standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}
SOURCE_QUANTIFIERS: as in bp:p2:iteration
SOURCE_CONCLUSION: (a) K_s→K_∞ and DK_s→DK_∞ uniformly on T_{ρ_∞}, K_∞ holomorphic on T_{ρ_∞}; (b) K_∞ primary on T_{ρ_∞}, real on reals; (c) |K_∞−K|≤2C_ΔKe/(γ²δ_0^a)≤μ/4 on T_{ρ_∞}; (d) B_{μ/2}(K_∞(θ))⊂𝔅 and |DK_∞(θ)|≤σ_K−μ/2 for θ∈T_{ρ_∞}; (e) E_∞(θ)=X_h(K_∞(θ))−DK_∞(θ)ω=0 for θ∈T_{ρ_∞}
CONSTANT_SCOPE: C_ΔK,a from bp:p2:constants; δ_0=δ_0(ρ,ρ_∞); all explicit
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:lim-k, step:p2:lim-dk, step:p2:lim-holo, step:p2:lim-primary, step:p2:lim-close, step:p2:lim-margins, step:p2:lim-invariance, bp:p2:iteration, bp:p2:constants, bp:p2:objects, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:lim-k | blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1055-L1055 | proof step of this result
EDGE: step:p2:lim-dk | blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1061-L1061 | proof step of this result
EDGE: step:p2:lim-holo | blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1065-L1065 | proof step of this result
EDGE: step:p2:lim-primary | blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1071-L1071 | proof step of this result
EDGE: step:p2:lim-close | blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1075-L1075 | proof step of this result
EDGE: step:p2:lim-margins | blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1080-L1080 | proof step of this result
EDGE: step:p2:lim-invariance | blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1085-L1085 | proof step of this result
EDGE: bp:p2:iteration | blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1033-L1033 | the sequence K_s
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1043-L1043 | C_ΔK, δ_0
EDGE: bp:p2:objects | blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1046-L1046 | E_∞ is the invariance error E of K_∞
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#bp:p2:limit@L1033-L1033 | Part 2 standing data remain in force; the result uses this local package, restricted to its frequency/parameter components where appropriate
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-r3
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.limit (def KAM.Apost.kamLimit)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:lim-k
KIND: step
TITLE: Uniform convergence of $K_s$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-k@L1055-L1059
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-k@L1055-L1059
CONTRACT_ID: step:p2:lim-k
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T_{ρ_∞}⊂T_{r_s}; |K_{s+1}−K_s|≤d_s; Σd_s≤2C_ΔKe/(γ²δ_0^a)
SOURCE_QUANTIFIERS: on T_{ρ_∞}
SOURCE_CONCLUSION: (K_s) uniformly Cauchy, converges uniformly to K_∞
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:schedule, bp:p2:iteration, bp:p2:error-decay
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:schedule | blueprint/parts/p2-aposteriori.tex#step:p2:lim-k@L1056-L1056 | T_{ρ_∞}⊂T_{r_s}
EDGE: bp:p2:iteration | blueprint/parts/p2-aposteriori.tex#step:p2:lim-k@L1057-L1057 | K_{s+1}−K_s≤d_s
EDGE: bp:p2:error-decay | blueprint/parts/p2-aposteriori.tex#step:p2:lim-k@L1058-L1058 | Σd_s finite via the sum bound with j=a
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.lim_k
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:lim-dk
KIND: step
TITLE: Uniform convergence of $DK_s$
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-dk@L1061-L1063
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-dk@L1061-L1063
CONTRACT_ID: step:p2:lim-dk
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<ρ_∞<ρ, μ>0; K holomorphic, primary, real on reals on T_ρ; B_μ(K(θ))⊂𝔅; |DK|≤σ_K−μ; det G≠0, |B|≤σ_B−μ; avg T invertible with |avgT^{-1}|≤σ_T−μ; |E|≤e on T_ρ; e≤1 and 𝔠_* e/(γ⁴δ_0^{2a})≤1; standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}; K_s denotes the sequence constructed by the induction; K_infty is its limit when established, extended by K outside T_{rho_infty}
SOURCE_QUANTIFIERS: on T_{ρ_∞}
SOURCE_CONCLUSION: DK_s converges uniformly to some Λ_∞ (values in C-linear maps)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:iteration, bp:p2:error-decay, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:iteration | blueprint/parts/p2-aposteriori.tex#step:p2:lim-dk@L1062-L1062 | (vi): DK_{s+1}−DK_s≤nd_s/δ_s
EDGE: bp:p2:error-decay | blueprint/parts/p2-aposteriori.tex#step:p2:lim-dk@L1062-L1062 | finiteness of Σnd_s/δ_s via the sum bound with j=a+1
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:lim-dk@L1062-L1063 | the limit is in the induction setting with the local Part 2 package, which supplies gamma>0 and the fixed parameters of d_s
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.lim_dk
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:lim-holo
KIND: step
TITLE: Holomorphy of the limit
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-holo@L1065-L1069
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-holo@L1065-L1069
CONTRACT_ID: step:p2:lim-holo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K_s holomorphic on the open T_{ρ_∞}; K_s→K_∞ pointwise; DK_s→Λ_∞ uniformly
SOURCE_QUANTIFIERS: on T_{ρ_∞}
SOURCE_CONCLUSION: K_∞ holomorphic with DK_∞=Λ_∞ (this is (a))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:uniform-limits, step:p2:lim-k, step:p2:lim-dk, bp:p2:iteration
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:uniform-limits | blueprint/parts/p2-aposteriori.tex#step:p2:lim-holo@L1067-L1067 | limit of holomorphic maps with uniformly convergent derivatives
EDGE: step:p2:lim-k | blueprint/parts/p2-aposteriori.tex#step:p2:lim-holo@L1066-L1066 | pointwise (uniform) limit K_∞
EDGE: step:p2:lim-dk | blueprint/parts/p2-aposteriori.tex#step:p2:lim-holo@L1067-L1067 | uniform convergence DK_s→Λ_∞
EDGE: bp:p2:iteration | blueprint/parts/p2-aposteriori.tex#step:p2:lim-holo@L1066-L1066 | K_s holomorphic by (i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.lim_holo
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:lim-primary
KIND: step
TITLE: Primary and real
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-primary@L1071-L1073
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-primary@L1071-L1073
CONTRACT_ID: step:p2:lim-primary
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<ρ_∞<ρ, μ>0; K holomorphic, primary, real on reals on T_ρ; B_μ(K(θ))⊂𝔅; |DK|≤σ_K−μ; det G≠0, |B|≤σ_B−μ; avg T invertible with |avgT^{-1}|≤σ_T−μ; |E|≤e on T_ρ; e≤1 and 𝔠_* e/(γ⁴δ_0^{2a})≤1; standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}; K_s denotes the sequence constructed by the induction; K_infty is its limit when established, extended by K outside T_{rho_infty}
SOURCE_QUANTIFIERS: on T_{ρ_∞}
SOURCE_CONCLUSION: K_∞ primary and real on reals (this is (b))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:iteration, bp:p1:uniform-limits, step:p2:lim-k, step:p2:lim-dk, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:iteration | blueprint/parts/p2-aposteriori.tex#step:p2:lim-primary@L1073-L1073 | K_s primary and real
EDGE: bp:p1:uniform-limits | blueprint/parts/p2-aposteriori.tex#step:p2:lim-primary@L1073-L1073 | primary and real are preserved under uniform limits
EDGE: step:p2:lim-k | blueprint/parts/p2-aposteriori.tex#step:p2:lim-primary@L1072-L1073 | pointwise convergence to K_infty supplies the limit premise for preservation of primarity and realness
EDGE: step:p2:lim-dk | blueprint/parts/p2-aposteriori.tex#step:p2:lim-primary@L1073-L1073 | uniform derivative convergence supplies the remaining hypothesis of the cited uniform-limits lemma
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:lim-primary@L1072-L1073 | the local Part 2 package is inherited by the induction setting whose primary real tori are restricted here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.lim_primary
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:lim-close
KIND: step
TITLE: Closeness
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-close@L1075-L1078
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-close@L1075-L1078
CONTRACT_ID: step:p2:lim-close
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<ρ_∞<ρ, μ>0; K holomorphic, primary, real on reals on T_ρ; B_μ(K(θ))⊂𝔅; |DK|≤σ_K−μ; det G≠0, |B|≤σ_B−μ; avg T invertible with |avgT^{-1}|≤σ_T−μ; |E|≤e on T_ρ; e≤1 and 𝔠_* e/(γ⁴δ_0^{2a})≤1; standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}; K_s denotes the sequence constructed by the induction; K_infty is its limit when established, extended by K outside T_{rho_infty}
SOURCE_QUANTIFIERS: on T_{ρ_∞}
SOURCE_CONCLUSION: |K_∞−K|≤2C_ΔKe/(γ²δ_0^a)≤μ/4 (this is (c))
CONSTANT_SCOPE: C_ΔK from bp:p2:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:iteration, step:p2:it-sums, step:p2:lim-k, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:iteration | blueprint/parts/p2-aposteriori.tex#step:p2:lim-close@L1076-L1076 | K_s−K≤D_s (ii)
EDGE: step:p2:it-sums | blueprint/parts/p2-aposteriori.tex#step:p2:lim-close@L1076-L1076 | Σd_s≤2Θ²C_ΔKe/(γ⁴δ_0^{2a})≤μ/4
EDGE: step:p2:lim-k | blueprint/parts/p2-aposteriori.tex#step:p2:lim-close@L1076-L1078 | uniform convergence justifies passage to the limit and L1057 supplies sum d_s<=2 C_DeltaK e/(gamma^2 delta_0^a)
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:lim-close@L1076-L1078 | the local Part 2 package fixes the positive gamma and constants in the summed displacement bounds
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.lim_close
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:lim-margins
KIND: step
TITLE: Margins
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-margins@L1080-L1083
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-margins@L1080-L1083
CONTRACT_ID: step:p2:lim-margins
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |K_∞−K|≤μ/4; hypothesis H2 B_μ(K(θ))⊂𝔅; |DK_s|≤σ_K−μ/2
SOURCE_QUANTIFIERS: θ∈T_{ρ_∞}
SOURCE_CONCLUSION: B_{μ/2}(K_∞(θ))⊂𝔅 and |DK_∞(θ)|≤σ_K−μ/2 (this is (d))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:lim-close, bp:p2:iteration, step:p2:lim-holo
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:lim-close | blueprint/parts/p2-aposteriori.tex#step:p2:lim-margins@L1081-L1081 | K_∞−K≤μ/4
EDGE: bp:p2:iteration | blueprint/parts/p2-aposteriori.tex#step:p2:lim-margins@L1083-L1083 | DK_s≤σ_K−μ/2
EDGE: step:p2:lim-holo | blueprint/parts/p2-aposteriori.tex#step:p2:lim-margins@L1082-L1082 | DK_∞=lim DK_s
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.lim_margins
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:lim-invariance
KIND: step
TITLE: Invariance
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-invariance@L1085-L1089
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:lim-invariance@L1085-L1089
CONTRACT_ID: step:p2:lim-invariance
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0<ρ_∞<ρ, μ>0; K holomorphic, primary, real on reals on T_ρ; B_μ(K(θ))⊂𝔅; |DK|≤σ_K−μ; det G≠0, |B|≤σ_B−μ; avg T invertible with |avgT^{-1}|≤σ_T−μ; |E|≤e on T_ρ; e≤1 and 𝔠_* e/(γ⁴δ_0^{2a})≤1; standing data of Part 2 (bp:p2:standing): n≥2, τ≥n−1, M,σ_K,σ_B,σ_T>0, 𝔅 open and Z^n-translation invariant, h holomorphic, 1-periodic in θ, real at real points, |X_h|,|DX_h|,|D²X_h|≤M on 𝔅, γ>0, ω∈Dio_{γ,τ}; K_s denotes the sequence constructed by the induction; K_infty is its limit when established, extended by K outside T_{rho_infty}
SOURCE_QUANTIFIERS: θ∈T_{ρ_∞}
SOURCE_CONCLUSION: E_∞(θ)=0 (this is (e))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:iteration, bp:p2:error-decay, bp:p2:hamiltonian, step:p2:lim-margins, step:p2:lim-holo, step:p2:lim-k, bp:p2:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:iteration | blueprint/parts/p2-aposteriori.tex#step:p2:lim-invariance@L1088-L1088 | E_s≤ε_s
EDGE: bp:p2:error-decay | blueprint/parts/p2-aposteriori.tex#step:p2:lim-invariance@L1089-L1089 | ε_s≤2^{-2as}e→0
EDGE: bp:p2:hamiltonian | blueprint/parts/p2-aposteriori.tex#step:p2:lim-invariance@L1086-L1086 | X_h holomorphic hence continuous
EDGE: step:p2:lim-margins | blueprint/parts/p2-aposteriori.tex#step:p2:lim-invariance@L1086-L1086 | K_∞(θ)∈𝔅 by the margin ball
EDGE: step:p2:lim-holo | blueprint/parts/p2-aposteriori.tex#step:p2:lim-invariance@L1087-L1087 | DK_s→DK_∞ pointwise
EDGE: step:p2:lim-k | blueprint/parts/p2-aposteriori.tex#step:p2:lim-invariance@L1086-L1087 | K_s(theta) tends to K_infty(theta), allowing continuity of X_h to pass to the limit
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:lim-invariance@L1086-L1089 | the local package supplies the open ambient domain and holomorphic X_h input used for continuity at the limiting point
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.lim_invariance
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p2:g1
KIND: theorem
TITLE: G1 with explicit constants
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:g1@L1095-L1108
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#bp:p2:g1@L1110-L1143
CONTRACT_ID: bp:p2:g1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n≥2, τ≥n−1, 0<ρ_∞<ρ, M,σ_K,σ_B,σ_T,μ,γ̄>0; C_1:=ρ^{4τ}max{γ̄⁴,𝔠_*δ_0^{-2a}}, C_2:=2C_ΔKρ^{2τ}δ_0^{-a}; hypotheses of bp:p0:g1 on 𝔅,h,K,ω,γ,e (including γ≤γ̄)
SOURCE_QUANTIFIERS: for the given n,τ,ρ,ρ_∞,M,σ_*,μ,γ̄; then for all 𝔅,h,K,ω,γ,e satisfying the hypotheses of bp:p0:g1
SOURCE_CONCLUSION: C_1,C_2>0 and the conclusion (seven clauses) of bp:p0:g1 holds with these constants
CONSTANT_SCOPE: C_1 depends only on (n,τ,ρ,ρ_∞,M,σ_K,σ_B,σ_T,μ,γ̄); C_2 only on (n,τ,ρ,ρ_∞,M,σ_K,σ_B,σ_T)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:g1-constants, step:p2:g1-standing, step:p2:g1-e, step:p2:g1-apply, step:p2:g1-check, bp:p2:constants
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:g1-constants | blueprint/parts/p2-aposteriori.tex#bp:p2:g1@L1111-L1111 | proof step of this result
EDGE: step:p2:g1-standing | blueprint/parts/p2-aposteriori.tex#bp:p2:g1@L1116-L1116 | proof step of this result
EDGE: step:p2:g1-e | blueprint/parts/p2-aposteriori.tex#bp:p2:g1@L1122-L1122 | proof step of this result
EDGE: step:p2:g1-apply | blueprint/parts/p2-aposteriori.tex#bp:p2:g1@L1127-L1127 | proof step of this result
EDGE: step:p2:g1-check | blueprint/parts/p2-aposteriori.tex#bp:p2:g1@L1132-L1132 | proof step of this result
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#bp:p2:g1@L1097-L1097 | 𝔠_*, δ_0, C_ΔK, a
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.g1_explicit (KAM/Apost/G1.lean:76), with KAM.Apost.C_1, C_2, C_1_pos, C_2_pos (G1.lean:48-61)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P2-14-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p2:g1-constants
KIND: step
TITLE: The constants
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:g1-constants@L1111-L1114
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:g1-constants@L1111-L1114
CONTRACT_ID: step:p2:g1-constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: constants of bp:p2:constants finite and ≥1, δ_0∈(0,1], ρ>0
SOURCE_QUANTIFIERS: as in the theorem
SOURCE_CONCLUSION: C_1≥ρ^{4τ}γ̄⁴>0, C_2≥2ρ^{2τ}>0; dependence of C_1,C_2 read off from the definitions (c(n,τ) enters through c_R)
CONSTANT_SCOPE: C_1,C_2 as stated in the theorem
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:constants, bp:p1:cohomological
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:constants | blueprint/parts/p2-aposteriori.tex#step:p2:g1-constants@L1112-L1112 | finiteness, ≥1, and dependence of the constants
EDGE: bp:p1:cohomological | blueprint/parts/p2-aposteriori.tex#step:p2:g1-constants@L1114-L1114 | c(n,τ) enters through c_R
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.C_1_pos, C_2_pos
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:g1-standing
KIND: step
TITLE: The standing assumptions
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:g1-standing@L1116-L1120
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:g1-standing@L1116-L1120
CONTRACT_ID: step:p2:g1-standing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: hypotheses H1 and H5 of bp:p0:g1
SOURCE_QUANTIFIERS: as in the theorem
SOURCE_CONCLUSION: H1 and H5 are the standing data of Part 2; the frozen norms are the operator norms of Part 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:standing, bp:p2:frozen-agreement
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:standing | blueprint/parts/p2-aposteriori.tex#step:p2:g1-standing@L1119-L1119 | H1 and H5 coincide with the standing package
EDGE: bp:p2:frozen-agreement | blueprint/parts/p2-aposteriori.tex#step:p2:g1-standing@L1120-L1120 | frozen norms and objects agree with Part 2 conventions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: inside KAM.Apost.g1_explicit
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:g1-e
KIND: step
TITLE: Size of the error
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:g1-e@L1122-L1125
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:g1-e@L1122-L1125
CONTRACT_ID: step:p2:g1-e
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T_ρ≠∅; |E|≤e on T_ρ; C_1e/(γ⁴ρ^{4τ})<1; γ≤γ̄
SOURCE_QUANTIFIERS: as in the theorem
SOURCE_CONCLUSION: 0≤|E(0)|≤e; e<γ⁴/γ̄⁴≤1; 𝔠_*e/(γ⁴δ_0^{2a})<1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p2:g1-constants
ROUTES: -
ROUTE_FOR: -
EDGE: step:p2:g1-constants | blueprint/parts/p2-aposteriori.tex#step:p2:g1-e@L1123-L1123 | C_1≥ρ^{4τ}γ̄⁴ and C_1≥ρ^{4τ}𝔠_*δ_0^{-2a}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Apost.g1_error_small
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:g1-apply
KIND: step
TITLE: Iteration and limit
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:g1-apply@L1127-L1130
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:g1-apply@L1127-L1130
CONTRACT_ID: step:p2:g1-apply
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H2–H4 of bp:p0:g1; e≤1 and 𝔠_*e/(γ⁴δ_0^{2a})≤1; standing data
SOURCE_QUANTIFIERS: as in the theorem
SOURCE_CONCLUSION: H2–H4 are the hypotheses of bp:p2:iteration; iteration and limit propositions apply and produce K_∞
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:iteration, bp:p2:limit, step:p2:g1-e, step:p2:g1-standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:iteration | blueprint/parts/p2-aposteriori.tex#step:p2:g1-apply@L1128-L1128 | the induction produces K_s
EDGE: bp:p2:limit | blueprint/parts/p2-aposteriori.tex#step:p2:g1-apply@L1130-L1130 | the limit torus K_∞
EDGE: step:p2:g1-e | blueprint/parts/p2-aposteriori.tex#step:p2:g1-apply@L1129-L1129 | e≤1 and 𝔠_*e/(γ⁴δ_0^{2a})<1
EDGE: step:p2:g1-standing | blueprint/parts/p2-aposteriori.tex#step:p2:g1-apply@L1128-L1128 | standing package supplied (H1, H5)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: inside KAM.Apost.g1_explicit
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p2:g1-check
KIND: step
TITLE: Checking the conclusion
STATEMENT_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:g1-check@L1132-L1142
PROOF_SOURCE: blueprint/parts/p2-aposteriori.tex#step:p2:g1-check@L1132-L1142
CONTRACT_ID: step:p2:g1-check
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K_∞ with properties (a)–(e) of bp:p2:limit; frozen agreement
SOURCE_QUANTIFIERS: on T_{ρ_∞}
SOURCE_CONCLUSION: the seven clauses of the conclusion of bp:p0:g1 with |K_∞−K|≤2C_ΔKe/(γ²δ_0^a)=C_2e/(γ²ρ^{2τ})
CONSTANT_SCOPE: C_2=2C_ΔKρ^{2τ}δ_0^{-a}
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:limit, bp:p2:frozen-agreement, step:p2:g1-apply, step:p2:g1-constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:limit | blueprint/parts/p2-aposteriori.tex#step:p2:g1-check@L1133-L1133 | properties (a)–(e) of K_∞
EDGE: bp:p2:frozen-agreement | blueprint/parts/p2-aposteriori.tex#step:p2:g1-check@L1142-L1142 | derivative, invariance error and ball agree with the frozen ones
EDGE: step:p2:g1-apply | blueprint/parts/p2-aposteriori.tex#step:p2:g1-check@L1133-L1133 | K_∞ produced by the previous step
EDGE: step:p2:g1-constants | blueprint/parts/p2-aposteriori.tex#step:p2:g1-check@L1138-L1138 | C_2=2C_ΔKρ^{2τ}δ_0^{-a}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p2b
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: inside KAM.Apost.g1_explicit
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P2-14-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p3:standing
KIND: definition
TITLE: Two invariant tori
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:standing@L55-L93
PROOF_SOURCE: -
CONTRACT_ID: bp:p3:standing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none beyond the typing data: B, h, K_1, K_2, omega, gamma; (S1) B open, invariant under integer shifts of theta, h holomorphic on B, 1-periodic in theta, real at real points of B, and |Dh|,|X_h|,|DX_h|,|D^2X_h|<=M on B; (S2) gamma>0, omega in Dio_{gamma,tau}; (S3) K_1 holomorphic, primary, real on reals on T_rho, ball of radius mu around K_1(theta) in B, |DK_1|<=sigma_K-mu, L^T L invertible, |B|<=sigma_B-mu, avg T invertible with |avg T^{-1}|<=sigma_T-mu, E_1=0 on T_rho; (S4) K_2 holomorphic, primary, real on reals on T_rho, K_2(T_rho) in B, E_2=0 on T_rho
SOURCE_QUANTIFIERS: n>=2, tau>=n-1, rho>0, M,sigma_K,sigma_B,sigma_T,mu>0 fixed; then data B,h,K_1,K_2,omega,gamma; theta ranges over T_rho in (S3)
SOURCE_CONCLUSION: defines the hypothesis package (S1)-(S4): the hypotheses of G2 without the closeness hypothesis (S1-S2 contain bp:p2:standing)
CONSTANT_SCOPE: M,sigma_K,sigma_B,sigma_T,mu are fixed constants of the part, independent of gamma; no derived constants here
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:diophantine#IsDiophantine, bp:p0:stripdata#IsPrimaryOnStrip, bp:p0:stripdata#IsRealOnReals, bp:p0:stripdata#invarianceError, bp:p0:stripdata#gramMatrix, bp:p0:stripdata#normalFrame, bp:p0:stripdata#torsion, bp:p0:stripdata#torsionAverage, bp:p2:standing, bp:p2:objects
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p3-uniqueness.tex#bp:p3:standing@L63-L63 | (S2) omega in Dio_{gamma,tau}
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p3-uniqueness.tex#bp:p3:standing@L64-L64 | (S3),(S4) primary on T_rho
EDGE: bp:p0:stripdata#IsRealOnReals | blueprint/parts/p3-uniqueness.tex#bp:p3:standing@L64-L64 | (S3),(S4) real on reals
EDGE: bp:p0:stripdata#invarianceError | blueprint/parts/p3-uniqueness.tex#bp:p3:standing@L68-L68 | E_i = X_h(K_i) - DK_i omega
EDGE: bp:p0:stripdata#gramMatrix | blueprint/parts/p3-uniqueness.tex#bp:p3:standing@L66-L66 | Gram matrix L^T L
EDGE: bp:p0:stripdata#normalFrame | blueprint/parts/p3-uniqueness.tex#bp:p3:standing@L85-L85 | N, P of the frame, B = (L^T L)^{-1}
EDGE: bp:p0:stripdata#torsion | blueprint/parts/p3-uniqueness.tex#bp:p3:standing@L87-L87 | torsion T = N^T Omega_0 X_N
EDGE: bp:p0:stripdata#torsionAverage | blueprint/parts/p3-uniqueness.tex#bp:p3:standing@L87-L87 | avg T used in (S3)
EDGE: bp:p2:standing | blueprint/parts/p3-uniqueness.tex#bp:p3:standing@L74-L77 | S1-S2 supply the Part 2 standing package with the same n,tau,M,sigma parameters; S3 supplies the additional torus premises when a Part 2 result is applied
EDGE: bp:p2:objects | blueprint/parts/p3-uniqueness.tex#bp:p3:standing@L77-L88 | the frame, torsion and error notation are specialized from the objects of Part 2 at K=K_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3+sol-review-r3
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.{Params, S1, S2, S3, S4}, KAM.Uniq.standing_of
LEAN_NOTE: standing data and constants per the audited design; audit docs/campaign/audits/P3-0-audit-1.md; kernel replay passed (2026-10-27)
NOTE: standing hypotheses of Part 3, a local package (SPEC): (S1)-(S4)

NODE: bp:p3:matrix-norms
KIND: lemma
TITLE: Matrix norms of the frame
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:matrix-norms@L124-L131
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:matrix-norms@L133-L140
CONTRACT_ID: bp:p3:matrix-norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (S3) (assumed for the lemma)
SOURCE_QUANTIFIERS: for every theta in T_rho; constants as in the setting
SOURCE_CONCLUSION: |L|<=sigma_K, |B|<=sigma_B, |N|<=sigma_K sigma_B, |BL^T|<=C_P, |L^T Omega_0|<=C_P, |P|<=C_P, and the stacked matrix (BL^T; -L^T Omega_0) has norm <=C_P
CONSTANT_SCOPE: C_P=2n sigma_K(1+sigma_B), depends only on n,sigma_K,sigma_B
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:standing, bp:p3:standing#constants, step:p3:norms-frame
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#bp:p3:matrix-norms@L125-L125 | assumes (S3)
EDGE: bp:p3:standing#constants | blueprint/parts/p3-uniqueness.tex#bp:p3:matrix-norms@L128-L128 | bounds are stated through C_P
EDGE: step:p3:norms-frame | blueprint/parts/p3-uniqueness.tex#bp:p3:matrix-norms@L134-L134 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.matrix_norms
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:norms-frame
KIND: step
TITLE: The frame
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:norms-frame@L134-L139
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:norms-frame@L134-L139
CONTRACT_ID: step:p3:norms-frame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (S3): |DK_1|<=sigma_K-mu, |B|<=sigma_B-mu on T_rho; operator norm convention
SOURCE_QUANTIFIERS: theta in T_rho
SOURCE_CONCLUSION: the seven bounds of the lemma
CONSTANT_SCOPE: C_P as in the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:matrix-norms, bp:p1:operator-norms, bp:p3:standing#constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:matrix-norms | blueprint/parts/p3-uniqueness.tex#step:p3:norms-frame@L136-L136 | bounds abs LBabs , abs L^Tabs , abs BL^Tabs  and the stacked-block identity
EDGE: bp:p1:operator-norms | blueprint/parts/p3-uniqueness.tex#step:p3:norms-frame@L139-L139 | block-row bound abs Pabs <=abs Labs +abs Nabs 
EDGE: bp:p3:standing#constants | blueprint/parts/p3-uniqueness.tex#step:p3:norms-frame@L137-L137 | C_P bounds the products
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.matrix_norms (KAM/Uniq/Frame.lean:220)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P3-1-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: bp:p3:lagrangian
KIND: lemma
TITLE: The reference torus is Lagrangian
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:lagrangian@L149-L151
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:lagrangian@L153-L171
CONTRACT_ID: bp:p3:lagrangian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (S1)-(S3)
SOURCE_QUANTIFIERS: theta in T_rho
SOURCE_CONCLUSION: Omega_{K_1}=L^T Omega_0 L=0 on T_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:standing, step:p3:lagrangian-transport, step:p3:lagrangian-unique
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#bp:p3:lagrangian@L150-L150 | assumes (S1)-(S3)
EDGE: step:p3:lagrangian-transport | blueprint/parts/p3-uniqueness.tex#bp:p3:lagrangian@L154-L154 | proof step
EDGE: step:p3:lagrangian-unique | blueprint/parts/p3-uniqueness.tex#bp:p3:lagrangian@L160-L160 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.lagrangian
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:lagrangian-transport
KIND: step
TITLE: Invariance of $\Omega_{K_1}$ along the flow
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:lagrangian-transport@L154-L158
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:lagrangian-transport@L154-L158
CONTRACT_ID: step:p3:lagrangian-transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (S3): K_1(T_rho) in B, det(L^T L)!=0, E_1=0 on the open set T_rho
SOURCE_QUANTIFIERS: on T_rho
SOURCE_CONCLUSION: d_omega Omega_{K_1}=0, Omega_{K_1} is 1-periodic, avg Omega_{K_1}=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frame-identities, bp:p2:periodicity, bp:p2:exactness
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frame-identities | blueprint/parts/p3-uniqueness.tex#step:p3:lagrangian-transport@L156-L156 | (d) gives d_omega Omega_{K_1}=0 for DE_1=0
EDGE: bp:p2:periodicity | blueprint/parts/p3-uniqueness.tex#step:p3:lagrangian-transport@L157-L157 | Omega_{K_1} 1-periodic
EDGE: bp:p2:exactness | blueprint/parts/p3-uniqueness.tex#step:p3:lagrangian-transport@L157-L157 | zero average of Omega_{K_1} for primary K_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.FrameAux.fderiv_lagrangeMat_eq_zero (KAM/Uniq/Frame.lean:165); KAM.Apost.periodic_lagrangeMat (KAM/Apost/Periodicity.lean:123); KAM.Apost.exactness, first conjunct (KAM/Apost/Exactness.lean:292)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P3-1-audit-1.md (route note D1); inputs: docs/campaign/audits/P2-6-audit-1.md (frame-identities), docs/campaign/audits/P2-7-audit-1.md (exactness), docs/campaign/audits/P2-4-audit-1.md (periodicity); kernel replay passed with the package
NOTE: -

NODE: step:p3:lagrangian-unique
KIND: step
TITLE: Nonresonance
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:lagrangian-unique@L160-L170
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:lagrangian-unique@L160-L170
CONTRACT_ID: step:p3:lagrangian-unique
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Omega_{K_1} holomorphic and bounded on T_rho by 2n sigma_K^2, zero average, d_omega Omega_{K_1}=0, periodic (previous step); omega in Dio (S2)
SOURCE_QUANTIFIERS: 0<delta<rho; each entry of Omega_{K_1}
SOURCE_CONCLUSION: Omega_{K_1}=0 on T_{rho-delta}, hence on T_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:matrix-norms, bp:p3:matrix-norms, bp:p1:cohomological, step:p3:lagrangian-transport
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:matrix-norms | blueprint/parts/p3-uniqueness.tex#step:p3:lagrangian-unique@L161-L161 | bound abs L^Tabs abs Omega_0 Labs 
EDGE: bp:p3:matrix-norms | blueprint/parts/p3-uniqueness.tex#step:p3:lagrangian-unique@L162-L162 | abs Labs <=sigma_K
EDGE: bp:p1:cohomological | blueprint/parts/p3-uniqueness.tex#step:p3:lagrangian-unique@L167-L167 | uniqueness part with g=0
EDGE: step:p3:lagrangian-transport | blueprint/parts/p3-uniqueness.tex#step:p3:lagrangian-unique@L168-L168 | entries have zero average, periodic, Du omega=0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: route substitution (D27): KAM.Uniq.lagrangian uses the operator a-priori bound of KAM.Apost.cohomological with H = 0 instead of uniqueness with g = 0; audit docs/campaign/audits/P3-1-audit-1.md (D1) confirms validity
NOTE: -

NODE: bp:p3:frequency-bound
KIND: lemma
TITLE: A priori bound on the frequency
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:frequency-bound@L176-L178
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:frequency-bound@L180-L191
CONTRACT_ID: bp:p3:frequency-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (S1)-(S3)
SOURCE_QUANTIFIERS: n,tau,rho,M,sigma_K,sigma_B,sigma_T fixed; Gamma=C_P M
SOURCE_CONCLUSION: |omega|<=Gamma and gamma<=Gamma
CONSTANT_SCOPE: Gamma depends only on n,sigma_K,sigma_B,M, not on gamma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:standing, bp:p3:standing#constants, step:p3:frequency-omega, step:p3:frequency-gamma
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#bp:p3:frequency-bound@L177-L177 | assumes (S1)-(S3)
EDGE: bp:p3:standing#constants | blueprint/parts/p3-uniqueness.tex#bp:p3:frequency-bound@L177-L177 | Gamma = C_P M
EDGE: step:p3:frequency-omega | blueprint/parts/p3-uniqueness.tex#bp:p3:frequency-bound@L181-L181 | proof step
EDGE: step:p3:frequency-gamma | blueprint/parts/p3-uniqueness.tex#bp:p3:frequency-bound@L188-L188 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.frequency_bound
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:frequency-omega
KIND: step
TITLE: Bound on $\omega$
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:frequency-omega@L181-L186
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:frequency-omega@L181-L186
CONTRACT_ID: step:p3:frequency-omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K_1(T_rho) in B; K_1 satisfies A3, A4 on T_rho and A6 with eps=0 (from (S3))
SOURCE_QUANTIFIERS: on T_rho
SOURCE_CONCLUSION: |omega|<=2n sigma_K sigma_B M<=C_P M=Gamma
CONSTANT_SCOPE: Gamma as in the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:admissible, bp:p2:frequency
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:admissible | blueprint/parts/p3-uniqueness.tex#step:p3:frequency-omega@L182-L182 | K_1 satisfies A3, A4, A6 with eps=0
EDGE: bp:p2:frequency | blueprint/parts/p3-uniqueness.tex#step:p3:frequency-omega@L183-L183 | frequency bound with eps=0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.frequency_bound (first conjunct, KAM/Uniq/Frame.lean:255) from KAM.Apost.frequency (KAM/Apost/Frame.lean:423) with eps=0
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P3-1-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p3:frequency-gamma
KIND: step
TITLE: Bound on $\gamma$
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:frequency-gamma@L188-L190
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:frequency-gamma@L188-L190
CONTRACT_ID: step:p3:frequency-gamma
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega in Dio_{gamma,tau}; |omega|<=Gamma
SOURCE_QUANTIFIERS: k=e_1
SOURCE_CONCLUSION: gamma<=|omega|<=Gamma
CONSTANT_SCOPE: Gamma as in the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frequency, bp:p0:diophantine#IsDiophantine, step:p3:frequency-omega
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frequency | blueprint/parts/p3-uniqueness.tex#step:p3:frequency-gamma@L189-L189 | gamma<=abs omegaabs 
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p3-uniqueness.tex#step:p3:frequency-gamma@L190-L190 | Diophantine inequality at k=e_1
EDGE: step:p3:frequency-omega | blueprint/parts/p3-uniqueness.tex#step:p3:frequency-gamma@L190-L190 | abs omegaabs <=Gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.frequency_bound (second conjunct, KAM/Uniq/Frame.lean:255)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P3-1-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: bp:p3:reducibility
KIND: lemma
TITLE: Exact reducibility
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:reducibility@L193-L203
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:reducibility@L205-L234
CONTRACT_ID: bp:p3:reducibility
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (S1)-(S3)
SOURCE_QUANTIFIERS: theta in T_rho
SOURCE_CONCLUSION: B,N,P holomorphic on T_rho; P invertible with P^{-1}=(BL^T;-L^T Omega_0), P^T Omega_0 P=Omega_0; T=BL^T X_N; DX_h(K_1)P-d_omega P=P Lambda with Lambda=(0 T;0 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:standing, step:p3:red-holomorphy, step:p3:red-frame, step:p3:red-tangent, step:p3:red-normal, step:p3:red-assembly
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#bp:p3:reducibility@L194-L194 | assumes (S1)-(S3)
EDGE: step:p3:red-holomorphy | blueprint/parts/p3-uniqueness.tex#bp:p3:reducibility@L206-L206 | proof step
EDGE: step:p3:red-frame | blueprint/parts/p3-uniqueness.tex#bp:p3:reducibility@L212-L212 | proof step
EDGE: step:p3:red-tangent | blueprint/parts/p3-uniqueness.tex#bp:p3:reducibility@L222-L222 | proof step
EDGE: step:p3:red-normal | blueprint/parts/p3-uniqueness.tex#bp:p3:reducibility@L226-L226 | proof step
EDGE: step:p3:red-assembly | blueprint/parts/p3-uniqueness.tex#bp:p3:reducibility@L231-L231 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.reducibility
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:red-holomorphy
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:red-holomorphy@L206-L210
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:red-holomorphy@L206-L210
CONTRACT_ID: step:p3:red-holomorphy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (S3): det(L^T L)!=0 on T_rho
SOURCE_QUANTIFIERS: on T_rho
SOURCE_CONCLUSION: L, L^T L, B=(L^T L)^{-1}, N, P are holomorphic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-regularity, bp:p1:holomorphic-inverse
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p3-uniqueness.tex#step:p3:red-holomorphy@L207-L207 | L=DK_1 holomorphic
EDGE: bp:p1:holomorphic-inverse | blueprint/parts/p3-uniqueness.tex#step:p3:red-holomorphy@L209-L209 | B holomorphic
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.reducibility (first three conjuncts, KAM/Uniq/Frame.lean:267: B, N, P holomorphic); KAM.Torus.differentiableOn_tangentMat, differentiableOn_gramMatrix (KAM/Torus/FrozenAgreement.lean:91,105) for L and L^T L
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P3-1-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p3:red-frame
KIND: step
TITLE: Symplectic frame
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:red-frame@L212-L220
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:red-frame@L212-L220
CONTRACT_ID: step:p3:red-frame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Omega_{K_1}=0 on T_rho; B symmetric
SOURCE_QUANTIFIERS: theta in T_rho
SOURCE_CONCLUSION: P^T Omega_0 P=Omega_0; P invertible with P^{-1}=Q=(BL^T;-L^T Omega_0); T=BL^T X_N
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:lagrangian, bp:p2:frame-identities, bp:p2:matrix
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:lagrangian | blueprint/parts/p3-uniqueness.tex#step:p3:red-frame@L213-L213 | E_sym=0 from Omega_{K_1}=0
EDGE: bp:p2:frame-identities | blueprint/parts/p3-uniqueness.tex#step:p3:red-frame@L214-L214 | (b) and (f): symplectic frame, QP=I
EDGE: bp:p2:matrix | blueprint/parts/p3-uniqueness.tex#step:p3:red-frame@L216-L216 | (d): formula for Q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.reducibility (KAM/Uniq/Frame.lean:267): IsUnit det P, P^{-1}=Q=(B L^T; -L^T Omega_0), P^T Omega_0 P = Omega_0, torsion = B L^T X_N
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P3-1-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p3:red-tangent
KIND: step
TITLE: Tangent columns
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:red-tangent@L222-L224
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:red-tangent@L222-L224
CONTRACT_ID: step:p3:red-tangent
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E_1=0 on T_rho
SOURCE_QUANTIFIERS: on T_rho
SOURCE_CONCLUSION: X_L=DX_h(K_1)L-d_omega L=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frame-identities
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frame-identities | blueprint/parts/p3-uniqueness.tex#step:p3:red-tangent@L223-L223 | (c) with E_1=0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: BYPASSED
LEAN_REF: none as a statement; ingredients KAM.Apost.frame_identities (d) (KAM/Apost/Identities.lean:445) and KAM.Uniq.FrameAux.errDerivMat_eq_zero (KAM/Uniq/Frame.lean:152)
LEAN_NOTE: route substitution (D27): X_L = DX_h L - d_omega L = 0 is never formed: reducibility uses frame_identities (e) with redDefect=0 (from DE_1=0) to get the assembled identity directly, so the column-wise step has no separate content. (docs/campaign/audits/P3-1-audit-1.md (reducibility parent only))
NOTE: -

NODE: step:p3:red-normal
KIND: step
TITLE: Normal columns
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:red-normal@L226-L229
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:red-normal@L226-L229
CONTRACT_ID: step:p3:red-normal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: DE_1=0 on T_rho; Q=P^{-1}
SOURCE_QUANTIFIERS: on T_rho
SOURCE_CONCLUSION: X_N=LT
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p2:frame-identities, step:p3:red-frame
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p2:frame-identities | blueprint/parts/p3-uniqueness.tex#step:p3:red-normal@L227-L227 | (e): Q(X_L X_N)=Lambda
EDGE: step:p3:red-frame | blueprint/parts/p3-uniqueness.tex#step:p3:red-normal@L229-L229 | Q^{-1}=P
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: BYPASSED
LEAN_REF: none as a statement; ingredients KAM.Apost.frame_identities (e) and KAM.Uniq.FrameAux.errDerivMat_eq_zero
LEAN_NOTE: route substitution (D27): X_N = L T is not stated; the last conjunct of reducibility is obtained from the reduced identity reducer*(A P - d_omega P)=Lambda+redDefect with redDefect=0, bypassing the column split. (docs/campaign/audits/P3-1-audit-1.md (reducibility parent only))
NOTE: -

NODE: step:p3:red-assembly
KIND: step
TITLE: Assembly
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:red-assembly@L231-L233
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:red-assembly@L231-L233
CONTRACT_ID: step:p3:red-assembly
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X_L=0 and X_N=LT
SOURCE_QUANTIFIERS: on T_rho
SOURCE_CONCLUSION: DX_h(K_1)P-d_omega P=P Lambda
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p3:red-tangent, step:p3:red-normal
ROUTES: -
ROUTE_FOR: -
EDGE: step:p3:red-tangent | blueprint/parts/p3-uniqueness.tex#step:p3:red-assembly@L232-L232 | columns (X_L X_N), X_L=0
EDGE: step:p3:red-normal | blueprint/parts/p3-uniqueness.tex#step:p3:red-assembly@L232-L232 | X_N=LT
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.reducibility, last conjunct (KAM/Uniq/Frame.lean:267): linMat*frameMat - d_omega frameMat = frameMat * triangularMat(torsion)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P3-1-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: bp:p3:torsion-bound
KIND: lemma
TITLE: The torsion
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:torsion-bound@L241-L245
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:torsion-bound@L247-L268
CONTRACT_ID: bp:p3:torsion-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (S1)-(S3)
SOURCE_QUANTIFIERS: n,tau,rho,M,sigma_K,sigma_B fixed; C_tor as in the setting
SOURCE_CONCLUSION: T holomorphic on T_rho, continuous on R^n, ||T||_{3rho/4}<=C_tor; T integrable on [0,1]^n and avg T in (S3) is the integral of a continuous function
CONSTANT_SCOPE: C_tor=C_P^2 M(1+4nC_P/rho), depends only on n,rho,M,sigma_K,sigma_B
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:standing, bp:p3:standing#constants, step:p3:torsion-holomorphy, step:p3:torsion-bound-step
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#bp:p3:torsion-bound@L242-L242 | assumes (S1)-(S3)
EDGE: bp:p3:standing#constants | blueprint/parts/p3-uniqueness.tex#bp:p3:torsion-bound@L243-L243 | C_tor
EDGE: step:p3:torsion-holomorphy | blueprint/parts/p3-uniqueness.tex#bp:p3:torsion-bound@L248-L248 | proof step
EDGE: step:p3:torsion-bound-step | blueprint/parts/p3-uniqueness.tex#bp:p3:torsion-bound@L254-L254 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.torsion_bound
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:torsion-holomorphy
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:torsion-holomorphy@L248-L252
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:torsion-holomorphy@L248-L252
CONTRACT_ID: step:p3:torsion-holomorphy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed parameters of Part 3 at L50; hypotheses (S1)-(S3) of bp:p3:standing; the frame and torsion objects at K_1 have the definitions at L81-L88
SOURCE_QUANTIFIERS: on T_rho
SOURCE_CONCLUSION: X_N and T=BL^T X_N are holomorphic, hence continuous on R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:reducibility, bp:p2:hamiltonian, bp:p1:holomorphic-regularity, bp:p3:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:reducibility | blueprint/parts/p3-uniqueness.tex#step:p3:torsion-holomorphy@L249-L249 | N holomorphic; T=BL^T X_N
EDGE: bp:p2:hamiltonian | blueprint/parts/p3-uniqueness.tex#step:p3:torsion-holomorphy@L250-L251 | (a) gives holomorphic X_h on the open domain; the derivative-regularity edge gives holomorphic DX_h
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p3-uniqueness.tex#step:p3:torsion-holomorphy@L249-L251 | derivatives of N and X_h are holomorphic on the relevant open domains
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#step:p3:torsion-holomorphy@L249-L252 | S1-S3 supply the Part 2 Hamiltonian package and holomorphic K_1 with its image in the open ambient domain for composition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.torsion_bound (first two conjuncts, KAM/Uniq/Frame.lean:313: T holomorphic on T_rho, continuous on R^n); X_N via KAM.Apost.FrameAux.differentiableOn_normalFieldMat (used inside torsion_bound)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P3-1-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p3:torsion-bound-step
KIND: step
TITLE: Bound
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:torsion-bound-step@L254-L267
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:torsion-bound-step@L254-L267
CONTRACT_ID: step:p3:torsion-bound-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ||N||_rho<=sigma_K sigma_B; |omega|<=Gamma; |DX_h|<=M; |BL^T|<=C_P
SOURCE_QUANTIFIERS: strip T_{3rho/4}, delta=rho/4
SOURCE_CONCLUSION: ||d_omega N||<=4n Gamma sigma_K sigma_B/rho; ||X_N||_{3rho/4}<=sigma_K sigma_B M(1+4nC_P/rho); ||T||_{3rho/4}<=C_tor
CONSTANT_SCOPE: C_tor as in the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:matrix-norms, bp:p1:cauchy-strip, bp:p3:frequency-bound, bp:p3:reducibility
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:matrix-norms | blueprint/parts/p3-uniqueness.tex#step:p3:torsion-bound-step@L255-L255 | abs abs Nabs abs <=sigma_K sigma_B and abs BL^Tabs <=C_P
EDGE: bp:p1:cauchy-strip | blueprint/parts/p3-uniqueness.tex#step:p3:torsion-bound-step@L255-L255 | Cauchy estimate with delta=rho/4
EDGE: bp:p3:frequency-bound | blueprint/parts/p3-uniqueness.tex#step:p3:torsion-bound-step@L257-L257 | abs omegaabs <=Gamma
EDGE: bp:p3:reducibility | blueprint/parts/p3-uniqueness.tex#step:p3:torsion-bound-step@L265-L265 | T=BL^T X_N
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.torsion_bound (third conjunct, KAM/Uniq/Frame.lean:313) with local facts hdir' (Cauchy, delta=rho/4, via KAM.cauchy_corollaries_directional_real) and hX in its proof
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P3-1-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: bp:p3:phase
KIND: lemma
TITLE: Phase normalization
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:phase@L279-L288
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:phase@L290-L342
CONTRACT_ID: bp:p3:phase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (S1)-(S4); eta=sup_{T_rho}|K_2-K_1| satisfies eta<=rho/(4nC_P(1+2C_P sigma_K))
SOURCE_QUANTIFIERS: real shifts psi; constants as in the setting
SOURCE_CONCLUSION: exists psi in R^n with |psi|<=2C_P eta and avg(BL^T(K_2(.+psi)-K_1))=0
CONSTANT_SCOPE: C_P depends only on n,sigma_K,sigma_B
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:standing, bp:p3:standing#constants, step:p3:phase-real, step:p3:phase-fixed-point, step:p3:phase-derivatives, step:p3:phase-contraction, step:p3:phase-conclusion
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#bp:p3:phase@L280-L280 | assumes (S1)-(S4)
EDGE: bp:p3:standing#constants | blueprint/parts/p3-uniqueness.tex#bp:p3:phase@L280-L280 | C_P
EDGE: step:p3:phase-real | blueprint/parts/p3-uniqueness.tex#bp:p3:phase@L294-L294 | proof step
EDGE: step:p3:phase-fixed-point | blueprint/parts/p3-uniqueness.tex#bp:p3:phase@L302-L302 | proof step
EDGE: step:p3:phase-derivatives | blueprint/parts/p3-uniqueness.tex#bp:p3:phase@L314-L314 | proof step
EDGE: step:p3:phase-contraction | blueprint/parts/p3-uniqueness.tex#bp:p3:phase@L322-L322 | proof step
EDGE: step:p3:phase-conclusion | blueprint/parts/p3-uniqueness.tex#bp:p3:phase@L339-L339 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.phase (def KAM.Uniq.diffMap)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:phase-real
KIND: step
TITLE: Realness
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:phase-real@L294-L300
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:phase-real@L294-L300
CONTRACT_ID: step:p3:phase-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K_1,K_2 real on reals (S3),(S4); W=K_2-K_1 holomorphic, periodic, bounded by eta
SOURCE_QUANTIFIERS: theta, psi in R^n
SOURCE_CONCLUSION: L, L^T L, B real on R^n; averages of the two integrands are real and the integrands continuous on R^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:real-inverse
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:real-inverse | blueprint/parts/p3-uniqueness.tex#step:p3:phase-real@L297-L297 | B real as inverse of real matrix
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.PhaseAux.im_integrand
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:phase-fixed-point
KIND: step
TITLE: Fixed-point form
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:phase-fixed-point@L302-L312
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:phase-fixed-point@L302-L312
CONTRACT_ID: step:p3:phase-fixed-point
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed parameters of Part 3 at L50; hypotheses (S1)-(S4) of bp:p3:standing; eta=sup_{T_rho}|K_2-K_1|; eta<=rho/(4n C_P(1+2 C_P sigma_K)); W=K_2-K_1; frame objects have their source definitions
SOURCE_QUANTIFIERS: theta,psi in R^n
SOURCE_CONCLUSION: normalization holds iff Phi(psi)=psi for Phi(psi)=-avg(BL^T(W(.+psi)+K_1(.+psi)-K_1-L psi))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p3:phase-real, bp:p3:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p3:phase-real | blueprint/parts/p3-uniqueness.tex#step:p3:phase-fixed-point@L308-L310 | the two averaged integrands are real, so Phi is a map R^n to R^n
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3+sol-review-r1
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.PhaseAux.exists_fixedPoint
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#step:p3:phase-fixed-point@L303-L306 | B=(L^T L)^{-1} at L85 and invertibility in S3 give BL^T L=I for the fixed-point identity

NODE: step:p3:phase-derivatives
KIND: step
TITLE: Derivative bounds on the real torus
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:phase-derivatives@L314-L320
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:phase-derivatives@L314-L320
CONTRACT_ID: step:p3:phase-derivatives
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W holomorphic on T_rho bounded by eta; L holomorphic bounded by sigma_K
SOURCE_QUANTIFIERS: theta,y,y' in R^n
SOURCE_CONCLUSION: |W(theta+y)-W(theta+y')|<=(2n eta/rho)|y-y'| and |L(theta+y)-L(theta)|<=(2n sigma_K/rho)|y|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:increments, bp:p1:holomorphic-regularity
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:increments | blueprint/parts/p3-uniqueness.tex#step:p3:phase-derivatives@L315-L315 | increment estimate with delta=rho/2
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p3-uniqueness.tex#step:p3:phase-derivatives@L316-L316 | L holomorphic
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.PhaseAux.norm_sub_le_real, norm_taylor_defect_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:phase-contraction
KIND: step
TITLE: Contraction
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:phase-contraction@L322-L337
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:phase-contraction@L322-L337
CONTRACT_ID: step:p3:phase-contraction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed parameters of Part 3 at L50; hypotheses (S1)-(S4) of bp:p3:standing; eta=sup_{T_rho}|K_2-K_1|; eta<=rho/(4n C_P(1+2 C_P sigma_K)); W=K_2-K_1; frame objects have their source definitions; Phi is defined at L308-L310; Y={psi in R^n: |psi|<=2 C_P eta}
SOURCE_QUANTIFIERS: psi,psi' in Y
SOURCE_CONCLUSION: Phi maps Y into Y and is a contraction with constant 1/2
CONSTANT_SCOPE: C_P as in the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p3:phase-derivatives, step:p3:phase-fixed-point, bp:p3:matrix-norms, bp:p1:ext-integral, bp:p3:standing
ROUTES: -
ROUTE_FOR: -
EDGE: step:p3:phase-derivatives | blueprint/parts/p3-uniqueness.tex#step:p3:phase-contraction@L328-L328 | Lipschitz bounds on W and L
EDGE: step:p3:phase-fixed-point | blueprint/parts/p3-uniqueness.tex#step:p3:phase-contraction@L332-L332 | definition of Phi
EDGE: bp:p3:matrix-norms | blueprint/parts/p3-uniqueness.tex#step:p3:phase-contraction@L330-L330 | abs BL^Tabs <=C_P
EDGE: bp:p1:ext-integral | blueprint/parts/p3-uniqueness.tex#step:p3:phase-contraction@L325-L336 | fundamental theorem of calculus along the real segment and norm-of-integral bounds for the segment integral and the averages
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#step:p3:phase-contraction@L323-L337 | the inherited phase-lemma package fixes the reference frame and real tori used in the segment integral; the local phase-small bound is L281-L282
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.PhaseAux.norm_phaseMap_sub_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:phase-conclusion
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:phase-conclusion@L339-L341
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:phase-conclusion@L339-L341
CONTRACT_ID: step:p3:phase-conclusion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Phi maps the closed set Y into itself and is a contraction
SOURCE_QUANTIFIERS: Y complete metric space
SOURCE_CONCLUSION: exists psi in Y with Phi(psi)=psi, i.e. the normalization
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-banach, step:p3:phase-fixed-point, step:p3:phase-contraction
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-banach | blueprint/parts/p3-uniqueness.tex#step:p3:phase-conclusion@L340-L340 | Banach fixed point theorem
EDGE: step:p3:phase-fixed-point | blueprint/parts/p3-uniqueness.tex#step:p3:phase-conclusion@L341-L341 | fixed point equals normalization
EDGE: step:p3:phase-contraction | blueprint/parts/p3-uniqueness.tex#step:p3:phase-conclusion@L340-L340 | Phi maps Y to Y, contraction
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.phase
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p3:difference-equation
KIND: lemma
TITLE: The difference in the frame
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:difference-equation@L350-L373
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:difference-equation@L375-L406
CONTRACT_ID: bp:p3:difference-equation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (S1)-(S4); psi in R^n; Delta=K_2(.+psi)-K_1 with ||Delta||_rho<mu
SOURCE_QUANTIFIERS: R, xi=P^{-1}Delta, q=P^{-1}R defined on T_rho
SOURCE_CONCLUSION: (a) Delta,xi,q holomorphic; Delta,xi 1-periodic; Delta=P xi; (b) d_omega xi^L=T xi^N+q^L, d_omega xi^N=q^N; (c) |xi|<=C_P|Delta|, |Delta|<=C_P|xi|, |q|<=(1/2)C_P M|Delta|^2
CONSTANT_SCOPE: C_P depends only on n,sigma_K,sigma_B
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:standing, bp:p3:standing#constants, step:p3:diff-regularity, step:p3:diff-linearized, step:p3:diff-triangular, step:p3:diff-bounds
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#bp:p3:difference-equation@L360-L360 | assumes (S1)-(S4)
EDGE: bp:p3:standing#constants | blueprint/parts/p3-uniqueness.tex#bp:p3:difference-equation@L371-L371 | C_P
EDGE: step:p3:diff-regularity | blueprint/parts/p3-uniqueness.tex#bp:p3:difference-equation@L376-L376 | proof step
EDGE: step:p3:diff-linearized | blueprint/parts/p3-uniqueness.tex#bp:p3:difference-equation@L386-L386 | proof step
EDGE: step:p3:diff-triangular | blueprint/parts/p3-uniqueness.tex#bp:p3:difference-equation@L393-L393 | proof step
EDGE: step:p3:diff-bounds | blueprint/parts/p3-uniqueness.tex#bp:p3:difference-equation@L399-L399 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3+sol-review-r3
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.difference_equation (defs remainder, diffXi, diffQ; diffMap in Uniq/Phase)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:diff-regularity
KIND: step
TITLE: Regularity and periodicity
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:diff-regularity@L376-L384
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:diff-regularity@L376-L384
CONTRACT_ID: step:p3:diff-regularity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed parameters of Part 3 at L50; hypotheses (S1)-(S4) of bp:p3:standing; psi in R^n; Delta(theta)=K_2(theta+psi)-K_1(theta) on T_rho; ||Delta||_rho<mu; R=X_h(K_1+Delta)-X_h(K_1)-DX_h(K_1)Delta, xi=P^{-1}Delta and q=P^{-1}R are the constructions at L363-L367
SOURCE_QUANTIFIERS: theta in T_rho
SOURCE_CONCLUSION: Delta,xi,q holomorphic; Delta,xi 1-periodic; Delta=P xi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:reducibility, bp:p2:periodicity, bp:p2:hamiltonian, bp:p1:holomorphic-regularity, bp:p3:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:reducibility | blueprint/parts/p3-uniqueness.tex#step:p3:diff-regularity@L382-L382 | P^{-1} holomorphic, explicit formula
EDGE: bp:p2:periodicity | blueprint/parts/p3-uniqueness.tex#step:p3:diff-regularity@L384-L384 | L is 1-periodic
EDGE: bp:p2:hamiltonian | blueprint/parts/p3-uniqueness.tex#step:p3:diff-regularity@L378-L380 | S1-S2 supply the Part 2 standing package; X_h is holomorphic on B and the ball inclusion puts the composed arguments there
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p3-uniqueness.tex#step:p3:diff-regularity@L380-L380 | DX_h is holomorphic because X_h is holomorphic on the open domain, so the remainder R is holomorphic
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#step:p3:diff-regularity@L377-L384 | S3-S4 supply holomorphy and primarity of both tori, and S3 supplies the radius-mu ball in the ambient domain
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.DiffAux.step_regularity
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:diff-linearized
KIND: step
TITLE: Linearized equation
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:diff-linearized@L386-L391
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:diff-linearized@L386-L391
CONTRACT_ID: step:p3:diff-linearized
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E_1=E_2=0 (S3),(S4)
SOURCE_QUANTIFIERS: theta in T_rho
SOURCE_CONCLUSION: d_omega Delta=DX_h(K_1)Delta+R
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.DiffAux.step_linearized
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:diff-triangular
KIND: step
TITLE: Triangular system
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:diff-triangular@L393-L397
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:diff-triangular@L393-L397
CONTRACT_ID: step:p3:diff-triangular
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed parameters of Part 3 at L50; hypotheses (S1)-(S4) of bp:p3:standing; psi in R^n; Delta(theta)=K_2(theta+psi)-K_1(theta) on T_rho; ||Delta||_rho<mu; R=X_h(K_1+Delta)-X_h(K_1)-DX_h(K_1)Delta, xi=P^{-1}Delta and q=P^{-1}R are the constructions at L363-L367
SOURCE_QUANTIFIERS: on T_rho
SOURCE_CONCLUSION: d_omega xi=Lambda xi+q, i.e. part (b)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:reducibility, step:p3:diff-linearized, step:p3:diff-regularity, bp:p3:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:reducibility | blueprint/parts/p3-uniqueness.tex#step:p3:diff-triangular@L395-L395 | triangular reduction identity
EDGE: step:p3:diff-linearized | blueprint/parts/p3-uniqueness.tex#step:p3:diff-triangular@L394-L394 | linearized equation for Delta
EDGE: step:p3:diff-regularity | blueprint/parts/p3-uniqueness.tex#step:p3:diff-triangular@L394-L394 | the established identity Delta=P xi permits substitution into the differential equation
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#step:p3:diff-triangular@L394-L397 | S1-S3 are the local source package for the exact reducibility application; S4 is inherited from the difference-lemma data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.DiffAux.step_triangular (fderiv_diffXi_eq)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:diff-bounds
KIND: step
TITLE: Bounds
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:diff-bounds@L399-L405
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:diff-bounds@L399-L405
CONTRACT_ID: step:p3:diff-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed parameters of Part 3 at L50; hypotheses (S1)-(S4) of bp:p3:standing; psi in R^n; Delta(theta)=K_2(theta+psi)-K_1(theta) on T_rho; ||Delta||_rho<mu; R=X_h(K_1+Delta)-X_h(K_1)-DX_h(K_1)Delta, xi=P^{-1}Delta and q=P^{-1}R are the constructions at L363-L367
SOURCE_QUANTIFIERS: theta in T_rho
SOURCE_CONCLUSION: |xi|<=C_P|Delta|, |Delta|<=C_P|xi|, |R|<=(1/2)M|Delta|^2, |q|<=(1/2)C_P M|Delta|^2
CONSTANT_SCOPE: C_P as in the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:matrix-norms, bp:p1:taylor, bp:p2:hamiltonian, step:p3:diff-regularity, bp:p1:holomorphic-regularity, bp:p3:reducibility, bp:p3:standing
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:matrix-norms | blueprint/parts/p3-uniqueness.tex#step:p3:diff-bounds@L401-L401 | abs Pabs ,abs P^{-1}abs <=C_P
EDGE: bp:p1:taylor | blueprint/parts/p3-uniqueness.tex#step:p3:diff-bounds@L401-L401 | second-order Taylor bound on R
EDGE: bp:p2:hamiltonian | blueprint/parts/p3-uniqueness.tex#step:p3:diff-bounds@L402-L402 | (a): X_h holomorphic on B
EDGE: step:p3:diff-regularity | blueprint/parts/p3-uniqueness.tex#step:p3:diff-bounds@L403-L403 | segment lies in B
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p3-uniqueness.tex#step:p3:diff-bounds@L405-L405 | abs D^2X_habs =abs D(DX_h)abs
EDGE: bp:p3:reducibility | blueprint/parts/p3-uniqueness.tex#step:p3:diff-bounds@L400-L401 | P^{-1}=(BL^T;-L^T Omega_0), so the stacked-matrix bound of matrix-norms applies to P^{-1}
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#step:p3:diff-bounds@L400-L405 | S1 supplies the bilinear second-derivative bound M in the Taylor application; S3 supplies the frame bounds
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.DiffAux.step_bounds
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p3:quadratic
KIND: proposition
TITLE: Quadratic estimate
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic@L415-L425
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic@L427-L500
CONTRACT_ID: bp:p3:quadratic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (S1)-(S4); psi in R^n; Delta=K_2(.+psi)-K_1 with ||Delta||_rho<mu and avg(BL^T Delta)=0
SOURCE_QUANTIFIERS: psi real; 0<rho''<rho'<=3rho/4, delta=(rho'-rho'')/2; C_quad as in the setting
SOURCE_CONCLUSION: ||Delta||_{rho''}<=C_quad gamma^{-2} delta^{-2(tau+n)} ||Delta||_{rho'}^2
CONSTANT_SCOPE: C_quad depends only on n,tau,rho,M,sigma_K,sigma_B,sigma_T, not on gamma, mu, psi, rho', rho''
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:standing, bp:p3:standing#constants, bp:p3:difference-equation, bp:p3:quadratic#absorb, step:p3:quad-remainder, step:p3:quad-normal-osc, step:p3:quad-normal-avg, step:p3:quad-normal, step:p3:quad-tangent, step:p3:quad-combine
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic@L416-L416 | assumes (S1)-(S4)
EDGE: bp:p3:standing#constants | blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic@L421-L421 | C_quad
EDGE: bp:p3:difference-equation | blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic@L428-L428 | xi, q and their equations
EDGE: bp:p3:quadratic#absorb | blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic@L431-L431 | absorption inequality used repeatedly
EDGE: step:p3:quad-remainder | blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic@L435-L435 | proof step
EDGE: step:p3:quad-normal-osc | blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic@L438-L438 | proof step
EDGE: step:p3:quad-normal-avg | blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic@L450-L450 | proof step
EDGE: step:p3:quad-normal | blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic@L463-L463 | proof step
EDGE: step:p3:quad-tangent | blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic@L470-L470 | proof step
EDGE: step:p3:quad-combine | blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic@L488-L488 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.quadratic
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:quad-remainder
KIND: step
TITLE: The remainder
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:quad-remainder@L435-L436
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:quad-remainder@L435-L436
CONTRACT_ID: step:p3:quad-remainder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |q|<=(1/2)C_P M|Delta|^2 on T_rho
SOURCE_QUANTIFIERS: on T_rho'
SOURCE_CONCLUSION: ||q||_{rho'}<=(1/2)C_P M ||Delta||_{rho'}^2
CONSTANT_SCOPE: C_P as in the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:difference-equation
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:difference-equation | blueprint/parts/p3-uniqueness.tex#step:p3:quad-remainder@L436-L436 | (c) bound on q
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: inside KAM.Uniq.quadratic
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:quad-normal-osc
KIND: step
TITLE: Oscillating part of the normal coordinate
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-osc@L438-L448
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-osc@L438-L448
CONTRACT_ID: step:p3:quad-normal-osc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d_omega xi^N=q^N; xi^N holomorphic, bounded, 1-periodic on T_rho'
SOURCE_QUANTIFIERS: delta; strips T_rho', T_{rho'-delta}
SOURCE_CONCLUSION: avg q^N=0 and ||xi^N-avg xi^N||_{rho'-delta}<=(1/2)C_P M C_coh gamma^{-1} delta^{-(tau+n)}||Delta||_rho'^2
CONSTANT_SCOPE: C_coh=c(n,tau)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:difference-equation, bp:p1:averages, bp:p1:cohomological, step:p3:quad-remainder
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:difference-equation | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-osc@L440-L440 | (b): d_omega xi^N=q^N, regularity
EDGE: bp:p1:averages | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-osc@L441-L441 | avg of d_omega of a periodic function is 0
EDGE: bp:p1:cohomological | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-osc@L443-L443 | uniqueness and estimate
EDGE: step:p3:quad-remainder | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-osc@L447-L447 | abs abs q^Nabs abs <=(1/2)C_P Mabs abs Deltaabs abs ^2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.QuadAux.osc_bound
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:quad-normal-avg
KIND: step
TITLE: Average of the normal coordinate
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-avg@L450-L461
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-avg@L450-L461
CONTRACT_ID: step:p3:quad-normal-avg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d_omega xi^L=T xi^N+q^L; avg T invertible, |avg T^{-1}|<=sigma_T-mu; |T|<=C_tor on real theta
SOURCE_QUANTIFIERS: averages over [0,1]^n
SOURCE_CONCLUSION: avg xi^N=-avg T^{-1}(avg(T xi~^N)+avg q^L); |avg xi^N|<=sigma_T(C_tor||xi~^N||+(1/2)C_P M||Delta||_rho'^2)
CONSTANT_SCOPE: C_tor,sigma_T as in the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:difference-equation, bp:p1:averages, bp:p3:torsion-bound, step:p3:quad-normal-osc, step:p3:quad-remainder
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:difference-equation | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-avg@L453-L453 | (b): equation for xi^L
EDGE: bp:p1:averages | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-avg@L452-L452 | avg d_omega xi^L=0
EDGE: bp:p3:torsion-bound | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-avg@L459-L459 | abs Tabs <=C_tor
EDGE: step:p3:quad-normal-osc | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-avg@L453-L453 | splitting xi^N, bound on xi~^N
EDGE: step:p3:quad-remainder | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal-avg@L461-L461 | bound on q^L
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.QuadAux.norm_avg_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:quad-normal
KIND: step
TITLE: The normal coordinate
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal@L463-L468
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal@L463-L468
CONTRACT_ID: step:p3:quad-normal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: bounds on xi~^N and avg xi^N; eq:p3:absorb
SOURCE_QUANTIFIERS: strip T_{rho'-delta}
SOURCE_CONCLUSION: ||xi^N||_{rho'-delta}<=C^N gamma^{-1} delta^{-(tau+n)}||Delta||_rho'^2
CONSTANT_SCOPE: C^N as in the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p3:quad-normal-osc, step:p3:quad-normal-avg, bp:p3:quadratic#absorb, bp:p3:standing#constants
ROUTES: -
ROUTE_FOR: -
EDGE: step:p3:quad-normal-osc | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal@L464-L464 | oscillating part
EDGE: step:p3:quad-normal-avg | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal@L464-L464 | average part
EDGE: bp:p3:quadratic#absorb | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal@L464-L464 | absorb term without small divisor
EDGE: bp:p3:standing#constants | blueprint/parts/p3-uniqueness.tex#step:p3:quad-normal@L467-L467 | C^N
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.QuadAux.normal_bound + local hN in KAM.Uniq.quadratic
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:quad-tangent
KIND: step
TITLE: The tangential coordinate
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:quad-tangent@L470-L486
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:quad-tangent@L470-L486
CONTRACT_ID: step:p3:quad-tangent
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g=d_omega xi^L=T xi^N+q^L; avg xi^L=0 by hypothesis; |T|<=C_tor on T_{3rho/4}
SOURCE_QUANTIFIERS: strips T_{rho'-delta}, T_{rho''}
SOURCE_CONCLUSION: ||xi^L||_{rho''}<=C^L gamma^{-2} delta^{-2(tau+n)}||Delta||_rho'^2
CONSTANT_SCOPE: C^L, C_coh as in the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:difference-equation, step:p3:quad-normal-avg, step:p3:quad-normal, bp:p3:torsion-bound, step:p3:quad-remainder, bp:p3:quadratic#absorb, bp:p1:cohomological, bp:p3:standing#constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:difference-equation | blueprint/parts/p3-uniqueness.tex#step:p3:quad-tangent@L471-L471 | (b): d_omega xi^L=g
EDGE: step:p3:quad-normal-avg | blueprint/parts/p3-uniqueness.tex#step:p3:quad-tangent@L472-L472 | g has zero average
EDGE: step:p3:quad-normal | blueprint/parts/p3-uniqueness.tex#step:p3:quad-tangent@L479-L479 | bound on xi^N
EDGE: bp:p3:torsion-bound | blueprint/parts/p3-uniqueness.tex#step:p3:quad-tangent@L475-L475 | abs Tabs <=C_tor on T_{3rho/4}
EDGE: step:p3:quad-remainder | blueprint/parts/p3-uniqueness.tex#step:p3:quad-tangent@L475-L475 | bound on q^L
EDGE: bp:p3:quadratic#absorb | blueprint/parts/p3-uniqueness.tex#step:p3:quad-tangent@L476-L476 | absorb term without small divisor
EDGE: bp:p1:cohomological | blueprint/parts/p3-uniqueness.tex#step:p3:quad-tangent@L481-L481 | uniqueness and estimate for xi^L
EDGE: bp:p3:standing#constants | blueprint/parts/p3-uniqueness.tex#step:p3:quad-tangent@L485-L485 | C^L
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: inside KAM.Uniq.quadratic
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:quad-combine
KIND: step
TITLE: Return to $\Delta$
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:quad-combine@L488-L499
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:quad-combine@L488-L499
CONTRACT_ID: step:p3:quad-combine
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: bounds on xi^L and xi^N; Delta=P xi; |P|<=C_P
SOURCE_QUANTIFIERS: strip T_{rho''}
SOURCE_CONCLUSION: ||Delta||_{rho''}<=C_quad gamma^{-2} delta^{-2(tau+n)}||Delta||_rho'^2
CONSTANT_SCOPE: C_quad as in the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p3:quad-normal, step:p3:quad-tangent, bp:p3:quadratic#absorb, bp:p3:difference-equation, bp:p3:matrix-norms, bp:p3:standing#constants
ROUTES: -
ROUTE_FOR: -
EDGE: step:p3:quad-normal | blueprint/parts/p3-uniqueness.tex#step:p3:quad-combine@L489-L489 | bound on xi^N
EDGE: step:p3:quad-tangent | blueprint/parts/p3-uniqueness.tex#step:p3:quad-combine@L496-L496 | bound on xi^L
EDGE: bp:p3:quadratic#absorb | blueprint/parts/p3-uniqueness.tex#step:p3:quad-combine@L489-L489 | absorb for xi^N
EDGE: bp:p3:difference-equation | blueprint/parts/p3-uniqueness.tex#step:p3:quad-combine@L494-L494 | Delta=P xi
EDGE: bp:p3:matrix-norms | blueprint/parts/p3-uniqueness.tex#step:p3:quad-combine@L494-L494 | abs Pabs <=C_P
EDGE: bp:p3:standing#constants | blueprint/parts/p3-uniqueness.tex#step:p3:quad-combine@L499-L499 | definition of C_quad
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: inside KAM.Uniq.quadratic
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:g2-constant
KIND: step
TITLE: Choice of the threshold
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:g2-constant@L513-L524
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:g2-constant@L513-L524
CONTRACT_ID: step:p3:g2-constant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G2 hypotheses: (S1)-(S4) data and closeness; constants of the setting
SOURCE_QUANTIFIERS: n,tau,rho,M,sigma_K,sigma_B,sigma_T,mu fixed first; then c; then data B,h,K_1,K_2,omega,gamma
SOURCE_CONCLUSION: c := (1/(1+2C_P sigma_K)) min{...} (eq:p3:c) is >0 and depends only on n,tau,rho,M,sigma_K,sigma_B,sigma_T,mu; the data satisfy bp:p3:standing and eta<=c gamma^2 rho^{2tau}
CONSTANT_SCOPE: c depends only on n,tau,rho,M,sigma_K,sigma_B,sigma_T,mu; not on gamma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:standing, bp:p3:standing#constants
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:standing | blueprint/parts/p3-uniqueness.tex#step:p3:g2-constant@L520-L520 | hypotheses of G2 give the standing package
EDGE: bp:p3:standing#constants | blueprint/parts/p3-uniqueness.tex#step:p3:g2-constant@L514-L514 | constants enter the definition of c
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.threshold (Uniq/Standing)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:g2-smallness
KIND: step
TITLE: The three smallness conditions
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:g2-smallness@L526-L533
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:g2-smallness@L526-L533
CONTRACT_ID: step:p3:g2-smallness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eta<=c gamma^2 rho^{2tau}; gamma<=Gamma
SOURCE_QUANTIFIERS: eta, c as in the previous step
SOURCE_CONCLUSION: eta<=rho/(4nC_P(1+2C_P sigma_K)); (1+2C_P sigma_K)eta<=mu/2; (1+2C_P sigma_K)eta<=gamma^2(rho/32)^{2(tau+n)}/(2C_quad)
CONSTANT_SCOPE: c depends only on n,tau,rho,M,sigma_K,sigma_B,sigma_T,mu
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:frequency-bound, step:p3:g2-constant
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:frequency-bound | blueprint/parts/p3-uniqueness.tex#step:p3:g2-smallness@L527-L527 | gamma<=Gamma gives eta<=c Gamma^2 rho^{2tau}
EDGE: step:p3:g2-constant | blueprint/parts/p3-uniqueness.tex#step:p3:g2-smallness@L528-L528 | the three terms of the minimum in (eq:p3:c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.g2_explicit (g2_smallness)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:g2-phase
KIND: step
TITLE: Phase
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:g2-phase@L535-L538
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:g2-phase@L535-L538
CONTRACT_ID: step:p3:g2-phase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: first smallness condition; (S1)-(S4)
SOURCE_QUANTIFIERS: Lemma phase applied to eta
SOURCE_CONCLUSION: exists psi in R^n with |psi|<=2C_P eta and avg(BL^T Delta)=0, Delta=K_2(.+psi)-K_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:phase, step:p3:g2-smallness, step:p3:g2-constant
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:phase | blueprint/parts/p3-uniqueness.tex#step:p3:g2-phase@L536-L536 | phase normalization
EDGE: step:p3:g2-smallness | blueprint/parts/p3-uniqueness.tex#step:p3:g2-phase@L536-L536 | first smallness condition
EDGE: step:p3:g2-constant | blueprint/parts/p3-uniqueness.tex#step:p3:g2-phase@L536-L536 | data satisfy the standing package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.g2_explicit (phase)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:g2-size
KIND: step
TITLE: Size of the difference
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:g2-size@L540-L547
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:g2-size@L540-L547
CONTRACT_ID: step:p3:g2-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |psi|<=2C_P eta; (1+2C_P sigma_K)eta<=mu/2; |DK_1|<=sigma_K on convex open T_rho
SOURCE_QUANTIFIERS: theta in T_rho
SOURCE_CONCLUSION: ||Delta||_rho<=(1+2C_P sigma_K)eta<=mu/2<mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:increments-open, step:p3:g2-phase, step:p3:g2-smallness
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:increments-open | blueprint/parts/p3-uniqueness.tex#step:p3:g2-size@L543-L543 | K_1(theta+psi)-K_1(theta) bounded on convex T_rho
EDGE: step:p3:g2-phase | blueprint/parts/p3-uniqueness.tex#step:p3:g2-size@L541-L541 | abs psiabs <=2C_P eta
EDGE: step:p3:g2-smallness | blueprint/parts/p3-uniqueness.tex#step:p3:g2-size@L544-L544 | second condition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.g2_explicit
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:g2-iteration
KIND: step
TITLE: Iteration on shrinking strips
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:g2-iteration@L549-L563
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:g2-iteration@L549-L563
CONTRACT_ID: step:p3:g2-iteration
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: ||Delta||_rho<mu; avg(BL^T Delta)=0; third smallness condition; rho_m=(1/2+2^{-m-2})rho
SOURCE_QUANTIFIERS: m>=0; y_m=||Delta||_{rho_m}; Q=C_quad gamma^{-2}(rho/16)^{-2(tau+n)}, p=2(tau+n)
SOURCE_CONCLUSION: y_{m+1}<=Q 2^{pm} y_m^2, Q 2^p y_0<=1/2, y_m->0, hence Delta=0 on T_{rho/2}
CONSTANT_SCOPE: Q depends on gamma through gamma^{-2}; absorbed by the third smallness condition
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:quadratic, step:p3:g2-size, step:p3:g2-phase, step:p3:g2-smallness, step:p3:g2-constant, bp:p1:iteration
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:quadratic | blueprint/parts/p3-uniqueness.tex#step:p3:g2-iteration@L552-L552 | quadratic estimate on rho_m, rho_{m+1}
EDGE: step:p3:g2-size | blueprint/parts/p3-uniqueness.tex#step:p3:g2-iteration@L558-L558 | abs abs Deltaabs abs _rho<mu and bound on y_0
EDGE: step:p3:g2-phase | blueprint/parts/p3-uniqueness.tex#step:p3:g2-iteration@L552-L552 | average hypothesis of the quadratic estimate
EDGE: step:p3:g2-smallness | blueprint/parts/p3-uniqueness.tex#step:p3:g2-iteration@L558-L558 | third condition gives Q 2^p y_0<=1/2
EDGE: step:p3:g2-constant | blueprint/parts/p3-uniqueness.tex#step:p3:g2-iteration@L552-L552 | standing package for the data
EDGE: bp:p1:iteration | blueprint/parts/p3-uniqueness.tex#step:p3:g2-iteration@L562-L562 | quadratic iteration gives y_m->0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.G2Aux.diffMap_eq_zero (majorant, quadratic_iteration)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p3:g2-conclusion
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:g2-conclusion@L565-L567
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#step:p3:g2-conclusion@L565-L567
CONTRACT_ID: step:p3:g2-conclusion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Delta=0 on T_{rho/2}; psi real
SOURCE_QUANTIFIERS: phi:=-psi in R^n
SOURCE_CONCLUSION: K_2=K_1(.+phi) on T_{rho/2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p3:g2-iteration, step:p3:g2-phase
ROUTES: -
ROUTE_FOR: -
EDGE: step:p3:g2-iteration | blueprint/parts/p3-uniqueness.tex#step:p3:g2-conclusion@L566-L566 | Delta=0 on T_{rho/2}
EDGE: step:p3:g2-phase | blueprint/parts/p3-uniqueness.tex#step:p3:g2-conclusion@L566-L566 | psi real, so phi real
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.g2_explicit (φ = −ψ)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p3:standing#constants
KIND: step
TITLE: Constants of Part 3
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:standing#constants@L95-L117
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:standing#constants@L95-L117
CONTRACT_ID: bp:p3:standing#constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=2, tau>=n-1, rho>0, M,sigma_K,sigma_B,sigma_T>0; c(n,tau) is the constant of bp:p1:cohomological; no B,h,K_1,K_2,omega,gamma or package (S1)-(S4) is assumed
SOURCE_QUANTIFIERS: n,tau,rho,M,sigma_K,sigma_B,sigma_T fixed before any data; then C_P, Gamma, C_tor, C_coh, C^N, C^L, C_quad
SOURCE_CONCLUSION: defines C_P=2n sigma_K(1+sigma_B), Gamma=C_P M, C_tor=C_P^2 M(1+4n C_P/rho), C_coh=c(n,tau), C^N=(1/2)C_P M[(1+sigma_T C_tor)C_coh+sigma_T Gamma rho^{tau+n}], C^L=C_coh[C_tor C^N+(1/2)C_P M Gamma rho^{tau+n}], C_quad=C_P max{C^L,Gamma rho^{tau+n} C^N}; forward descriptions at L113-L117 add no dependencies
CONSTANT_SCOPE: all constants depend only on n,tau,rho,M,sigma_K,sigma_B,sigma_T (C_coh only on n,tau; C_P only on n,sigma_K,sigma_B); not on gamma, mu or the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cohomological
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cohomological | blueprint/parts/p3-uniqueness.tex#bp:p3:standing#constants@L104-L104 | C_coh is the constant c(n,tau) of that lemma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3+sol-review-r3
REVIEWER: sol-review-r1
LEAN_STATUS: PROVED
LEAN_REF: KAM.Uniq.{C_P, C_Gamma, C_tor, C_coh, C_N, C_L, C_quad}, KAM.Uniq.threshold
LEAN_NOTE: standing data and constants per the audited design; audit docs/campaign/audits/P3-0-audit-1.md; kernel replay passed (2026-10-27)
NOTE: ADDED step: the constants paragraph of the setting (L95-117) is a construction reused throughout; not a labelled environment

NODE: bp:p3:quadratic#absorb
KIND: step
TITLE: Absorption inequality
STATEMENT_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic#absorb@L428-L433
PROOF_SOURCE: blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic#absorb@L428-L433
CONTRACT_ID: bp:p3:quadratic#absorb
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: delta<rho (from rho''<rho'<=3rho/4); gamma<=Gamma
SOURCE_QUANTIFIERS: delta=(rho'-rho'')/2
SOURCE_CONCLUSION: 1<=Gamma rho^{tau+n} gamma^{-1} delta^{-(tau+n)} (eq:p3:absorb)
CONSTANT_SCOPE: Gamma as in the setting
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p3:frequency-bound
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p3:frequency-bound | blueprint/parts/p3-uniqueness.tex#bp:p3:quadratic#absorb@L430-L430 | gamma<=Gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p3
REVIEWER: sol-review-r3
LEAN_STATUS: PROVED
LEAN_REF: inside KAM.Uniq.quadratic
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P3-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: ADDED step: reused intermediate inequality (eq:p3:absorb), used in four steps

NODE: bp:p4:lattice-count
KIND: lemma
TITLE: Counting lattice points on $\ell^1$ spheres
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:lattice-count@L53-L55
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:lattice-count@L57-L64
CONTRACT_ID: bp:p4:lattice-count
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1, m>=1 integers
SOURCE_QUANTIFIERS: n,m integers
SOURCE_CONCLUSION: #{k in Z^n : |k|_1=m} <= 2(2m+1)^{n-1} <= 2*3^{n-1} m^{n-1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:count-projection
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:count-projection | blueprint/parts/p4-measure.tex#bp:p4:lattice-count@L58-L58 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Measure.lattice_count
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:count-projection
KIND: step
TITLE: Projection to the first $n-1$ coordinates
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:count-projection@L58-L63
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:count-projection@L58-L63
CONTRACT_ID: step:p4:count-projection
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n,m>=1; |k|_1=m
SOURCE_QUANTIFIERS: P(k)=(k_1..k_{n-1}) and its fibres
SOURCE_CONCLUSION: image of P lies in {-m..m}^{n-1}, fibres have <=2 points, so count <= 2(2m+1)^{n-1}, and 2m+1<=3m
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Measure.card_l1Sphere_succ_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:lattice-sum
KIND: lemma
TITLE: Lattice sum
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:lattice-sum@L66-L71
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:lattice-sum@L73-L82
CONTRACT_ID: bp:p4:lattice-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1, tau>n-1
SOURCE_QUANTIFIERS: n, tau, then the sum
SOURCE_CONCLUSION: sum_{k in Z^n\{0}} |k|_1^{-tau-1} <= S(n,tau)=2*3^{n-1}(tau+2-n)/(tau+1-n)
CONSTANT_SCOPE: S depends only on n, tau
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:latsum-shells, step:p4:latsum-integral
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:latsum-shells | blueprint/parts/p4-measure.tex#bp:p4:lattice-sum@L74-L74 | proof step of this result
EDGE: step:p4:latsum-integral | blueprint/parts/p4-measure.tex#bp:p4:lattice-sum@L78-L78 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Measure.lattice_sum
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:latsum-shells
KIND: step
TITLE: Summation by shells
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:latsum-shells@L74-L76
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:latsum-shells@L74-L76
CONTRACT_ID: step:p4:latsum-shells
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1, tau>n-1
SOURCE_QUANTIFIERS: m=|k|_1>=1, p=tau+2-n>1
SOURCE_CONCLUSION: sum <= 2*3^{n-1} sum_{m>=1} m^{-p}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:lattice-count
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:lattice-count | blueprint/parts/p4-measure.tex#step:p4:latsum-shells@L75-L75 | shell cardinalities
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Measure.sum_finset_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:latsum-integral
KIND: step
TITLE: Integral comparison
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:latsum-integral@L78-L81
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:latsum-integral@L78-L81
CONTRACT_ID: step:p4:latsum-integral
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: p>1
SOURCE_QUANTIFIERS: p>1
SOURCE_CONCLUSION: sum_{m>=1} m^{-p} <= p/(p-1), hence the claimed bound with p=tau+2-n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Measure.tsum_rpow_neg_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:slab
KIND: lemma
TITLE: Slabs in a cube
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:slab@L84-L89
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:slab@L91-L102
CONTRACT_ID: bp:p4:slab
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1, R>0, a>0, k in Z^n\{0}
SOURCE_QUANTIFIERS: n,R,a,k
SOURCE_CONCLUSION: meas{omega in [-R,R]^n : |k.omega|<a} <= 2n(2R)^{n-1} a/|k|_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:slab-coordinate, step:p4:slab-fubini
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:slab-coordinate | blueprint/parts/p4-measure.tex#bp:p4:slab@L92-L92 | proof step of this result
EDGE: step:p4:slab-fubini | blueprint/parts/p4-measure.tex#bp:p4:slab@L95-L95 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Measure.slab_measure_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:slab-coordinate
KIND: step
TITLE: A dominant coordinate
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:slab-coordinate@L92-L93
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:slab-coordinate@L92-L93
CONTRACT_ID: step:p4:slab-coordinate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: k in Z^n\{0}
SOURCE_QUANTIFIERS: index i
SOURCE_CONCLUSION: |k_i|=max_j|k_j| >=1 and |k|_1 <= n|k_i|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Measure.exists_dominant_coord
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:slab-fubini
KIND: step
TITLE: Fubini in the coordinate $\omega_i$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:slab-fubini@L95-L101
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:slab-fubini@L95-L101
CONTRACT_ID: step:p4:slab-fubini
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: dominant coordinate i with |k|_1<=n|k_i|; R,a>0
SOURCE_QUANTIFIERS: fixed other coordinates omega' in [-R,R]^{n-1}
SOURCE_CONCLUSION: each section in omega_i has length <= 2a/|k_i|, so by Fubini the slab has measure <= (2R)^{n-1} 2a/|k_i| <= 2n(2R)^{n-1}a/|k|_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:slab-coordinate, bp:p1:ext-measure
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:slab-coordinate | blueprint/parts/p4-measure.tex#step:p4:slab-fubini@L101-L101 | dominant coordinate bound
EDGE: bp:p1:ext-measure | blueprint/parts/p4-measure.tex#step:p4:slab-fubini@L96-L101 | Tonelli for the indicator of a measurable set (E11)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-d3
REVIEWER: sol-review-d4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Measure.volume_slab_le_of_coord
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: repaired F1: uses Tonelli for the indicator of a measurable set (E11); formerly a source gap before (E11) was listed

NODE: step:p4:g3-n0
KIND: step
TITLE: The case $n=0$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:g3-n0@L105-L107
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:g3-n0@L105-L107
CONTRACT_ID: step:p4:g3-n0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n=0 (hypotheses of G3)
SOURCE_QUANTIFIERS: Omega, alpha, tau
SOURCE_CONCLUSION: every omega is (alpha,tau)-Diophantine, the exceptional set is empty, any C works
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:diophantine#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p4-measure.tex#step:p4:g3-n0@L106-L106 | Diophantine condition is vacuous for k=0 only
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Provider.isDiophantine_of_dim_zero
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:g3-cube
KIND: step
TITLE: Bounding cube and constant
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:g3-cube@L109-L112
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:g3-cube@L109-L112
CONTRACT_ID: step:p4:g3-cube
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; Omega bounded; tau>n-1
SOURCE_QUANTIFIERS: R>0 with Omega in [-R,R]^n
SOURCE_CONCLUSION: C=2n(2R)^{n-1}S(n,tau) depends only on n,tau,R
CONSTANT_SCOPE: C depends only on n, tau, R
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:lattice-sum
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:lattice-sum | blueprint/parts/p4-measure.tex#step:p4:g3-cube@L111-L111 | S(n,tau) from the lattice sum
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Provider.exists_cube_superset
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:g3-union
KIND: step
TITLE: Union of slabs
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:g3-union@L114-L120
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:g3-union@L114-L120
CONTRACT_ID: step:p4:g3-union
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=1; alpha>0; Omega in [-R,R]^n
SOURCE_QUANTIFIERS: alpha>0
SOURCE_CONCLUSION: {omega in Omega not in Dio_{alpha,tau}} is contained in the union over k!=0 of {omega in [-R,R]^n : |k.omega|<alpha|k|_1^{-tau}}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:diophantine#IsDiophantine, step:p4:g3-cube
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p4-measure.tex#step:p4:g3-union@L115-L115 | negation of the Diophantine condition
EDGE: step:p4:g3-cube | blueprint/parts/p4-measure.tex#step:p4:g3-union@L115-L120 | Bounding cube is consumed in the union inclusion; L110 is the prerequisite construction, outside this step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Provider.not_diophantine_subset_iUnion
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:g3-sum
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:g3-sum@L122-L127
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:g3-sum@L122-L127
CONTRACT_ID: step:p4:g3-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: slab inclusion of the union step; constant C of the cube step; Lemma slab; Lemma lattice-sum
SOURCE_QUANTIFIERS: alpha>0
SOURCE_CONCLUSION: meas{omega in Omega not in Dio_{alpha,tau}} <= sum_k 2n(2R)^{n-1} alpha |k|_1^{-tau-1} <= C alpha
CONSTANT_SCOPE: C as in the cube step
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:slab, bp:p4:lattice-sum, step:p4:g3-union, step:p4:g3-cube, bp:p1:ext-lebesgue
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:slab | blueprint/parts/p4-measure.tex#step:p4:g3-sum@L123-L123 | slab measure with a=alpha k-norm^-tau
EDGE: bp:p4:lattice-sum | blueprint/parts/p4-measure.tex#step:p4:g3-sum@L124-L124 | lattice sum bound
EDGE: step:p4:g3-union | blueprint/parts/p4-measure.tex#step:p4:g3-sum@L126-L126 | union inclusion
EDGE: step:p4:g3-cube | blueprint/parts/p4-measure.tex#step:p4:g3-sum@L126-L126 | constant C
EDGE: bp:p1:ext-lebesgue | blueprint/parts/p4-measure.tex#step:p4:g3-sum@L123-L123 | monotonicity and countable subadditivity of outer measure
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Provider.volume_not_diophantine_le_of_cube
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P-G3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:data
KIND: definition
TITLE: Shrunken domains and basic constants
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:data@L138-L163
PROOF_SOURCE: -
CONTRACT_ID: bp:p4:data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n>=2, tau>n-1, s0,r0>0; B open bounded nonempty; h holomorphic on B_{r0} and real at real points; fixed witnesses L_h of the inverse frequency inequality on closure B and C_B of the boundary-layer inequality; f and epsilon as in HEAD
SOURCE_QUANTIFIERS: L_h, C_B, s0, r0, B, h fixed; then s, delta_*, mu, D, D' defined; c(m,j) from Cauchy-open
SOURCE_CONCLUSION: defines L_+=max(L_h,1), C_B^+, s=min(s0,1), delta_*=min(s,r0)/4, mu=delta_*/2, D=T_{s/2} x B_{r0/2}, D'=T_{3s/4} x B_{3r0/4}, cbar=max{1,c(n,j),c(2n,j)}, and the unperturbed torus K^0_{I*}(theta)=(theta,iota I*); hbold(theta,I)=h(I)+f(theta,I) on D(s0,r0), realHamiltonian h f=Re hbold at real points
CONSTANT_SCOPE: all constants depend only on n,tau,s0,r0,B,h,L_h,C_B
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cauchy-open, bp:p0:nearlyintegrable#realHamiltonian, bp:p0:domains#complexStrip, bp:p0:domains#actionNbhd
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cauchy-open | blueprint/parts/p4-measure.tex#bp:p4:data@L160-L160 | cbar uses the constants c(m,j) of Cauchy-open
EDGE: bp:p0:nearlyintegrable#realHamiltonian | blueprint/parts/p4-measure.tex#bp:p4:data@L151-L152 | the expanded source range explicitly identifies the frozen real Hamiltonian
EDGE: bp:p0:domains#complexStrip | blueprint/parts/p4-measure.tex#bp:p4:data@L157-L158 | the shrunken phase domains use the complex strips
EDGE: bp:p0:domains#actionNbhd | blueprint/parts/p4-measure.tex#bp:p4:data@L158-L158 | B_{r0/2} and B_{3r0/4} are the action neighbourhoods
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r2
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.{Lplus, CBplus, stripWidth, deltaStar, muParam, domainD, domainD', cauchyConst, cbar, unperturbedTorus, hbold}
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:h-bounded
KIND: lemma
TITLE: $h$ is bounded on a shrunken neighbourhood
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:h-bounded@L168-L170
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:h-bounded@L172-L181
CONTRACT_ID: bp:p4:h-bounded
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of HEAD
SOURCE_QUANTIFIERS: M_h
SOURCE_CONCLUSION: M_h:=sup{|h(I)| : I in B_{3r0/4}} is finite
CONSTANT_SCOPE: M_h depends only on the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:hbdd-compact, step:p4:hbdd-continuity
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:hbdd-compact | blueprint/parts/p4-measure.tex#bp:p4:h-bounded@L173-L173 | proof step of this result
EDGE: step:p4:hbdd-continuity | blueprint/parts/p4-measure.tex#bp:p4:h-bounded@L178-L178 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.h_bounded (+ hBound, norm_le_hBound, isLUB_hBound)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:hbdd-compact
KIND: step
TITLE: A compact set between the neighbourhoods
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hbdd-compact@L173-L176
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hbdd-compact@L173-L176
CONTRACT_ID: step:p4:hbdd-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B bounded; h holomorphic on B_{r0}
SOURCE_QUANTIFIERS: Q:={I : infDist(I,iota B)<=3r0/4}
SOURCE_CONCLUSION: Q is compact and B_{3r0/4} subset Q subset B_{r0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.isCompact_hbddCompact
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:hbdd-continuity
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hbdd-continuity@L178-L180
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hbdd-continuity@L178-L180
CONTRACT_ID: step:p4:hbdd-continuity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Q compact, Q subset B_{r0}, h holomorphic on B_{r0}
SOURCE_QUANTIFIERS: sup over Q
SOURCE_CONCLUSION: |h| is bounded on Q hence on B_{3r0/4}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:hbdd-compact
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:hbdd-compact | blueprint/parts/p4-measure.tex#step:p4:hbdd-continuity@L179-L179 | uses Q compact inside B_{r0}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.bddAbove_norm_image_of_isCompact
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:derivative-bounds
KIND: lemma
TITLE: Derivative bounds
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:derivative-bounds@L183-L195
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:derivative-bounds@L197-L223
CONTRACT_ID: bp:p4:derivative-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of HEAD; shrunken domains of Definition data; (d) additionally eps<=1
SOURCE_QUANTIFIERS: H_j=cbar M_h delta_*^{-j}, F_j=cbar delta_*^{-j} (j=1,2,3), M=cbar(M_h+1)delta_*^{-3}; z, I points
SOURCE_CONCLUSION: (a) polydiscs of radius delta_* around D lie in D' and around B_{r0/2} in B_{3r0/4}; (b) |D^j h|<=H_j on B_{r0/2}; (c) |D^j f|<=F_j eps on D, |X_f|<=F_1 eps, |DX_f|<=F_2 eps; (d) if eps<=1, |Dh~|,|X_h~|,|DX_h~|,|D^2 X_h~|<=M on D
CONSTANT_SCOPE: H_j,F_j,M depend only on the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:db-polydisc, step:p4:db-cauchy, step:p4:db-vectorfield, bp:p4:data, bp:p4:h-bounded
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:db-polydisc | blueprint/parts/p4-measure.tex#bp:p4:derivative-bounds@L198-L198 | proof step of this result
EDGE: step:p4:db-cauchy | blueprint/parts/p4-measure.tex#bp:p4:derivative-bounds@L204-L204 | proof step of this result
EDGE: step:p4:db-vectorfield | blueprint/parts/p4-measure.tex#bp:p4:derivative-bounds@L210-L210 | proof step of this result
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#bp:p4:derivative-bounds@L184-L184 | delta_*, D, D', cbar of Definition data
EDGE: bp:p4:h-bounded | blueprint/parts/p4-measure.tex#bp:p4:derivative-bounds@L184-L184 | M_h in the constants
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.derivative_bounds (I-P4B) + design-form adapter KAM.Head.derivative_bounds_design
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:db-polydisc
KIND: step
TITLE: Polydiscs
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:db-polydisc@L198-L202
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:db-polydisc@L198-L202
CONTRACT_ID: step:p4:db-polydisc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z in D, |w-z|<=delta_*
SOURCE_QUANTIFIERS: w, J in B
SOURCE_CONCLUSION: (a): polydiscs of radius delta_* around D lie in D' and those around B_{r0/2} lie in B_{3r0/4}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#step:p4:db-polydisc@L200-L200 | delta_*, D, D' of Definition data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.closedBall_subset_domainD', closedBall_subset_actionNbhd_three_quarters
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:db-cauchy
KIND: step
TITLE: Cauchy estimates
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:db-cauchy@L204-L208
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:db-cauchy@L204-L208
CONTRACT_ID: step:p4:db-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (a); |h|<=M_h on B_{3r0/4} (h-bounded); |f|<=eps on D'
SOURCE_QUANTIFIERS: j=1,2,3
SOURCE_CONCLUSION: (b), (c) for D^j f, and |D^j h~|<=cbar(M_h+eps)delta_*^{-j} on D
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:h-bounded, bp:p1:cauchy-open, step:p4:db-polydisc
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:h-bounded | blueprint/parts/p4-measure.tex#step:p4:db-cauchy@L205-L205 |  h <=M_h on B_{3r0/4}
EDGE: bp:p1:cauchy-open | blueprint/parts/p4-measure.tex#step:p4:db-cauchy@L206-L206 | Cauchy estimates on polydiscs
EDGE: step:p4:db-polydisc | blueprint/parts/p4-measure.tex#step:p4:db-cauchy@L206-L206 | polydiscs of (a)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.norm_iteratedFDeriv_{le_cbar,h_le,f_le,hbold_le}
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:db-vectorfield
KIND: step
TITLE: From $D\pfh$ to $X_\pfh$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:db-vectorfield@L210-L222
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:db-vectorfield@L210-L222
CONTRACT_ID: step:p4:db-vectorfield
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed HEAD data and perturbation hypotheses of Part 4 L138-L152, with domains and constants defined in bp:p4:data and derivative-bounds L184-L185; for the general identity phi is holomorphic on an open subset of C^n x C^n; additionally epsilon<=1 only for specialization (d) with phi=hbold
SOURCE_QUANTIFIERS: the general holomorphic phi; specialize to phi=f for (c), and to phi=hbold with epsilon<=1 for (d)
SOURCE_CONCLUSION: X_phi=J D phi with |X_phi|<=|D phi|, |DX_phi|<=|D^2 phi|, |D^2 X_phi|<=|D^3 phi|; completes (c) and gives (d)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:hamiltonian#hamiltonianVectorFieldC, step:p4:db-cauchy, bp:p1:hamiltonian-real, bp:p1:holomorphic-regularity
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:hamiltonian#hamiltonianVectorFieldC | blueprint/parts/p4-measure.tex#step:p4:db-vectorfield@L211-L215 | the frozen complex vector-field formula identifies X_phi with the continuous linear map J applied to D phi
EDGE: step:p4:db-cauchy | blueprint/parts/p4-measure.tex#step:p4:db-vectorfield@L219-L219 | Cauchy bounds on D^j f and D^j h~
EDGE: bp:p1:hamiltonian-real | blueprint/parts/p4-measure.tex#step:p4:db-vectorfield@L211-L218 | Missing direct use of the vector-field formula cited at L213
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p4-measure.tex#step:p4:db-vectorfield@L216-L218 | Missing direct use establishing holomorphy of derivatives
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.hamJ, hamiltonianVectorFieldℂ_eq_hamJ, hamiltonianVectorField_bounds
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:freq-map
KIND: lemma
TITLE: The frequency map
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:freq-map@L225-L237
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:freq-map@L239-L272
CONTRACT_ID: bp:p4:freq-map
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: fixed HEAD data of Section sec-data; U={I real : iota I in B_{r0}}, g=frequencyMap h; H_1,H_2 are defined constants, not assumed derivative estimates
SOURCE_QUANTIFIERS: fixed HEAD data; U={I in R^n : iota I in B_{r0}}, g=frequencyMap h; (ii),(iii) for every I in U; (iv) for every real I with iota I in B_{r0/2}; (v) for every pair I,J in B
SOURCE_CONCLUSION: (i) U open and closure B subset U; (ii) for I in U, all partial_i h(iota I) are real and g(I)=(partial_i h(iota I))_i; (iii) g differentiable on U with Dg(I) the real symmetric Hessian there; (iv) for iota I in B_{r0/2}, |g(I)|<=H_1 and |Hessian h(iota I)|<=H_2; (v) g is Lambda_g-Lipschitz on B, Lambda_g=max(H_2,2H_1/delta_*), and |omega|<=W_inf=H_1 for omega in g(B)
CONSTANT_SCOPE: Lambda_g, W_inf depend only on the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:fm-domain, step:p4:fm-gradient, step:p4:fm-hessian, step:p4:fm-bounds, step:p4:fm-lipschitz, bp:p0:nearlyintegrable#frequencyMap, bp:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:fm-domain | blueprint/parts/p4-measure.tex#bp:p4:freq-map@L240-L240 | proof step of this result
EDGE: step:p4:fm-gradient | blueprint/parts/p4-measure.tex#bp:p4:freq-map@L244-L244 | proof step of this result
EDGE: step:p4:fm-hessian | blueprint/parts/p4-measure.tex#bp:p4:freq-map@L254-L254 | proof step of this result
EDGE: step:p4:fm-bounds | blueprint/parts/p4-measure.tex#bp:p4:freq-map@L262-L262 | proof step of this result
EDGE: step:p4:fm-lipschitz | blueprint/parts/p4-measure.tex#bp:p4:freq-map@L267-L267 | proof step of this result
EDGE: bp:p0:nearlyintegrable#frequencyMap | blueprint/parts/p4-measure.tex#bp:p4:freq-map@L226-L226 | g is the frozen frequencyMap h
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#bp:p4:freq-map@L226-L235 | fixed h,B,r0 and the defined delta_* enter the domain and Lipschitz constant
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r2
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.freq_map
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:fm-domain
KIND: step
TITLE: The real domain
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:fm-domain@L240-L242
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:fm-domain@L240-L242
CONTRACT_ID: step:p4:fm-domain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B open; h holomorphic on B_{r0}
SOURCE_QUANTIFIERS: J in closure of B
SOURCE_CONCLUSION: (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: helpers of KAM.Head.freq_map (KAM/Head/Frequency.lean)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:fm-gradient
KIND: step
TITLE: Guarded fact: the frozen frequency map is the gradient
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:fm-gradient@L244-L252
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:fm-gradient@L244-L252
CONTRACT_ID: step:p4:fm-gradient
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h holomorphic on B_{r0}, real at real points
SOURCE_QUANTIFIERS: J in U
SOURCE_CONCLUSION: (ii): the frozen g is the real gradient on U (guarded fact of totality)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:nearlyintegrable#frequencyMap
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:nearlyintegrable#frequencyMap | blueprint/parts/p4-measure.tex#step:p4:fm-gradient@L250-L250 | the Re h composition in the definition of g
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: helpers of KAM.Head.freq_map
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:fm-hessian
KIND: step
TITLE: The Hessian
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:fm-hessian@L254-L260
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:fm-hessian@L254-L260
CONTRACT_ID: step:p4:fm-hessian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ii); holomorphy of d_i h
SOURCE_QUANTIFIERS: I in U
SOURCE_CONCLUSION: (iii): g differentiable on U with real symmetric Hessian
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-regularity, step:p4:fm-gradient
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p4-measure.tex#step:p4:fm-hessian@L255-L255 | d_i h holomorphic and symmetry of mixed derivatives
EDGE: step:p4:fm-gradient | blueprint/parts/p4-measure.tex#step:p4:fm-hessian@L257-L257 | gradient argument and reality (ii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: helpers of KAM.Head.freq_map
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:fm-bounds
KIND: step
TITLE: Bounds
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:fm-bounds@L262-L265
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:fm-bounds@L262-L265
CONTRACT_ID: step:p4:fm-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (iii); derivative bounds (b)
SOURCE_QUANTIFIERS: I with iota I in B_{r0/2}
SOURCE_CONCLUSION: (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:derivative-bounds, step:p4:fm-gradient
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:derivative-bounds | blueprint/parts/p4-measure.tex#step:p4:fm-bounds@L265-L265 | bounds (b)
EDGE: step:p4:fm-gradient | blueprint/parts/p4-measure.tex#step:p4:fm-bounds@L263-L263 | g(I)=Dh(iota I)e_i
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: helpers of KAM.Head.freq_map (derivative_bounds_design)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:fm-lipschitz
KIND: step
TITLE: Lipschitz bound on $B$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:fm-lipschitz@L267-L271
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:fm-lipschitz@L267-L271
CONTRACT_ID: step:p4:fm-lipschitz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (iii),(iv); I,J in B
SOURCE_QUANTIFIERS: I,J in B
SOURCE_CONCLUSION: (v): Lipschitz bound with Lambda_g, and boundedness of g(B) by W_inf
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:fm-bounds, step:p4:fm-hessian, bp:p1:ext-mvt, bp:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:fm-bounds | blueprint/parts/p4-measure.tex#step:p4:fm-lipschitz@L269-L269 | uses (iv)
EDGE: step:p4:fm-hessian | blueprint/parts/p4-measure.tex#step:p4:fm-lipschitz@L269-L269 | differentiability (iii) for the mean value inequality
EDGE: bp:p1:ext-mvt | blueprint/parts/p4-measure.tex#step:p4:fm-lipschitz@L269-L269 | mean value inequality
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#step:p4:fm-lipschitz@L268-L268 | delta_* of Definition data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: helpers of KAM.Head.freq_map
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:hessian-inverse
KIND: lemma
TITLE: Kolmogorov nondegeneracy at a point
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:hessian-inverse@L274-L278
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:hessian-inverse@L280-L292
CONTRACT_ID: bp:p4:hessian-inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of HEAD incl. nondegeneracy witness L_h; L_+=max(L_h,1)
SOURCE_QUANTIFIERS: I in B, v in R^n
SOURCE_CONCLUSION: |v|<=L_+|nabla^2 h(iota I)v|; nabla^2 h(iota I) invertible with real inverse, |nabla^2 h(iota I)^{-1}|<=L_+ in the row-sum norm, also as a complex matrix
CONSTANT_SCOPE: L_+ depends only on the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:hess-quotient, step:p4:hess-norm
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:hess-quotient | blueprint/parts/p4-measure.tex#bp:p4:hessian-inverse@L281-L281 | proof step of this result
EDGE: step:p4:hess-norm | blueprint/parts/p4-measure.tex#bp:p4:hessian-inverse@L287-L287 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.hessian_inverse (hessian_inverse_at)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:hess-quotient
KIND: step
TITLE: Difference quotients
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hess-quotient@L281-L285
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hess-quotient@L281-L285
CONTRACT_ID: step:p4:hess-quotient
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: nondegeneracy hypothesis of HEAD with L_h<=L_+; B open
SOURCE_QUANTIFIERS: I in B, v, small t>0
SOURCE_CONCLUSION: |v|<=L_+|nabla^2 h(iota I)v|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:freq-map, bp:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:freq-map | blueprint/parts/p4-measure.tex#step:p4:hess-quotient@L285-L285 | Dg=nabla^2 h by freq-map(iii)
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#step:p4:hess-quotient@L282-L282 | L_+ of Definition data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: helpers of KAM.Head.hessian_inverse_at
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:hess-norm
KIND: step
TITLE: Inverse and its norm
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hess-norm@L287-L291
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hess-norm@L287-L291
CONTRACT_ID: step:p4:hess-norm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |v|<=L_+|Av| for a real square A
SOURCE_QUANTIFIERS: A=nabla^2 h(iota I)
SOURCE_CONCLUSION: A invertible, |A^{-1}|<=L_+ in the row-sum norm, also as complex operator norm
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:hess-quotient
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:hess-quotient | blueprint/parts/p4-measure.tex#step:p4:hess-norm@L288-L288 | the inequality  v <=L_+ Av  for A=nabla^2 h
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: helpers of KAM.Head.hessian_inverse_at
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:inverse-freq
KIND: lemma
TITLE: The inverse frequency map
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:inverse-freq@L294-L300
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:inverse-freq@L302-L307
CONTRACT_ID: bp:p4:inverse-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of HEAD; Omega=g(B)
SOURCE_QUANTIFIERS: omega in Omega
SOURCE_CONCLUSION: g injective on closure of B with L_+-Lipschitz inverse; I_omega unique in B with g(I_omega)=omega, |I_omega-I_omega'|<=L_+|omega-omega'|, |omega|<=W_inf
CONSTANT_SCOPE: L_+, W_inf depend only on the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:invfreq-proof
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:invfreq-proof | blueprint/parts/p4-measure.tex#bp:p4:inverse-freq@L303-L303 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.inverse_freq
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:invfreq-proof
KIND: step
TITLE: Inverse Lipschitz bound
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:invfreq-proof@L303-L306
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:invfreq-proof@L303-L306
CONTRACT_ID: step:p4:invfreq-proof
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |I-J|<=L_+|g(I)-g(J)| on closure of B; (v)
SOURCE_QUANTIFIERS: omega,omega' in Omega
SOURCE_CONCLUSION: injectivity, Lipschitz inverse, |omega|<=W_inf
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:hess-quotient, bp:p4:freq-map
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:hess-quotient | blueprint/parts/p4-measure.tex#step:p4:invfreq-proof@L305-L305 | inequality on closure of B
EDGE: bp:p4:freq-map | blueprint/parts/p4-measure.tex#step:p4:invfreq-proof@L306-L306 | norm omega bounded by W_inf by (v)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.inverse_freq
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-1-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:h1
KIND: lemma
TITLE: The Hamiltonian hypothesis H1
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:h1@L309-L313
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:h1@L315-L331
CONTRACT_ID: bp:p4:h1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eps<=1; the data of HEAD; D and h~=h+f
SOURCE_QUANTIFIERS: (D,h~)
SOURCE_CONCLUSION: D and h~ satisfy the H1 block of G1 and G2 (D open, Z^n-invariant in theta; h~ holomorphic, periodic, real; four derivative bounds by M) with M of derivative-bounds
CONSTANT_SCOPE: M depends only on the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:h1-open, step:p4:h1-holo, step:p4:h1-bounds, bp:p4:derivative-bounds
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:h1-open | blueprint/parts/p4-measure.tex#bp:p4:h1@L316-L316 | proof step of this result
EDGE: step:p4:h1-holo | blueprint/parts/p4-measure.tex#bp:p4:h1@L321-L321 | proof step of this result
EDGE: step:p4:h1-bounds | blueprint/parts/p4-measure.tex#bp:p4:h1@L329-L329 | proof step of this result
EDGE: bp:p4:derivative-bounds | blueprint/parts/p4-measure.tex#bp:p4:h1@L312-L312 | the constant M
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.h1
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: Candidate edges to G1/G2 dropped: the statement only names the H1 block being verified, it does not consume their conclusions.

NODE: step:p4:h1-open
KIND: step
TITLE: Openness and invariance
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:h1-open@L316-L319
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:h1-open@L316-L319
CONTRACT_ID: step:p4:h1-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: D=T_{s/2} x B_{r0/2}
SOURCE_QUANTIFIERS: k in Z^n
SOURCE_CONCLUSION: D open and Z^n-invariant in theta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#step:p4:h1-open@L317-L317 | D of Definition data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.h1 (h1_domainD_add_intCast)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:h1-holo
KIND: step
TITLE: Holomorphy, periodicity, reality
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:h1-holo@L321-L327
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:h1-holo@L321-L327
CONTRACT_ID: step:p4:h1-holo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: h holomorphic on B_{r0}, real at real points; f holomorphic, 1-periodic, real on D(s0,r0)
SOURCE_QUANTIFIERS: z in D, k in Z^n
SOURCE_CONCLUSION: h~ holomorphic on D, periodic in theta, real at real points of D
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#step:p4:h1-holo@L322-L322 | D and h~ of Definition data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.h1_differentiableOn, h1_add_intCast, h1_im_eq_zero
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:h1-bounds
KIND: step
TITLE: Derivative bounds
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:h1-bounds@L329-L330
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:h1-bounds@L329-L330
CONTRACT_ID: step:p4:h1-bounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eps<=1
SOURCE_QUANTIFIERS: on D
SOURCE_CONCLUSION: |Dh~|,|X_h~|,|DX_h~|,|D^2X_h~|<=M
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:derivative-bounds
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:derivative-bounds | blueprint/parts/p4-measure.tex#step:p4:h1-bounds@L330-L330 | part (d)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.h1 (derivative_bounds_design)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:unperturbed
KIND: lemma
TITLE: Geometry of the unperturbed torus
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:unperturbed@L341-L361
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:unperturbed@L363-L404
CONTRACT_ID: bp:p4:unperturbed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eps<=1; I_* in B, omega in R^n; K^0=K^0_{I_*}; for (e) L_+F_2 eps<=1/2; for (f) omega=g(I_*)
SOURCE_QUANTIFIERS: I_*, omega, theta
SOURCE_CONCLUSION: (a) K^0 holomorphic, primary on strips, real on reals, DK^0=L^0, |L^0|=1; (b) G=Id, det unit, |G^{-1}|=1; (c) N^0 constant, DN^0[omega]=0; (d) T^0=nabla^2 h+d_I^2 f continuous, avg T^0 formula; (e) avg T^0 invertible with |avg T^0 ^{-1}|<=2L_+; (f) E^0=X_f(theta,iota I_*), |E^0|<=F_1 eps; (g) ball of radius delta_* around K^0(theta), theta in T_{s/4}, lies in D
CONSTANT_SCOPE: none (constants of derivative-bounds and data)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:unp-frame, step:p4:unp-normal, step:p4:unp-torsion, step:p4:unp-twist, step:p4:unp-error, step:p4:unp-ball, bp:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:unp-frame | blueprint/parts/p4-measure.tex#bp:p4:unperturbed@L364-L364 | proof step of this result
EDGE: step:p4:unp-normal | blueprint/parts/p4-measure.tex#bp:p4:unperturbed@L371-L371 | proof step of this result
EDGE: step:p4:unp-torsion | blueprint/parts/p4-measure.tex#bp:p4:unperturbed@L376-L376 | proof step of this result
EDGE: step:p4:unp-twist | blueprint/parts/p4-measure.tex#bp:p4:unperturbed@L386-L386 | proof step of this result
EDGE: step:p4:unp-error | blueprint/parts/p4-measure.tex#bp:p4:unperturbed@L393-L393 | proof step of this result
EDGE: step:p4:unp-ball | blueprint/parts/p4-measure.tex#bp:p4:unperturbed@L400-L400 | proof step of this result
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#bp:p4:unperturbed@L342-L342 | K^0_{I_*} of Definition data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.unperturbed
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:unp-frame
KIND: step
TITLE: Frame and Gram matrix
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:unp-frame@L364-L369
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:unp-frame@L364-L369
CONTRACT_ID: step:p4:unp-frame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K^0 affine
SOURCE_QUANTIFIERS: theta, v
SOURCE_CONCLUSION: (a) and (b): DK^0=L^0, |L^0|=1, G=Id, det 1, G^{-1}=Id
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:data, bp:p0:stripdata#gramMatrix, bp:p0:stripdata#dotC, bp:p0:stripdata#IsPrimaryOnStrip, bp:p0:stripdata#IsRealOnReals
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#step:p4:unp-frame@L365-L365 | K^0_{I_*} of Definition data
EDGE: bp:p0:stripdata#gramMatrix | blueprint/parts/p4-measure.tex#step:p4:unp-frame@L367-L367 | frozen Gram matrix
EDGE: bp:p0:stripdata#dotC | blueprint/parts/p4-measure.tex#step:p4:unp-frame@L367-L367 | bilinear dot product
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p4-measure.tex#step:p4:unp-frame@L365-L365 | primarity K^0(theta+k)=K^0(theta)+(k,0)
EDGE: bp:p0:stripdata#IsRealOnReals | blueprint/parts/p4-measure.tex#step:p4:unp-frame@L366-L366 | reality of K^0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.tangentMat_unperturbedTorus, gramMatrix_unperturbedTorus, norm_fderiv_unperturbedTorus
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:unp-normal
KIND: step
TITLE: Normal frame
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:unp-normal@L371-L374
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:unp-normal@L371-L374
CONTRACT_ID: step:p4:unp-normal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G=Id
SOURCE_QUANTIFIERS: theta
SOURCE_CONCLUSION: N^0(theta)e_j=(0,e_j), constant, DN^0[omega]=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:stripdata#normalFrame, bp:p0:hamiltonian#omegaZero, step:p4:unp-frame
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:stripdata#normalFrame | blueprint/parts/p4-measure.tex#step:p4:unp-normal@L372-L372 | frozen normal frame
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p4-measure.tex#step:p4:unp-normal@L372-L372 | Omega_0(a,b)=(-b,a)
EDGE: step:p4:unp-frame | blueprint/parts/p4-measure.tex#step:p4:unp-normal@L372-L372 | G^{-1}=Id
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.normalFrame_unperturbedTorus, normalMat_unperturbedTorus, fderiv_normalFrame_unperturbedTorus
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:unp-torsion
KIND: step
TITLE: Torsion
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:unp-torsion@L376-L384
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:unp-torsion@L376-L384
CONTRACT_ID: step:p4:unp-torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: z=(theta,iota I_*) in D; N^0 constant
SOURCE_QUANTIFIERS: theta in T_{s/2}
SOURCE_CONCLUSION: (d): T^0=d_I^2 h~, omega does not enter, T^0 continuous, avg T^0=nabla^2 h+avg of d_I^2 f
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:db-vectorfield, step:p4:unp-normal, bp:p0:stripdata#torsion, bp:p0:stripdata#dotC, bp:p0:hamiltonian#omegaZero, bp:p0:stripdata#torsionAverage, bp:p1:holomorphic-regularity, bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:db-vectorfield | blueprint/parts/p4-measure.tex#step:p4:unp-torsion@L377-L377 | DX_h~ via D^2 h~
EDGE: step:p4:unp-normal | blueprint/parts/p4-measure.tex#step:p4:unp-torsion@L381-L381 | derivative term vanishes
EDGE: bp:p0:stripdata#torsion | blueprint/parts/p4-measure.tex#step:p4:unp-torsion@L379-L379 | frozen torsion
EDGE: bp:p0:stripdata#dotC | blueprint/parts/p4-measure.tex#step:p4:unp-torsion@L380-L380 | dot product in torsion
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p4-measure.tex#step:p4:unp-torsion@L380-L380 | Omega_0
EDGE: bp:p0:stripdata#torsionAverage | blueprint/parts/p4-measure.tex#step:p4:unp-torsion@L383-L383 | frozen torsionAverage
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p4-measure.tex#step:p4:unp-torsion@L382-L384 | Holomorphy of second derivatives supplies continuity before the frozen integral is used
EDGE: bp:p1:ext-integral | blueprint/parts/p4-measure.tex#step:p4:unp-torsion@L382-L384 | Continuous torsion on the real unit cube is integrable; linearity integrates its constant term
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.torsion_unperturbedTorus_eq, unperturbed_continuous_torsion, unperturbed_torsionAverage
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:unp-twist
KIND: step
TITLE: Twist
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:unp-twist@L386-L391
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:unp-twist@L386-L391
CONTRACT_ID: step:p4:unp-twist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (d); L_+F_2 eps<=1/2
SOURCE_QUANTIFIERS: row sums
SOURCE_CONCLUSION: (e): avg T^0 invertible with inverse norm <=2L_+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:derivative-bounds, bp:p1:ext-integral, bp:p4:hessian-inverse, bp:p1:neumann, step:p4:unp-torsion
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:derivative-bounds | blueprint/parts/p4-measure.tex#step:p4:unp-twist@L387-L387 |  D^2 f <=F_2 eps by (c)
EDGE: bp:p1:ext-integral | blueprint/parts/p4-measure.tex#step:p4:unp-twist@L388-L388 | integral bounded by sup
EDGE: bp:p4:hessian-inverse | blueprint/parts/p4-measure.tex#step:p4:unp-twist@L390-L390 |  A^{-1} <=L_+
EDGE: bp:p1:neumann | blueprint/parts/p4-measure.tex#step:p4:unp-twist@L391-L391 | Neumann series for A+Delta
EDGE: step:p4:unp-torsion | blueprint/parts/p4-measure.tex#step:p4:unp-twist@L389-L389 | avg T^0 = A + Delta
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.unperturbed_twist
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:unp-error
KIND: step
TITLE: Invariance error
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:unp-error@L393-L398
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:unp-error@L393-L398
CONTRACT_ID: step:p4:unp-error
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega=g(I_*)
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: (f): E^0=X_f, |E^0|<=F_1 eps
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:freq-map, bp:p4:derivative-bounds, bp:p0:stripdata#invarianceError, step:p4:db-vectorfield
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:freq-map | blueprint/parts/p4-measure.tex#step:p4:unp-error@L395-L395 | grad h(iota I_*)=g(I_*)=omega by (ii)
EDGE: bp:p4:derivative-bounds | blueprint/parts/p4-measure.tex#step:p4:unp-error@L398-L398 |  X_f <=F_1 eps by (c)
EDGE: bp:p0:stripdata#invarianceError | blueprint/parts/p4-measure.tex#step:p4:unp-error@L396-L396 | frozen invariance error
EDGE: step:p4:db-vectorfield | blueprint/parts/p4-measure.tex#step:p4:unp-error@L394-L394 | X_h~ computation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.unperturbed_invarianceError
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:unp-ball
KIND: step
TITLE: Neighbourhood
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:unp-ball@L400-L403
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:unp-ball@L400-L403
CONTRACT_ID: step:p4:unp-ball
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: theta in T_{s/4}, I_* in B
SOURCE_QUANTIFIERS: (theta',I')
SOURCE_CONCLUSION: (g)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#step:p4:unp-ball@L401-L401 | delta_*, D of Definition data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.ball_unperturbedTorus_subset_domainD
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-2-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:parameters
KIND: definition
TITLE: Parameters of the applications of G1 and G2
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:parameters@L406-L436
PROOF_SOURCE: -
CONTRACT_ID: bp:p4:parameters
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: fixed HEAD data; all tuple side conditions are checked at L415-L416; G1 and G2 are dependencies supplying the constants
SOURCE_QUANTIFIERS: tuples for G1 (two) and G2 (one); constants C_1^(i),C_2^(i),c_G from G1,G2
SOURCE_CONCLUSION: defines sigma_K=sigma_B=2+mu, sigma_T=4L_++mu, gammabar=1, A_0..A_4, lambda_*, c_T, eta_*(delta), c_*=min of eight numbers; all depend only on the data; c_*>0 is fixed before f, epsilon and gamma
CONSTANT_SCOPE: C_1^(i),C_2^(i) are the constants of G1 for the stated tuple, c_G of G2; all derived constants depend only on the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:g1, bp:p0:g2, bp:p4:data, bp:p4:derivative-bounds, bp:p4:freq-map
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:g1 | blueprint/parts/p4-measure.tex#bp:p4:parameters@L411-L411 | G1 tuples and constants C_1,C_2
EDGE: bp:p0:g2 | blueprint/parts/p4-measure.tex#bp:p4:parameters@L414-L414 | G2 tuple and constant c_G
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#bp:p4:parameters@L409-L409 | mu, s, L_+, delta_*
EDGE: bp:p4:derivative-bounds | blueprint/parts/p4-measure.tex#bp:p4:parameters@L419-L419 | H_3,F_1,F_2,M
EDGE: bp:p4:freq-map | blueprint/parts/p4-measure.tex#bp:p4:parameters@L425-L425 | W_inf, Lambda_g
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.parameters
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:smallness
KIND: lemma
TITLE: Smallness consequences
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:smallness@L445-L456
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:smallness@L458-L466
CONTRACT_ID: bp:p4:smallness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA): 0<gamma<=1 and 0<=eps<=c_* gamma^4
SOURCE_QUANTIFIERS: gamma, eps
SOURCE_CONCLUSION: (s1) epsilon<=1 and L_+ F_2 epsilon<=1/2; (s2) C_1^(1) F_1 epsilon/(gamma^4 (s/4)^(4tau))<=1/2; (s3) eta_0<=eta_*(s/32)<=eta_*(s/16), eta_0<=mu, 16n eta_0/s<=1/2; (s4) C_1^(2) A_1 lambda_* epsilon/(gamma^4 (3s/32)^(4tau))<=1/2; (s5) (2A_0+C_2^(2) A_1 lambda_* (3s/32)^(-2tau)) epsilon gamma^(-2)<=c_G gamma^2 (s/16)^(2tau); (s6) (A_3 Lambda_g+A_4) epsilon gamma^(-4)<=1/4; (s7) eta_0<=gamma^2/2<=min(gamma,1)/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:small-proof, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:small-proof | blueprint/parts/p4-measure.tex#bp:p4:smallness@L459-L459 | proof step of this result
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#bp:p4:smallness@L445-L456 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r2
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.smallness
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:small-proof
KIND: step
TITLE: Reduction to $c_*$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:small-proof@L459-L465
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:small-proof@L459-L465
CONTRACT_ID: step:p4:small-proof
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA); definition of c_* as a minimum
SOURCE_QUANTIFIERS: gamma,eps
SOURCE_CONCLUSION: each of (s1)-(s7) is an entry of the minimum defining c_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:parameters, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:small-proof@L460-L460 | entries of c_*, eta_*, c_T
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:small-proof@L459-L465 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Parameters.smallness_s1..s7
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-3-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:apply
KIND: theorem
TITLE: APPLY: a torus for every Diophantine frequency
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:apply@L468-L474
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:apply@L476-L496
CONTRACT_ID: bp:p4:apply
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data of HEAD; (SA); omega in Omega_gamma=g(B) cap Dio_{gamma,tau}
SOURCE_QUANTIFIERS: omega
SOURCE_CONCLUSION: exists K^inf_omega holomorphic and primary on T_{s/8}, real on reals, invariant with frequency omega, B_{mu/2}(K)subset D, |DK|<=sigma_K-mu/2, |K-K^0_omega|<=eta_0/2 on T_{s/8}
CONSTANT_SCOPE: K^inf depends on omega,eps,gamma; constants depend only on the data
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:apply-g1, bp:p4:parameters, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:apply-g1 | blueprint/parts/p4-measure.tex#bp:p4:apply@L477-L477 | proof step of this result
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#bp:p4:apply@L469-L469 | SA, Omega_gamma, sigma_K, mu
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#bp:p4:apply@L468-L474 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.apply
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:apply-g1
KIND: step
TITLE: Application of G1 at the unperturbed torus
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:apply-g1@L477-L495
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:apply-g1@L477-L495
CONTRACT_ID: step:p4:apply-g1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: fixed HEAD data; (SA); omega in Omega_gamma; K=K^0_omega and e=F_1 epsilon (H1-H5 and smallness are established by the listed dependencies)
SOURCE_QUANTIFIERS: first G1 tuple, D, h~, K=K^0_omega
SOURCE_CONCLUSION: K^inf_omega with all stated properties on T_{s/8} and |K^inf-K^0|<=eta_0/2
CONSTANT_SCOPE: constants C_1^(1),C_2^(1) from G1
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:g1, bp:p4:parameters, bp:p4:h1, bp:p4:unperturbed, bp:p4:smallness, bp:p4:inverse-freq, bp:p0:diophantine#IsDiophantine, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:g1 | blueprint/parts/p4-measure.tex#step:p4:apply-g1@L478-L478 | G1 applied
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:apply-g1@L478-L478 | tuple and constants
EDGE: bp:p4:h1 | blueprint/parts/p4-measure.tex#step:p4:apply-g1@L483-L483 | H1
EDGE: bp:p4:unperturbed | blueprint/parts/p4-measure.tex#step:p4:apply-g1@L485-L485 | H2,H3,H4 and error from unperturbed
EDGE: bp:p4:smallness | blueprint/parts/p4-measure.tex#step:p4:apply-g1@L483-L483 | (s1),(s2)
EDGE: bp:p4:inverse-freq | blueprint/parts/p4-measure.tex#step:p4:apply-g1@L488-L488 | I_omega in B, g(I_omega)=omega
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p4-measure.tex#step:p4:apply-g1@L489-L489 | omega in Dio_{gamma,tau} (H5)
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:apply-g1@L477-L495 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.apply (GValid.g1a)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:matrix-norms
KIND: corollary
TITLE: Matrix norms
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:matrix-norms@L518-L533
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:matrix-norms@L535-L544
CONTRACT_ID: bp:p4:matrix-norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A in C^{p x q}; L^0=(Id;0), N^0=(0;Id); for the integral clause A is continuous on [0,1]^n; no epsilon bound is a premise
SOURCE_QUANTIFIERS: A, p, q, x, y
SOURCE_CONCLUSION: (i) row-sum norm is the operator norm, submultiplicative; (ii) |A^T|<=p|A|; (iii) |Omega_0|=|L^0|=|L^0T|=|N^0|=|N^0T|=1; (iv) dotC(x,Omega_0 y)=x^T Omega_0 y, Omega_0^T Omega_0=Id, Omega_0^2=-Id, symplecticForm(x,y)=(iota x)^T Omega_0 (iota y); (v) |int A|<=sup|A|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:mn-rowsum, bp:p0:stripdata#dotC, bp:p0:hamiltonian#symplecticForm, bp:p0:hamiltonian#omegaZero
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:mn-rowsum | blueprint/parts/p4-measure.tex#bp:p4:matrix-norms@L536-L536 | proof step of this result
EDGE: bp:p0:stripdata#dotC | blueprint/parts/p4-measure.tex#bp:p4:matrix-norms@L528-L528 | bilinear dot product
EDGE: bp:p0:hamiltonian#symplecticForm | blueprint/parts/p4-measure.tex#bp:p4:matrix-norms@L530-L530 | symplecticForm
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p4-measure.tex#bp:p4:matrix-norms@L525-L525 | Omega_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-global-K
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.matrix_norms_cor
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: L^0,N^0 are identified by the notation pointer at L525-L526; their norms are computed directly at L539-L540. No application of the conditional unperturbed-torus lemma is made.

NODE: step:p4:mn-rowsum
KIND: step
TITLE: Row sums
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mn-rowsum@L536-L543
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mn-rowsum@L536-L543
CONTRACT_ID: step:p4:mn-rowsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A in C^{p x q}; L^0=(Id;0), N^0=(0;Id); for the integral clause A is continuous on [0,1]^n; no epsilon bound is a premise
SOURCE_QUANTIFIERS: A, p, q
SOURCE_CONCLUSION: (i)-(v)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:hamiltonian#symplecticForm, bp:p0:hamiltonian#omegaZero, bp:p1:operator-norms, bp:p1:matrix-norms, bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:hamiltonian#symplecticForm | blueprint/parts/p4-measure.tex#step:p4:mn-rowsum@L541-L541 | frozen formula of symplecticForm
EDGE: bp:p0:hamiltonian#omegaZero | blueprint/parts/p4-measure.tex#step:p4:mn-rowsum@L541-L541 | Omega_0
EDGE: bp:p1:operator-norms | blueprint/parts/p4-measure.tex#step:p4:mn-rowsum@L537-L539 | Missing cited identification of row-sum and operator norms
EDGE: bp:p1:matrix-norms | blueprint/parts/p4-measure.tex#step:p4:mn-rowsum@L537-L539 | Missing cited submultiplicativity and transpose bounds
EDGE: bp:p1:ext-integral | blueprint/parts/p4-measure.tex#step:p4:mn-rowsum@L542-L543 | Missing explicitly cited integral norm bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-global-K
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.norm_frameL0, norm_frameN0, norm_matrixAverage_le (+ transposes, dotℂ_omegaZero, omegaZeroMatrix_transpose_mul_self, ofReal_symplecticForm)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: L^0,N^0 are identified by the notation pointer at L525-L526; their norms are computed directly at L539-L540. No application of the conditional unperturbed-torus lemma is made.

NODE: bp:p4:torsion-regular
KIND: lemma
TITLE: Guarded facts for the frame and the torsion
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:torsion-regular@L546-L561
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:torsion-regular@L563-L581
CONTRACT_ID: bp:p4:torsion-regular
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: rho>0; K holomorphic on T_rho, K(T_rho) in D, det G_K != 0; omega in R^n
SOURCE_QUANTIFIERS: rho, K, omega
SOURCE_CONCLUSION: (a) Lean G_K^{-1} is the inverse, holomorphic with derivative formula; (b) N=Omega_0 L G^{-1} holomorphic and the derivative term of the frozen torsion is d_omega N; (c) T=N^T Omega_0 X_N holomorphic, avg T an integral of a continuous function; (d) if K primary, u,v,L,G,N,T are Z^n-periodic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:tr-inverse, step:p4:tr-torsion, step:p4:tr-periodic, bp:p4:data, bp:p0:stripdata#gramMatrix, bp:p0:stripdata#normalFrame, bp:p0:stripdata#torsion, bp:p0:stripdata#torsionAverage, bp:p0:stripdata#IsPrimaryOnStrip
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:tr-inverse | blueprint/parts/p4-measure.tex#bp:p4:torsion-regular@L564-L564 | proof step of this result
EDGE: step:p4:tr-torsion | blueprint/parts/p4-measure.tex#bp:p4:torsion-regular@L570-L570 | proof step of this result
EDGE: step:p4:tr-periodic | blueprint/parts/p4-measure.tex#bp:p4:torsion-regular@L576-L576 | proof step of this result
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#bp:p4:torsion-regular@L547-L547 | D of Definition data
EDGE: bp:p0:stripdata#gramMatrix | blueprint/parts/p4-measure.tex#bp:p4:torsion-regular@L548-L548 | G_K
EDGE: bp:p0:stripdata#normalFrame | blueprint/parts/p4-measure.tex#bp:p4:torsion-regular@L554-L554 | N
EDGE: bp:p0:stripdata#torsion | blueprint/parts/p4-measure.tex#bp:p4:torsion-regular@L555-L555 | frozen torsion
EDGE: bp:p0:stripdata#torsionAverage | blueprint/parts/p4-measure.tex#bp:p4:torsion-regular@L557-L557 | avg T
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p4-measure.tex#bp:p4:torsion-regular@L558-L558 | primary K
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.torsion_regular (I-P4B) + adapter KAM.Head.torsion_regular_design
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:tr-inverse
KIND: step
TITLE: Inverse
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:tr-inverse@L564-L568
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:tr-inverse@L564-L568
CONTRACT_ID: step:p4:tr-inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K holomorphic on T_rho, det G!=0
SOURCE_QUANTIFIERS: theta
SOURCE_CONCLUSION: (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:stripdata#gramMatrix, bp:p1:holomorphic-regularity, bp:p1:holomorphic-inverse
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:stripdata#gramMatrix | blueprint/parts/p4-measure.tex#step:p4:tr-inverse@L566-L566 | frozen Gram matrix and Lean inverse
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p4-measure.tex#step:p4:tr-inverse@L565-L568 | Missing cited holomorphy of DK
EDGE: bp:p1:holomorphic-inverse | blueprint/parts/p4-measure.tex#step:p4:tr-inverse@L567-L568 | Missing explicitly cited inverse holomorphy and differentiation result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.gramMatrix_inverse_regular
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:tr-torsion
KIND: step
TITLE: Frame and torsion
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:tr-torsion@L570-L574
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:tr-torsion@L570-L574
CONTRACT_ID: step:p4:tr-torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (a)
SOURCE_QUANTIFIERS: theta
SOURCE_CONCLUSION: (b),(c)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:tr-inverse, bp:p0:stripdata#normalFrame, bp:p0:stripdata#torsion, bp:p4:matrix-norms, step:p4:h1-holo, bp:p1:holomorphic-regularity
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:tr-inverse | blueprint/parts/p4-measure.tex#step:p4:tr-torsion@L571-L571 | N holomorphic by (a)
EDGE: bp:p0:stripdata#normalFrame | blueprint/parts/p4-measure.tex#step:p4:tr-torsion@L571-L571 | frozen normal frame
EDGE: bp:p0:stripdata#torsion | blueprint/parts/p4-measure.tex#step:p4:tr-torsion@L571-L571 | frozen torsion
EDGE: bp:p4:matrix-norms | blueprint/parts/p4-measure.tex#step:p4:tr-torsion@L573-L574 | Missing explicitly cited conversion of frozen sums into matrix products
EDGE: step:p4:h1-holo | blueprint/parts/p4-measure.tex#step:p4:tr-torsion@L572-L574 | Supply holomorphy directly without the unused epsilon<=1 premise of H1
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p4-measure.tex#step:p4:tr-torsion@L571-L574 | Holomorphic derivatives of N and X_hbold are needed for holomorphic torsion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.normalFrame_regular, differentiableOn_linMat, torsion_regular_of_isOpen
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:tr-periodic
KIND: step
TITLE: Periodicity
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:tr-periodic@L576-L580
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:tr-periodic@L576-L580
CONTRACT_ID: step:p4:tr-periodic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K primary on T_rho
SOURCE_QUANTIFIERS: k in Z^n
SOURCE_CONCLUSION: (d)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:stripdata#IsPrimaryOnStrip, step:p4:h1-holo, step:p4:tr-inverse, bp:p1:holomorphic-regularity
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p4-measure.tex#step:p4:tr-periodic@L577-L577 | K(theta+k)=K(theta)+(k,0)
EDGE: step:p4:h1-holo | blueprint/parts/p4-measure.tex#step:p4:tr-periodic@L579-L580 | Missing direct use of Hamiltonian periodicity; use the part of H1 that has no epsilon<=1 premise
EDGE: step:p4:tr-inverse | blueprint/parts/p4-measure.tex#step:p4:tr-periodic@L579-L580 | Periodic Gram inverse on the nonsingular domain is used in the frame
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p4-measure.tex#step:p4:tr-periodic@L577-L580 | Differentiation of primarity and of periodic derivatives supplies periodic L and DN
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.periodic_regular, hbold_periodic
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:stab
KIND: theorem
TITLE: STAB
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:stab@L583-L601
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:stab@L603-L665
CONTRACT_ID: bp:p4:stab
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eps<=1, L_+F_2 eps<=1/2; I_* in B; |omega|<=W_inf; 0<delta<rho<=s/4; K holomorphic on T_rho with |K-K^0_{I_*}|<=eta on T_rho, eta<=eta_*(delta)
SOURCE_QUANTIFIERS: I_*, omega, delta, rho, K, eta
SOURCE_CONCLUSION: on T_{rho-delta}: (a) |DK-L^0|<=n eta/delta, |DK|<=2; (b) B_mu(K) in D; (c) det G_K!=0, |G_K^{-1}|<=2; (d) |T-T^0|<=c_T eta delta^{-2}, avg T invertible with |avg T^{-1}|<=4L_+; if K primary and real on reals, K satisfies H2-H4 of G1 relative to (D,h~) with sigma_K,sigma_B,sigma_T,mu of parameters
CONSTANT_SCOPE: c_T and eta_* are those of parameters (depend only on the data); eta,delta,rho free
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:stab-small, step:p4:stab-cauchy, step:p4:stab-ball, step:p4:stab-gram, step:p4:stab-frame, step:p4:stab-xn, step:p4:stab-torsion, step:p4:stab-twist, step:p4:stab-h2h4, bp:p4:parameters
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:stab-small | blueprint/parts/p4-measure.tex#bp:p4:stab@L604-L604 | proof step of this result
EDGE: step:p4:stab-cauchy | blueprint/parts/p4-measure.tex#bp:p4:stab@L610-L610 | proof step of this result
EDGE: step:p4:stab-ball | blueprint/parts/p4-measure.tex#bp:p4:stab@L619-L619 | proof step of this result
EDGE: step:p4:stab-gram | blueprint/parts/p4-measure.tex#bp:p4:stab@L624-L624 | proof step of this result
EDGE: step:p4:stab-frame | blueprint/parts/p4-measure.tex#bp:p4:stab@L631-L631 | proof step of this result
EDGE: step:p4:stab-xn | blueprint/parts/p4-measure.tex#bp:p4:stab@L638-L638 | proof step of this result
EDGE: step:p4:stab-torsion | blueprint/parts/p4-measure.tex#bp:p4:stab@L649-L649 | proof step of this result
EDGE: step:p4:stab-twist | blueprint/parts/p4-measure.tex#bp:p4:stab@L654-L654 | proof step of this result
EDGE: step:p4:stab-h2h4 | blueprint/parts/p4-measure.tex#bp:p4:stab@L661-L661 | proof step of this result
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#bp:p4:stab@L587-L587 | eta_*, c_T, sigma_K,sigma_B,sigma_T,mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.stab
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:stab-small
KIND: step
TITLE: Smallness bookkeeping
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-small@L604-L608
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-small@L604-L608
CONTRACT_ID: step:p4:stab-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eta<=eta_*(delta) with c_T>=304n^3, L_+>=1, delta<s/4<=1
SOURCE_QUANTIFIERS: Delta=K-K^0, a=n eta/delta, b=4n^2W_inf eta delta^{-2}
SOURCE_CONCLUSION: 12 n a<=1 and c_T eta delta^{-2}<=1/16
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:parameters
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:stab-small@L606-L606 | c_T>=304n^3, eta_*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Stab.eta_small
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:stab-cauchy
KIND: step
TITLE: Cauchy estimates
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-cauchy@L610-L617
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-cauchy@L610-L617
CONTRACT_ID: step:p4:stab-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K holomorphic on T_rho, |Delta|<=eta
SOURCE_QUANTIFIERS: Delta
SOURCE_CONCLUSION: |D Delta|<=a on T_{rho-delta}; |d_m d_l Delta|<=4eta/delta^2; |d_omega L|<=b; |L|<=2; this is (a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cauchy-strip, bp:p1:holomorphic-regularity, step:p4:stab-small, bp:p4:unperturbed
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cauchy-strip | blueprint/parts/p4-measure.tex#step:p4:stab-cauchy@L611-L611 | Cauchy estimate on strips
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p4-measure.tex#step:p4:stab-cauchy@L613-L613 | d_l Delta holomorphic
EDGE: step:p4:stab-small | blueprint/parts/p4-measure.tex#step:p4:stab-cauchy@L611-L611 | a, b bookkeeping
EDGE: bp:p4:unperturbed | blueprint/parts/p4-measure.tex#step:p4:stab-cauchy@L617-L617 |  L^0 =1 and D^2K^0=0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Stab.tangent_close, norm_fderiv_fderiv_le, norm_dL_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:stab-ball
KIND: step
TITLE: Neighbourhood
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-ball@L619-L622
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-ball@L619-L622
CONTRACT_ID: step:p4:stab-ball
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |K-K^0|<=eta<=mu
SOURCE_QUANTIFIERS: theta in T_{rho-delta}
SOURCE_CONCLUSION: (b): B_mu(K(theta)) in D and K(T_{rho-delta}) in D
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:unperturbed, bp:p4:parameters, bp:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:unperturbed | blueprint/parts/p4-measure.tex#step:p4:stab-ball@L621-L621 | (g): ball around K^0 lies in D
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:stab-ball@L620-L620 | eta<=eta_*(delta)<=mu
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#step:p4:stab-ball@L621-L621 | 2mu=delta_*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Stab.ball_subset_domainD
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:stab-gram
KIND: step
TITLE: Gram matrix
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-gram@L624-L629
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-gram@L624-L629
CONTRACT_ID: step:p4:stab-gram
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: L=L^0+D Delta, |D Delta|<=a, 12na<=1
SOURCE_QUANTIFIERS: theta in T_{rho-delta}
SOURCE_CONCLUSION: (c): |G_K-Id|<=5na<=1/2, G_K invertible, |G^{-1}|<=2, |G^{-1}-Id|<=10na; torsion-regular applies on T_{rho-delta}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:matrix-norms, bp:p1:neumann, bp:p4:torsion-regular, step:p4:stab-cauchy, bp:p4:unperturbed, step:p4:stab-small, step:p4:stab-ball
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:matrix-norms | blueprint/parts/p4-measure.tex#step:p4:stab-gram@L625-L625 | transpose and L^0 norms
EDGE: bp:p1:neumann | blueprint/parts/p4-measure.tex#step:p4:stab-gram@L627-L627 | Neumann series with A=Id
EDGE: bp:p4:torsion-regular | blueprint/parts/p4-measure.tex#step:p4:stab-gram@L629-L629 | applies once det G_K!=0
EDGE: step:p4:stab-cauchy | blueprint/parts/p4-measure.tex#step:p4:stab-gram@L625-L625 | a and  L <=2
EDGE: bp:p4:unperturbed | blueprint/parts/p4-measure.tex#step:p4:stab-gram@L626-L626 | G_{K^0}=Id, L^0
EDGE: step:p4:stab-small | blueprint/parts/p4-measure.tex#step:p4:stab-gram@L626-L626 | 5na<=1/2
EDGE: step:p4:stab-ball | blueprint/parts/p4-measure.tex#step:p4:stab-gram@L629-L629 | The application of torsion-regular needs K(T_{rho-delta}) subset D, supplied by the neighbourhood step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Stab.norm_gram_sub_one_le, gram_inv
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:stab-frame
KIND: step
TITLE: Normal frame
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-frame@L631-L636
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-frame@L631-L636
CONTRACT_ID: step:p4:stab-frame
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (c); a,b; |L|<=2
SOURCE_QUANTIFIERS: theta
SOURCE_CONCLUSION: |N-N^0|<=12na, |N|<=2, |d_omega G|<=8nb, |d_omega G^{-1}|<=32nb, |d_omega N|<=66nb
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:torsion-regular, step:p4:stab-gram, step:p4:stab-cauchy, bp:p4:matrix-norms, bp:p4:unperturbed, step:p4:stab-small
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:torsion-regular | blueprint/parts/p4-measure.tex#step:p4:stab-frame@L633-L633 | derivative formula (a) for G^{-1}
EDGE: step:p4:stab-gram | blueprint/parts/p4-measure.tex#step:p4:stab-frame@L632-L632 | bounds on G^{-1}
EDGE: step:p4:stab-cauchy | blueprint/parts/p4-measure.tex#step:p4:stab-frame@L632-L632 |  L-L^0 <=a,  d_omega L <=b
EDGE: bp:p4:matrix-norms | blueprint/parts/p4-measure.tex#step:p4:stab-frame@L632-L632 |  Omega_0 =1, transpose norms
EDGE: bp:p4:unperturbed | blueprint/parts/p4-measure.tex#step:p4:stab-frame@L632-L632 | N^0,L^0
EDGE: step:p4:stab-small | blueprint/parts/p4-measure.tex#step:p4:stab-frame@L632-L636 | The conclusion ¦N¦<=2 uses ¦N0¦=1 and 12na<=1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Stab.norm_normal_sub_le, norm_dN_le, frame_basic, frame_deriv
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:stab-xn
KIND: step
TITLE: The vector $X_N$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-xn@L638-L647
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-xn@L638-L647
CONTRACT_ID: step:p4:stab-xn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K(T_{rho-delta}) in D; frame bounds
SOURCE_QUANTIFIERS: theta
SOURCE_CONCLUSION: |X_N-X_N^0|<=c_T eta delta^{-2}, |X_N|<=M+1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:h1, bp:p1:increments-open, bp:p4:unperturbed, step:p4:stab-frame, bp:p4:parameters, step:p4:stab-small
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:h1 | blueprint/parts/p4-measure.tex#step:p4:stab-xn@L640-L640 |  D^2 X_h~ <=M on D
EDGE: bp:p1:increments-open | blueprint/parts/p4-measure.tex#step:p4:stab-xn@L641-L641 | increment estimate on the ball
EDGE: bp:p4:unperturbed | blueprint/parts/p4-measure.tex#step:p4:stab-xn@L643-L643 | (g) ball in D; (c) torsion vector of K^0
EDGE: step:p4:stab-frame | blueprint/parts/p4-measure.tex#step:p4:stab-xn@L645-L645 |  N ,  N-N^0 ,  d_omega N 
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:stab-xn@L645-L645 | c_T
EDGE: step:p4:stab-small | blueprint/parts/p4-measure.tex#step:p4:stab-xn@L645-L645 | delta<=1, c_T eta delta^{-2}<=1/16
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Stab.norm_fderivX_sub_le, normalField_close
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:stab-torsion
KIND: step
TITLE: Torsion
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-torsion@L649-L652
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-torsion@L649-L652
CONTRACT_ID: step:p4:stab-torsion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: T=N^T Omega_0 X_N; frame and X_N bounds
SOURCE_QUANTIFIERS: theta
SOURCE_CONCLUSION: (d) first part: |T-T^0|<=c_T eta delta^{-2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:matrix-norms, step:p4:stab-frame, step:p4:stab-xn, bp:p4:torsion-regular, bp:p4:unperturbed, bp:p4:parameters
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:matrix-norms | blueprint/parts/p4-measure.tex#step:p4:stab-torsion@L651-L651 | norm calculus
EDGE: step:p4:stab-frame | blueprint/parts/p4-measure.tex#step:p4:stab-torsion@L650-L650 |  N-N^0 
EDGE: step:p4:stab-xn | blueprint/parts/p4-measure.tex#step:p4:stab-torsion@L650-L650 |  X_N-X_N^0 ,  X_N <=M+1
EDGE: bp:p4:torsion-regular | blueprint/parts/p4-measure.tex#step:p4:stab-torsion@L650-L650 | T=N^T Omega_0 X_N
EDGE: bp:p4:unperturbed | blueprint/parts/p4-measure.tex#step:p4:stab-torsion@L650-L650 | T^0 from N^0, X_N^0
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:stab-torsion@L652-L652 | The final coefficient comparison uses the definition c_T=304n^3(M+W_inf+1)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Stab.torsion_close
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:stab-twist
KIND: step
TITLE: Twist
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-twist@L654-L659
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-twist@L654-L659
CONTRACT_ID: step:p4:stab-twist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: torsion bound; (e) of unperturbed
SOURCE_QUANTIFIERS: avg over unit cube
SOURCE_CONCLUSION: (d) second part: |avg T - avg T^0|<=c_T eta delta^{-2}; avg T invertible with |avg T^{-1}|<=4L_+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:torsion-regular, bp:p4:unperturbed, bp:p4:matrix-norms, bp:p1:neumann, step:p4:stab-torsion, bp:p4:parameters
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:torsion-regular | blueprint/parts/p4-measure.tex#step:p4:stab-twist@L655-L655 | avg T integral of continuous function
EDGE: bp:p4:unperturbed | blueprint/parts/p4-measure.tex#step:p4:stab-twist@L655-L655 | avg T^0 integral;  avg T0^{-1} <=2L_+
EDGE: bp:p4:matrix-norms | blueprint/parts/p4-measure.tex#step:p4:stab-twist@L656-L656 |  int A <=sup A 
EDGE: bp:p1:neumann | blueprint/parts/p4-measure.tex#step:p4:stab-twist@L658-L658 | Neumann series
EDGE: step:p4:stab-torsion | blueprint/parts/p4-measure.tex#step:p4:stab-twist@L657-L657 |  T-T^0  bound
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:stab-twist@L658-L658 | 2L_+ c_T eta delta^{-2}<=1/8 from eta<=eta_*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Stab.twist_close
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:stab-h2h4
KIND: step
TITLE: The hypotheses H2--H4
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-h2h4@L661-L664
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:stab-h2h4@L661-L664
CONTRACT_ID: step:p4:stab-h2h4
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K primary and real on reals; (a)-(d)
SOURCE_QUANTIFIERS: theta in T_{rho-delta}
SOURCE_CONCLUSION: H2,H3,H4 of G1 on T_{rho-delta} with sigma_K,sigma_B,sigma_T,mu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:stab-cauchy, step:p4:stab-ball, step:p4:stab-gram, step:p4:stab-twist, bp:p0:stripdata#IsPrimaryOnStrip, bp:p0:stripdata#IsRealOnReals
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:stab-cauchy | blueprint/parts/p4-measure.tex#step:p4:stab-h2h4@L663-L663 | (a)
EDGE: step:p4:stab-ball | blueprint/parts/p4-measure.tex#step:p4:stab-h2h4@L663-L663 | (b)
EDGE: step:p4:stab-gram | blueprint/parts/p4-measure.tex#step:p4:stab-h2h4@L663-L663 | (c)
EDGE: step:p4:stab-twist | blueprint/parts/p4-measure.tex#step:p4:stab-h2h4@L664-L664 | (d)
EDGE: bp:p0:stripdata#IsPrimaryOnStrip | blueprint/parts/p4-measure.tex#step:p4:stab-h2h4@L662-L662 | primarity restricts
EDGE: bp:p0:stripdata#IsRealOnReals | blueprint/parts/p4-measure.tex#step:p4:stab-h2h4@L662-L662 | reality restricts
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4a
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: inside KAM.Head.stab
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-4-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:SA
KIND: display
TITLE: Local smallness package and frequency notation
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:SA@L438-L443
PROOF_SOURCE: -
CONTRACT_ID: bp:p4:SA
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: fixed HEAD data of Part 4 and constants of Definition parameters
SOURCE_QUANTIFIERS: gamma, epsilon real, after the data-dependent constants have been fixed
SOURCE_CONCLUSION: local package (SA) is 0<gamma<=1 and 0<=epsilon<=c_* gamma^4; eta_0=A_0 epsilon gamma^{-2}; Omega_gamma=g(B) intersect Dio_{gamma,tau}
CONSTANT_SCOPE: c_*, A_0 fixed before gamma, epsilon; eta_0 and Omega_gamma depend on gamma (and eta_0 on epsilon)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:parameters, bp:p4:freq-map, bp:p0:diophantine#IsDiophantine
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#bp:p4:SA@L438-L443 | c_*, A_0 and their scope
EDGE: bp:p4:freq-map | blueprint/parts/p4-measure.tex#bp:p4:SA@L443-L443 | g(B), with g the frequency map
EDGE: bp:p0:diophantine#IsDiophantine | blueprint/parts/p4-measure.tex#bp:p4:SA@L443-L443 | Diophantine set
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: new+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.SA (structure), KAM.Head.eta0, KAM.Head.OmegaGamma (KAM/Head/Defs.lean:262-275)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P4-0-audit-1.md; docs/campaign/audits/DESIGN-P4-audit-1.md; kernel replay passed with the package
NOTE: Local hypothesis package only; STANDING_ASSUMPTIONS remains none.

NODE: bp:p4:phase-average
KIND: definition
TITLE: Angle displacement and phase average
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:phase-average@L677-L684
PROOF_SOURCE: -
CONTRACT_ID: bp:p4:phase-average
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K holomorphic on T_rho, primary on T_rho, real on reals
SOURCE_QUANTIFIERS: rho>0; K; (then a in R^n for K^[a])
SOURCE_CONCLUSION: defines u_K(theta)=K_1(theta)-theta, ph(K)=int_[0,1]^n Re u_K(ix)dx in R^n, K normalized iff ph(K)=0, K^[a](theta)=K(theta+i a)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.angleDisplacement, phaseAverage, IsNormalized, phaseShift (+ continuous_angleDisplacement_ofReal, angleDisplacement_ofReal_im, ofReal_phaseAverage_eq_integral)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:shift
KIND: lemma
TITLE: Phase shifts
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:shift@L686-L701
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:shift@L703-L718
CONTRACT_ID: bp:p4:shift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K holomorphic and primary on T_rho, real on reals; a,omega in R^n; (e) I_* in R^n
SOURCE_QUANTIFIERS: K,rho; a,omega in R^n; I_* in R^n
SOURCE_CONCLUSION: (a) K^[a] holomorphic, primary, real on reals, DK^[a](theta)=DK(theta+ia); (b) E_{K^[a]}(theta)=E_K(theta+ia), invariance preserved; (c) pointwise bounds transfer; (d) ph(K^[a])=ph(K)+a, unique normalized shift K^[-ph K], K and K^[a] normalized => a=0; (e) |ph K|<=sup_x |K(ix)-K0_{I*}(ix)| and |K^[a]-K0_{I*}|(theta)<=|K-K0_{I*}|(theta+ia)+|a|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:phase-average, bp:p4:data, step:p4:shift-translation, step:p4:shift-phase
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:phase-average | blueprint/parts/p4-measure.tex#bp:p4:shift@L687-L687 | K^[a], ph(K) used by name
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#bp:p4:shift@L698-L698 | unperturbed torus K0_{I*} in (e)
EDGE: step:p4:shift-translation | blueprint/parts/p4-measure.tex#bp:p4:shift@L704-L704 | proof step of this result
EDGE: step:p4:shift-phase | blueprint/parts/p4-measure.tex#bp:p4:shift@L711-L711 | proof step of this result
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.phase_shift (I-P4B) + adapter KAM.Head.shift_design
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:shift-translation
KIND: step
TITLE: Translation
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:shift-translation@L704-L709
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:shift-translation@L704-L709
CONTRACT_ID: step:p4:shift-translation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K holomorphic, primary on T_rho, real on reals; a in R^n
SOURCE_QUANTIFIERS: K,rho,a,omega
SOURCE_CONCLUSION: (a),(b),(c) of Lemma shift: K^[a] holomorphic with derivative DK(.+ia), primary, real; E_{K^[a]}=E_K(.+ia); bounds transfer
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:phase-average
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:phase-average | blueprint/parts/p4-measure.tex#step:p4:shift-translation@L705-L705 | K^[a] defined there
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.{differentiableOn,isPrimaryOnStrip,isRealOnReals}_phaseShift, fderiv_phaseShift, invarianceError_phaseShift, phaseShift_transfer
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:shift-phase
KIND: step
TITLE: Phase average
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:shift-phase@L711-L717
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:shift-phase@L711-L717
CONTRACT_ID: step:p4:shift-phase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K holomorphic, primary on T_rho, real on reals; a in R^n; u_K o iota continuous and Z^n-periodic (primarity)
SOURCE_QUANTIFIERS: K,rho,a,I_*
SOURCE_CONCLUSION: (d) ph(K^[a])=ph(K)+a and uniqueness of normalized shift; (e) the phase and shifted-distance bounds against K0_{I*}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:periodic-average, bp:p4:phase-average, bp:p4:data, bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:periodic-average | blueprint/parts/p4-measure.tex#step:p4:shift-phase@L714-L714 | real parts of u_K(i(x+a)) averaged over the period cell, shift invariance
EDGE: bp:p4:phase-average | blueprint/parts/p4-measure.tex#step:p4:shift-phase@L712-L714 | u_K, ph(K) defined there
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#step:p4:shift-phase@L715-L715 | K0_{I*} and u_{K0}=0
EDGE: bp:p1:ext-integral | blueprint/parts/p4-measure.tex#step:p4:shift-phase@L714-L717 | The bound on the phase uses the integral norm bound on a unit-volume cube
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r2
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.phaseAverage_phaseShift, isNormalized_phaseShift_iff, norm_phaseAverage_le, norm_phaseShift_sub_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:normalized-torus
KIND: definition
TITLE: The normalized torus $K_\omega$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:normalized-torus@L720-L726
PROOF_SOURCE: -
CONTRACT_ID: bp:p4:normalized-torus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing assumption (SA) 0<gamma<=1 and 0<=eps<=c_* gamma^4 (display bp:p4:SA); omega in Omega_gamma; K^inf_omega from Theorem APPLY (fixed by choice)
SOURCE_QUANTIFIERS: gamma,eps; omega in Omega_gamma; a chosen K^inf_omega
SOURCE_CONCLUSION: defines K_omega=(K^inf_omega)^[-ph(K^inf_omega)], W_omega=K_omega-K0_omega=(u_omega,v_omega)
CONSTANT_SCOPE: all named constants (c_*, A_0..A_4, lambda_*, L_+, delta_*, mu, M, W_inf, Lambda_g, sigma_K, sigma_B, sigma_T, c_T, eta_*) depend only on the data n,tau,s0,r0,B,h,L_h,C_B (never on f, eps, gamma); eta_0=A_0 eps gamma^-2 depends also on eps,gamma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:apply, bp:p4:phase-average, bp:p4:inverse-freq, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:apply | blueprint/parts/p4-measure.tex#bp:p4:normalized-torus@L721-L721 | K^inf_omega is a torus given by APPLY
EDGE: bp:p4:phase-average | blueprint/parts/p4-measure.tex#bp:p4:normalized-torus@L723-L723 | ph and the shift K^[a] defined there
EDGE: bp:p4:inverse-freq | blueprint/parts/p4-measure.tex#bp:p4:normalized-torus@L724-L724 | K0_omega=K0_{I_omega}, I_omega
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#bp:p4:normalized-torus@L720-L726 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r2
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.applyTorus, KAM.Head.normTorus, KAM.Head.normDisp (KAM/Head/Defs.lean:292-310)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P4-0-audit-1.md; docs/campaign/audits/DESIGN-P4-audit-1.md (consumption: docs/campaign/audits/P4-9-audit-2.md); kernel replay passed with the package
NOTE: -

NODE: bp:p4:normalize
KIND: lemma
TITLE: Properties of $K_\omega$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:normalize@L728-L734
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:normalize@L736-L742
CONTRACT_ID: bp:p4:normalize
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing assumption (SA) 0<gamma<=1 and 0<=eps<=c_* gamma^4 (display bp:p4:SA); omega in Omega_gamma
SOURCE_QUANTIFIERS: gamma,eps with (SA); omega in Omega_gamma; theta in T_{s/8}
SOURCE_CONCLUSION: K_omega holomorphic and primary on T_{s/8}, real on reals, invariant with frequency omega on T_{s/8}, normalized (avg u_omega=0), B_{mu/2}(K_omega(theta)) in D, |DK_omega|<=sigma_K-mu/2, |W_omega|<=eta_0
CONSTANT_SCOPE: all named constants (c_*, A_0..A_4, lambda_*, L_+, delta_*, mu, M, W_inf, Lambda_g, sigma_K, sigma_B, sigma_T, c_T, eta_*) depend only on the data n,tau,s0,r0,B,h,L_h,C_B (never on f, eps, gamma); eta_0=A_0 eps gamma^-2 depends also on eps,gamma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:normalized-torus, bp:p4:parameters, step:p4:normalize-proof, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:normalized-torus | blueprint/parts/p4-measure.tex#bp:p4:normalize@L729-L729 | K_omega, W_omega defined there
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#bp:p4:normalize@L729-L729 | standing assumption (SA), sigma_K, mu, eta_0
EDGE: step:p4:normalize-proof | blueprint/parts/p4-measure.tex#bp:p4:normalize@L737-L737 | proof step of this result
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#bp:p4:normalize@L728-L734 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.normalize
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:normalize-proof
KIND: step
TITLE: Shift of the G1 output
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:normalize-proof@L737-L741
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:normalize-proof@L737-L741
CONTRACT_ID: step:p4:normalize-proof
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed HEAD data and perturbation hypotheses of Part 4; (SA); omega in Omega_gamma; K^infty_omega is the torus chosen from APPLY and K_omega is the construction in normalized-torus, without an added closeness premise
SOURCE_QUANTIFIERS: gamma,eps,omega; theta in T_{s/8}
SOURCE_CONCLUSION: all clauses of Lemma normalize: first from APPLY and shift (a)-(d); |ph K^inf|<=eta_0/2 and |W_omega|<=eta_0 from shift (e)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:apply, bp:p4:shift, bp:p4:normalized-torus, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:apply | blueprint/parts/p4-measure.tex#step:p4:normalize-proof@L738-L738 | properties of K^inf_omega on T_{s/8} and the eta_0/2 closeness
EDGE: bp:p4:shift | blueprint/parts/p4-measure.tex#step:p4:normalize-proof@L738-L738 | parts (a)-(e) of the phase shift lemma
EDGE: bp:p4:normalized-torus | blueprint/parts/p4-measure.tex#step:p4:normalize-proof@L738-L741 | K_omega=(K^inf)^[-ph]
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:normalize-proof@L737-L741 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.isApplyTorus_phaseShift
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-5-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:mixed-difference
KIND: corollary
TITLE: Mixed second differences
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:mixed-difference@L800-L806
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:mixed-difference@L808-L818
CONTRACT_ID: bp:p4:mixed-difference
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U in C^n open; F:U->C^n holomorphic; a,v,w in C^n with a+tv+t'w in U for t,t' in [0,1]; |D^2F|<=Q at these points
SOURCE_QUANTIFIERS: U,F,a,v,w,Q
SOURCE_CONCLUSION: |F(a+v+w)-F(a+v)-F(a+w)+F(a)|<=Q|v||w|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:mixed-proof
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:mixed-proof | blueprint/parts/p4-measure.tex#bp:p4:mixed-difference@L809-L817 | Use the actual proof step rather than the bare proof-environment line L808
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.mixed_difference (I-P4B) + adapter KAM.Head.mixed_difference_design
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:mixed-proof
KIND: step
TITLE: Two mean value inequalities
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mixed-proof@L809-L817
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mixed-proof@L809-L817
CONTRACT_ID: step:p4:mixed-proof
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F holomorphic on U; parallelogram {a+tv+t'w} in U; |D^2F|<=Q there
SOURCE_QUANTIFIERS: U,F,a,v,w,Q
SOURCE_CONCLUSION: the mixed second difference bound Q|v||w| via two mean value inequalities
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-mvt, bp:p1:holomorphic-regularity
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-mvt | blueprint/parts/p4-measure.tex#step:p4:mixed-proof@L810-L817 | Mean value inequality is applied on the parallelogram segments
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p4-measure.tex#step:p4:mixed-proof@L812-L813 | Holomorphic regularity is used at L812-L813, not L811
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.mixed_difference_of_finiteDimensional
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4B-audit-1.md; kernel replay passed (2026-10-27)
NOTE: L809-810 references Lemma bp:p1:mixed-difference only as the model of the argument; the proof here is self-contained, so no edge.

NODE: bp:p4:lip-error
KIND: lemma
TITLE: The error of the shifted torus
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:lip-error@L820-L829
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:lip-error@L831-L874
CONTRACT_ID: bp:p4:lip-error
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA); omega,omega' in Omega_gamma with |omega'-omega|<=lambda_* gamma^2; Delta omega=omega'-omega, Delta I=I_omega'-I_omega, K'=K_omega+(0,i Delta I)
SOURCE_QUANTIFIERS: gamma,eps with (SA); omega,omega'; theta in T_{3s/32}
SOURCE_CONCLUSION: K' holomorphic and primary on T_{s/8}, real on reals, K'-K0_omega'=W_omega (|.|<=eta_0 on T_{s/8}); invariance error |E'(theta)|<=A_1 eps gamma^-2 |Delta omega| on T_{3s/32}
CONSTANT_SCOPE: A_1 depends only on the data (A_1=L_+(H_3A_0+F_2)+32nA_0/s); lambda_* depends only on data; all named constants (c_*, A_0..A_4, lambda_*, L_+, delta_*, mu, M, W_inf, Lambda_g, sigma_K, sigma_B, sigma_T, c_T, eta_*) depend only on the data n,tau,s0,r0,B,h,L_h,C_B (never on f, eps, gamma); eta_0=A_0 eps gamma^-2 depends also on eps,gamma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:normalized-torus, bp:p4:parameters, step:p4:le-basic, step:p4:le-split, step:p4:le-h, step:p4:le-f, step:p4:le-transport, step:p4:le-sum, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:normalized-torus | blueprint/parts/p4-measure.tex#bp:p4:lip-error@L823-L824 | K_omega, W_omega
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#bp:p4:lip-error@L821-L821 | standing assumption (SA), lambda_*, A_1
EDGE: step:p4:le-basic | blueprint/parts/p4-measure.tex#bp:p4:lip-error@L832-L832 | proof step of this result
EDGE: step:p4:le-split | blueprint/parts/p4-measure.tex#bp:p4:lip-error@L838-L838 | proof step of this result
EDGE: step:p4:le-h | blueprint/parts/p4-measure.tex#bp:p4:lip-error@L853-L853 | proof step of this result
EDGE: step:p4:le-f | blueprint/parts/p4-measure.tex#bp:p4:lip-error@L860-L860 | proof step of this result
EDGE: step:p4:le-transport | blueprint/parts/p4-measure.tex#bp:p4:lip-error@L867-L867 | proof step of this result
EDGE: step:p4:le-sum | blueprint/parts/p4-measure.tex#bp:p4:lip-error@L871-L871 | proof step of this result
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#bp:p4:lip-error@L820-L829 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r2
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.lip_error
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:le-basic
KIND: step
TITLE: Elementary properties
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:le-basic@L832-L836
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:le-basic@L832-L836
CONTRACT_ID: step:p4:le-basic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA); omega,omega' close; K'=K_omega+(0,i Delta I)
SOURCE_QUANTIFIERS: omega,omega',gamma,eps
SOURCE_CONCLUSION: K' holomorphic, primary, real; K0_omega'=K0_omega+(0,i Delta I); |Delta I|<=L_+ |Delta omega|<=delta_*/4; |W_omega|+|Delta I|<=3 delta_*/4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:inverse-freq, bp:p4:smallness, bp:p4:parameters, bp:p4:SA, bp:p4:normalize
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:inverse-freq | blueprint/parts/p4-measure.tex#step:p4:le-basic@L834-L834 | /Delta I/<=L_+/Delta omega/
EDGE: bp:p4:smallness | blueprint/parts/p4-measure.tex#step:p4:le-basic@L835-L836 | (s3) is consumed at L836, not L835
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:le-basic@L834-L835 | Definition of lambda_* in the action-shift bound
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:le-basic@L832-L836 | Missing direct dependency on the explicit local package (SA), required by SPEC
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:le-basic@L833-L836 | Holomorphy, primarity, reality and ¦W_omega¦<=eta_0 must be supplied, not inferred from smallness alone
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.lip_error (normalize clauses), invarianceError_shift_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:le-split
KIND: step
TITLE: Splitting the error
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:le-split@L838-L851
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:le-split@L838-L851
CONTRACT_ID: step:p4:le-split
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: omega,omega' close; K_omega invariant on T_{s/8}; K'=K_omega+(0,i Delta I); pfh=h+f; Delta omega=grad h(i I_omega+i Delta I)-grad h(i I_omega)
SOURCE_QUANTIFIERS: theta in T_{s/8}
SOURCE_CONCLUSION: E'=(P_h,0)+P_f-DW_omega Delta omega with P_h the mixed difference of grad h and P_f=X_f(K'(theta))-X_f(K_omega(theta))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:normalize, bp:p4:freq-map
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:le-split@L839-L839 | X_pfh(K_omega)=DK_omega omega
EDGE: bp:p4:freq-map | blueprint/parts/p4-measure.tex#step:p4:le-split@L842-L842 | (ii): g=grad h at real points, Delta omega as gradient difference
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.invarianceError_shift_eq, hamiltonianVectorField_hbold, lipError_split
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:le-h
KIND: step
TITLE: The integrable part: a mixed difference
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:le-h@L853-L858
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:le-h@L853-L858
CONTRACT_ID: step:p4:le-h
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |W_omega|+|Delta I|<=3delta_*/4; points a+tv+t' i Delta I in B_{r0/2}
SOURCE_QUANTIFIERS: theta in T_{3s/32}; t,t' in [0,1]
SOURCE_CONCLUSION: |P_h|<=H_3 eta_0 L_+ |Delta omega|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:derivative-bounds, bp:p4:mixed-difference, step:p4:le-split, step:p4:le-basic, bp:p4:normalize
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:derivative-bounds | blueprint/parts/p4-measure.tex#step:p4:le-h@L855-L855 | (b): /D^3 h/<=H_3
EDGE: bp:p4:mixed-difference | blueprint/parts/p4-measure.tex#step:p4:le-h@L854-L858 | The mixed-difference lemma is invoked at L857, not L856
EDGE: step:p4:le-split | blueprint/parts/p4-measure.tex#step:p4:le-h@L854-L858 | P_h from the error decomposition is consumed in the estimate
EDGE: step:p4:le-basic | blueprint/parts/p4-measure.tex#step:p4:le-h@L854-L858 | Parallelogram containment uses the earlier action-shift bound
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:le-h@L854-L858 | The estimate uses ¦v_omega¦<=eta_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.gradC_mixed_difference, norm_iteratedFDeriv_two_gradC_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:le-f
KIND: step
TITLE: The perturbation
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:le-f@L860-L865
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:le-f@L860-L865
CONTRACT_ID: step:p4:le-f
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: segment from K_omega(theta) to K'(theta) stays within 3delta_*/4 of K0_omega(theta); |DX_f|<=F_2 eps on D
SOURCE_QUANTIFIERS: theta in T_{3s/32}
SOURCE_CONCLUSION: |P_f|<=F_2 eps |Delta I|<=F_2 eps L_+ |Delta omega|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:unperturbed, bp:p1:increments-open, bp:p4:derivative-bounds, step:p4:le-split, step:p4:le-basic
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:unperturbed | blueprint/parts/p4-measure.tex#step:p4:le-f@L862-L862 | (g): ball B_{delta_*}(K0_omega(theta)) in D
EDGE: bp:p1:increments-open | blueprint/parts/p4-measure.tex#step:p4:le-f@L861-L865 | The increment lemma is invoked at L864, not L863
EDGE: bp:p4:derivative-bounds | blueprint/parts/p4-measure.tex#step:p4:le-f@L863-L865 | The DX_f bound is used at L864
EDGE: step:p4:le-split | blueprint/parts/p4-measure.tex#step:p4:le-f@L861-L865 | The P_f expression is consumed in this increment estimate
EDGE: step:p4:le-basic | blueprint/parts/p4-measure.tex#step:p4:le-f@L861-L861 | 3delta_*/4 bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.norm_hamiltonianVectorField_f_shift_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:le-transport
KIND: step
TITLE: The transport term
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:le-transport@L867-L869
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:le-transport@L867-L869
CONTRACT_ID: step:p4:le-transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W_omega holomorphic on T_{s/8} with |W_omega|<=eta_0
SOURCE_QUANTIFIERS: theta in T_{3s/32}
SOURCE_CONCLUSION: |DW_omega|<=32 n eta_0/s
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cauchy-strip, bp:p4:normalize
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cauchy-strip | blueprint/parts/p4-measure.tex#step:p4:le-transport@L868-L868 | Cauchy estimate with loss s/32
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:le-transport@L868-L868 | W_omega holomorphic on T_{s/8} with /W_omega/<=eta_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.norm_fderiv_sub_unperturbed_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:le-sum
KIND: step
TITLE: Sum
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:le-sum@L871-L873
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:le-sum@L871-L873
CONTRACT_ID: step:p4:le-sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the three bounds for P_h, P_f, DW_omega Delta omega; gamma<=1
SOURCE_QUANTIFIERS: theta in T_{3s/32}
SOURCE_CONCLUSION: |E'|<=A_1 eps gamma^-2 |Delta omega|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:le-split, step:p4:le-h, step:p4:le-f, step:p4:le-transport, bp:p4:parameters
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:le-split | blueprint/parts/p4-measure.tex#step:p4:le-sum@L871-L871 | E' decomposition
EDGE: step:p4:le-h | blueprint/parts/p4-measure.tex#step:p4:le-sum@L871-L871 | bound on P_h
EDGE: step:p4:le-f | blueprint/parts/p4-measure.tex#step:p4:le-sum@L871-L871 | bound on P_f
EDGE: step:p4:le-transport | blueprint/parts/p4-measure.tex#step:p4:le-sum@L871-L871 | bound on DW_omega
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:le-sum@L872-L872 | definition of A_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.lipError_const_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-7-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:lip
KIND: theorem
TITLE: LIP
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:lip@L876-L882
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:lip@L884-L946
CONTRACT_ID: bp:p4:lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA)
SOURCE_QUANTIFIERS: gamma,eps with (SA); all omega,omega' in Omega_gamma; all theta in T_{s/32}
SOURCE_CONCLUSION: |W_omega'(theta)-W_omega(theta)|<=A_3 eps gamma^-4 |omega'-omega|
CONSTANT_SCOPE: A_3 depends only on the data (A_3=max(A_2,2A_0/lambda_*)); all named constants (c_*, A_0..A_4, lambda_*, L_+, delta_*, mu, M, W_inf, Lambda_g, sigma_K, sigma_B, sigma_T, c_T, eta_*) depend only on the data n,tau,s0,r0,B,h,L_h,C_B (never on f, eps, gamma); eta_0=A_0 eps gamma^-2 depends also on eps,gamma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:parameters, bp:p4:normalized-torus, step:p4:lip-far, step:p4:lip-g1, step:p4:lip-g2, step:p4:lip-phase, step:p4:lip-close, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#bp:p4:lip@L880-L880 | A_3 is the data-dependent constant defined in parameters; SA has its separate package edge
EDGE: bp:p4:normalized-torus | blueprint/parts/p4-measure.tex#bp:p4:lip@L880-L880 | W_omega defined there
EDGE: step:p4:lip-far | blueprint/parts/p4-measure.tex#bp:p4:lip@L885-L885 | proof step of this result
EDGE: step:p4:lip-g1 | blueprint/parts/p4-measure.tex#bp:p4:lip@L892-L892 | proof step of this result
EDGE: step:p4:lip-g2 | blueprint/parts/p4-measure.tex#bp:p4:lip@L913-L913 | proof step of this result
EDGE: step:p4:lip-phase | blueprint/parts/p4-measure.tex#bp:p4:lip@L929-L929 | proof step of this result
EDGE: step:p4:lip-close | blueprint/parts/p4-measure.tex#bp:p4:lip@L936-L936 | proof step of this result
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#bp:p4:lip@L876-L882 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.lip
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-10-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:lip-far
KIND: step
TITLE: Far pairs
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lip-far@L885-L890
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lip-far@L885-L890
CONTRACT_ID: step:p4:lip-far
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA); omega,omega' in Omega_gamma
SOURCE_QUANTIFIERS: omega,omega'
SOURCE_CONCLUSION: if |Delta omega|>lambda_* gamma^2 then |W_omega'-W_omega|<=(2A_0/lambda_*) eps gamma^-4 |Delta omega|; otherwise set e'=A_1 eps gamma^-2|Delta omega|<=A_1 lambda_* eps
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:normalize, bp:p4:lip-error, bp:p4:parameters, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:lip-far@L886-L886 | /W_omega/<=eta_0
EDGE: bp:p4:lip-error | blueprint/parts/p4-measure.tex#step:p4:lip-far@L888-L888 | K',E' for close pairs
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:lip-far@L887-L887 | lambda_*, A_0, A_1
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:lip-far@L885-L890 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Lip.far_case, far_arith
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-10-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:lip-g1
KIND: step
TITLE: Re-application of G1 at $\omega'$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lip-g1@L892-L911
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lip-g1@L892-L911
CONTRACT_ID: step:p4:lip-g1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed HEAD data and perturbation hypotheses of Part 4; (SA); omega,omega_prime in Omega_gamma with |Delta omega|<=lambda_* gamma^2; Delta omega=omega_prime-omega, Delta I=I_omega_prime-I_omega, K_prime=K_omega+(0,iota Delta I), and e_prime=A_1 epsilon gamma^(-2)|Delta omega| as constructed at L888-L890; no additional error-bound premise
SOURCE_QUANTIFIERS: omega,omega',gamma; G1 applied with second tuple rho=3s/32, rho_inf=s/16, e=e'
SOURCE_CONCLUSION: exists K~ holomorphic on T_{s/16}, primary, real, invariant with frequency omega', B_{mu/2}(K~) in D, |DK~|<=sigma_K-mu/2, |K~-K'|<=d_1=C_2^(2) e'/(gamma^2 (3s/32)^{2tau})
CONSTANT_SCOPE: all named constants (c_*, A_0..A_4, lambda_*, L_+, delta_*, mu, M, W_inf, Lambda_g, sigma_K, sigma_B, sigma_T, c_T, eta_*) depend only on the data n,tau,s0,r0,B,h,L_h,C_B (never on f, eps, gamma); eta_0=A_0 eps gamma^-2 depends also on eps,gamma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:g1, bp:p4:parameters, bp:p4:h1, bp:p4:stab, bp:p4:lip-error, bp:p4:smallness, bp:p4:inverse-freq, step:p4:lip-far, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:g1 | blueprint/parts/p4-measure.tex#step:p4:lip-g1@L893-L893 | frozen a-posteriori theorem applied
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:lip-g1@L893-L893 | second tuple, constants C_1^(2), C_2^(2)
EDGE: bp:p4:h1 | blueprint/parts/p4-measure.tex#step:p4:lip-g1@L897-L897 | H1 use is L897, not L895
EDGE: bp:p4:stab | blueprint/parts/p4-measure.tex#step:p4:lip-g1@L898-L901 | STAB application is at L898-L901, not L897
EDGE: bp:p4:lip-error | blueprint/parts/p4-measure.tex#step:p4:lip-g1@L900-L903 | K' primary, real, close to K0_omega', /E'/<=e'
EDGE: bp:p4:smallness | blueprint/parts/p4-measure.tex#step:p4:lip-g1@L897-L905 | (s1) supplies epsilon<=1 for H1 and STAB, (s3) supplies the STAB threshold, and (s4) supplies strict G1 smallness via a bound by 1/2
EDGE: bp:p4:inverse-freq | blueprint/parts/p4-measure.tex#step:p4:lip-g1@L898-L901 | The reference action and frequency bounds are used in the STAB application
EDGE: step:p4:lip-far | blueprint/parts/p4-measure.tex#step:p4:lip-g1@L895-L895 | definition of e' and close-pair assumption
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:lip-g1@L892-L911 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Lip.g1_step, err_le, g1_small
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-10-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:lip-g2
KIND: step
TITLE: Local uniqueness at $\omega'$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lip-g2@L913-L927
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lip-g2@L913-L927
CONTRACT_ID: step:p4:lip-g2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA); K~ from the G1 step; K_omega' normalized
SOURCE_QUANTIFIERS: omega',gamma; G2 applied with rho=s/16, K_1=K_omega', K_2=K~
SOURCE_CONCLUSION: exists phi in R^n with K~(theta)=K_omega'(theta+i phi) for theta in T_{s/32}
CONSTANT_SCOPE: all named constants (c_*, A_0..A_4, lambda_*, L_+, delta_*, mu, M, W_inf, Lambda_g, sigma_K, sigma_B, sigma_T, c_T, eta_*) depend only on the data n,tau,s0,r0,B,h,L_h,C_B (never on f, eps, gamma); eta_0=A_0 eps gamma^-2 depends also on eps,gamma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:g2, bp:p4:parameters, bp:p4:h1, bp:p4:stab, bp:p4:normalize, bp:p4:smallness, step:p4:lip-g1, bp:p4:lip-error, bp:p4:inverse-freq, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:g2 | blueprint/parts/p4-measure.tex#step:p4:lip-g2@L914-L914 | frozen local uniqueness theorem applied
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:lip-g2@L914-L914 | tuple and c_G
EDGE: bp:p4:h1 | blueprint/parts/p4-measure.tex#step:p4:lip-g2@L917-L917 | H1 use is L917, not the itemize delimiter at L916
EDGE: bp:p4:stab | blueprint/parts/p4-measure.tex#step:p4:lip-g2@L918-L918 | H2-H4 for K_omega' on T_{s/16}
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:lip-g2@L920-L920 | K_omega' primary, real, E_1=0, Diophantine
EDGE: bp:p4:smallness | blueprint/parts/p4-measure.tex#step:p4:lip-g2@L919-L919 | (s3), (s5) closeness
EDGE: step:p4:lip-g1 | blueprint/parts/p4-measure.tex#step:p4:lip-g2@L921-L924 | G1 output properties and closeness are consumed here, not on L914
EDGE: bp:p4:lip-error | blueprint/parts/p4-measure.tex#step:p4:lip-g2@L924-L924 | K'-K0_omega'=W_omega, /K0_omega'-K'/ closeness
EDGE: bp:p4:inverse-freq | blueprint/parts/p4-measure.tex#step:p4:lip-g2@L918-L918 | I_omega' in B
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:lip-g2@L913-L927 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Lip.g2_step, close_arith
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-10-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:lip-phase
KIND: step
TITLE: The phase is controlled by normalization
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lip-phase@L929-L934
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lip-phase@L929-L934
CONTRACT_ID: step:p4:lip-phase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K~=K_omega'(.+i phi) on real points; ph(K_omega')=ph(K_omega)=0; angle components of K' and K_omega coincide
SOURCE_QUANTIFIERS: phi in R^n
SOURCE_CONCLUSION: ph(K~)=phi and |phi|<=d_1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:periodic-average, step:p4:lip-g2, bp:p4:normalize, bp:p4:phase-average, step:p4:lip-g1, bp:p4:lip-error, bp:p1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:periodic-average | blueprint/parts/p4-measure.tex#step:p4:lip-phase@L930-L934 | The average lemma is invoked at L931
EDGE: step:p4:lip-g2 | blueprint/parts/p4-measure.tex#step:p4:lip-phase@L930-L930 | The shifted-torus identity is used in the first formula, not the heading
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:lip-phase@L931-L931 | ph(K_omega')=ph(K_omega)=0
EDGE: bp:p4:phase-average | blueprint/parts/p4-measure.tex#step:p4:lip-phase@L930-L930 | u_K, ph
EDGE: step:p4:lip-g1 | blueprint/parts/p4-measure.tex#step:p4:lip-phase@L933-L933 | /K~-K'/<=d_1
EDGE: bp:p4:lip-error | blueprint/parts/p4-measure.tex#step:p4:lip-phase@L932-L932 | K' and K_omega share angle component
EDGE: bp:p1:ext-integral | blueprint/parts/p4-measure.tex#step:p4:lip-phase@L933-L934 | The bound ¦phi¦<=d_1 uses the integral norm inequality
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Lip.norm_phi_le, norm_phaseAverage_sub_le, phaseAverage_shiftedTorus
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-10-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:lip-close
KIND: step
TITLE: Conclusion for close pairs
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lip-close@L936-L945
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lip-close@L936-L945
CONTRACT_ID: step:p4:lip-close
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K~(theta)=K_omega'(theta+i phi); |phi|<=d_1; |DK~|<=sigma_K on T_{s/16}
SOURCE_QUANTIFIERS: theta in T_{s/32}
SOURCE_CONCLUSION: |W_omega'(theta)-W_omega(theta)|<=(sigma_K+1)d_1=A_2 eps gamma^-4|Delta omega|<=A_3 eps gamma^-4|Delta omega|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:increments, step:p4:lip-phase, step:p4:lip-g1, step:p4:lip-g2, bp:p4:lip-error, bp:p4:parameters
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:increments | blueprint/parts/p4-measure.tex#step:p4:lip-close@L940-L944 | The increment lemma is invoked at L942, not the display delimiter at L941
EDGE: step:p4:lip-phase | blueprint/parts/p4-measure.tex#step:p4:lip-close@L940-L940 | The phase bound is used in the last inequality at L940
EDGE: step:p4:lip-g1 | blueprint/parts/p4-measure.tex#step:p4:lip-close@L940-L944 | The G1 distance and derivative bounds are used at L940-L944
EDGE: step:p4:lip-g2 | blueprint/parts/p4-measure.tex#step:p4:lip-close@L937-L937 | K_omega'(theta)=K~(theta-i phi)
EDGE: bp:p4:lip-error | blueprint/parts/p4-measure.tex#step:p4:lip-close@L938-L938 | W_omega'-W_omega=K_omega'-K'
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:lip-close@L944-L944 | A_2, A_3 definitions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.Lip.close_case, final_arith
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-10-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:lagrangian
KIND: lemma
TITLE: Invariant tori with nonresonant frequency are Lagrangian
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:lagrangian@L961-L966
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:lagrangian@L973-L1007
CONTRACT_ID: bp:p4:lagrangian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: eps<=1; rho>0, gamma>0, omega in Dio_{gamma,tau}; K holomorphic and primary on T_rho, K(T_rho) in D, DK bounded on T_rho, E=0 at omega on T_rho
SOURCE_QUANTIFIERS: rho,gamma,omega,K; theta in T_rho
SOURCE_CONCLUSION: Lambda(theta)=DK(theta)^T Omega_0 DK(theta)=0 on T_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:lag-regular, step:p4:lag-exact, step:p4:lag-transport, step:p4:lag-unique, bp:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:lag-regular | blueprint/parts/p4-measure.tex#bp:p4:lagrangian@L974-L974 | proof step
EDGE: step:p4:lag-exact | blueprint/parts/p4-measure.tex#bp:p4:lagrangian@L980-L980 | proof step
EDGE: step:p4:lag-transport | blueprint/parts/p4-measure.tex#bp:p4:lagrangian@L990-L990 | proof step
EDGE: step:p4:lag-unique | blueprint/parts/p4-measure.tex#bp:p4:lagrangian@L1001-L1001 | proof step
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#bp:p4:lagrangian@L962-L962 | D and pfh fixed there
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.lagrangian
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-8-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:lag-regular
KIND: step
TITLE: Regularity and periodicity
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lag-regular@L974-L978
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lag-regular@L974-L978
CONTRACT_ID: step:p4:lag-regular
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K=(theta+u,v) primary on T_rho, DK bounded, K holomorphic
SOURCE_QUANTIFIERS: rho
SOURCE_CONCLUSION: DK periodic and holomorphic; Lambda holomorphic, periodic, bounded on T_rho; u,v,Du bounded on T_{rho/2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-regularity, bp:p1:periodic-bounded
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p4-measure.tex#step:p4:lag-regular@L975-L978 | DK holomorphy is cited at L977
EDGE: bp:p1:periodic-bounded | blueprint/parts/p4-measure.tex#step:p4:lag-regular@L977-L978 | The periodic boundedness lemma is cited at L978
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: BYPASSED
LEAN_REF: KAM.Head.lagrangeMat_regular (holomorphy and periodicity only)
LEAN_NOTE: route substitution (D27; overnight ruling 23:00): KAM.Head.lagrangian applies coh_unique_zero directly on T_ρ, which needs no boundedness of Λ, u, v, Du; the bound clauses of this step are therefore not formalized. Audit docs/campaign/audits/P4-8-audit-1.md F1 (major for the step mapping; main theorem PASS)
NOTE: -

NODE: step:p4:lag-exact
KIND: step
TITLE: $\Lambda$ is a sum of derivatives
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lag-exact@L980-L988
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lag-exact@L980-L988
CONTRACT_ID: step:p4:lag-exact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lambda holomorphic, periodic, bounded on T_rho; u,v,Du bounded on T_{rho/2}
SOURCE_QUANTIFIERS: rho
SOURCE_CONCLUSION: avg Lambda=0: each entry is a sum of partial derivatives of bounded periodic holomorphic functions
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:matrix-norms, bp:p1:averages, step:p4:lag-regular
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:matrix-norms | blueprint/parts/p4-measure.tex#step:p4:lag-exact@L981-L981 | (iv): Lambda_ij formula
EDGE: bp:p1:averages | blueprint/parts/p4-measure.tex#step:p4:lag-exact@L987-L987 | average of a derivative of a periodic holomorphic function is 0
EDGE: step:p4:lag-regular | blueprint/parts/p4-measure.tex#step:p4:lag-exact@L987-L988 | The averages application consumes bounded periodic holomorphic factors
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.avg_lagrangeMat_eq_zero (via bp:p2:exactness)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-8-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:lag-transport
KIND: step
TITLE: $\Lambda$ is constant along $\omega$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lag-transport@L990-L999
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lag-transport@L990-L999
CONTRACT_ID: step:p4:lag-transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: X_pfh(K)=DK omega on T_rho; S symmetric complex Hessian of pfh
SOURCE_QUANTIFIERS: rho,omega
SOURCE_CONCLUSION: partial_omega Lambda_ij=0 on T_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:holomorphic-regularity, step:p4:db-vectorfield, bp:p4:matrix-norms
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:holomorphic-regularity | blueprint/parts/p4-measure.tex#step:p4:lag-transport@L991-L991 | symmetry of D^2K
EDGE: step:p4:db-vectorfield | blueprint/parts/p4-measure.tex#step:p4:lag-transport@L993-L993 | DX_pfh=-Omega_0 S with S symmetric
EDGE: bp:p4:matrix-norms | blueprint/parts/p4-measure.tex#step:p4:lag-transport@L996-L996 | (iv): Omega_0 identities
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.fderiv_lagrangeMat_omega
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-8-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:lag-unique
KIND: step
TITLE: Uniqueness for the cohomological equation
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lag-unique@L1001-L1006
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:lag-unique@L1001-L1006
CONTRACT_ID: step:p4:lag-unique
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: avg Lambda=0 and partial_omega Lambda=0 on T_{rho/2}; omega in Dio_{gamma,tau}
SOURCE_QUANTIFIERS: rho,gamma,omega; entries i,j
SOURCE_CONCLUSION: Lambda=0 on T_{rho/4}, hence on T_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cohomological, step:p4:lag-exact, step:p4:lag-transport, bp:p1:strip-identity, step:p4:lag-regular
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cohomological | blueprint/parts/p4-measure.tex#step:p4:lag-unique@L1002-L1005 | Cohomological uniqueness is invoked at L1002, not the heading
EDGE: step:p4:lag-exact | blueprint/parts/p4-measure.tex#step:p4:lag-unique@L1004-L1004 | avg Lambda_ij=0
EDGE: step:p4:lag-transport | blueprint/parts/p4-measure.tex#step:p4:lag-unique@L1004-L1005 | The transport step is invoked at L1005
EDGE: bp:p1:strip-identity | blueprint/parts/p4-measure.tex#step:p4:lag-unique@L1006-L1006 | extension from T_{rho/4} to T_rho
EDGE: step:p4:lag-regular | blueprint/parts/p4-measure.tex#step:p4:lag-unique@L1003-L1003 | Lambda holomorphic periodic
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.lagrangian (coh_unique_zero entrywise on T_ρ)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-8-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:real-torus
KIND: theorem
TITLE: The real tori are KAM tori
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1009-L1021
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1023-L1069
CONTRACT_ID: bp:p4:real-torus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA); omega in Omega_gamma; k_omega real restriction of K_omega
SOURCE_QUANTIFIERS: gamma,eps with (SA); omega in Omega_gamma
SOURCE_CONCLUSION: (i) k_omega invariant Lagrangian torus of H=realHamiltonian h f with frequency omega; (ii) |k_omega(x)_2-I_omega|<r0, I_omega in B; (iii) I_omega in B, g(I_omega)=omega; (iv) |k_omega(x)-(x,I_omega)|<=eta_0; hence k_omega(R^n) in kamCover(eta_0) with witnesses k_omega,omega,gamma,I_omega
CONSTANT_SCOPE: all named constants (c_*, A_0..A_4, lambda_*, L_+, delta_*, mu, M, W_inf, Lambda_g, sigma_K, sigma_B, sigma_T, c_T, eta_*) depend only on the data n,tau,s0,r0,B,h,L_h,C_B (never on f, eps, gamma); eta_0=A_0 eps gamma^-2 depends also on eps,gamma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:normalized-torus, bp:p0:nearlyintegrable#realHamiltonian, bp:p0:nearlyintegrable#frequencyMap, bp:p0:cover#kamCover, step:p4:rt-analytic, step:p4:rt-small, step:p4:rt-immersion, step:p4:rt-embedding, step:p4:rt-lagrangian, step:p4:rt-ode, step:p4:rt-cover, bp:p4:SA, bp:p0:torus#IsInvariantLagrangianTorus, bp:p1:real-restriction
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:normalized-torus | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1010-L1010 | K_omega
EDGE: bp:p0:nearlyintegrable#realHamiltonian | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1013-L1014 | H=realHamiltonian h f
EDGE: bp:p0:nearlyintegrable#frequencyMap | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1016-L1016 | The frequency identity is on L1016, not the cover-membership line L1019
EDGE: bp:p0:cover#kamCover | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1020-L1020 | conclusion membership in the cover
EDGE: step:p4:rt-analytic | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1024-L1024 | proof step of this result
EDGE: step:p4:rt-small | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1028-L1028 | proof step of this result
EDGE: step:p4:rt-immersion | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1035-L1035 | proof step of this result
EDGE: step:p4:rt-embedding | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1039-L1039 | proof step of this result
EDGE: step:p4:rt-lagrangian | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1045-L1045 | proof step of this result
EDGE: step:p4:rt-ode | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1052-L1052 | proof step of this result
EDGE: step:p4:rt-cover | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1063-L1063 | proof step of this result
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1009-L1021 | Missing direct dependency on the explicit local package (SA), required by SPEC
EDGE: bp:p0:torus#IsInvariantLagrangianTorus | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1013-L1014 | the conclusion uses the six-clause frozen invariant Lagrangian torus predicate
EDGE: bp:p1:real-restriction | blueprint/parts/p4-measure.tex#bp:p4:real-torus@L1010-L1011 | k_omega is defined as the real restriction of K_omega using the cited real-restriction lemma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.real_torus
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/P4-9-audit-1.md (F1 rt-small) and P4-9-audit-2.md (F1 closed, PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:rt-analytic
KIND: step
TITLE: Analyticity and primarity
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-analytic@L1024-L1026
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-analytic@L1024-L1026
CONTRACT_ID: step:p4:rt-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed HEAD data and perturbation hypotheses of Part 4; (SA); omega in Omega_gamma; K_omega is the normalized-torus construction and k_omega its real restriction as defined at L1010-L1011
SOURCE_QUANTIFIERS: gamma,epsilon satisfying (SA); omega in Omega_gamma; x in R^n and m in Z^n for the primarity conclusion
SOURCE_CONCLUSION: k_omega is real analytic and primary: k_omega(x+m)=k_omega(x)+(m,0) for every real x and integer m
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:real-restriction, bp:p4:normalize, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:real-restriction | blueprint/parts/p4-measure.tex#step:p4:rt-analytic@L1025-L1026 | The restriction lemma is used at L1025, not the heading
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:rt-analytic@L1026-L1026 | K_omega holomorphic, primary, real
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:rt-analytic@L1025-L1026 | the inherited local SA package and omega in Omega_gamma are the premises for normalize at K_omega
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.rt_analytic
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/P4-9-audit-1.md (F1 rt-small) and P4-9-audit-2.md (F1 closed, PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:rt-small
KIND: step
TITLE: Small angle displacement
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-small@L1028-L1033
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-small@L1028-L1033
CONTRACT_ID: step:p4:rt-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W_omega holomorphic on T_{s/8}, |W_omega|<=eta_0
SOURCE_QUANTIFIERS: omega
SOURCE_CONCLUSION: |DW_omega|<=16 n eta_0/s<=1/2 on T_{s/16}; |D u~(x)|<=1/2 for real x; u~ Z^n-periodic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:cauchy-strip, bp:p1:real-restriction, bp:p4:smallness, bp:p4:normalize
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:cauchy-strip | blueprint/parts/p4-measure.tex#step:p4:rt-small@L1030-L1030 | Cauchy estimate with loss s/16
EDGE: bp:p1:real-restriction | blueprint/parts/p4-measure.tex#step:p4:rt-small@L1031-L1033 | The real derivative restriction is used at L1032
EDGE: bp:p4:smallness | blueprint/parts/p4-measure.tex#step:p4:rt-small@L1031-L1031 | (s3): 16 n eta_0/s<=1/2
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:rt-small@L1029-L1029 | W_omega bounded and holomorphic
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.rt_small_full, rt_small_normDisp, rt_small_complex, rt_small, angleReal_add_int
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/P4-9-audit-1.md (F1 rt-small) and P4-9-audit-2.md (F1 closed, PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:rt-immersion
KIND: step
TITLE: Immersion
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-immersion@L1035-L1037
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-immersion@L1035-L1037
CONTRACT_ID: step:p4:rt-immersion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |D u~|<=1/2 on R^n
SOURCE_QUANTIFIERS: x,v
SOURCE_CONCLUSION: Dk_omega(x) is injective
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:rt-small
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:rt-small | blueprint/parts/p4-measure.tex#step:p4:rt-immersion@L1036-L1037 | The derivative bound is consumed in the lower bound, not the heading
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.rt_immersion
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/P4-9-audit-1.md (F1 rt-small) and P4-9-audit-2.md (F1 closed, PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:rt-embedding
KIND: step
TITLE: Embedding modulo $\Z^n$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-embedding@L1039-L1043
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-embedding@L1039-L1043
CONTRACT_ID: step:p4:rt-embedding
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |D u~|<=1/2 on R^n; u~ Z^n-periodic
SOURCE_QUANTIFIERS: x,x' in R^n, m in Z^n
SOURCE_CONCLUSION: k_omega(x')=k_omega(x)+(m,0) implies x'=x+m
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:rt-small, bp:p1:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:rt-small | blueprint/parts/p4-measure.tex#step:p4:rt-embedding@L1041-L1041 | /D u~/<=1/2 and periodicity of u~
EDGE: bp:p1:ext-mvt | blueprint/parts/p4-measure.tex#step:p4:rt-embedding@L1041-L1043 | The derivative bound is integrated along the real segment on the convex set R^n
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.rt_embedding
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/P4-9-audit-1.md (F1 rt-small) and P4-9-audit-2.md (F1 closed, PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:rt-lagrangian
KIND: step
TITLE: Lagrangian
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-lagrangian@L1045-L1050
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-lagrangian@L1045-L1050
CONTRACT_ID: step:p4:rt-lagrangian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Lemma lagrangian hypotheses for K_omega on T_{s/8}
SOURCE_QUANTIFIERS: x,u,v in R^n
SOURCE_CONCLUSION: symplecticForm(Dk_omega(x)u,Dk_omega(x)v)=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:lagrangian, bp:p4:normalize, bp:p4:matrix-norms, bp:p1:real-restriction, bp:p4:smallness
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:lagrangian | blueprint/parts/p4-measure.tex#step:p4:rt-lagrangian@L1046-L1050 | The Lagrangian lemma is applied at L1046
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:rt-lagrangian@L1046-L1046 | K_omega properties
EDGE: bp:p4:matrix-norms | blueprint/parts/p4-measure.tex#step:p4:rt-lagrangian@L1049-L1050 | Matrix-form comparison with the real symplectic form occurs at L1049-L1050
EDGE: bp:p1:real-restriction | blueprint/parts/p4-measure.tex#step:p4:rt-lagrangian@L1049-L1049 | derivative of real restriction
EDGE: bp:p4:smallness | blueprint/parts/p4-measure.tex#step:p4:rt-lagrangian@L1048-L1048 | (s1): eps<=1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.rt_lagrangian, dotProduct_mulVec_lagrange
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/P4-9-audit-1.md (F1 rt-small) and P4-9-audit-2.md (F1 closed, PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:rt-ode
KIND: step
TITLE: Hamilton's equations
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-ode@L1052-L1061
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-ode@L1052-L1061
CONTRACT_ID: step:p4:rt-ode
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K_omega invariant on T_{s/8}; pfh holomorphic on D and real at real points
SOURCE_QUANTIFIERS: x in R^n, t in R; y=x+t omega
SOURCE_CONCLUSION: d/dt' k_omega(x+t' omega)=X_H(k_omega(y)), clause (vi) of Definition torus
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:hamiltonian-real, bp:p4:h1, bp:p0:nearlyintegrable#realHamiltonian, bp:p1:real-restriction, bp:p0:torus#IsInvariantLagrangianTorus, bp:p4:normalize, bp:p4:smallness
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:hamiltonian-real | blueprint/parts/p4-measure.tex#step:p4:rt-ode@L1054-L1054 | real and complex Hamiltonian fields agree at real points
EDGE: bp:p4:h1 | blueprint/parts/p4-measure.tex#step:p4:rt-ode@L1055-L1055 | pfh holomorphic on D and real
EDGE: bp:p0:nearlyintegrable#realHamiltonian | blueprint/parts/p4-measure.tex#step:p4:rt-ode@L1056-L1056 | H=Re pfh o iota at real points
EDGE: bp:p1:real-restriction | blueprint/parts/p4-measure.tex#step:p4:rt-ode@L1060-L1060 | derivative of real restriction
EDGE: bp:p0:torus#IsInvariantLagrangianTorus | blueprint/parts/p4-measure.tex#step:p4:rt-ode@L1061-L1061 | clause (vi) of the torus definition
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:rt-ode@L1058-L1058 | invariance at i y in T_{s/8}, K_omega(iy) in D
EDGE: bp:p4:smallness | blueprint/parts/p4-measure.tex#step:p4:rt-ode@L1055-L1055 | (s1) for H1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.rt_ode
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/P4-9-audit-1.md (F1 rt-small) and P4-9-audit-2.md (F1 closed, PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:rt-cover
KIND: step
TITLE: Cover clauses
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-cover@L1063-L1068
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:rt-cover@L1063-L1068
CONTRACT_ID: step:p4:rt-cover
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |W_omega|<=eta_0 on T_{s/8}; eta_0<=mu<r0
SOURCE_QUANTIFIERS: x in R^n
SOURCE_CONCLUSION: clauses (ii),(iii),(iv) and all clauses of Definition cover with radius eta_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:normalize, bp:p4:inverse-freq, bp:p0:cover#kamCover, bp:p4:smallness, step:p4:rt-analytic, step:p4:rt-immersion, step:p4:rt-embedding, step:p4:rt-lagrangian, step:p4:rt-ode
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:rt-cover@L1064-L1064 | /W_omega/<=eta_0
EDGE: bp:p4:inverse-freq | blueprint/parts/p4-measure.tex#step:p4:rt-cover@L1066-L1066 | Inverse-frequency clause (iii) is invoked at L1066
EDGE: bp:p0:cover#kamCover | blueprint/parts/p4-measure.tex#step:p4:rt-cover@L1067-L1067 | clauses of the cover definition
EDGE: bp:p4:smallness | blueprint/parts/p4-measure.tex#step:p4:rt-cover@L1065-L1065 | (s3): eta_0<=mu<r0
EDGE: step:p4:rt-analytic | blueprint/parts/p4-measure.tex#step:p4:rt-cover@L1066-L1068 | Cover membership requires the already established analytic and primary clauses
EDGE: step:p4:rt-immersion | blueprint/parts/p4-measure.tex#step:p4:rt-cover@L1066-L1068 | Missing direct discharge of the invariant Lagrangian torus premise in the cover application
EDGE: step:p4:rt-embedding | blueprint/parts/p4-measure.tex#step:p4:rt-cover@L1066-L1068 | Missing direct discharge of the invariant Lagrangian torus premise in the cover application
EDGE: step:p4:rt-lagrangian | blueprint/parts/p4-measure.tex#step:p4:rt-cover@L1066-L1068 | Missing direct discharge of the invariant Lagrangian torus premise in the cover application
EDGE: step:p4:rt-ode | blueprint/parts/p4-measure.tex#step:p4:rt-cover@L1066-L1068 | Missing direct discharge of the invariant Lagrangian torus premise in the cover application
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.rt_cover
LEAN_NOTE: prover evidence + independent audits docs/campaign/audits/P4-9-audit-1.md (F1 rt-small) and P4-9-audit-2.md (F1 closed, PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:preimage-measure
KIND: lemma
TITLE: Actions with non-Diophantine frequency
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:preimage-measure@L1087-L1093
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:preimage-measure@L1095-L1100
CONTRACT_ID: bp:p4:preimage-measure
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: C_3 the constant of G3 for the bounded set Omega=g(B); C_3^+=max(C_3,0)
SOURCE_QUANTIFIERS: alpha>0
SOURCE_CONCLUSION: meas{I in B: g(I) not in Dio_{alpha,tau}}<=L_+^n C_3^+ alpha
CONSTANT_SCOPE: C_3 is the G3 constant for Omega=g(B), depends only on (n,tau,Omega); L_+ depends only on L_h
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:pm-proof, bp:p0:g3, bp:p4:freq-map
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:pm-proof | blueprint/parts/p4-measure.tex#bp:p4:preimage-measure@L1096-L1096 | proof step
EDGE: bp:p0:g3 | blueprint/parts/p4-measure.tex#bp:p4:preimage-measure@L1088-L1088 | constant C_3 of G3
EDGE: bp:p4:freq-map | blueprint/parts/p4-measure.tex#bp:p4:preimage-measure@L1088-L1088 | (v): g(B) bounded
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.preimage_measure
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-6-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:pm-proof
KIND: step
TITLE: Image under the inverse frequency map
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:pm-proof@L1096-L1099
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:pm-proof@L1096-L1099
CONTRACT_ID: step:p4:pm-proof
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: g inverse is L_+-Lipschitz on g(bar B); G3 bound for {omega in g(B) not in Dio_{alpha,tau}}
SOURCE_QUANTIFIERS: alpha>0
SOURCE_CONCLUSION: the action set has measure <=L_+^n C_3^+ alpha
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:inverse-freq, bp:p1:lip-image, bp:p0:g3
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:inverse-freq | blueprint/parts/p4-measure.tex#step:p4:pm-proof@L1097-L1098 | Inverse Lipschitz use is at L1097-L1098, not the heading
EDGE: bp:p1:lip-image | blueprint/parts/p4-measure.tex#step:p4:pm-proof@L1099-L1099 | The image-measure lemma is invoked at L1099
EDGE: bp:p0:g3 | blueprint/parts/p4-measure.tex#step:p4:pm-proof@L1099-L1099 | measure of non-Diophantine frequencies
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.preimage_measure
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-6-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:good-actions
KIND: definition
TITLE: Good actions and the displacement
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:good-actions@L1102-L1111
PROOF_SOURCE: -
CONTRACT_ID: bp:p4:good-actions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA)
SOURCE_QUANTIFIERS: gamma,eps with (SA)
SOURCE_CONCLUSION: defines Z, A_gamma, G_0 on R^n x (A_gamma u Z); G_0(theta,I) is the real restriction of W_{g(I)} on A_gamma
CONSTANT_SCOPE: all named constants (c_*, A_0..A_4, lambda_*, L_+, delta_*, mu, M, W_inf, Lambda_g, sigma_K, sigma_B, sigma_T, c_T, eta_*) depend only on the data n,tau,s0,r0,B,h,L_h,C_B (never on f, eps, gamma); eta_0=A_0 eps gamma^-2 depends also on eps,gamma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:inverse-freq, bp:p4:real-torus, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:inverse-freq | blueprint/parts/p4-measure.tex#bp:p4:good-actions@L1109-L1109 | g(I) in Omega_gamma and I_{g(I)}=I
EDGE: bp:p4:real-torus | blueprint/parts/p4-measure.tex#bp:p4:good-actions@L1107-L1107 | k_omega, real restriction of K_omega
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#bp:p4:good-actions@L1102-L1111 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r2
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.good_actions
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: bp:p4:map-lipschitz
KIND: lemma
TITLE: The displacement is small and $\tfrac12$-Lipschitz
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:map-lipschitz@L1113-L1116
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:map-lipschitz@L1118-L1140
CONTRACT_ID: bp:p4:map-lipschitz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA)
SOURCE_QUANTIFIERS: gamma,eps with (SA)
SOURCE_CONCLUSION: A_gamma and Z are disjoint, |G_0|<=eta_0 and G_0 is 1/2-Lipschitz on R^n x (A_gamma u Z) for the max norm
CONSTANT_SCOPE: all named constants (c_*, A_0..A_4, lambda_*, L_+, delta_*, mu, M, W_inf, Lambda_g, sigma_K, sigma_B, sigma_T, c_T, eta_*) depend only on the data n,tau,s0,r0,B,h,L_h,C_B (never on f, eps, gamma); eta_0=A_0 eps gamma^-2 depends also on eps,gamma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:ml-size, step:p4:ml-good, step:p4:ml-mixed, bp:p4:good-actions, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:ml-size | blueprint/parts/p4-measure.tex#bp:p4:map-lipschitz@L1119-L1119 | proof step
EDGE: step:p4:ml-good | blueprint/parts/p4-measure.tex#bp:p4:map-lipschitz@L1123-L1123 | proof step
EDGE: step:p4:ml-mixed | blueprint/parts/p4-measure.tex#bp:p4:map-lipschitz@L1133-L1133 | proof step
EDGE: bp:p4:good-actions | blueprint/parts/p4-measure.tex#bp:p4:map-lipschitz@L1114-L1114 | G_0, A_gamma, Z
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#bp:p4:map-lipschitz@L1113-L1116 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r2
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.map_lipschitz (map_lipschitz_of_lip)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:ml-size
KIND: step
TITLE: Disjointness and size
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:ml-size@L1119-L1121
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:ml-size@L1119-L1121
CONTRACT_ID: step:p4:ml-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA)
SOURCE_QUANTIFIERS: I in A_gamma
SOURCE_CONCLUSION: A_gamma cap Z empty; |G_0|<=eta_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:normalize, bp:p4:good-actions, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:normalize | blueprint/parts/p4-measure.tex#step:p4:ml-size@L1121-L1121 | /W_omega/<=eta_0
EDGE: bp:p4:good-actions | blueprint/parts/p4-measure.tex#step:p4:ml-size@L1120-L1121 | A_gamma, Z, G_0
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:ml-size@L1119-L1121 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r2
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.disjoint_goodActions_layerSet, norm_disp_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:ml-good
KIND: step
TITLE: Two good actions
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:ml-good@L1123-L1131
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:ml-good@L1123-L1131
CONTRACT_ID: step:p4:ml-good
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed HEAD data and perturbation hypotheses of Part 4; (SA); Z,A_gamma,G_0 as defined in good-actions; the derivative estimate is supplied by rt-small, not assumed
SOURCE_QUANTIFIERS: I,J in A_gamma; theta,theta' in R^n
SOURCE_CONCLUSION: |G_0(theta,I)-G_0(theta',J)|<=(1/4)|(theta,I)-(theta',J)|
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:rt-small, bp:p4:lip, bp:p4:freq-map, bp:p4:smallness, bp:p4:good-actions, bp:p4:parameters, bp:p4:SA, bp:p1:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:rt-small | blueprint/parts/p4-measure.tex#step:p4:ml-good@L1124-L1124 | derivative bound 16 n eta_0/s on R^n
EDGE: bp:p4:lip | blueprint/parts/p4-measure.tex#step:p4:ml-good@L1126-L1126 | Lipschitz dependence on omega
EDGE: bp:p4:freq-map | blueprint/parts/p4-measure.tex#step:p4:ml-good@L1126-L1126 | (v): g is Lambda_g-Lipschitz on B
EDGE: bp:p4:smallness | blueprint/parts/p4-measure.tex#step:p4:ml-good@L1129-L1129 | (s6)
EDGE: bp:p4:good-actions | blueprint/parts/p4-measure.tex#step:p4:ml-good@L1124-L1129 | G_0, A_gamma
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:ml-good@L1125-L1129 | A_4, A_3, Lambda_g definitions
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:ml-good@L1123-L1131 | Missing direct dependency on the explicit local package (SA), required by SPEC
EDGE: bp:p1:ext-mvt | blueprint/parts/p4-measure.tex#step:p4:ml-good@L1124-L1129 | The real derivative bound is converted to a difference bound on convex R^n
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-d2
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.disp_sub_le_good_good
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:ml-mixed
KIND: step
TITLE: A good action and a boundary action
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:ml-mixed@L1133-L1139
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:ml-mixed@L1133-L1139
CONTRACT_ID: step:p4:ml-mixed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA); I in A_gamma, J in Z; theta,theta_prime in R^n; G_0 as defined in good-actions
SOURCE_QUANTIFIERS: I in A_gamma, J in Z
SOURCE_CONCLUSION: |G_0(theta,I)-G_0(theta',J)|<=(1/2)|(theta,I)-(theta',J)|; two boundary actions give 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:smallness, step:p4:ml-size, bp:p4:good-actions, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:smallness | blueprint/parts/p4-measure.tex#step:p4:ml-mixed@L1137-L1137 | (s7): eta_0<=gamma/2
EDGE: step:p4:ml-size | blueprint/parts/p4-measure.tex#step:p4:ml-mixed@L1138-L1138 | /G_0/<=eta_0
EDGE: bp:p4:good-actions | blueprint/parts/p4-measure.tex#step:p4:ml-mixed@L1134-L1136 | A_gamma, Z, G_0
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:ml-mixed@L1133-L1139 | Missing direct dependency on the explicit local package (SA), required by SPEC
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-d3
REVIEWER: sol-review-d4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.disp_sub_le_mixed
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: repaired F1: the 1-Lipschitz property of infDist(.,B^c) is now proved inline in the step

NODE: bp:p4:main-measure
KIND: theorem
TITLE: Measure of the complement at a given $\gamma$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:main-measure@L1142-L1149
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:main-measure@L1151-L1186
CONTRACT_ID: bp:p4:main-measure
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (SA); B nonempty; fixed HEAD data (n>=2, tau>n-1, s0,r0>0, B open bounded nonempty, h holomorphic on B_{r0} and real at real points, witnesses L_h, C_B); C_meas=2C_B^++(9/2)^n(2C_B^++L_+^n C_3^+)
SOURCE_QUANTIFIERS: gamma,eps with (SA)
SOURCE_CONCLUSION: meas(F_B minus kamCover(eta_0)) <= C_meas gamma
CONSTANT_SCOPE: C_meas depends only on n, C_B, L_+, C_3 (data); not on f, eps, gamma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:mm-extension, step:p4:mm-tori, step:p4:mm-complement, step:p4:mm-bad, step:p4:mm-count, bp:p0:cover#kamCover, bp:p4:SA, bp:p4:data, bp:p4:preimage-measure
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:mm-extension | blueprint/parts/p4-measure.tex#bp:p4:main-measure@L1152-L1152 | proof step
EDGE: step:p4:mm-tori | blueprint/parts/p4-measure.tex#bp:p4:main-measure@L1160-L1160 | proof step
EDGE: step:p4:mm-complement | blueprint/parts/p4-measure.tex#bp:p4:main-measure@L1164-L1164 | proof step
EDGE: step:p4:mm-bad | blueprint/parts/p4-measure.tex#bp:p4:main-measure@L1173-L1173 | proof step
EDGE: step:p4:mm-count | blueprint/parts/p4-measure.tex#bp:p4:main-measure@L1179-L1179 | proof step
EDGE: bp:p0:cover#kamCover | blueprint/parts/p4-measure.tex#bp:p4:main-measure@L1147-L1147 | cover appearing in the conclusion
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#bp:p4:main-measure@L1142-L1149 | Missing direct dependency on the explicit local package (SA), required by SPEC
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#bp:p4:main-measure@L1144-L1144 | C_B^+ and L_+ in the definition of C_meas
EDGE: bp:p4:preimage-measure | blueprint/parts/p4-measure.tex#bp:p4:main-measure@L1144-L1144 | C_3^+ in C_meas is the G3 constant fixed for g(B) in preimage-measure
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r2
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.main_measure
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:mm-extension
KIND: step
TITLE: Extension and lipeomorphism
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mm-extension@L1152-L1158
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mm-extension@L1152-L1158
CONTRACT_ID: step:p4:mm-extension
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: |G_0|<=eta_0<=1/2 and G_0 is 1/2-Lipschitz on S=R^n x (A_gamma u Z)
SOURCE_QUANTIFIERS: gamma,eps
SOURCE_CONCLUSION: exists Gbar:R^{2n}->R^{2n}, 1/2-Lipschitz, =G_0 on S, |Gbar|<=eta_0<=1/2; Psi=id+Gbar is a bijection of R^{2n}, 3/2-Lipschitz, mapping R^n x Z^c onto itself
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:map-lipschitz, bp:p1:mcshane, bp:p1:lipeo, bp:p1:lip-image-product, bp:p4:good-actions, bp:p4:smallness
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:map-lipschitz | blueprint/parts/p4-measure.tex#step:p4:mm-extension@L1153-L1153 | G_0 bounded and 1/2-Lipschitz on S
EDGE: bp:p1:mcshane | blueprint/parts/p4-measure.tex#step:p4:mm-extension@L1153-L1153 | McShane extension with clamping
EDGE: bp:p1:lipeo | blueprint/parts/p4-measure.tex#step:p4:mm-extension@L1157-L1157 | id+Gbar is a lipeomorphism
EDGE: bp:p1:lip-image-product | blueprint/parts/p4-measure.tex#step:p4:mm-extension@L1157-L1157 | product-space image estimate
EDGE: bp:p4:good-actions | blueprint/parts/p4-measure.tex#step:p4:mm-extension@L1155-L1155 | S and G_0
EDGE: bp:p4:smallness | blueprint/parts/p4-measure.tex#step:p4:mm-extension@L1157-L1157 | (s7): eta_0<=1/2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.measure_diff_le_of_displacement
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:mm-tori
KIND: step
TITLE: Good actions lie on tori
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mm-tori@L1160-L1162
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mm-tori@L1160-L1162
CONTRACT_ID: step:p4:mm-tori
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi=id+Gbar with Gbar=G_0 on R^n x A_gamma
SOURCE_QUANTIFIERS: I in A_gamma; theta in R^n
SOURCE_CONCLUSION: Psi(theta,I)=k_{g(I)}(theta) in kamCover(eta_0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:real-torus, step:p4:mm-extension, bp:p4:good-actions
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:real-torus | blueprint/parts/p4-measure.tex#step:p4:mm-tori@L1161-L1161 | k_omega in kamCover(eta_0) for omega=g(I) in Omega_gamma
EDGE: step:p4:mm-extension | blueprint/parts/p4-measure.tex#step:p4:mm-tori@L1160-L1160 | Psi=id+Gbar, Gbar=G_0 on S
EDGE: bp:p4:good-actions | blueprint/parts/p4-measure.tex#step:p4:mm-tori@L1160-L1160 | G_0(theta,I)=k_{g(I)}(theta)-(theta,I)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.main_measure (hcover), measure_diff_le_of_displacement
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:mm-complement
KIND: step
TITLE: The complement is the image of bad actions
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mm-complement@L1164-L1171
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mm-complement@L1164-L1171
CONTRACT_ID: step:p4:mm-complement
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Psi bijection, |Gbar|<=1/2, Psi maps R^n x Z^c onto itself; good actions lie on tori
SOURCE_QUANTIFIERS: y in F_B minus kamCover(eta_0)
SOURCE_CONCLUSION: F_B minus kamCover(eta_0) is contained in ([0,1)^n x (B cap Z)) u Psi(Q x (Z^c minus A_gamma)), Q=[-1/2,3/2]^n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:mm-tori, step:p4:mm-extension, bp:p4:good-actions
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:mm-tori | blueprint/parts/p4-measure.tex#step:p4:mm-complement@L1166-L1166 | x not in R^n x A_gamma
EDGE: step:p4:mm-extension | blueprint/parts/p4-measure.tex#step:p4:mm-complement@L1165-L1165 | Psi surjective on R^n x Z^c, /Gbar/<=1/2
EDGE: bp:p4:good-actions | blueprint/parts/p4-measure.tex#step:p4:mm-complement@L1164-L1164 | Z, A_gamma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.measure_diff_le_of_displacement (hsub)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:mm-bad
KIND: step
TITLE: Bad actions
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mm-bad@L1173-L1177
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mm-bad@L1173-L1177
CONTRACT_ID: step:p4:mm-bad
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: boundary-layer hypothesis meas{I in B: infDist(I,B^c)<delta}<=C_B delta for all delta>0 (HEAD hypothesis, witness C_B)
SOURCE_QUANTIFIERS: gamma
SOURCE_CONCLUSION: Z^c in B, B cap Z in Y, Z^c minus A_gamma in Y u {g not Dio}; meas Y<=2C_B^+ gamma and meas{I in B: g(I) not in Dio_{gamma,tau}}<=L_+^n C_3^+ gamma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:preimage-measure, bp:p4:good-actions
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:preimage-measure | blueprint/parts/p4-measure.tex#step:p4:mm-bad@L1176-L1177 | The preimage-measure bound is invoked at L1175
EDGE: bp:p4:good-actions | blueprint/parts/p4-measure.tex#step:p4:mm-bad@L1174-L1174 | A_gamma, Z
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.main_measure (hY, hBad, hBZ, hZA)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:mm-count
KIND: step
TITLE: Measure count
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mm-count@L1179-L1185
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:mm-count@L1179-L1185
CONTRACT_ID: step:p4:mm-count
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed HEAD data and perturbation hypotheses of Part 4 L138-L152; (SA); B nonempty; Z and A_gamma are defined in good-actions; Psi=id+Gbar and Q=[-1/2,3/2]^n are the constructions at L1151-L1166; C_meas=2 C_B^++(9/2)^n(2 C_B^++L_+^n C_3^+) as defined at L1142; no extra Lipschitz, bad-set-estimate or measurability premise
SOURCE_QUANTIFIERS: gamma,epsilon satisfying (SA), in the fixed main-measure setting
SOURCE_CONCLUSION: meas(F_B minus kamCover(eta_0))<=C_meas gamma by subadditivity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:lip-image, step:p4:mm-complement, step:p4:mm-bad, step:p4:mm-extension, bp:p4:good-actions, bp:p1:ext-lebesgue, bp:p4:SA, bp:p1:ext-measure
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:lip-image | blueprint/parts/p4-measure.tex#step:p4:mm-count@L1181-L1181 | measure of the Lipschitz image Psi(Q x (...))
EDGE: step:p4:mm-complement | blueprint/parts/p4-measure.tex#step:p4:mm-count@L1180-L1185 | covering of the complement
EDGE: step:p4:mm-bad | blueprint/parts/p4-measure.tex#step:p4:mm-count@L1180-L1183 | measure of Y and of the non-Diophantine set
EDGE: step:p4:mm-extension | blueprint/parts/p4-measure.tex#step:p4:mm-count@L1181-L1183 | Psi is 3/2-Lipschitz
EDGE: bp:p4:good-actions | blueprint/parts/p4-measure.tex#step:p4:mm-count@L1180-L1180 | Z, A_gamma
EDGE: bp:p1:ext-lebesgue | blueprint/parts/p4-measure.tex#step:p4:mm-count@L1180-L1185 | Monotonicity and subadditivity are directly used in the measure count
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:mm-count@L1180-L1185 | the inherited main-measure source setting assumes the local SA package; gamma is the positive width used in the bad-action estimates
EDGE: bp:p1:ext-measure | blueprint/parts/p4-measure.tex#step:p4:mm-count@L1180-L1180 | product volume of action sets times the angle cube (E11)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-d2+claude-main-orchestrator
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.main_measure, measure_diff_le_of_displacement, volume_cubeHalf, measure_count_eq
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-11-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: repaired F1: uses product volume of action sets times the angle cube (E11); formerly a source gap before (E11) was listed

NODE: bp:p4:cover-mono
KIND: lemma
TITLE: Monotonicity of the cover
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:cover-mono@L1188-L1191
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:cover-mono@L1193-L1200
CONTRACT_ID: bp:p4:cover-mono
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B' subset B; kappa'<=kappa
SOURCE_QUANTIFIERS: h,f,B',B,r0,tau,kappa',kappa
SOURCE_CONCLUSION: kamCover h f B' r0 tau kappa' subset kamCover h f B r0 tau kappa
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:cm-proof, bp:p0:cover#kamCover
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:cm-proof | blueprint/parts/p4-measure.tex#bp:p4:cover-mono@L1194-L1194 | proof step
EDGE: bp:p0:cover#kamCover | blueprint/parts/p4-measure.tex#bp:p4:cover-mono@L1189-L1189 | cover definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.kamCover_mono
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:cm-proof
KIND: step
TITLE: Same witnesses
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:cm-proof@L1194-L1199
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:cm-proof@L1194-L1199
CONTRACT_ID: step:p4:cm-proof
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B' subset B; kappa'<=kappa; z in kamCover(B',kappa')
SOURCE_QUANTIFIERS: z
SOURCE_CONCLUSION: the same witnesses K,omega,gamma,I_0 show z in kamCover(B,kappa)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:cover#kamCover
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:cover#kamCover | blueprint/parts/p4-measure.tex#step:p4:cm-proof@L1195-L1195 | clauses of the cover definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.kamCover_mono
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:head-empty
KIND: step
TITLE: Empty action domain
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:head-empty@L1203-L1204
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:head-empty@L1203-L1204
CONTRACT_ID: step:p4:head-empty
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: HEAD data, allowing B empty: n>=2, tau>n-1, s0,r0>0, B open bounded, boundary-layer witness C_B, h holomorphic and real on B_{r0}, inverse-frequency witness L_h on closure B
SOURCE_QUANTIFIERS: B
SOURCE_CONCLUSION: if B empty then F_B empty and C=eps_0=1 work; otherwise continue with B nonempty
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:domains#fundamentalDomain
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:domains#fundamentalDomain | blueprint/parts/p4-measure.tex#step:p4:head-empty@L1204-L1204 | The empty case unfolds F_B
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.head_empty
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-12-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:head-constants
KIND: step
TITLE: Constants
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:head-constants@L1206-L1214
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:head-constants@L1206-L1214
CONTRACT_ID: step:p4:head-constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B nonempty; c_*, A_0 from Definition parameters; C_meas from Theorem main-measure
SOURCE_QUANTIFIERS: f, eps<=eps_0 as in HEAD
SOURCE_CONCLUSION: C=max(1,A_0 c_*^{1/2},C_meas c_*^{-1/4}), eps_0=c_*, both positive and depending only on data n,tau,s0,r0,B,h and witnesses L_h,C_B
CONSTANT_SCOPE: C, eps_0 depend only on n,tau,s0,r0,B,h and the witnesses L_h, C_B (fixed once before choosing C, eps_0); not on f, eps
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:parameters, bp:p4:main-measure
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:head-constants@L1207-L1207 | c_*, A_0
EDGE: bp:p4:main-measure | blueprint/parts/p4-measure.tex#step:p4:head-constants@L1207-L1207 | C_meas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.headC, one_le_headC, A0_mul_le_headC, Cmeas_div_le_headC
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-12-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:head-negative
KIND: step
TITLE: Negative $\varepsilon$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:head-negative@L1216-L1218
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:head-negative@L1216-L1218
CONTRACT_ID: step:p4:head-negative
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B nonempty, so D(s0,r0) nonempty; |f|<=eps on D(s0,r0)
SOURCE_QUANTIFIERS: eps
SOURCE_CONCLUSION: eps>=0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:data
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:data | blueprint/parts/p4-measure.tex#step:p4:head-negative@L1217-L1218 | The nonempty domain and the perturbation bound from the fixed data supply epsilon>=0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r4
REVIEWER: sol-review-r2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.nonneg_of_bound_nonempty (KAM/Head/HeadQ.lean)
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-Q-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:head-positive
KIND: step
TITLE: Positive $\varepsilon$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:head-positive@L1220-L1226
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:head-positive@L1220-L1226
CONTRACT_ID: step:p4:head-positive
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B nonempty; 0<eps<=c_*; eps<=eps_0
SOURCE_QUANTIFIERS: eps
SOURCE_CONCLUSION: with gamma=(eps/c_*)^{1/4}, (SA) holds, eta_0<=C sqrt(eps), meas(F_B minus kamCover(C sqrt eps))<=C eps^{1/4}
CONSTANT_SCOPE: gamma=(eps/c_*)^{1/4}; C as in head-constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:cover-mono, bp:p4:main-measure, step:p4:head-constants, bp:p4:parameters, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:cover-mono | blueprint/parts/p4-measure.tex#step:p4:head-positive@L1223-L1223 | kamCover(eta_0) subset kamCover(C sqrt eps)
EDGE: bp:p4:main-measure | blueprint/parts/p4-measure.tex#step:p4:head-positive@L1223-L1223 | measure bound C_meas gamma
EDGE: step:p4:head-constants | blueprint/parts/p4-measure.tex#step:p4:head-positive@L1221-L1221 | C, eps_0, c_*
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:head-positive@L1221-L1222 | use c_*>0 and A_0 in the choice of gamma and in eta_0=A_0 epsilon gamma^-2
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:head-positive@L1221-L1222 | the chosen gamma lies in (0,1] and epsilon=c_* gamma^4, supplying the local package required by main-measure
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-global-K
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.head_positive
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-12-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:head-zero
KIND: step
TITLE: Vanishing perturbation
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:head-zero@L1228-L1231
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:head-zero@L1228-L1231
CONTRACT_ID: step:p4:head-zero
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B nonempty; eps=0
SOURCE_QUANTIFIERS: gamma in (0,1]
SOURCE_CONCLUSION: (SA) holds for every gamma, eta_0=0, so meas(F_B minus kamCover(0))<=C_meas gamma for all gamma, hence =0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:main-measure, bp:p4:parameters, step:p4:head-constants, bp:p4:SA
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:main-measure | blueprint/parts/p4-measure.tex#step:p4:head-zero@L1230-L1231 | measure bound for each gamma in (0,1]
EDGE: step:p4:head-constants | blueprint/parts/p4-measure.tex#step:p4:head-zero@L1229-L1231 | constant C
EDGE: bp:p4:parameters | blueprint/parts/p4-measure.tex#step:p4:head-zero@L1229-L1230 | use c_*>0 and eta_0=A_0 epsilon gamma^-2 at epsilon=0
EDGE: bp:p4:SA | blueprint/parts/p4-measure.tex#step:p4:head-zero@L1229-L1230 | epsilon=0 supplies (SA) for every gamma in (0,1], before applying main-measure
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-d3
REVIEWER: sol-review-d4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.head_zero
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/P4-12-audit-1.md (PASS); kernel replay passed (2026-10-27)
NOTE: - [final: main-measure EDGE locator set to L1230-L1231 exactly as sol-review-d4 specified; the writer verified mechanically that these lines contain the ref to bp:p4:main-measure and its bound]

NODE: bp:p4:dyadic-approx
KIND: lemma
TITLE: Inner dyadic approximation
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:dyadic-approx@L1241-L1245
PROOF_SOURCE: blueprint/parts/p4-measure.tex#bp:p4:dyadic-approx@L1247-L1268
CONTRACT_ID: bp:p4:dyadic-approx
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B in R^n open and bounded; eta>0
SOURCE_QUANTIFIERS: B,eta
SOURCE_CONCLUSION: exists B' open subset of B with meas(B minus B')<=eta and C_B' with meas{I in B': infDist(I,B'^c)<t}<=C_B' t for all t>0
CONSTANT_SCOPE: C_B' depends on B' (number and side of cubes); chosen after B', eta
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:dy-exhaust, step:p4:dy-open, step:p4:dy-layer
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:dy-exhaust | blueprint/parts/p4-measure.tex#bp:p4:dyadic-approx@L1248-L1248 | proof step
EDGE: step:p4:dy-open | blueprint/parts/p4-measure.tex#bp:p4:dyadic-approx@L1256-L1256 | proof step
EDGE: step:p4:dy-layer | blueprint/parts/p4-measure.tex#bp:p4:dyadic-approx@L1261-L1261 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.dyadic_approx
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:dy-exhaust
KIND: step
TITLE: Dyadic exhaustion
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:dy-exhaust@L1248-L1254
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:dy-exhaust@L1248-L1254
CONTRACT_ID: step:p4:dy-exhaust
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B open bounded; eta>0
SOURCE_QUANTIFIERS: j in N
SOURCE_CONCLUSION: for each j, D_j is the finite collection of generation-j closed dyadic cubes contained in B, and E_j=union D_j is closed; E_j subset E_(j+1), union_j E_j=B, and meas(B minus E_j)<=eta for some j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p1:ext-measure
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p1:ext-measure | blueprint/parts/p4-measure.tex#step:p4:dy-exhaust@L1253-L1254 | continuity of Lebesgue measure from below (E11)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-d3
REVIEWER: sol-review-d4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.exists_dyadicUnion_diff_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: repaired F1: uses continuity of Lebesgue measure from below (E11); formerly a source gap before (E11) was listed

NODE: step:p4:dy-open
KIND: step
TITLE: The open set
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:dy-open@L1256-L1259
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:dy-open@L1256-L1259
CONTRACT_ID: step:p4:dy-open
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E_j from dyadic exhaustion with meas(B minus E_j)<=eta
SOURCE_QUANTIFIERS: j
SOURCE_CONCLUSION: B'=union of interiors of the N cubes of D_j is open, B' in B, meas(B minus B')<=eta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:dy-exhaust, bp:p1:ext-measure
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:dy-exhaust | blueprint/parts/p4-measure.tex#step:p4:dy-open@L1257-L1257 | cubes D_j and E_j with measure bound
EDGE: bp:p1:ext-measure | blueprint/parts/p4-measure.tex#step:p4:dy-open@L1258-L1259 | null boundaries of boxes (E11)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-d3
REVIEWER: sol-review-d4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.volume_diff_dyadicInterior_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: repaired F1: uses null boundaries of boxes (E11); formerly a source gap before (E11) was listed

NODE: step:p4:dy-layer
KIND: step
TITLE: Boundary layer
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:dy-layer@L1261-L1267
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:dy-layer@L1261-L1267
CONTRACT_ID: step:p4:dy-layer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B' union of interiors of N cubes of side l=2^-j
SOURCE_QUANTIFIERS: t>0; I in B'
SOURCE_CONCLUSION: meas{I in B': infDist(I,B'^c)<t}<=2 n N l^{n-1} t, so C_B'=2nNl^{n-1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: step:p4:dy-open
ROUTES: -
ROUTE_FOR: -
EDGE: step:p4:dy-open | blueprint/parts/p4-measure.tex#step:p4:dy-layer@L1262-L1262 | B' and its cubes
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.volume_layer_dyadicInterior_le
LEAN_NOTE: prover evidence + independent audit docs/campaign/audits/I-P4A-audit-1.md; kernel replay passed (2026-10-27)
NOTE: -

NODE: step:p4:hq-trivial
KIND: step
TITLE: Trivial cases
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hq-trivial@L1271-L1274
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hq-trivial@L1271-L1274
CONTRACT_ID: step:p4:hq-trivial
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: HEAD-Q data (n>=2, tau>n-1, s0,r0>0, B open bounded, h holomorphic and real on B_{r0}, nondegeneracy on closure of B); kappa>0
SOURCE_QUANTIFIERS: B,kappa
SOURCE_CONCLUSION: if B empty, eps_0=1 works; otherwise 0<meas B<infty and meas F_B=meas B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:domains#fundamentalDomain, bp:p1:ext-measure
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:domains#fundamentalDomain | blueprint/parts/p4-measure.tex#step:p4:hq-trivial@L1272-L1273 | unfold F_B as the half-open unit angle cube times B; the volume identity remains the explicit source gap
EDGE: bp:p1:ext-measure | blueprint/parts/p4-measure.tex#step:p4:hq-trivial@L1273-L1273 | product volume meas([0,1)^n x B) = meas B (E11)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-global-K+claude-main-orchestrator
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.headq_of_head (KAM/Head/HeadQ.lean:107, lines 126-134); KAM.Head.volume_fundamentalDomain (:46), volume_pi_Ico_zero_one (:40)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P4-Q-audit-1.md; kernel replay passed with the package
NOTE: repaired F1: uses product volume meas([0,1)^n x B) = meas B (E11); formerly a source gap before (E11) was listed

NODE: step:p4:hq-approx
KIND: step
TITLE: Inner approximation
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hq-approx@L1276-L1277
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hq-approx@L1276-L1277
CONTRACT_ID: step:p4:hq-approx
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B nonempty open bounded; kappa>0
SOURCE_QUANTIFIERS: kappa
SOURCE_CONCLUSION: B' subset B open with meas(B minus B')<=(1/2)kappa meas B and boundary-layer constant C_B'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:dyadic-approx, step:p4:hq-trivial
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:dyadic-approx | blueprint/parts/p4-measure.tex#step:p4:hq-approx@L1277-L1277 | Dyadic approximation is invoked at L1275, not the heading
EDGE: step:p4:hq-trivial | blueprint/parts/p4-measure.tex#step:p4:hq-approx@L1277-L1277 | 0<meas B<infty and kappa fixed
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r2
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.headq_of_head (lines 134-137) using KAM.Head.dyadic_approx (KAM/Head/DyadicApprox.lean:265)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P4-Q-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p4:hq-head
KIND: step
TITLE: HEAD for $B'$
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hq-head@L1279-L1287
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hq-head@L1279-L1287
CONTRACT_ID: step:p4:hq-head
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B' from inner approximation; HEAD-Q data for B
SOURCE_QUANTIFIERS: kappa
SOURCE_CONCLUSION: (n,tau,s0,r0,B',h) satisfy HEAD's hypotheses; HEAD gives C',eps_0'>0; eps_0=min(eps_0',(kappa/C')^2,(kappa meas B/(2C'))^4)>0
CONSTANT_SCOPE: C', eps_0' depend on B' (hence on kappa, B) and n,tau,s0,r0,h; eps_0 chosen after kappa
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:head, step:p4:hq-approx
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:head | blueprint/parts/p4-measure.tex#step:p4:hq-head@L1280-L1280 | HEAD applied to B' to obtain C',eps_0'
EDGE: step:p4:hq-approx | blueprint/parts/p4-measure.tex#step:p4:hq-head@L1279-L1279 | B' and C_B'
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b
REVIEWER: sol-review-r4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.headq_of_head (lines 139-148); KAM.Head.actionNbhd_subset_of_subset (HeadQ.lean:52)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P4-Q-audit-1.md; kernel replay passed with the package
NOTE: -

NODE: step:p4:hq-transfer
KIND: step
TITLE: Transfer of the perturbation hypotheses
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hq-transfer@L1289-L1295
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hq-transfer@L1289-L1295
CONTRACT_ID: step:p4:hq-transfer
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f, eps<=eps_0 satisfy HEAD-Q hypotheses for B
SOURCE_QUANTIFIERS: f,eps
SOURCE_CONCLUSION: hypotheses hold for B'; eps>=0; meas(F_B' minus kamCover_B'(C' sqrt eps))<=C' eps^{1/4}<=(1/2)kappa meas B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p0:head, step:p4:hq-head, step:p4:hq-approx, step:p4:hq-trivial
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p0:head | blueprint/parts/p4-measure.tex#step:p4:hq-transfer@L1293-L1293 | HEAD conclusion for B'
EDGE: step:p4:hq-head | blueprint/parts/p4-measure.tex#step:p4:hq-transfer@L1290-L1290 | eps<=eps_0'; C', eps_0
EDGE: step:p4:hq-approx | blueprint/parts/p4-measure.tex#step:p4:hq-transfer@L1291-L1291 | B' subset B
EDGE: step:p4:hq-trivial | blueprint/parts/p4-measure.tex#step:p4:hq-transfer@L1292-L1293 | B is nonempty; as in the earlier argument, a point of D(s0,r0) and the original perturbation norm bound give epsilon>=0 directly
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-r2
REVIEWER: sol-review-d2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.headq_of_head (lines 150-156); KAM.Head.nonneg_of_bound_nonempty (:72), headq_epsilon_bounds (:82)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P4-Q-audit-1.md; kernel replay passed with the package
NOTE: The reference "As in Step head-negative" is an analogy to its nonempty-domain argument, not an application requiring the HEAD boundary-layer data. Nonnegativity follows here from the original HEAD-Q domain B, which is nonempty, even if the approximating Bprime is empty.

NODE: step:p4:hq-cover
KIND: step
TITLE: Comparison of covers
STATEMENT_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hq-cover@L1297-L1304
PROOF_SOURCE: blueprint/parts/p4-measure.tex#step:p4:hq-cover@L1297-L1304
CONTRACT_ID: step:p4:hq-cover
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the fixed HEAD-Q data (n>=2, tau>n-1, s0,r0>0, B open bounded, h holomorphic on B_{r0}, real at real points, and the inverse-frequency inequality on closure B); in the B nonempty branch fix kappa>0; B_prime,C_B_prime,C_prime,epsilon_0_prime,epsilon_0 are the constructions at L1274-L1284; f and epsilon<=epsilon_0 satisfy the original HEAD-Q perturbation hypotheses on B; no boundary-layer hypothesis on B is added
SOURCE_QUANTIFIERS: fixed HEAD-Q data; kappa>0; the previously chosen epsilon_0>0; for every f and epsilon satisfying the perturbation hypotheses and epsilon<=epsilon_0
SOURCE_CONCLUSION: meas(F_B minus kamCover_B(kappa))<=kappa meas B = kappa meas F_B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bp:p4:cover-mono, step:p4:hq-transfer, step:p4:hq-approx, step:p4:hq-trivial, step:p4:hq-head, bp:p1:ext-lebesgue, bp:p1:ext-measure
ROUTES: -
ROUTE_FOR: -
EDGE: bp:p4:cover-mono | blueprint/parts/p4-measure.tex#step:p4:hq-cover@L1298-L1298 | kamCover_B'(C' sqrt eps) subset kamCover_B(kappa)
EDGE: step:p4:hq-transfer | blueprint/parts/p4-measure.tex#step:p4:hq-cover@L1300-L1303 | The measure inequality is used at L1301, not the display delimiter L1300
EDGE: step:p4:hq-approx | blueprint/parts/p4-measure.tex#step:p4:hq-cover@L1300-L1303 | The approximation error is consumed in the final measure inequality
EDGE: step:p4:hq-trivial | blueprint/parts/p4-measure.tex#step:p4:hq-cover@L1303-L1303 | meas F_B = meas B
EDGE: step:p4:hq-head | blueprint/parts/p4-measure.tex#step:p4:hq-cover@L1298-L1298 | The chosen epsilon_0 supplies Cprime sqrt(epsilon)<=kappa; transfer only records the measure part
EDGE: bp:p1:ext-lebesgue | blueprint/parts/p4-measure.tex#step:p4:hq-cover@L1300-L1303 | monotonicity and subadditivity apply to the displayed cover of the complement
EDGE: bp:p1:ext-measure | blueprint/parts/p4-measure.tex#step:p4:hq-cover@L1303-L1303 | product volume meas([0,1)^n x S) = meas S (E11)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-K-p4b+sol-review-d2+claude-main-orchestrator
REVIEWER: sol-review-d3
LEAN_STATUS: PROVED
LEAN_REF: KAM.Head.headq_of_head (lines 158-174); KAM.Head.fundamentalDomain_diff_subset (:59), KAM.Head.kamCover_mono (KAM/Head/CoverMono.lean:25)
LEAN_NOTE: recorded 2026-10-27 (bookkeeping pass); covered by docs/campaign/audits/P4-Q-audit-1.md; kernel replay passed with the package
NOTE: repaired F1: uses product volume meas([0,1)^n x S) = meas S (E11); formerly a source gap before (E11) was listed

## Append-only structural amendments

AMEND: K-A001-n-ge-1-decay
TARGET: bp:p1:decay
AUTHOR: claude-main-orchestrator
REVIEWER: sol-amend-reviewer-K
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); u holomorphic, bounded and 1-periodic on T_rho
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39: strip widths positive, n >= 1 wherever a strip occurs) was omitted from the source premises; found by track N global review (docs/graph/N/reviews/GLOBAL-review.md G1). No mathematical change.

AMEND: K-A002-n-ge-1-summation
TARGET: bp:p1:summation
AUTHOR: claude-main-orchestrator
REVIEWER: sol-amend-reviewer-K
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 (standing, p1-analysis.tex L37-L39); (forward) sum_k |a_k| e^{2 pi |k|_1 rho} finite, rho > 0; (converse) u as in decay, 0<delta<rho
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39: strip widths positive, n >= 1 wherever a strip occurs) was omitted from the source premises; found by track N global review (docs/graph/N/reviews/GLOBAL-review.md G1). No mathematical change.

AMEND: K-A003-n-ge-1-fourier-basic
TARGET: bp:p1:fourier-basic
AUTHOR: claude-main-orchestrator
REVIEWER: sol-amend-reviewer-K
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 (standing, p1-analysis.tex L37-L39); v C-valued (componentwise for vector/matrix); (a) v continuous, 1-periodic, C^1; (b) v continuous, 1-periodic, sum |hat v_k| finite; (c) r>0, v holomorphic and 1-periodic on T_r, not necessarily bounded, all hat v_k=0
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39: strip widths positive, n >= 1 wherever a strip occurs) was omitted from the source premises; found by track N global review (docs/graph/N/reviews/GLOBAL-review.md G1). No mathematical change.

AMEND: K-A004-n-ge-1-averages
TARGET: bp:p1:averages
AUTHOR: claude-main-orchestrator
REVIEWER: sol-amend-reviewer-K
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); v holomorphic, bounded and 1-periodic on T_rho; scalar, C^p or C^{pxq} valued
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39: strip widths positive, n >= 1 wherever a strip occurs) was omitted from the source premises; found by track N global review (docs/graph/N/reviews/GLOBAL-review.md G1). No mathematical change.

AMEND: K-A005-n-ge-1-real-restriction
TARGET: bp:p1:real-restriction
AUTHOR: claude-main-orchestrator
REVIEWER: sol-amend-reviewer-K
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); K holomorphic on T_rho and real on reals; for the primary claim, K primary on T_rho (p=2n)
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39: strip widths positive, n >= 1 wherever a strip occurs) was omitted from the source premises; found by track N global review (docs/graph/N/reviews/GLOBAL-review.md G1). No mathematical change.

AMEND: K-A006-n-ge-1-uniform-limits
TARGET: bp:p1:uniform-limits
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: for the V=T_r clauses only, n >= 1 and r > 0 (standing, p1-analysis.tex L37-L39); K_s holomorphic on an open set V; K_s->K pointwise; DK_s->Lambda uniformly on V; for V=T_r, every K_s primary on T_r, respectively real on reals
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A007-n-ge-1-ul-primary
TARGET: step:p1:ul-primary
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and r > 0 (standing, p1-analysis.tex L37-L39); V=T_r, W=C^n x C^n; every K_s primary on T_r (resp. 1-periodic, resp. real on reals)
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A008-n-ge-1-strip-identity
TARGET: bp:p1:strip-identity
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 (standing, p1-analysis.tex L37-L39); r>0; v holomorphic on T_r with values in W; v(x)=0 for all real x
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A009-n-ge-1-si-induction
TARGET: step:p1:si-induction
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and r > 0 (standing, p1-analysis.tex L37-L39); v holomorphic on T_r, vanishing on R^n
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A010-n-ge-1-increments
TARGET: bp:p1:increments
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 (standing, p1-analysis.tex L37-L39); u holomorphic on T_rho; 0<delta<rho; theta, theta+v in T_{rho-delta}; (second claim) u bounded on T_rho
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A011-n-ge-1-inc-mvt
TARGET: step:p1:inc-mvt
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 (standing, p1-analysis.tex L37-L39); u holomorphic on T_rho; 0<delta<rho; theta, theta+v in T_{rho-delta} (convex)
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A012-n-ge-1-inc-cauchy
TARGET: step:p1:inc-cauchy
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 (standing, p1-analysis.tex L37-L39); u bounded holomorphic on T_rho; 0<delta<rho
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A013-n-ge-1-cauchy-strip
TARGET: bp:p1:cauchy-strip
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 (standing, p1-analysis.tex L37-L39); u holomorphic and bounded on T_rho; 0<delta<rho; u scalar, vector (max norm) or matrix (operator norm) valued
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A014-n-ge-1-cs-coordinate
TARGET: step:p1:cs-coordinate
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 (standing, p1-analysis.tex L37-L39); u holomorphic bounded on T_rho, 0<delta<rho, theta in T_{rho-delta}, 1<=ell<=n
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A015-n-ge-1-cs-full
TARGET: step:p1:cs-full
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); coordinate bound of the previous step; theta in T_{rho-delta}
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A016-n-ge-1-cauchy-corollaries
TARGET: bp:p1:cauchy-corollaries
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 (standing, p1-analysis.tex L37-L39); f holomorphic and bounded on T_rho; 0<delta<rho; f valued in C^p (first claim) or C^p / C^{pxq} (second claim)
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A017-n-ge-1-cc-transpose
TARGET: step:p1:cc-transpose
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); f holomorphic bounded on T_rho with values in C^p; theta in T_{rho-delta}
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A018-n-ge-1-cc-omega
TARGET: step:p1:cc-omega
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); f holomorphic bounded on T_rho with values in any W; theta in T_{rho-delta}
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A019-n-ge-1-av-derivatives
TARGET: step:p1:av-derivatives
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); v holomorphic 1-periodic on T_rho
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A020-n-ge-1-av-bound
TARGET: step:p1:av-bound
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); v bounded on T_rho; [0,1]^n has measure 1
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A021-n-ge-1-fb-holomorphic
TARGET: step:p1:fb-holomorphic
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and r > 0 (standing, p1-analysis.tex L37-L39); part (c): v holomorphic 1-periodic on T_r with vanishing coefficients; part (b)
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A022-n-ge-1-dec-shift
TARGET: step:p1:dec-shift
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); u holomorphic 1-periodic on T_rho, k, rho'<rho, t_j=-rho' sgn(k_j); I_j integrals
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A023-n-ge-1-dec-bound
TARGET: step:p1:dec-bound
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); I_n=hat u_k via the shifts; |u|<=||u||_rho
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A024-n-ge-1-sum-bound
TARGET: step:p1:sum-bound
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); M=sum |a_k| e^{2 pi |k|_1 rho} finite; S_N partial sums
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A025-n-ge-1-sum-holo
TARGET: step:p1:sum-holo
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); M finite; u the uniform limit of S_N on T_rho
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A026-n-ge-1-sum-converse
TARGET: step:p1:sum-converse
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 (standing, p1-analysis.tex L37-L39); u holomorphic, bounded and 1-periodic on T_rho; 0<delta<rho (the boundary-radius decay is a dependency, not an extra premise)
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A027-n-ge-1-sum-representation
TARGET: step:p1:sum-representation
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); u as in decay; converse estimate; first part of the lemma
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A028-n-ge-1-cohomological
TARGET: bp:p1:cohomological
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 (standing, p1-analysis.tex L37-L39); omega in Dio_{gamma,tau}, gamma>0, tau>=0; g holomorphic, bounded, 1-periodic on T_rho with avg(g)=0; 0<delta<rho; g real on real points (for realness); vector/matrix valued componentwise
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A029-n-ge-1-coh-data
TARGET: step:p1:coh-data
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); g scalar holomorphic bounded 1-periodic on T_rho, avg(g)=0
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A030-n-ge-1-coh-weighted
TARGET: step:p1:coh-weighted
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); coefficient bounds of coh-data and coh-coefficients; s=2 pi(rho-delta/2)
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A031-n-ge-1-coh-existence
TARGET: step:p1:coh-existence
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); weighted estimate; a_k
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A032-n-ge-1-coh-equation
TARGET: step:p1:coh-equation
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); u=sum a_k chi_k on T_rho-delta
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A033-n-ge-1-coh-unique
TARGET: step:p1:coh-unique
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); u~ holomorphic and 1-periodic on T_{rho-delta}, avg(u~)=0, Du~ omega=g (no bound)
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A034-n-ge-1-coh-vector
TARGET: step:p1:coh-vector
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); scalar case (existence, bound, equation, uniqueness, realness)
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A035-n-ge-1-cohomological-operator
TARGET: bp:p1:cohomological-operator
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); the cohomological lemma; g:T_rho->C^{pxq} holomorphic bounded 1-periodic, avg(g)=0, operator norm; (second claim) u holomorphic periodic with avg(u)=0
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A036-n-ge-1-coo-entries
TARGET: step:p1:coo-entries
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); g matrix valued; cohomological lemma applied entrywise
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A037-n-ge-1-coo-vectors
TARGET: step:p1:coo-vectors
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); v in C^q, |v|<=1; u from coo-entries
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A038-n-ge-1-coo-norm
TARGET: step:p1:coo-norm
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); vector bound of previous step; u from coo-entries
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A039-n-ge-1-coo-apriori
TARGET: step:p1:coo-apriori
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 and rho-delta > 0 (standing, p1-analysis.tex L37-L39); u holomorphic 1-periodic on T_rho, C^p or C^{pxq} valued, avg(u)=0, ||Du omega||_rho <= H < infinity
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A040-n-ge-1-decay-boundary-radius
TARGET: bp:p1:decay#boundary-radius
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 (standing, p1-analysis.tex L37-L39); u holomorphic, bounded and 1-periodic on T_rho; rho>0
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A041-n-ge-1-real-restriction-consequences
TARGET: bp:p1:real-restriction-consequences
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); l:C^n->C^p C-linear with l(R^n) in R^p, l_R its restriction; K:T_rho->C^n x C^n primary on T_rho and real on reals, k its restriction to R^n
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A042-n-ge-1-rr-analytic
TARGET: step:p1:rr-analytic
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); K:T_rho->C^p holomorphic with K(R^n) in R^p; T_rho open, T_rho cap R^n=R^n
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A043-n-ge-1-rr-derivative
TARGET: step:p1:rr-derivative
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); K holomorphic on T_rho, K(R^n) in R^p; x in R^n
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A044-n-ge-1-rr-consequences
TARGET: step:p1:rr-consequences
AUTHOR: sol-amend-reviewer-K
REVIEWER: claude-main-orchestrator
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: n >= 1 and rho > 0 (standing, p1-analysis.tex L37-L39); K:T_rho->C^p holomorphic and real on reals; k its real restriction; x in R^n; K primary when the primarity clause is claimed
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 standing convention (p1-analysis.tex L37-L39) made explicit; proposed in the sol-amend-reviewer-K scan (docs/graph/K/reviews/AMEND-n-ge-1-review.md), checked by the orchestrator: new field = standing prefix + old field verbatim. No mathematical change.

AMEND: K-A045-w-findim-decay
TARGET: bp:p1:decay
AUTHOR: claude-suborch-W
REVIEWER: sol-kamend-W
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: typing conventions K p1 L24-L47: n >= 1, rho > 0, u takes values in a finite-dimensional complex normed W; u holomorphic, bounded and 1-periodic on T_rho
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 typing conventions made explicit in the source premises: p1-analysis.tex L26 (W denotes a finite-dimensional complex normed space) and L37-L39 (positive widths, n >= 1); the statement L786-L789 is for such u. Found by the track-W global review (docs/graph/W/reviews/GLOBAL-review.md G2); ruling root-b8 option (a). New field = the convention prefix plus the old premises; no mathematical change, hence no contract-version bump (as K-A001-K-A044). The text equals the reviewed W import record.

AMEND: K-A046-w-conventions-fourier-basic
TARGET: bp:p1:fourier-basic
AUTHOR: claude-suborch-W
REVIEWER: sol-kamend-W
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: typing convention K p1 L34-L47: n >= 1, Fourier indices in Z^n, period one; v C-valued (componentwise for vector/matrix); (a) v continuous, 1-periodic, C^1; (b) v continuous, 1-periodic, sum |hat v_k| finite; (c) r>0, v holomorphic and 1-periodic on T_r, not necessarily bounded, all hat v_k=0
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 typing conventions made explicit in the source premises: p1-analysis.tex L36-L47 (1-periodicity on T_r, chi_k for k in Z^n, hat v_k entrywise) and L37-L39 (n >= 1); the statement L757-L768 is read in these conventions. Found by the track-W global review (docs/graph/W/reviews/GLOBAL-review.md G2); ruling root-b8 option (a). New field = the convention prefix plus the old premises; no mathematical change, hence no contract-version bump (as K-A001-K-A044). The text equals the reviewed W import record.

AMEND: K-A047-w-findim-holomorphic-analytic
TARGET: bp:p1:holomorphic-analytic
AUTHOR: claude-suborch-W
REVIEWER: sol-kamend-W
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: typing convention K p1 L24-L32: W is a finite-dimensional complex normed space; m is a natural-number dimension; U in C^m open; F:U->W holomorphic; (a) z_0 in U, r>0 with P-bar(z_0,r) in U, A=max_{P-bar(z_0,r)}|F|; (b) U_R=U cap R^m, x_0 in U_R; W=C^p and F(U_R) in R^p for the real clause
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 typing conventions made explicit in the source premises: p1-analysis.tex L26 (W finite-dimensional complex normed) and L29-L32 (holomorphic on open U in C^m, operator norms); the statement L296-L312 has F : U -> W. Found by the track-W global review (docs/graph/W/reviews/GLOBAL-review.md G2); ruling root-b8 option (a). New field = the convention prefix plus the old premises; no mathematical change, hence no contract-version bump (as K-A001-K-A044). The text equals the reviewed W import record.

AMEND: K-A048-w-findim-strip-identity
TARGET: bp:p1:strip-identity
AUTHOR: claude-suborch-W
REVIEWER: sol-kamend-W
ADD_DEPS: -
DROP_DEPS: -
ADD_ROUTES: -
DROP_ROUTES: -
SET_TITLE: -
SET_STATEMENT_SOURCE: -
SET_PROOF_SOURCE: -
SET_CONTRACT_ID: -
SET_CONTRACT_VERSION: -
SET_SOURCE_HYPOTHESES: typing conventions K p1 L24-L47: n >= 1 and W a finite-dimensional complex normed space; r>0; v holomorphic on T_r with values in W; v(x)=0 for all real x
SET_SOURCE_QUANTIFIERS: -
SET_SOURCE_CONCLUSION: -
SET_CONSTANT_SCOPE: -
SET_ROUTE_FOR: -
NOTE: Part 1 typing conventions made explicit in the source premises: p1-analysis.tex L26 (W finite-dimensional complex normed) and L37-L39 (n >= 1); the statement L531-L534 has values in W. Found by the track-W global review (docs/graph/W/reviews/GLOBAL-review.md G2); ruling root-b8 option (a). New field = the convention prefix plus the old premises; no mathematical change, hence no contract-version bump (as K-A001-K-A044). The text equals the reviewed W import record.

<!-- BEGIN PROOF DEPGRAPH GENERATED -->
Regenerated by `proof_depgraph.py`; do not hand-edit.

### Dashboard

* Total nodes: **453**
* Frozen anchors: **25**
* Versioned statement contracts: **453**
* Total edges: **1420**
* Root-closure nodes: **453**
* Dependency leaves in root closure: **44**
* Assumption boundary leaves: **0**
* External boundary leaves: **11**
* Alternative routes: **2**
* Topology review queue: **0**
* Explicit source gaps: **0**
* Coverage items: **583**; excluded: **113**

### Roots

* `bp:p0:head` [REVIEWED; frozen] — contract `kam.kam_positive_measure@1`
* `bp:p0:headq` [REVIEWED; frozen] — contract `kam.kam_positive_measure_qualitative@1`
* `bp:p0:g1` [REVIEWED; frozen] — contract `kam.aposteriori_kam@1`
* `bp:p0:g2` [REVIEWED; frozen] — contract `kam.local_uniqueness_flow@1`
* `bp:p0:g3` [REVIEWED; frozen] — contract `kam.volume_not_diophantine_le@1`

### Topology review queue

* _(none)_

### Dependency leaves in root closure

* `bp:p0:diophantine#IsDiophantine` [REVIEWED] — Diophantine vectors: KAM.IsDiophantine
* `bp:p0:domains#actionNbhd` [REVIEWED] — Complex neighbourhoods and the fundamental domain: KAM.actionNbhd
* `bp:p0:domains#complexStrip` [REVIEWED] — Complex neighbourhoods and the fundamental domain: KAM.complexStrip
* `bp:p0:domains#fundamentalDomain` [REVIEWED] — Complex neighbourhoods and the fundamental domain: KAM.fundamentalDomain
* `bp:p0:hamiltonian#hamiltonianVectorField` [REVIEWED] — Hamiltonian vector fields, symplectic form: KAM.hamiltonianVectorField
* `bp:p0:hamiltonian#hamiltonianVectorFieldC` [REVIEWED] — Hamiltonian vector fields, symplectic form: KAM.hamiltonianVectorFieldℂ
* `bp:p0:hamiltonian#omegaZero` [REVIEWED] — Hamiltonian vector fields, symplectic form: KAM.omegaZero
* `bp:p0:hamiltonian#symplecticForm` [REVIEWED] — Hamiltonian vector fields, symplectic form: KAM.symplecticForm
* `bp:p0:nearlyintegrable#frequencyMap` [REVIEWED] — The integrable part, the perturbation, the frequency map: KAM.frequencyMap
* `bp:p0:nearlyintegrable#realHamiltonian` [REVIEWED] — The integrable part, the perturbation, the frequency map: KAM.realHamiltonian
* `bp:p0:stripdata#IsRealOnReals` [REVIEWED] — Torus data on strips: KAM.IsRealOnReals
* `bp:p0:stripdata#dotC` [REVIEWED] — Torus data on strips: KAM.dotℂ
* `bp:p1:ext-banach` [REVIEWED] — Banach's fixed point theorem
* `bp:p1:ext-cauchy` [REVIEWED] — Cauchy's formulas in one variable
* `bp:p1:ext-cramer` [REVIEWED] — Cramer's rule
* `bp:p1:ext-fourier` [REVIEWED] — Fourier series on the torus
* `bp:p1:ext-identity` [REVIEWED] — Identity theorem in one variable
* `bp:p1:ext-integral` [REVIEWED] — Integrals
* `bp:p1:ext-lebesgue` [REVIEWED] — Lebesgue outer measure
* `bp:p1:ext-measure` [REVIEWED] — (E11) Lebesgue measure on products and boxes
* `bp:p1:ext-mvt` [REVIEWED] — Mean value inequality
* `bp:p1:ext-rectangle` [REVIEWED] — Cauchy's theorem for rectangles
* `bp:p1:ext-schwarz` [REVIEWED] — Symmetry of second derivatives
* `bp:p1:lipeo-fixed` [REVIEWED] — Bijections fixing a set
* `bp:p4:phase-average` [REVIEWED] — Angle displacement and phase average
* `step:p1:es-power` [REVIEWED] — The power times the exponential
* `step:p1:es-product` [REVIEWED] — Product structure
* `step:p1:han-margin` [REVIEWED] — A larger polydisc
* `step:p1:hr-derivative` [REVIEWED] — The real derivative
* `step:p1:it-linear` [REVIEWED] — The form linear in $y_0$
* `step:p1:it-super` [REVIEWED] — Super-exponential decay
* `step:p1:lipeo-bounds` [REVIEWED] — Bi-Lipschitz bounds
* `step:p1:mc-component` [REVIEWED] — One component
* `step:p1:mn-transpose` [REVIEWED] — Transposes
* `step:p1:opn-rowsum` [REVIEWED] — Row sums
* `step:p1:pb-compact` [REVIEWED] — A compact fundamental set
* `step:p1:rr-derivative` [REVIEWED] — The derivative
* `step:p1:sum-bound` [REVIEWED] — Convergence and the bound
* `step:p3:diff-linearized` [REVIEWED] — Linearized equation
* `step:p4:count-projection` [REVIEWED] — Projection to the first $n-1$ coordinates
* `step:p4:fm-domain` [REVIEWED] — The real domain
* `step:p4:hbdd-compact` [REVIEWED] — A compact set between the neighbourhoods
* `step:p4:latsum-integral` [REVIEWED] — Integral comparison
* `step:p4:slab-coordinate` [REVIEWED] — A dominant coordinate

### Assumption boundary leaves

* _(none)_

### External boundary leaves

* `bp:p1:ext-banach` [REVIEWED] — Banach's fixed point theorem
* `bp:p1:ext-cauchy` [REVIEWED] — Cauchy's formulas in one variable
* `bp:p1:ext-cramer` [REVIEWED] — Cramer's rule
* `bp:p1:ext-fourier` [REVIEWED] — Fourier series on the torus
* `bp:p1:ext-identity` [REVIEWED] — Identity theorem in one variable
* `bp:p1:ext-integral` [REVIEWED] — Integrals
* `bp:p1:ext-lebesgue` [REVIEWED] — Lebesgue outer measure
* `bp:p1:ext-measure` [REVIEWED] — (E11) Lebesgue measure on products and boxes
* `bp:p1:ext-mvt` [REVIEWED] — Mean value inequality
* `bp:p1:ext-rectangle` [REVIEWED] — Cauchy's theorem for rectangles
* `bp:p1:ext-schwarz` [REVIEWED] — Symmetry of second derivatives

### Uncovered graph nodes

* _(none)_

### Nodes outside every root closure

* _(none)_

### Explicit source gaps

* _(none)_
<!-- END PROOF DEPGRAPH GENERATED -->
