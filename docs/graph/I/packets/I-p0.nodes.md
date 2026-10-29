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
