NODE: bpP:p0:diophantine#IsDiophantine
KIND: definition
TITLE: Diophantine vectors: KAM.IsDiophantine
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:diophantine@L44-L50
PROOF_SOURCE: -
CONTRACT_ID: kam.IsDiophantine
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): n in N, gamma,tau in R, omega in R^n (Fin n -> R)
SOURCE_QUANTIFIERS: gamma, tau, omega (n implicit)
SOURCE_CONCLUSION: defines IsDiophantine gamma tau omega: for every k in Z^n \ {0}, gamma / ¦k¦_1^tau <= ¦k . omega¦ (¦k¦_1 = sum ¦k_i¦)
CONSTANT_SCOPE: none (gamma, tau arbitrary reals; no sign condition)
FROZEN_FILE: KAM/Frozen/Defs/IsDiophantine.lean
FROZEN_DECL: KAM.IsDiophantine
FROZEN_ANCHOR_ID: kam.IsDiophantine.v1
FROZEN_ABI_SHA256: 24a486c6ccc5648791465ec3577c2e37fd464ecaec8f0dab9c74a5588535e717
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.IsDiophantine (KAM/Frozen/Defs/IsDiophantine.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:hamsymp#hamiltonianVectorField
KIND: definition
TITLE: Hamiltonian vector field and symplectic form: KAM.hamiltonianVectorField
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:hamsymp@L52-L63
PROOF_SOURCE: -
CONTRACT_ID: kam.hamiltonianVectorField
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): H: Ph_d -> R, z in Ph_d; D is the Frechet derivative (0 where H is not differentiable)
SOURCE_QUANTIFIERS: d implicit; H, z
SOURCE_CONCLUSION: defines X_H(z) = (d_{z2} H(z), -d_{z1} H(z)), X_H(z)_{1,i} = DH(z)(0,e_i), X_H(z)_{2,i} = -DH(z)(e_i,0)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/HamiltonianVectorField.lean
FROZEN_DECL: KAM.hamiltonianVectorField
FROZEN_ANCHOR_ID: kam.hamiltonianVectorField.v1
FROZEN_ABI_SHA256: 427a145572df4c3e14079cf88feb16d60e1cd92fcd1770faddd36ad706562ca6
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.hamiltonianVectorField (KAM/Frozen/Defs/HamiltonianVectorField.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:hamsymp#symplecticForm
KIND: definition
TITLE: Hamiltonian vector field and symplectic form: KAM.symplecticForm
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:hamsymp@L52-L63
PROOF_SOURCE: -
CONTRACT_ID: kam.symplecticForm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): v=(v1,v2), w=(w1,w2) in Ph_d
SOURCE_QUANTIFIERS: d implicit; v, w
SOURCE_CONCLUSION: defines Omega(v,w) = sum_i (v_{2,i} w_{1,i} - v_{1,i} w_{2,i})
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/SymplecticForm.lean
FROZEN_DECL: KAM.symplecticForm
FROZEN_ANCHOR_ID: kam.symplecticForm.v1
FROZEN_ABI_SHA256: 542b8d8eb08283f5c961a969dd96003cbb23fc447da8ea444498cb92a48f6d75
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.symplecticForm (KAM/Frozen/Defs/SymplecticForm.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:phase#Phase
KIND: definition
TITLE: Phase space: KAM.Planetary.Phase
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:phase@L67-L70
PROOF_SOURCE: -
CONTRACT_ID: planetary.Phase
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): d in N
SOURCE_QUANTIFIERS: d
SOURCE_CONCLUSION: defines Ph_d = R^d x R^d (canonical coordinates position, momentum)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/Phase.lean
FROZEN_DECL: KAM.Planetary.Phase
FROZEN_ANCHOR_ID: planetary.Phase.v1
FROZEN_ABI_SHA256: 0b8db62a1a83c34b9c3562bd1bb6043b1db7174c9222df403355844422056af8
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.Phase (KAM/Frozen/Planetary/Defs/Phase.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:plane#planeSq
KIND: definition
TITLE: Planar length and scalar product: KAM.Planetary.planeSq
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:plane@L72-L76
PROOF_SOURCE: -
CONTRACT_ID: planetary.planeSq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): v in R^2
SOURCE_QUANTIFIERS: v
SOURCE_CONCLUSION: defines sq(v) = sum_k v_k^2 (planeSq)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlaneSq.lean
FROZEN_DECL: KAM.Planetary.planeSq
FROZEN_ANCHOR_ID: planetary.planeSq.v1
FROZEN_ABI_SHA256: b0de2d3150c6c723a7af40b0f9ef8d6849b211bf81ab6685ebd870b7aa618d5e
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planeSq (KAM/Frozen/Planetary/Defs/PlaneSq.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:plane#planeLength
KIND: definition
TITLE: Planar length and scalar product: KAM.Planetary.planeLength
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:plane@L72-L76
PROOF_SOURCE: -
CONTRACT_ID: planetary.planeLength
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): v in R^2
SOURCE_QUANTIFIERS: v
SOURCE_CONCLUSION: defines planeLength(v) = sqrt(sq(v)), the physical length ¦v¦ (never the max norm)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlaneLength.lean
FROZEN_DECL: KAM.Planetary.planeLength
FROZEN_ANCHOR_ID: planetary.planeLength.v1
FROZEN_ABI_SHA256: 385b5a3f2a85cef8e532266e97df0d7f79ac00c08d2c9b635dafa0f3c3ccc6f9
DEPS: bpP:p0:plane#planeSq
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:plane#planeSq | blueprint-P/parts/p0-conventions.tex#bpP:p0:plane@L73-L73 | ¦v¦ = sqrt(sq(v))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planeLength (KAM/Frozen/Planetary/Defs/PlaneLength.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:plane#planeDot
KIND: definition
TITLE: Planar length and scalar product: KAM.Planetary.planeDot
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:plane@L72-L76
PROOF_SOURCE: -
CONTRACT_ID: planetary.planeDot
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): v, w in R^2
SOURCE_QUANTIFIERS: v, w
SOURCE_CONCLUSION: defines planeDot(v,w) = sum_k v_k w_k
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlaneDot.lean
FROZEN_DECL: KAM.Planetary.planeDot
FROZEN_ANCHOR_ID: planetary.planeDot.v1
FROZEN_ABI_SHA256: 8cf08c43a712bf1c8d3e6fd5426b13d34d07a93597447a35b7b671e1126ae661
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planeDot (KAM/Frozen/Planetary/Defs/PlaneDot.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:body#bodyVector
KIND: definition
TITLE: Body vectors: KAM.Planetary.bodyVector
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:body@L78-L81
PROOF_SOURCE: -
CONTRACT_ID: planetary.bodyVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): q in R^{2n}, i < n
SOURCE_QUANTIFIERS: n implicit; q, i
SOURCE_CONCLUSION: defines body(q,i) = q^(i) = (q_(i,1), q_(i,2)) in R^2, pair index (i,k) <-> k+2i (finProdFinEquiv)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/BodyVector.lean
FROZEN_DECL: KAM.Planetary.bodyVector
FROZEN_ANCHOR_ID: planetary.bodyVector.v1
FROZEN_ABI_SHA256: 09f09ead30448301bb78763192f9a9c6ca3edcf4d3d2a771d616c548347661b4
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.bodyVector (KAM/Frozen/Planetary/Defs/BodyVector.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:blocks#fast
KIND: definition
TITLE: Fast and slow blocks, assembly: KAM.Planetary.fast
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:blocks@L83-L89
PROOF_SOURCE: -
CONTRACT_ID: planetary.fast
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): v in R^{a+b}
SOURCE_QUANTIFIERS: a, b implicit; v
SOURCE_CONCLUSION: defines the fast part v^f = (v_i)_{i<a} (first a coordinates)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/Fast.lean
FROZEN_DECL: KAM.Planetary.fast
FROZEN_ANCHOR_ID: planetary.fast.v1
FROZEN_ABI_SHA256: 592a25e5b4ec439e42bd78bc02e0dfd989b1d261387db6319bca10c6d17c1067
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.fast (KAM/Frozen/Planetary/Defs/Fast.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:blocks#slow
KIND: definition
TITLE: Fast and slow blocks, assembly: KAM.Planetary.slow
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:blocks@L83-L89
PROOF_SOURCE: -
CONTRACT_ID: planetary.slow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): v in R^{a+b}
SOURCE_QUANTIFIERS: a, b implicit; v
SOURCE_CONCLUSION: defines the slow part v^s = (v_{a+j})_{j<b} (last b coordinates)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/Slow.lean
FROZEN_DECL: KAM.Planetary.slow
FROZEN_ANCHOR_ID: planetary.slow.v1
FROZEN_ABI_SHA256: ae34da51fbaf5eb81f8a1436fe5e53cd0413d280bf280221ca79639b92661332
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.slow (KAM/Frozen/Planetary/Defs/Slow.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:blocks#assemble
KIND: definition
TITLE: Fast and slow blocks, assembly: KAM.Planetary.assemble
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:blocks@L83-L89
PROOF_SOURCE: -
CONTRACT_ID: planetary.assemble
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): I, phi in R^a; p, q in R^b
SOURCE_QUANTIFIERS: a, b implicit; I, phi, p, q
SOURCE_CONCLUSION: defines assemble(I,phi,p,q) = ((phi,q),(I,p)) in Ph_{a+b} (concatenated coordinate vectors; phase order (phi,q;I,p))
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/Assemble.lean
FROZEN_DECL: KAM.Planetary.assemble
FROZEN_ANCHOR_ID: planetary.assemble.v1
FROZEN_ABI_SHA256: e68095f14a537fe2d147c6127a51ac3755b9a5d71ebbacbb2f316d3aaafdbd80
DEPS: bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:blocks@L86-L86 | the value lies in Ph_{a+b}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.assemble (KAM/Frozen/Planetary/Defs/Assemble.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:oscaction#oscillatorAction
KIND: definition
TITLE: Oscillator actions: KAM.Planetary.oscillatorAction
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:oscaction@L91-L95
PROOF_SOURCE: -
CONTRACT_ID: planetary.oscillatorAction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): p, q in R^b, j <= b
SOURCE_QUANTIFIERS: b implicit; p, q, j
SOURCE_CONCLUSION: defines R_j(p,q) = (p_j^2 + q_j^2)/2
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/OscillatorAction.lean
FROZEN_DECL: KAM.Planetary.oscillatorAction
FROZEN_ANCHOR_ID: planetary.oscillatorAction.v1
FROZEN_ABI_SHA256: b37f7928355c64fc3555d65704a95ecdb67fe55bdd7bb2471ac609553f2a962a
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.oscillatorAction (KAM/Frozen/Planetary/Defs/OscillatorAction.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:fastshift#fastShift
KIND: definition
TITLE: Fast shift: KAM.Planetary.fastShift
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:fastshift@L97-L101
PROOF_SOURCE: -
CONTRACT_ID: planetary.fastShift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): k in Z^a
SOURCE_QUANTIFIERS: a, b implicit; k
SOURCE_CONCLUSION: defines shift(k) = (((2 pi k_i)_{i<a}, 0_b), 0) in Ph_{a+b}: fast angles translated by 2 pi k, slow positions and all momenta unchanged
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/FastShift.lean
FROZEN_DECL: KAM.Planetary.fastShift
FROZEN_ANCHOR_ID: planetary.fastShift.v1
FROZEN_ABI_SHA256: 8b53f2de2ba13a01ff80cdf95a405e5d5a39eaa40db32a87062c077ddf0775a5
DEPS: bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:fastshift@L98-L98 | shift(k) lies in Ph_{a+b}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.fastShift (KAM/Frozen/Planetary/Defs/FastShift.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:fastfreq#fastFrequency
KIND: definition
TITLE: Fast frequency map: KAM.Planetary.fastFrequency
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:fastfreq@L103-L108
PROOF_SOURCE: -
CONTRACT_ID: planetary.fastFrequency
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): H_0: R^a -> R, I in R^a
SOURCE_QUANTIFIERS: a implicit; H_0, I
SOURCE_CONCLUSION: defines omega_{H_0}(I)_i = DH_0(I)(e_i) (Frechet derivative, 0 where H_0 is not differentiable)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/FastFrequency.lean
FROZEN_DECL: KAM.Planetary.fastFrequency
FROZEN_ANCHOR_ID: planetary.fastFrequency.v1
FROZEN_ABI_SHA256: d0081126e210d1039ca9367456c22dba50e4760d8c9196e28ca66bc83aa11494
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.fastFrequency (KAM/Frozen/Planetary/Defs/FastFrequency.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:cylinder#cylinder
KIND: definition
TITLE: Cylinder and its fundamental cell: KAM.Planetary.cylinder
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:cylinder@L112-L121
PROOF_SOURCE: -
CONTRACT_ID: planetary.cylinder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): V subset R^a, r in R
SOURCE_QUANTIFIERS: a, b implicit; V, r
SOURCE_CONCLUSION: defines C(V,r) = {z in Ph_{a+b}: z_2^f in V, (z_2^s)_j^2 + (z_1^s)_j^2 < r^2 for all j <= b} (a product of discs, not a box); uses require r > 0
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/Cylinder.lean
FROZEN_DECL: KAM.Planetary.cylinder
FROZEN_ANCHOR_ID: planetary.cylinder.v1
FROZEN_ABI_SHA256: 2b886daef9e82b3f00e219775145a57d7bb5062e9297e931e6776018bcc25090
DEPS: bpP:p0:phase#Phase, bpP:p0:blocks#fast, bpP:p0:blocks#slow
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:cylinder@L114-L114 | C(V,r) is a subset of Ph_{a+b}
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p0-conventions.tex#bpP:p0:cylinder@L114-L114 | z_2^f in V
EDGE: bpP:p0:blocks#slow | blueprint-P/parts/p0-conventions.tex#bpP:p0:cylinder@L114-L114 | (z_2^s)_j and (z_1^s)_j
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.cylinder (KAM/Frozen/Planetary/Defs/Cylinder.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:cylinder#cylinderCell
KIND: definition
TITLE: Cylinder and its fundamental cell: KAM.Planetary.cylinderCell
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:cylinder@L112-L121
PROOF_SOURCE: -
CONTRACT_ID: planetary.cylinderCell
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): V subset R^a, r in R
SOURCE_QUANTIFIERS: a, b implicit; V, r
SOURCE_CONCLUSION: defines the fundamental cell F(V,r) = {z in C(V,r): 0 <= z^f_{1,i} < 2 pi for all i <= a}
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/CylinderCell.lean
FROZEN_DECL: KAM.Planetary.cylinderCell
FROZEN_ANCHOR_ID: planetary.cylinderCell.v1
FROZEN_ABI_SHA256: cf3b19044d5505dc3df6123c3e3a050db55f59c5174c2aaab9d0118e3ad4fc32
DEPS: bpP:p0:cylinder#cylinder, bpP:p0:phase#Phase, bpP:p0:blocks#fast
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:cylinder#cylinder | blueprint-P/parts/p0-conventions.tex#bpP:p0:cylinder@L117-L117 | F(V,r) is cut out of C(V,r)
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:cylinder@L117-L117 | F(V,r) subset Ph_{a+b}
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p0-conventions.tex#bpP:p0:cylinder@L117-L117 | z^f_{1,i}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.cylinderCell (KAM/Frozen/Planetary/Defs/CylinderCell.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:degham#degenerateHamiltonian
KIND: definition
TITLE: The family $H_0+\mu P$: KAM.Planetary.degenerateHamiltonian
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:degham@L123-L127
PROOF_SOURCE: -
CONTRACT_ID: planetary.degenerateHamiltonian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): H_0: R^a -> R, P: R x Ph_{a+b} -> R
SOURCE_QUANTIFIERS: a, b implicit; H_0, P, mu, z
SOURCE_CONCLUSION: defines H_mu(z) = H_0(z_2^f) + mu P(mu,z)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/DegenerateHamiltonian.lean
FROZEN_DECL: KAM.Planetary.degenerateHamiltonian
FROZEN_ANCHOR_ID: planetary.degenerateHamiltonian.v1
FROZEN_ABI_SHA256: 331c8377743700e4a9163dbc7e9b05d210b63657fbfc42851bf92ee8731f02a6
DEPS: bpP:p0:phase#Phase, bpP:p0:blocks#fast
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:degham@L124-L124 | P is defined on R x Ph_{a+b}
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p0-conventions.tex#bpP:p0:degham@L124-L124 | H_0 is evaluated at z_2^f
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.degenerateHamiltonian (KAM/Frozen/Planetary/Defs/DegenerateHamiltonian.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:secavg#secularAverage
KIND: definition
TITLE: Averaged perturbation: KAM.Planetary.secularAverage
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:secavg@L129-L135
PROOF_SOURCE: -
CONTRACT_ID: planetary.secularAverage
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): P: R x Ph_{a+b} -> R, mu in R, I in R^a, p, q in R^b
SOURCE_QUANTIFIERS: a, b implicit; P, mu, I, p, q
SOURCE_CONCLUSION: defines P_av(mu,I;p,q) = (2 pi)^{-a} int_{[0,2 pi]^a} P(mu, assemble(I,phi,p,q)) dphi (Bochner integral; 0 for a non-integrable integrand, so every use asserts integrability)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/SecularAverage.lean
FROZEN_DECL: KAM.Planetary.secularAverage
FROZEN_ANCHOR_ID: planetary.secularAverage.v1
FROZEN_ABI_SHA256: a08f4d400b04c055d8ab2b4fd85c1f584be0216f0c80fa9dd84b78a88e36171c
DEPS: bpP:p0:blocks#assemble, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:blocks#assemble | blueprint-P/parts/p0-conventions.tex#bpP:p0:secavg@L131-L131 | the integrand evaluates P at assemble(I,phi,p,q)
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:secavg@L131-L131 | P is defined on R x Ph_{a+b}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.secularAverage (KAM/Frozen/Planetary/Defs/SecularAverage.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:fastdiffeo#HasFastDiffeomorphism
KIND: definition
TITLE: Fast diffeomorphism: KAM.Planetary.HasFastDiffeomorphism
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:fastdiffeo@L137-L144
PROOF_SOURCE: -
CONTRACT_ID: planetary.HasFastDiffeomorphism
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): H_0: R^a -> R, W subset R^a
SOURCE_QUANTIFIERS: a implicit; H_0, W
SOURCE_CONCLUSION: defines HasFastDiffeo(H_0,W): (i) H_0 real analytic at every point of W; (ii) omega_{H_0}(W) open; (iii) exists g: R^a -> R^a of class C^1 on omega_{H_0}(W) with g(omega_{H_0}(I)) = I for I in W and g(w) in W, omega_{H_0}(g(w)) = w for w in omega_{H_0}(W)
CONSTANT_SCOPE: g is explicit (not a totalized inverse); no dependence on constants
FROZEN_FILE: KAM/Frozen/Planetary/Defs/HasFastDiffeomorphism.lean
FROZEN_DECL: KAM.Planetary.HasFastDiffeomorphism
FROZEN_ANCHOR_ID: planetary.HasFastDiffeomorphism.v1
FROZEN_ABI_SHA256: 91718a20f82c0046ed31c76db7aeaf5bc53257ab286e32d58ae1b57f548333c0
DEPS: bpP:p0:fastfreq#fastFrequency
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:fastfreq#fastFrequency | blueprint-P/parts/p0-conventions.tex#bpP:p0:fastdiffeo@L139-L140 | omega_{H_0} is the fast frequency map in (ii) and (iii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.HasFastDiffeomorphism (KAM/Frozen/Planetary/Defs/HasFastDiffeomorphism.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:birkhoff#HasSecularBirkhoffForm
KIND: definition
TITLE: Secular Birkhoff form (A2''): KAM.Planetary.HasSecularBirkhoffForm
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:birkhoff@L146-L162
PROOF_SOURCE: -
CONTRACT_ID: planetary.HasSecularBirkhoffForm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): V subset R^a, r_0, mu_0 in R, P_0: R x R^a -> R, Omega: R x R^a -> R^b, beta: R x R^a -> R^{bxb}, P: R x Ph_{a+b} -> R
SOURCE_QUANTIFIERS: a, b implicit; P, V, r_0, mu_0, P_0, Omega, beta
SOURCE_CONCLUSION: defines HasBirkhoff(P,V,r_0,mu_0,P_0,Omega,beta): for every mu in [0,mu_0] and I in V: (i) phi -> P(mu,assemble(I,phi,p,q)) integrable on [0,2 pi]^a whenever p_j^2+q_j^2 < r_0^2 for all j; (ii) for every eps > 0 there is delta with 0 < delta <= r_0 such that for all p,q with p_j^2+q_j^2 < delta^2: ¦P_av(mu,I;p,q) - (P_0(mu,I) + sum_j Omega_j(mu,I) R_j + 1/2 sum_{ij} beta_ij(mu,I) R_i R_j)¦ <= eps ¦(p,q)¦_inf^4
CONSTANT_SCOPE: delta may depend on (mu, I, eps); uniformity is not part of the definition (derived from joint analyticity in the proof of P-G)
FROZEN_FILE: KAM/Frozen/Planetary/Defs/HasSecularBirkhoffForm.lean
FROZEN_DECL: KAM.Planetary.HasSecularBirkhoffForm
FROZEN_ANCHOR_ID: planetary.HasSecularBirkhoffForm.v1
FROZEN_ABI_SHA256: 23c3c24aeeabeff49e172e319b46b6a0794586af9def232fcfe9b3c981542d5d
DEPS: bpP:p0:phase#Phase, bpP:p0:blocks#assemble, bpP:p0:secavg#secularAverage, bpP:p0:oscaction#oscillatorAction
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:birkhoff@L148-L148 | P is defined on R x Ph_{a+b}
EDGE: bpP:p0:blocks#assemble | blueprint-P/parts/p0-conventions.tex#bpP:p0:birkhoff@L151-L151 | integrability of phi -> P(mu,assemble(I,phi,p,q))
EDGE: bpP:p0:secavg#secularAverage | blueprint-P/parts/p0-conventions.tex#bpP:p0:birkhoff@L154-L154 | P_av in (ii)
EDGE: bpP:p0:oscaction#oscillatorAction | blueprint-P/parts/p0-conventions.tex#bpP:p0:birkhoff@L156-L156 | R_j = R_j(p,q)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.HasSecularBirkhoffForm (KAM/Frozen/Planetary/Defs/HasSecularBirkhoffForm.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:cyltorus#IsCylinderTorus
KIND: definition
TITLE: Cylinder torus: KAM.Planetary.IsCylinderTorus
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:cyltorus@L164-L179
PROOF_SOURCE: -
CONTRACT_ID: planetary.IsCylinderTorus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): H: Ph_{a+b} -> R, U subset Ph_{a+b}, w in R^{a+b}, K: R^{a+b} -> Ph_{a+b}
SOURCE_QUANTIFIERS: a, b implicit; H, U, w, K
SOURCE_CONCLUSION: defines IsCylTorus(H,U,w,K): (i) K real analytic on R^{a+b}; (ii) K(theta) in U and H differentiable at K(theta) for all theta; (iii) K(theta+k) = K(theta) + shift((k_i)_{i<a}) for theta in R^{a+b}, k in Z^{a+b}; (iv) K(theta') = K(theta) + shift(k) for some k in Z^a implies theta'-theta in Z^{a+b}; (v) DK(theta) injective; (vi) Omega(DK(theta)u, DK(theta)v) = 0; (vii) for all theta,t: s -> K(theta+s w) has derivative X_H(K(theta+t w)) at s = t; no Diophantine condition
CONSTANT_SCOPE: none (no constants; period-one parameters, canonical fast angles of period 2 pi)
FROZEN_FILE: KAM/Frozen/Planetary/Defs/IsCylinderTorus.lean
FROZEN_DECL: KAM.Planetary.IsCylinderTorus
FROZEN_ANCHOR_ID: planetary.IsCylinderTorus.v1
FROZEN_ABI_SHA256: 893a9c95428e4164d60643242685c4a3fe7279646423770a6bec4d0b24af625d
DEPS: bpP:p0:phase#Phase, bpP:p0:fastshift#fastShift, bpP:p0:hamsymp#symplecticForm, bpP:p0:hamsymp#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:cyltorus@L165-L165 | H, U, K live on Ph_{a+b}
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p0-conventions.tex#bpP:p0:cyltorus@L170-L170 | (iii) and (iv) use shift
EDGE: bpP:p0:hamsymp#symplecticForm | blueprint-P/parts/p0-conventions.tex#bpP:p0:cyltorus@L173-L173 | Omega in (vi)
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p0-conventions.tex#bpP:p0:cyltorus@L174-L174 | X_H in (vii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.IsCylinderTorus (KAM/Frozen/Planetary/Defs/IsCylinderTorus.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:cylkol#IsCylinderKolmogorovSet
KIND: definition
TITLE: Cylinder Kolmogorov set: KAM.Planetary.IsCylinderKolmogorovSet
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:cylkol@L181-L189
PROOF_SOURCE: -
CONTRACT_ID: planetary.IsCylinderKolmogorovSet
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): H: Ph_{a+b} -> R, V subset R^a, r, mu, C in R, S subset Ph_{a+b}
SOURCE_QUANTIFIERS: a, b implicit; H, V, r, mu, C, S
SOURCE_CONCLUSION: defines IsCylKol(H,V,r,mu,C,S): S Lebesgue measurable, S subset C(V,r), and every z in S has w in R^{a+b}, K: R^{a+b} -> Ph_{a+b}, theta with K(theta) = z, K(R^{a+b}) subset S, IsCylTorus(H,C(V,r),w,K), gamma > 0 and tau > a+b with w (gamma,tau)-Diophantine, ¦w^f¦_inf <= C and ¦w^s¦_inf <= C mu
CONSTANT_SCOPE: gamma, tau (and w, K, theta) may depend on the torus (on z); C is a fixed argument bounding every torus
FROZEN_FILE: KAM/Frozen/Planetary/Defs/IsCylinderKolmogorovSet.lean
FROZEN_DECL: KAM.Planetary.IsCylinderKolmogorovSet
FROZEN_ANCHOR_ID: planetary.IsCylinderKolmogorovSet.v1
FROZEN_ABI_SHA256: cd61045edccdb765913328f48142744df56c9a03a533171b60f77ff40f5a93b6
DEPS: bpP:p0:phase#Phase, bpP:p0:cylinder#cylinder, bpP:p0:cyltorus#IsCylinderTorus, bpP:p0:diophantine#IsDiophantine, bpP:p0:blocks#fast, bpP:p0:blocks#slow
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:cylkol@L182-L182 | H and S live on Ph_{a+b}
EDGE: bpP:p0:cylinder#cylinder | blueprint-P/parts/p0-conventions.tex#bpP:p0:cylkol@L183-L183 | S subset C(V,r) and the torus predicate is taken on C(V,r)
EDGE: bpP:p0:cyltorus#IsCylinderTorus | blueprint-P/parts/p0-conventions.tex#bpP:p0:cylkol@L185-L185 | IsCylTorus(H,C(V,r),w,K)
EDGE: bpP:p0:diophantine#IsDiophantine | blueprint-P/parts/p0-conventions.tex#bpP:p0:cylkol@L185-L185 | w is (gamma,tau)-Diophantine
EDGE: bpP:p0:blocks#fast | blueprint-P/parts/p0-conventions.tex#bpP:p0:cylkol@L186-L186 | ¦w^f¦_inf <= C
EDGE: bpP:p0:blocks#slow | blueprint-P/parts/p0-conventions.tex#bpP:p0:cylkol@L186-L186 | ¦w^s¦_inf <= C mu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.IsCylinderKolmogorovSet (KAM/Frozen/Planetary/Defs/IsCylinderKolmogorovSet.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:circular#circularPoint
KIND: definition
TITLE: Reference circular configurations and the tube: KAM.Planetary.circularPoint
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:circular@L195-L203
PROOF_SOURCE: -
CONTRACT_ID: planetary.circularPoint
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): G, m_0 in R (positive by the guard), m, a, phi in R^n (a_i > 0 guards the square root and the division)
SOURCE_QUANTIFIERS: n implicit; G, m_0, m, a, phi
SOURCE_CONCLUSION: defines circ(phi) = ((a_i (cos 2 pi phi_i, sin 2 pi phi_i))_i, (m_i sqrt(G m_0/a_i) (-sin 2 pi phi_i, cos 2 pi phi_i))_i) in Ph_{2n}: circular prograde Kepler configurations at coupling 0
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/CircularPoint.lean
FROZEN_DECL: KAM.Planetary.circularPoint
FROZEN_ANCHOR_ID: planetary.circularPoint.v1
FROZEN_ABI_SHA256: f098aa87920dcac584bb1679a00460099740cfd59c2b2d8a97abc988f607b476
DEPS: bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:circular@L197-L197 | circ(phi) lies in Ph_{2n}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.circularPoint (KAM/Frozen/Planetary/Defs/CircularPoint.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:circular#circularTube
KIND: definition
TITLE: Reference circular configurations and the tube: KAM.Planetary.circularTube
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:circular@L195-L203
PROOF_SOURCE: -
CONTRACT_ID: planetary.circularTube
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): G, m_0 in R, m, a in R^n, eta in R
SOURCE_QUANTIFIERS: n implicit; G, m_0, m, a, eta
SOURCE_CONCLUSION: defines the circular tube U_eta = {z in Ph_{2n}: exists phi in R^n, ¦z - circ(phi)¦_inf < eta} (open eta-neighbourhood in the phase max norm)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/CircularTube.lean
FROZEN_DECL: KAM.Planetary.circularTube
FROZEN_ANCHOR_ID: planetary.circularTube.v1
FROZEN_ABI_SHA256: 60ddb9bd5c857d511be9a8751354ff2855097972776a8e31b586f90dd0fbb01e
DEPS: bpP:p0:circular#circularPoint, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:circular#circularPoint | blueprint-P/parts/p0-conventions.tex#bpP:p0:circular@L200-L200 | U_eta is the eta-neighbourhood of the circular points circ(phi)
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:circular@L200-L200 | U_eta subset Ph_{2n}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.circularTube (KAM/Frozen/Planetary/Defs/CircularTube.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:nocoll#NoCollision
KIND: definition
TITLE: No collision, pair bounds: KAM.Planetary.NoCollision
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:nocoll@L205-L211
PROOF_SOURCE: -
CONTRACT_ID: planetary.NoCollision
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): q in R^{2n}
SOURCE_QUANTIFIERS: n implicit; q
SOURCE_CONCLUSION: defines NoColl(q): ¦q^(i)¦ > 0 for all i and ¦q^(i) - q^(j)¦ > 0 for all i != j (heliocentric configurations, Sun at the origin)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/NoCollision.lean
FROZEN_DECL: KAM.Planetary.NoCollision
FROZEN_ANCHOR_ID: planetary.NoCollision.v1
FROZEN_ABI_SHA256: 31e597095beb23bba20a6793288094acda1208d7d884eb456886c2787f7d244b
DEPS: bpP:p0:plane#planeLength, bpP:p0:body#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:nocoll@L206-L206 | ¦.¦ is the physical length
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:nocoll@L206-L206 | q^(i) = body(q,i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.NoCollision (KAM/Frozen/Planetary/Defs/NoCollision.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:nocoll#PairBounds
KIND: definition
TITLE: No collision, pair bounds: KAM.Planetary.PairBounds
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:nocoll@L205-L211
PROOF_SOURCE: -
CONTRACT_ID: planetary.PairBounds
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): d, D in R, Q_0..Q_{N-1} in R^2
SOURCE_QUANTIFIERS: N implicit; d, D, Q
SOURCE_CONCLUSION: defines PairBounds(d,D;Q): d <= ¦Q_j - Q_i¦ <= D for all i != j
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PairBounds.lean
FROZEN_DECL: KAM.Planetary.PairBounds
FROZEN_ANCHOR_ID: planetary.PairBounds.v1
FROZEN_ABI_SHA256: 5cbec024474835d4c12fff797b2f2b21ebd9701e058b18573159de21d56ada16
DEPS: bpP:p0:plane#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:nocoll@L208-L208 | ¦.¦ is the physical length
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.PairBounds (KAM/Frozen/Planetary/Defs/PairBounds.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:barycentric#actualMasses
KIND: definition
TITLE: Actual masses, barycentric reconstruction: KAM.Planetary.actualMasses
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:barycentric@L213-L224
PROOF_SOURCE: -
CONTRACT_ID: planetary.actualMasses
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): m_0 in R, m in R^n, mu in R
SOURCE_QUANTIFIERS: n implicit; m_0, m, mu
SOURCE_CONCLUSION: defines mass_mu = (m_0, mu m_1, ..., mu m_n) in R^{n+1} (index 0 is the Sun)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/ActualMasses.lean
FROZEN_DECL: KAM.Planetary.actualMasses
FROZEN_ANCHOR_ID: planetary.actualMasses.v1
FROZEN_ABI_SHA256: 37d0c6b0a92ae0e0c839d24e591536f697c601419b11cc5c864150814a680b60
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.actualMasses (KAM/Frozen/Planetary/Defs/ActualMasses.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:barycentric#barycentricPositions
KIND: definition
TITLE: Actual masses, barycentric reconstruction: KAM.Planetary.barycentricPositions
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:barycentric@L213-L224
PROOF_SOURCE: -
CONTRACT_ID: planetary.barycentricPositions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): n in N; m_0, mu in R; m in R^n; q in R^{2n}
SOURCE_QUANTIFIERS: n implicit; m_0, m, mu, q
SOURCE_CONCLUSION: defines x_0(q) = -mu/(m_0 + mu sum_i m_i) sum_i m_i q^(i) and x_i(q) = x_0(q) + q^(i) (Sun at index 0, planet i at index i, order of Fin.cons)
CONSTANT_SCOPE: none; the definition is total for arbitrary real data. In the physical applications, m_0 > 0, m_i > 0 and mu > 0 guard divisions as described at P0 L193, L220-L221, L319-L320.
FROZEN_FILE: KAM/Frozen/Planetary/Defs/BarycentricPositions.lean
FROZEN_DECL: KAM.Planetary.barycentricPositions
FROZEN_ANCHOR_ID: planetary.barycentricPositions.v1
FROZEN_ABI_SHA256: 222cb379298aba4da485faf152163725857fac2c6578168946b7d79fc09910d1
DEPS: bpP:p0:body#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:barycentric@L217-L217 | q^(i) = body(q,i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.barycentricPositions (KAM/Frozen/Planetary/Defs/BarycentricPositions.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:barycentric#barycentricVelocities
KIND: definition
TITLE: Actual masses, barycentric reconstruction: KAM.Planetary.barycentricVelocities
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:barycentric@L213-L224
PROOF_SOURCE: -
CONTRACT_ID: planetary.barycentricVelocities
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): n in N; m_0, mu in R; m in R^n; p in R^{2n}
SOURCE_QUANTIFIERS: n implicit; m_0, m, mu, p
SOURCE_CONCLUSION: defines v_0(p) = -(mu/m_0) sum_i p^(i) and v_i(p) = p^(i)/m_i (1 <= i <= n; Sun at index 0)
CONSTANT_SCOPE: none; the definition is total for arbitrary real data. In the physical applications, m_0 > 0, m_i > 0 and mu > 0 guard divisions as described at P0 L193, L220-L221, L319-L320.
FROZEN_FILE: KAM/Frozen/Planetary/Defs/BarycentricVelocities.lean
FROZEN_DECL: KAM.Planetary.barycentricVelocities
FROZEN_ANCHOR_ID: planetary.barycentricVelocities.v1
FROZEN_ABI_SHA256: f0bb61447643e18562ffdde5d8ddbd4bc7ed46d52985b4fabaeab4a657a15480
DEPS: bpP:p0:body#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:barycentric@L218-L218 | p^(i) = body(p,i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.barycentricVelocities (KAM/Frozen/Planetary/Defs/BarycentricVelocities.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:newton#IsNewtonSolution
KIND: definition
TITLE: Newton solutions: KAM.Planetary.IsNewtonSolution
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:newton@L226-L233
PROOF_SOURCE: -
CONTRACT_ID: planetary.IsNewtonSolution
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): N in N, G in R, M in R^N, Q, V: R -> (R^2)^N
SOURCE_QUANTIFIERS: N implicit; G, M, Q, V
SOURCE_CONCLUSION: defines IsNewton(G,M,Q,V) as the conjunction: (i) for every t in R and i,j < N with i != j, ¦Q_j(t)-Q_i(t)¦ > 0; (ii) for every t in R and i < N, Q_i has derivative V_i(t) at t; (iii) for every t in R and i < N, V_i has derivative sum_{j != i} G M_j/¦Q_j(t)-Q_i(t)¦^3 (Q_j(t)-Q_i(t)) at t (all-time Newton equations)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/IsNewtonSolution.lean
FROZEN_DECL: KAM.Planetary.IsNewtonSolution
FROZEN_ANCHOR_ID: planetary.IsNewtonSolution.v1
FROZEN_ABI_SHA256: 8402f230d795a683f6ad950f3be88f5af078b355ff661cbdd9c85ed215b5675e
DEPS: bpP:p0:plane#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:newton@L228-L228 | ¦.¦ is the physical length in (i) and (iii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.IsNewtonSolution (KAM/Frozen/Planetary/Defs/IsNewtonSolution.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:fixedsol#IsFixedSolution
KIND: definition
TITLE: Fixed-Sun solutions: KAM.Planetary.IsFixedSolution
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:fixedsol@L235-L242
PROOF_SOURCE: -
CONTRACT_ID: planetary.IsFixedSolution
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): n in N; G, m_0, eps in R; m in R^n; Q, V: R -> (R^2)^n
SOURCE_QUANTIFIERS: n implicit; G, m_0, m, eps, Q, V
SOURCE_CONCLUSION: defines IsFixedSol(G,m_0,m,eps,Q,V) as the conjunction: for every t and i < n, ¦Q_i(t)¦ > 0; for every t and i,j < n with i != j, ¦Q_j(t)-Q_i(t)¦ > 0; for every t and i < n, Q_i has derivative V_i(t) at t; for every t and i < n, V_i has derivative -G m_0/¦Q_i(t)¦^3 Q_i(t) + eps sum_{j != i} G m_j/¦Q_j(t)-Q_i(t)¦^3 (Q_j(t)-Q_i(t)) at t. The Sun is the constant origin.
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/IsFixedSolution.lean
FROZEN_DECL: KAM.Planetary.IsFixedSolution
FROZEN_ANCHOR_ID: planetary.IsFixedSolution.v1
FROZEN_ABI_SHA256: 6af3b94b20194109c8fa7add7b37df97b99d75e798ffbe8c6d5edc188df0ad80
DEPS: bpP:p0:plane#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixedsol@L237-L237 | ¦.¦ is the physical length
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.IsFixedSolution (KAM/Frozen/Planetary/Defs/IsFixedSolution.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:movham#movingHamiltonian
KIND: definition
TITLE: Moving-Sun Hamiltonian: KAM.Planetary.movingHamiltonian
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:movham@L244-L255
PROOF_SOURCE: -
CONTRACT_ID: planetary.movingHamiltonian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): n in N; G, m_0, mu in R; m in R^n; z = (q,p) in Ph_{2n}
SOURCE_QUANTIFIERS: n implicit; G, m_0, m, mu, z
SOURCE_CONCLUSION: defines H_mov(z) = sum_i [(1/m_i + mu/m_0) ¦p^(i)¦^2/2 - G m_0 m_i/¦q^(i)¦] + mu sum_{i<j} [p^(i).p^(j)/m_0 - G m_i m_j/¦q^(i) - q^(j)¦] (every term kept: the Sun moves)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/MovingHamiltonian.lean
FROZEN_DECL: KAM.Planetary.movingHamiltonian
FROZEN_ANCHOR_ID: planetary.movingHamiltonian.v1
FROZEN_ABI_SHA256: 8286a501cf934fd5f341976b5390802b17da25398fc9059edc35fd65d3ab79d8
DEPS: bpP:p0:phase#Phase, bpP:p0:plane#planeSq, bpP:p0:plane#planeLength, bpP:p0:plane#planeDot, bpP:p0:body#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:movham@L245-L245 | z in Ph_{2n}
EDGE: bpP:p0:plane#planeSq | blueprint-P/parts/p0-conventions.tex#bpP:p0:movham@L247-L247 | ¦p^(i)¦^2
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:movham@L247-L247 | ¦q^(i)¦
EDGE: bpP:p0:plane#planeDot | blueprint-P/parts/p0-conventions.tex#bpP:p0:movham@L248-L248 | p^(i).p^(j)
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:movham@L247-L247 | q^(i), p^(i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.movingHamiltonian (KAM/Frozen/Planetary/Defs/MovingHamiltonian.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:fixham#fixedHamiltonian
KIND: definition
TITLE: Fixed-Sun Hamiltonian: KAM.Planetary.fixedHamiltonian
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:fixham@L257-L263
PROOF_SOURCE: -
CONTRACT_ID: planetary.fixedHamiltonian
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): n in N; G, m_0, eps in R; m in R^n; z = (q,p) in Ph_{2n}
SOURCE_QUANTIFIERS: n implicit; G, m_0, m, eps, z
SOURCE_CONCLUSION: defines H_fix(z) = sum_i [¦p^(i)¦^2/(2 m_i) - G m_0 m_i/¦q^(i)¦] - eps sum_{i<j} G m_i m_j/¦q^(i) - q^(j)¦ (Sun at the origin; only the planet-planet interaction, with coefficient eps)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/FixedHamiltonian.lean
FROZEN_DECL: KAM.Planetary.fixedHamiltonian
FROZEN_ANCHOR_ID: planetary.fixedHamiltonian.v1
FROZEN_ABI_SHA256: 60485f51ed52fdf21458b60ec11010aa47658aa6ddb09a132faf7e83e33d99f3
DEPS: bpP:p0:phase#Phase, bpP:p0:plane#planeSq, bpP:p0:plane#planeLength, bpP:p0:body#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixham@L258-L258 | z in Ph_{2n}
EDGE: bpP:p0:plane#planeSq | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixham@L259-L259 | ¦p^(i)¦^2
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixham@L259-L259 | ¦q^(i)¦
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixham@L259-L259 | q^(i), p^(i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.fixedHamiltonian (KAM/Frozen/Planetary/Defs/FixedHamiltonian.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:phystorus#IsPhysicalTorus
KIND: definition
TITLE: Physical torus: KAM.Planetary.IsPhysicalTorus
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:phystorus@L265-L281
PROOF_SOURCE: -
CONTRACT_ID: planetary.IsPhysicalTorus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): H: Ph_d -> R, w in R^d, K: R^d -> Ph_d
SOURCE_QUANTIFIERS: d implicit; H, w, K
SOURCE_CONCLUSION: defines IsPhysTorus(H,w,K): (i) K real analytic on R^d; (ii) H differentiable at K(theta) for all theta; (iii) K(theta+k) = K(theta) for k in Z^d; (iv) K(theta) = K(theta') implies theta'-theta in Z^d; (v) DK(theta) injective; (vi) Omega(DK(theta)u, DK(theta)v) = 0; (vii) exist gamma > 0 and tau > d-1 with w (gamma,tau)-Diophantine; (viii) for all theta,t: s -> K(theta+s w) has derivative X_H(K(theta+t w)) at s = t
CONSTANT_SCOPE: gamma, tau depend on w; tau > d-1 here against tau > a+b for cylinder tori; period-one parameters
FROZEN_FILE: KAM/Frozen/Planetary/Defs/IsPhysicalTorus.lean
FROZEN_DECL: KAM.Planetary.IsPhysicalTorus
FROZEN_ANCHOR_ID: planetary.IsPhysicalTorus.v1
FROZEN_ABI_SHA256: 2411bc7f3bfda703f06e8078c56064502ffbd88a21145dd36cf2cba1d399badf
DEPS: bpP:p0:phase#Phase, bpP:p0:hamsymp#symplecticForm, bpP:p0:diophantine#IsDiophantine, bpP:p0:hamsymp#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:phystorus@L266-L266 | H and K live on Ph_d
EDGE: bpP:p0:hamsymp#symplecticForm | blueprint-P/parts/p0-conventions.tex#bpP:p0:phystorus@L273-L273 | Omega in (vi)
EDGE: bpP:p0:diophantine#IsDiophantine | blueprint-P/parts/p0-conventions.tex#bpP:p0:phystorus@L274-L274 | w is (gamma,tau)-Diophantine in (vii)
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p0-conventions.tex#bpP:p0:phystorus@L275-L275 | X_H in (viii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.IsPhysicalTorus (KAM/Frozen/Planetary/Defs/IsPhysicalTorus.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:movkol#MovingKolmogorovSet
KIND: definition
TITLE: Moving-Sun Kolmogorov set: KAM.Planetary.MovingKolmogorovSet
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:movkol@L283-L295
PROOF_SOURCE: -
CONTRACT_ID: planetary.MovingKolmogorovSet
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): n in N; G, m_0, mu, eta, d, D in R; m, a in R^n; S subset Ph_{2n}
SOURCE_QUANTIFIERS: n implicit; G, m_0, m, a, mu, eta, d, D, S
SOURCE_CONCLUSION: defines MovKol(G,m_0,m,a,mu,eta,d,D,S): S measurable, S subset U_eta, and every z in S has w, K, theta with K(theta) = z, K(R^{2n}) subset S, IsPhysTorus(H_mov,w,K), and for every phi in R^{2n}: (a) NoColl(K(phi)_1); (b) IsNewton(G,mass_mu, t -> x(K(phi+t w)_1), t -> v(K(phi+t w)_2)); (c) PairBounds(d,D; x(K(phi)_1))
CONSTANT_SCOPE: w, K, theta depend on z; d, D are fixed arguments. The source uses this total predicate under the physical convention G, m_0 > 0 and m_i > 0 (P0 L193); these are not additional arguments or conjuncts of the definition.
FROZEN_FILE: KAM/Frozen/Planetary/Defs/MovingKolmogorovSet.lean
FROZEN_DECL: KAM.Planetary.MovingKolmogorovSet
FROZEN_ANCHOR_ID: planetary.MovingKolmogorovSet.v1
FROZEN_ABI_SHA256: 2f6ca8e426b3436532e15e8e5946808d686bd351b4dddf6c1ef2e89294654dad
DEPS: bpP:p0:phase#Phase, bpP:p0:circular#circularTube, bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:movham#movingHamiltonian, bpP:p0:nocoll#NoCollision, bpP:p0:newton#IsNewtonSolution, bpP:p0:barycentric#actualMasses, bpP:p0:barycentric#barycentricPositions, bpP:p0:barycentric#barycentricVelocities, bpP:p0:nocoll#PairBounds
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:movkol@L284-L284 | S subset Ph_{2n}
EDGE: bpP:p0:circular#circularTube | blueprint-P/parts/p0-conventions.tex#bpP:p0:movkol@L285-L285 | S subset U_eta
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p0-conventions.tex#bpP:p0:movkol@L286-L286 | IsPhysTorus(H_mov,w,K)
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p0-conventions.tex#bpP:p0:movkol@L286-L286 | H_mov is the Hamiltonian of the torus predicate
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p0-conventions.tex#bpP:p0:movkol@L288-L288 | clause (a)
EDGE: bpP:p0:newton#IsNewtonSolution | blueprint-P/parts/p0-conventions.tex#bpP:p0:movkol@L289-L289 | clause (b)
EDGE: bpP:p0:barycentric#actualMasses | blueprint-P/parts/p0-conventions.tex#bpP:p0:movkol@L289-L289 | masses mass_mu in (b)
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p0-conventions.tex#bpP:p0:movkol@L290-L290 | x in (b) and (c)
EDGE: bpP:p0:barycentric#barycentricVelocities | blueprint-P/parts/p0-conventions.tex#bpP:p0:movkol@L290-L290 | v in (b)
EDGE: bpP:p0:nocoll#PairBounds | blueprint-P/parts/p0-conventions.tex#bpP:p0:movkol@L291-L291 | clause (c)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.MovingKolmogorovSet (KAM/Frozen/Planetary/Defs/MovingKolmogorovSet.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:fixkol#FixedKolmogorovSet
KIND: definition
TITLE: Fixed-Sun Kolmogorov set: KAM.Planetary.FixedKolmogorovSet
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:fixkol@L297-L304
PROOF_SOURCE: -
CONTRACT_ID: planetary.FixedKolmogorovSet
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): n in N; G, m_0, eps, eta, d, D in R; m, a in R^n; S subset Ph_{2n}
SOURCE_QUANTIFIERS: n implicit; G, m_0, m, a, eps, eta, d, D, S
SOURCE_CONCLUSION: defines FixKol(G,m_0,m,a,eps,eta,d,D,S): S measurable, S subset U_eta, and every z in S has w, K, theta with K(theta) = z, K(R^{2n}) subset S, IsPhysTorus(H_fix,w,K), and for every phi: NoColl(K(phi)_1); IsFixedSol(G,m_0,m,eps, t -> (K(phi+t w)_1^(i))_i, t -> (K(phi+t w)_2^(i)/m_i)_i); PairBounds(d,D; (0,K(phi)_1^(1),...,K(phi)_1^(n)))
CONSTANT_SCOPE: w, K, theta depend on z; d, D are fixed arguments. The source uses this total predicate under the physical convention G, m_0 > 0 and m_i > 0 (P0 L193); these are not additional arguments or conjuncts of the definition.
FROZEN_FILE: KAM/Frozen/Planetary/Defs/FixedKolmogorovSet.lean
FROZEN_DECL: KAM.Planetary.FixedKolmogorovSet
FROZEN_ANCHOR_ID: planetary.FixedKolmogorovSet.v1
FROZEN_ABI_SHA256: 52da59adfe14308434550d0b0436813de09bfc89b46c325cd3cbb46201acc460
DEPS: bpP:p0:phase#Phase, bpP:p0:circular#circularTube, bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:fixham#fixedHamiltonian, bpP:p0:nocoll#NoCollision, bpP:p0:fixedsol#IsFixedSolution, bpP:p0:body#bodyVector, bpP:p0:nocoll#PairBounds
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixkol@L298-L298 | S subset Ph_{2n}
EDGE: bpP:p0:circular#circularTube | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixkol@L298-L298 | S subset U_eta
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixkol@L299-L299 | IsPhysTorus(H_fix,w,K)
EDGE: bpP:p0:fixham#fixedHamiltonian | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixkol@L299-L299 | H_fix is the Hamiltonian of the torus predicate
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixkol@L300-L300 | NoColl clause
EDGE: bpP:p0:fixedsol#IsFixedSolution | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixkol@L300-L300 | IsFixedSol clause
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixkol@L300-L300 | K(..)_1^(i) are body vectors
EDGE: bpP:p0:nocoll#PairBounds | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixkol@L301-L301 | PairBounds clause
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.FixedKolmogorovSet (KAM/Frozen/Planetary/Defs/FixedKolmogorovSet.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:totality
KIND: claim
TITLE: Lean totality
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L306-L329
PROOF_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L306-L329
CONTRACT_ID: bpP:p0:totality
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the relevant guards of the Part 0 statements, clause by clause (not new standing assumptions): analyticity/differentiability on the stated domains; HasFastDiffeomorphism on W containing closure(V); integrability in HasSecularBirkhoffForm and 0 < delta <= r_0; collision-free clauses; G, m_0, m_i, a_i, mu > 0 where the corresponding divisions are used; 0 < r < r_* < 1; k != 0; V open and bounded and S measurable for the measure clause
SOURCE_QUANTIFIERS: none (a list of guarded facts attached to the definitions of Part 0)
SOURCE_CONCLUSION: guard summary: fderiv is zero at non-differentiability, whereas the torus derivatives are genuine by the differentiability of H and analyticity of K; H_mu is analytic on C(V,r) under the P-G data and r < r_0, mu in [0,mu_0]; the Bochner integral P_av is zero for a non-integrable integrand and HasBirkhoff (i) supplies integrability for every point of (ii); physical lengths have nonnegative square-root radicands and collision and positivity clauses guard the stated reciprocals; log(1/r) > 0 and sqrt r has r > 0; ¦k¦_1 >= 1 for nonzero integer k; ofReal(1-C sqrt r) equals the real lower factor if positive and zero otherwise, so in the latter case the strict lower measure inequality follows from 0 < meas(S cap F); F(V,r) is Borel, S is measurable, and meas F(V,r) < infinity for bounded V
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpP:p0:fastfreq#fastFrequency, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p0:fastdiffeo#HasFastDiffeomorphism, bpP:p0:birkhoff#HasSecularBirkhoffForm, bpP:p0:secavg#secularAverage, bpP:p0:plane#planeLength, bpP:p0:nocoll#NoCollision, bpP:p0:newton#IsNewtonSolution, bpP:p0:fixedsol#IsFixedSolution, bpP:p0:circular#circularPoint, bpP:p0:barycentric#barycentricPositions, bpP:p0:barycentric#barycentricVelocities, bpP:p0:diophantine#IsDiophantine, bpP:p0:cylinder#cylinderCell, bpP:p0:cyltorus#IsCylinderTorus, bpP:p0:phystorus#IsPhysicalTorus, bpP:p0:cylinder#cylinder, bpP:p0:degham#degenerateHamiltonian, bpP:p0:hamsymp#symplecticForm
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:fastfreq#fastFrequency | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L310-L310 | omega_{H_0} totality (Frechet derivative 0 at non-differentiability)
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L310-L310 | X_H totality
EDGE: bpP:p0:fastdiffeo#HasFastDiffeomorphism | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L311-L311 | omega_{H_0} used only through HasFastDiffeo
EDGE: bpP:p0:birkhoff#HasSecularBirkhoffForm | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L315-L315 | (i) asserts integrability, (ii) has delta <= r_0
EDGE: bpP:p0:secavg#secularAverage | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L315-L315 | Bochner integral P_av is 0 for non-integrable integrands
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L317-L317 | sqrt in the physical length has nonnegative radicand
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L318-L318 | collision-free clause (a)
EDGE: bpP:p0:newton#IsNewtonSolution | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L318-L318 | IsNewton (i) guards the divisions
EDGE: bpP:p0:fixedsol#IsFixedSolution | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L318-L318 | IsFixedSol first two conjuncts guard the divisions
EDGE: bpP:p0:circular#circularPoint | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L319-L319 | sqrt(G m_0/a_i) and 1/a_i are guarded
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L319-L319 | denominator m_0 + mu sum m_i in x_0
EDGE: bpP:p0:barycentric#barycentricVelocities | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L319-L319 | denominators m_0 and m_i in v_0, v_i
EDGE: bpP:p0:diophantine#IsDiophantine | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L322-L322 | ¦k¦_1^tau with ¦k¦_1 >= 1 for k != 0
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L327-L327 | meas F(V,r) < infinity
EDGE: bpP:p0:cyltorus#IsCylinderTorus | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L311-L314 | the cylinder torus predicate supplies differentiability of H and analyticity of K
EDGE: bpP:p0:phystorus#IsPhysicalTorus | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L311-L314 | the physical torus predicate supplies the corresponding genuine derivative guards
EDGE: bpP:p0:cylinder#cylinder | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L312-L313 | the smaller cylinder C(V,r) is the analytic domain being used
EDGE: bpP:p0:degham#degenerateHamiltonian | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L313-L313 | H_mu is the family whose analyticity guards the vector field
EDGE: bpP:p0:hamsymp#symplecticForm | blueprint-P/parts/p0-conventions.tex#bpP:p0:totality@L314-L314 | the Lagrangian assertion Omega(DK .,DK .)=0 uses the genuine derivatives
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: convention/remark with purely definitional content (gap survey GAP-PLAN-P.md section 2 item 6; ruling OVERNIGHT 03:55, owner review); re-kind pending: the graph schema has no SET_KIND amendment and no remark kind
NOTE: remark kept as a node: Part 5 (stepP:p5:mn-meas) and Part 6 (bpP:p6:domain) cite it for guarded facts they consume (meas F(V,r) < infinity, domain guards). No edge to bpP:p0:pg: the remark explains the guards of that statement, and an edge would close a cycle through bpP:p5:main.

NODE: bpP:p0:pg
KIND: theorem
TITLE: P-G: corrected properly degenerate KAM
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:pg@L333-L365
PROOF_SOURCE: blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L317-L320
CONTRACT_ID: planetary.properlyDegenerateKAM
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a, b >= 1; V subset R^a open, connected, bounded; W subset R^a open with closure(V) subset W; boundary collar: there are A, d > 0 with meas{I: exists J in boundary V, ¦I-J¦_inf < t} <= A t for all 0 < t < d; r_0, mu_0, B > 0; H_0: R^a -> R, P: R x Ph_{a+b} -> R, P_0: R x R^a -> R, Omega: R x R^a -> R^b, beta: R x R^a -> R^{bxb}; (H1) (mu,z) -> P(mu,z) real analytic at every point of [0,mu_0] x closure(C(V,r_0)); (H2) P(mu, z + shift(k)) = P(mu,z) for mu in [0,mu_0], z in C(V,r_0), k in Z^a; (H3) HasFastDiffeo(H_0,W); (H4) HasBirkhoff(P,V,r_0,mu_0,P_0,Omega,beta); (H5) ¦det beta(mu,I)¦ >= B for mu in [0,mu_0], I in V; (H6) beta(mu,I) symmetric for mu in [0,mu_0], I in V
SOURCE_QUANTIFIERS: forall a, b (>= 1), V, W, (A,d collar), r_0, mu_0, B, H_0, P, P_0, Omega, beta (all data fixed first), hypotheses (H1)-(H6); exists r_*, C, c; forall r, mu with 0 < r < r_*, 0 < mu < mu_0, mu < r^6/(log(1/r))^c; exists S
SOURCE_CONCLUSION: there exist r_*, C, c with 0 < r_* < r_0, r_* < 1, C > 0, c > 0 such that for all r, mu with 0 < r < r_*, 0 < mu < mu_0, mu < r^6/(log(1/r))^c there is S subset Ph_{a+b} with IsCylKol(H_mu,V,r,mu,C,S) (H_mu = H_0 + mu P(mu,.)) and 0 < meas(S cap F(V,r)), ofReal(1 - C sqrt r) meas F(V,r) < meas(S cap F(V,r)) < meas F(V,r)
CONSTANT_SCOPE: r_*, C, c depend on all the data and hypotheses (a, b, V, W, A, d, r_0, mu_0, B, H_0, P, P_0, Omega, beta) and not on r or mu; C is simultaneously the frequency bound of IsCylKol and the measure constant; S depends on (r, mu)
FROZEN_FILE: KAM/Frozen/Planetary/Theorems/ProperlyDegenerateKAM.lean
FROZEN_DECL: KAM.Planetary.properlyDegenerateKAM
FROZEN_ANCHOR_ID: planetary.properlyDegenerateKAM.v1
FROZEN_ABI_SHA256: d347498b8bc8935acd3895d5fd5316822593add37c2eff43f9d7f66bfa63d001
DEPS: bpP:p0:phase#Phase, bpP:p0:cylinder#cylinder, bpP:p0:fastshift#fastShift, bpP:p0:fastdiffeo#HasFastDiffeomorphism, bpP:p0:birkhoff#HasSecularBirkhoffForm, bpP:p0:degham#degenerateHamiltonian, bpP:p0:cylkol#IsCylinderKolmogorovSet, bpP:p0:cylinder#cylinderCell, bpP:p5:main
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:pg@L337-L337 | P is defined on R x Ph_{a+b}
EDGE: bpP:p0:cylinder#cylinder | blueprint-P/parts/p0-conventions.tex#bpP:p0:pg@L342-L342 | C(V,r_0) in (H1) and (H2)
EDGE: bpP:p0:fastshift#fastShift | blueprint-P/parts/p0-conventions.tex#bpP:p0:pg@L343-L343 | shift(k) in (H2)
EDGE: bpP:p0:fastdiffeo#HasFastDiffeomorphism | blueprint-P/parts/p0-conventions.tex#bpP:p0:pg@L344-L344 | (H3) HasFastDiffeo(H_0,W)
EDGE: bpP:p0:birkhoff#HasSecularBirkhoffForm | blueprint-P/parts/p0-conventions.tex#bpP:p0:pg@L345-L345 | (H4) HasBirkhoff
EDGE: bpP:p0:degham#degenerateHamiltonian | blueprint-P/parts/p0-conventions.tex#bpP:p0:pg@L351-L351 | H_mu = H_0 + mu P(mu,.)
EDGE: bpP:p0:cylkol#IsCylinderKolmogorovSet | blueprint-P/parts/p0-conventions.tex#bpP:p0:pg@L351-L351 | IsCylKol(H_mu,V,r,mu,C,S)
EDGE: bpP:p0:cylinder#cylinderCell | blueprint-P/parts/p0-conventions.tex#bpP:p0:pg@L353-L353 | F(V,r) in the measure conclusions
EDGE: bpP:p5:main | blueprint-P/parts/p5-pg-assembly.tex#bpP:p5:main@L317-L317 | this result carries \frozen{KAM.Planetary.properlyDegenerateKAM}: it proves the anchor
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.properlyDegenerateKAM (KAM/Frozen/Planetary/Theorems/ProperlyDegenerateKAM.lean)
LEAN_NOTE: P-G anchor SEALED (manifest planetary.properlyDegenerateKAM.v1); seal-key audit P5-MAIN-audit-1 PASS WITH NOTES
NOTE: root anchor. Proof: Theorem bpP:p5:main (Part 5), which carries the \frozen tag. Source fields follow Part 0 L333-L365 and the frozen file (quantifier order: all data, then r_*,C,c, then r,mu, then S). The reference in HasBirkhoff to this theorem (L159) is a forward pointer, deleted. The sourcegap at L362 is covered by bpP:p5:strictness and bpP:p5:uniform-remainder.

NODE: bpP:p0:planar
KIND: theorem
TITLE: P-PLANAR: two planar planets with a moving Sun
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:planar@L367-L377
PROOF_SOURCE: blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:planar@L159-L163
CONTRACT_ID: planetary.planarTwoPlanetKAM
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G, m_0 > 0; m, a: Fin 2 -> R with m_i > 0 and a_i > 0 for i = 0,1 and a_0 < a_1 (strictly ordered axes, no numerical separation); eta > 0
SOURCE_QUANTIFIERS: forall G, m_0, m, a, eta (data fixed first); exists mu_0, d, D; forall mu with 0 < mu < mu_0; exists S
SOURCE_CONCLUSION: there exist mu_0, d, D with 0 < mu_0 and 0 < d < D such that for every mu with 0 < mu < mu_0 there is S subset Ph_{2.2} with 0 < meas S < infinity and MovKol(G,m_0,m,a,mu,eta,d,D,S) (n = 2)
CONSTANT_SCOPE: mu_0, d, D depend on (G, m_0, m, a, eta) and not on mu; S depends on mu
FROZEN_FILE: KAM/Frozen/Planetary/Theorems/PlanarTwoPlanetKAM.lean
FROZEN_DECL: KAM.Planetary.planarTwoPlanetKAM
FROZEN_ANCHOR_ID: planetary.planarTwoPlanetKAM.v1
FROZEN_ABI_SHA256: 53360f66c8f0dfa90319b671830d07e0f10087b394eab73dce5a2bded2651fba
DEPS: bpP:p0:phase#Phase, bpP:p0:movkol#MovingKolmogorovSet, bpP:p12:planar
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:planar@L370-L370 | S subset Ph_{2.2}
EDGE: bpP:p0:movkol#MovingKolmogorovSet | blueprint-P/parts/p0-conventions.tex#bpP:p0:planar@L371-L371 | MovKol(G,m_0,m,a,mu,eta,d,D,S) with n = 2
EDGE: bpP:p12:planar | blueprint-P/parts/p12-planar-assembly.tex#bpP:p12:planar@L159-L159 | this result carries \frozen{KAM.Planetary.planarTwoPlanetKAM}: it proves the anchor
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planarTwoPlanetKAM (KAM/Frozen/Planetary/Theorems/PlanarTwoPlanetKAM.lean)
LEAN_NOTE: P-PLANAR anchor SEALED (manifest planetary.planarTwoPlanetKAM.v1); seal-key audit P12-E-audit-1 PASS WITH NOTES
NOTE: root anchor. Proof: Theorem bpP:p12:planar (Part 12), which carries the \frozen tag; Part 12 applies the frozen P-G (edges owned by P-p12). The stale sourcegap sentence of L376 was fixed in Part 0 (it now names Part 12 as the proof).

NODE: bpP:p0:fixed
KIND: theorem
TITLE: P-FIXED: $n$ planar planets around a fixed Sun
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:fixed@L379-L388
PROOF_SOURCE: blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:fixed@L153-L161
CONTRACT_ID: planetary.fixedSunPlanetaryKAM
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 2; G, m_0 > 0; m, a: Fin n -> R with m_i > 0 and a_i > 0 for all i, and a_i < a_j whenever i < j (strictly ordered axes, no numerical separation); eta > 0
SOURCE_QUANTIFIERS: forall n, G, m_0, m, a, eta (data fixed first); exists eps_0, d, D; forall eps with 0 < eps < eps_0; exists S
SOURCE_CONCLUSION: there exist eps_0, d, D with 0 < eps_0 and 0 < d < D such that for every eps with 0 < eps < eps_0 there is S subset Ph_{n.2} with 0 < meas S < infinity and FixKol(G,m_0,m,a,eps,eta,d,D,S)
CONSTANT_SCOPE: eps_0, d, D depend on (n, G, m_0, m, a, eta) and not on eps; S depends on eps
FROZEN_FILE: KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.lean
FROZEN_DECL: KAM.Planetary.fixedSunPlanetaryKAM
FROZEN_ANCHOR_ID: planetary.fixedSunPlanetaryKAM.v1
FROZEN_ABI_SHA256: a710d06469f0efa43a0eede7aa23e7e13216737ac0895ff11757e256903b2eec
DEPS: bpP:p0:phase#Phase, bpP:p0:fixkol#FixedKolmogorovSet, bpP:p13:fixed
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixed@L381-L381 | S subset Ph_{n.2}
EDGE: bpP:p0:fixkol#FixedKolmogorovSet | blueprint-P/parts/p0-conventions.tex#bpP:p0:fixed@L382-L382 | FixKol(G,m_0,m,a,eps,eta,d,D,S)
EDGE: bpP:p13:fixed | blueprint-P/parts/p13-fixed-assembly.tex#bpP:p13:fixed@L153-L153 | this result carries \frozen{KAM.Planetary.fixedSunPlanetaryKAM}: it proves the anchor
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: writer-pfixed-revision
REVIEWER: sol-review-P-w
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: root anchor (P-FIXED revision 2026-10-28; block restored from draft/deferred-p0-fixed.md, identity fields re-checked against the manifest). Proof: Theorem bpP:p13:fixed (Part 13), which carries the \frozen tag and splits n = 2 (bpP:p13:n2, route (c) through the frozen P-G) from n >= 3 (bpP:p13:n-general, Part 11's wrapper); bpP:p13:n2 and bpP:p13:n-general also carry the tag (edges owned by P-p13). The \sourcegap (L386-L387) is mapped in the coverage.

NODE: bpP:p0:d25-cross#planeCross
KIND: definition
TITLE: Planar cross product: KAM.Planetary.planeCross
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-cross@L404-L408
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.planeCross
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (typing data): u, v in R^2
SOURCE_QUANTIFIERS: u, v
SOURCE_CONCLUSION: defines cr(u,v) = u_0 v_1 - u_1 v_0 (planar angular momentum of the canonical pair (u,v))
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlaneCross.lean
FROZEN_DECL: KAM.Planetary.planeCross
FROZEN_ANCHOR_ID: planetary.d25.planeCross.v1
FROZEN_ABI_SHA256: 27b7e3e428e60b15c01126bb9108975bef6f4c08bdd2bcd42149bf2229dab898
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planeCross (KAM/Frozen/Planetary/Defs/PlaneCross.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-kepler#keplerEnergy
KIND: definition
TITLE: Osculating Kepler quantities: KAM.Planetary.keplerEnergy
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L410-L422
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.keplerEnergy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G = m_0 = 1; m in R^n; z = (q,p) in Ph_{2n}; i < n
SOURCE_QUANTIFIERS: n implicit; m, z, i
SOURCE_CONCLUSION: defines E_i(z) = ¦p_i¦^2/(2 m_i) - m_i/¦q_i¦ (keplerEnergy), total Lean function (division by 0 is 0)
CONSTANT_SCOPE: none (total function; used only where ProgradeElliptic holds)
FROZEN_FILE: KAM/Frozen/Planetary/Defs/KeplerEnergy.lean
FROZEN_DECL: KAM.Planetary.keplerEnergy
FROZEN_ANCHOR_ID: planetary.d25.keplerEnergy.v1
FROZEN_ABI_SHA256: 16c4abfa143974cfab2700e7d6d8677f17282610a4442788226f49d67dc35bc7
DEPS: bpP:p0:phase#Phase, bpP:p0:plane#planeSq, bpP:p0:plane#planeLength, bpP:p0:body#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L411-L411 | z in Ph_{2n}
EDGE: bpP:p0:plane#planeSq | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L413-L413 | ¦p_i¦^2
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L413-L413 | ¦q_i¦
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L413-L413 | q_i = body(q,i), p_i = body(p,i) (section convention L400)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.keplerEnergy (KAM/Frozen/Planetary/Defs/KeplerEnergy.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-kepler#keplerAxis
KIND: definition
TITLE: Osculating Kepler quantities: KAM.Planetary.keplerAxis
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L410-L422
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.keplerAxis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G = m_0 = 1; m in R^n; z in Ph_{2n}; i < n
SOURCE_QUANTIFIERS: n implicit; m, z, i
SOURCE_CONCLUSION: defines a_i(z) = -m_i/(2 E_i(z)) (keplerAxis), total function
CONSTANT_SCOPE: none (total function)
FROZEN_FILE: KAM/Frozen/Planetary/Defs/KeplerAxis.lean
FROZEN_DECL: KAM.Planetary.keplerAxis
FROZEN_ANCHOR_ID: planetary.d25.keplerAxis.v1
FROZEN_ABI_SHA256: 8b55c0149ea62631a5254e243408a8d995b7e8f4808a16a0a580ed961a24913f
DEPS: bpP:p0:d25-kepler#keplerEnergy, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:d25-kepler#keplerEnergy | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L414-L414 | a_i is defined through E_i
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L411-L411 | z is a point of Ph_{2n}, explicitly the domain of this definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.keplerAxis (KAM/Frozen/Planetary/Defs/KeplerAxis.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-kepler#keplerAction
KIND: definition
TITLE: Osculating Kepler quantities: KAM.Planetary.keplerAction
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L410-L422
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.keplerAction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G = m_0 = 1; m in R^n; z in Ph_{2n}; i < n
SOURCE_QUANTIFIERS: n implicit; m, z, i
SOURCE_CONCLUSION: defines Lambda_i(z) = m_i sqrt(a_i(z)) (keplerAction), total function (sqrt x = 0 for x < 0)
CONSTANT_SCOPE: none (total function)
FROZEN_FILE: KAM/Frozen/Planetary/Defs/KeplerAction.lean
FROZEN_DECL: KAM.Planetary.keplerAction
FROZEN_ANCHOR_ID: planetary.d25.keplerAction.v1
FROZEN_ABI_SHA256: bb4ff50c2f5da52bcb864343bc951d280ef83bd68edbe387811453a1e42f10da
DEPS: bpP:p0:d25-kepler#keplerAxis, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:d25-kepler#keplerAxis | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L415-L415 | Lambda_i is defined through a_i
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L411-L411 | z is a point of Ph_{2n}, explicitly the domain of this definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.keplerAction (KAM/Frozen/Planetary/Defs/KeplerAction.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-kepler#keplerEccVector
KIND: definition
TITLE: Osculating Kepler quantities: KAM.Planetary.keplerEccVector
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L410-L422
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.keplerEccVector
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G = m_0 = 1; m in R^n; z = (q,p) in Ph_{2n}; i < n
SOURCE_QUANTIFIERS: n implicit; m, z, i
SOURCE_CONCLUSION: defines e_i(z) = (¦p_i¦^2/m_i^2 - 1/¦q_i¦) q_i - (q_i.p_i/m_i^2) p_i in R^2 (keplerEccVector, the Laplace-Runge-Lenz vector), total function
CONSTANT_SCOPE: none (total function)
FROZEN_FILE: KAM/Frozen/Planetary/Defs/KeplerEccVector.lean
FROZEN_DECL: KAM.Planetary.keplerEccVector
FROZEN_ANCHOR_ID: planetary.d25.keplerEccVector.v1
FROZEN_ABI_SHA256: 754654458593f4c80d7e127afc0bd14f866161831a7400aeec7e374efcb4d7a3
DEPS: bpP:p0:phase#Phase, bpP:p0:plane#planeSq, bpP:p0:plane#planeLength, bpP:p0:plane#planeDot, bpP:p0:body#bodyVector
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L411-L411 | z in Ph_{2n}
EDGE: bpP:p0:plane#planeSq | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L416-L416 | ¦p_i¦^2
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L416-L416 | ¦q_i¦
EDGE: bpP:p0:plane#planeDot | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L416-L416 | q_i.p_i
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-kepler@L416-L416 | q_i, p_i (section convention L400)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.keplerEccVector (KAM/Frozen/Planetary/Defs/KeplerEccVector.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-amd#totalMomentum
KIND: definition
TITLE: Total momentum and AMD: KAM.Planetary.totalMomentum
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-amd@L424-L428
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.totalMomentum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G = m_0 = 1; z in Ph_{2n}
SOURCE_QUANTIFIERS: n implicit; z
SOURCE_CONCLUSION: defines J(z) = sum_{i<n} cr(q_i,p_i) (totalMomentum)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/TotalMomentum.lean
FROZEN_DECL: KAM.Planetary.totalMomentum
FROZEN_ANCHOR_ID: planetary.d25.totalMomentum.v1
FROZEN_ABI_SHA256: 176b9c28336577a54e1e706d18da24caf3646966e591da4333bfde457dcd66ee
DEPS: bpP:p0:d25-cross#planeCross, bpP:p0:body#bodyVector, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:d25-cross#planeCross | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-amd@L425-L425 | J sums the planar cross products
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-amd@L425-L425 | q_i, p_i (section convention L400)
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-amd@L425-L425 | z in Ph_{2n} (section convention L400)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.totalMomentum (KAM/Frozen/Planetary/Defs/TotalMomentum.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-amd#physicalAMD
KIND: definition
TITLE: Total momentum and AMD: KAM.Planetary.physicalAMD
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-amd@L424-L428
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.physicalAMD
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G = m_0 = 1; m in R^n; z in Ph_{2n}
SOURCE_QUANTIFIERS: n implicit; m, z
SOURCE_CONCLUSION: defines A(z) = sum_{i<n} Lambda_i(z) - J(z) (physicalAMD)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PhysicalAMD.lean
FROZEN_DECL: KAM.Planetary.physicalAMD
FROZEN_ANCHOR_ID: planetary.d25.physicalAMD.v1
FROZEN_ABI_SHA256: ba00e36f137dbd51631d3ac6f5f1f0ce57b5615103d9ce8c7626a12373c9cb8c
DEPS: bpP:p0:d25-kepler#keplerAction, bpP:p0:d25-amd#totalMomentum, bpP:p0:phase#Phase
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:d25-kepler#keplerAction | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-amd@L425-L425 | A sums the actions Lambda_i
EDGE: bpP:p0:d25-amd#totalMomentum | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-amd@L425-L425 | A subtracts J(z)
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-amd@L425-L425 | z in Ph_{2n} (section convention L400)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.physicalAMD (KAM/Frozen/Planetary/Defs/PhysicalAMD.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-prograde#ProgradeElliptic
KIND: definition
TITLE: Prograde elliptic points: KAM.Planetary.ProgradeElliptic
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-prograde@L430-L434
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.ProgradeElliptic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m in R^n; z in Ph_{2n}
SOURCE_QUANTIFIERS: n implicit; m, z
SOURCE_CONCLUSION: defines ProgradeElliptic(m,z) iff for every i < n: 0 < m_i, 0 < ¦q_i¦, E_i(z) < 0, 0 < cr(q_i,p_i)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/ProgradeElliptic.lean
FROZEN_DECL: KAM.Planetary.ProgradeElliptic
FROZEN_ANCHOR_ID: planetary.d25.ProgradeElliptic.v1
FROZEN_ABI_SHA256: 4ae950e5489e67a623c41350bde5cf6b02707e8569b59d913829135fbf5a6ca5
DEPS: bpP:p0:phase#Phase, bpP:p0:plane#planeLength, bpP:p0:body#bodyVector, bpP:p0:d25-kepler#keplerEnergy, bpP:p0:d25-cross#planeCross
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-prograde@L431-L431 | z in Ph_{2n}
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-prograde@L432-L432 | 0 < ¦q_i¦
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-prograde@L432-L432 | q_i, p_i
EDGE: bpP:p0:d25-kepler#keplerEnergy | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-prograde@L432-L432 | E_i(z) < 0
EDGE: bpP:p0:d25-cross#planeCross | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-prograde@L432-L432 | 0 < cr(q_i,p_i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.ProgradeElliptic (KAM/Frozen/Planetary/Defs/ProgradeElliptic.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-lowamd#LowAMDRegion
KIND: definition
TITLE: Low-AMD region: KAM.Planetary.LowAMDRegion
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-lowamd@L436-L441
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.LowAMDRegion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m, l, u in R^n; A in R
SOURCE_QUANTIFIERS: n implicit; m, l, u, A
SOURCE_CONCLUSION: defines LowAMD(m,l,u,A) = {z in Ph_{2n}: ProgradeElliptic(m,z), l_i < Lambda_i(z) < u_i for all i, A(z) < A}
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/LowAMDRegion.lean
FROZEN_DECL: KAM.Planetary.LowAMDRegion
FROZEN_ANCHOR_ID: planetary.d25.LowAMDRegion.v1
FROZEN_ABI_SHA256: 099ef8d402a4189229f67f0a93b12107c793bcc5e01b75578ed068fb1c98617c
DEPS: bpP:p0:phase#Phase, bpP:p0:d25-prograde#ProgradeElliptic, bpP:p0:d25-kepler#keplerAction, bpP:p0:d25-amd#physicalAMD
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-lowamd@L438-L438 | LowAMD subset Ph_{2n}
EDGE: bpP:p0:d25-prograde#ProgradeElliptic | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-lowamd@L438-L438 | ProgradeElliptic(m,z)
EDGE: bpP:p0:d25-kepler#keplerAction | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-lowamd@L438-L438 | l_i < Lambda_i(z) < u_i
EDGE: bpP:p0:d25-amd#physicalAMD | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-lowamd@L438-L438 | A(z) < A
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.LowAMDRegion (KAM/Frozen/Planetary/Defs/LowAMDRegion.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-box#AMDBox
KIND: definition
TITLE: Geometric data $\mathcal B$ and admissibility: KAM.Planetary.AMDBox
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-box@L443-L455
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.AMDBox
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (record data)
SOURCE_QUANTIFIERS: n implicit; fields m, l, l^0, u^0, u in R^n; e_*, A_0, A_1, d, R in R
SOURCE_CONCLUSION: defines the box B for n planets as the record of m, l, l^0, u^0, u in R^n (fields mass, lower, innerLower, innerUpper, upper) and e_*, A_0, A_1, d, R in R (fields ecc, initialAMD, outerAMD, distance, radius)
CONSTANT_SCOPE: none (no condition ties B to mu)
FROZEN_FILE: KAM/Frozen/Planetary/Defs/AMDBox.lean
FROZEN_DECL: KAM.Planetary.AMDBox
FROZEN_ANCHOR_ID: planetary.d25.AMDBox.v1
FROZEN_ABI_SHA256: 0bff76a43af54d835cd965e8c6c403f8e6761ccb9f0780910c240cdb1f3d184c
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.AMDBox (KAM/Frozen/Planetary/Defs/AMDBox.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-box#Admissible
KIND: definition
TITLE: Geometric data $\mathcal B$ and admissibility: KAM.Planetary.AMDBox.Admissible
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-box@L443-L455
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.AMDBox.Admissible
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a box B for n planets (AMDBox)
SOURCE_QUANTIFIERS: n implicit; B
SOURCE_CONCLUSION: defines Admissible(B): (B1) for all i: 0 < m_i, 0 < l_i < l^0_i < u^0_i < u_i; (B2) 0 < e_* < 1, 0 < A_0 < A_1, A_1 < l_i (1 - sqrt(1-e_*^2)) for all i; (B3) 0 < d, 0 < R, and for all i: d <= (l_i/m_i)^2 (1-e_*) and (u_i/m_i)^2 (1+e_*) <= R; (B4) for all i < j: (u_i/m_i)^2 (1+e_*) + d <= (l_j/m_j)^2 (1-e_*)
CONSTANT_SCOPE: none (no condition ties B to mu)
FROZEN_FILE: KAM/Frozen/Planetary/Defs/AMDBoxAdmissible.lean
FROZEN_DECL: KAM.Planetary.AMDBox.Admissible
FROZEN_ANCHOR_ID: planetary.d25.AMDBox.Admissible.v1
FROZEN_ABI_SHA256: f76ce0736a484b9aee346714b5946db7ab37a3cc691cfa0bb95c8abac00ed94d
DEPS: bpP:p0:d25-box#AMDBox
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:d25-box#AMDBox | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-box@L445-L445 | the predicate is on the fields of the box B
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.AMDBox.Admissible (KAM/Frozen/Planetary/Defs/AMDBoxAdmissible.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-movsol#IsMovingSolutionOn
KIND: definition
TITLE: Moving-Sun solutions on a time set: KAM.Planetary.IsMovingSolutionOn
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-movsol@L457-L462
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.IsMovingSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m in R^n, mu in R, J subset R, z: R -> Ph_{2n}; G = m_0 = 1
SOURCE_QUANTIFIERS: n implicit; m, mu, J, z
SOURCE_CONCLUSION: defines IsMovSolOn(m,mu,J,z) iff for every t in J: H_mov differentiable at z(t), z has derivative X_{H_mov}(z(t)) at t (two-sided, z defined on R), and NoColl(z(t)_1); equals IsHamiltonianSolutionOn(movingHamiltonian 1 1 m mu, Set.univ, J, z) and NoColl
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/IsMovingSolutionOn.lean
FROZEN_DECL: KAM.Planetary.IsMovingSolutionOn
FROZEN_ANCHOR_ID: planetary.d25.IsMovingSolutionOn.v1
FROZEN_ABI_SHA256: b09b6a924851b13c3ab5d708da0cd1cbeff1a2088abc7803ffaa956c257b3708
DEPS: bpP:p0:phase#Phase, bpP:p0:movham#movingHamiltonian, bpP:p0:hamsymp#hamiltonianVectorField, bpP:p0:nocoll#NoCollision, bpP:p0:d25-movsol#IsHamiltonianSolutionOn
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-movsol@L458-L458 | z: R -> Ph_{2n}
EDGE: bpP:p0:movham#movingHamiltonian | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-movsol@L458-L458 | H_mov = movingHamiltonian 1 1 m mu
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-movsol@L459-L459 | X_{H_mov}
EDGE: bpP:p0:nocoll#NoCollision | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-movsol@L459-L459 | NoColl(z(t)_1)
EDGE: bpP:p0:d25-movsol#IsHamiltonianSolutionOn | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-movsol@L460-L460 | IsHamiltonianSolutionOn with momentum-domain slot Set.univ
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.IsMovingSolutionOn (KAM/Frozen/Planetary/Defs/IsMovingSolutionOn.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-movsol#IsHamiltonianSolutionOn
KIND: definition
TITLE: Moving-Sun solutions on a time set: KAM.Iso.IsHamiltonianSolutionOn
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-movsol@L457-L462
PROOF_SOURCE: -
CONTRACT_ID: iso.IsHamiltonianSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H: Ph_d -> R; B subset R^d (momentum domain); J subset R; z: R -> Ph_d (transcribed with B = Set.univ)
SOURCE_QUANTIFIERS: d implicit; H, B, J, z
SOURCE_CONCLUSION: defines IsHamiltonianSolutionOn(H,B,J,z): for every t in J: z(t)_2 in B, H differentiable at z(t), and z has derivative X_H(z(t)) at t
CONSTANT_SCOPE: none (track-I frozen definition reused; momentum-domain slot Set.univ in P)
FROZEN_FILE: KAM/Frozen/Iso/Defs/IsHamiltonianSolutionOn.lean
FROZEN_DECL: KAM.Iso.IsHamiltonianSolutionOn
FROZEN_ANCHOR_ID: iso.IsHamiltonianSolutionOn.v1
FROZEN_ABI_SHA256: b20065362bfe0068a5eb3cfdf98a886d7ffd591bdef0464cebfbe3e171d56beb
DEPS: bpP:p0:hamsymp#hamiltonianVectorField
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:hamsymp#hamiltonianVectorField | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-movsol@L459-L459 | z has derivative X_H(z(t))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Iso.IsHamiltonianSolutionOn (KAM/Frozen/Iso/Defs/IsHamiltonianSolutionOn.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: track-I frozen definition (KAM.Iso.IsHamiltonianSolutionOn, manifest iso.*) transcribed with a \frozen tag at Part 0 L460 together with IsMovingSolutionOn; the generic statement is read from the frozen file, the blueprint gives it only for the momentum-domain slot Set.univ.

NODE: bpP:p0:d25-newton#IsNewtonSolutionOn
KIND: definition
TITLE: Newton solutions on a time set: KAM.Planetary.IsNewtonSolutionOn
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-newton@L464-L469
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.IsNewtonSolutionOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: N in N, M in R^N, J subset R, Q, V: R -> (R^2)^N
SOURCE_QUANTIFIERS: N implicit; M, J, Q, V
SOURCE_CONCLUSION: defines IsNewtonOn(M,J,Q,V): for all t in J and all indices: (i) ¦Q_j(t) - Q_i(t)¦ > 0 for i != j; (ii) Q_i has derivative V_i(t) at t; (iii) V_i has derivative sum_{j != i} M_j/¦Q_j(t) - Q_i(t)¦^3 (Q_j(t) - Q_i(t)) at t (IsNewton with G = 1 and t in R replaced by t in J)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/IsNewtonSolutionOn.lean
FROZEN_DECL: KAM.Planetary.IsNewtonSolutionOn
FROZEN_ANCHOR_ID: planetary.d25.IsNewtonSolutionOn.v1
FROZEN_ABI_SHA256: a03730db1e938d4da88e154ebbb322ec514de0aa287e030a2de6e8a1625e397f
DEPS: bpP:p0:plane#planeLength
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-newton@L465-L465 | ¦.¦ is the physical length
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.IsNewtonSolutionOn (KAM/Frozen/Planetary/Defs/IsNewtonSolutionOn.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-unique#MovingUniqueOn
KIND: definition
TITLE: Uniqueness among local solutions: KAM.Planetary.MovingUniqueOn
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-unique@L471-L475
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.MovingUniqueOn
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m in R^n, mu in R, J subset R, z: R -> Ph_{2n}
SOURCE_QUANTIFIERS: n implicit; m, mu, J, z
SOURCE_CONCLUSION: defines MovUniqueOn(m,mu,J,z) iff for every open convex U subset R with 0 in U and every w: R -> Ph_{2n} with w(0) = z(0) and IsMovSolOn(m,mu,U,w): w(t) = z(t) for all t in U cap J (no global flow presupposed)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/MovingUniqueOn.lean
FROZEN_DECL: KAM.Planetary.MovingUniqueOn
FROZEN_ANCHOR_ID: planetary.d25.MovingUniqueOn.v1
FROZEN_ABI_SHA256: d7cd7186c2539239b187c02b6e2523a88981cb2e7c3c158ace598e407b45089e
DEPS: bpP:p0:phase#Phase, bpP:p0:d25-movsol#IsMovingSolutionOn
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-unique@L472-L472 | z, w: R -> Ph_{2n}
EDGE: bpP:p0:d25-movsol#IsMovingSolutionOn | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-unique@L473-L473 | IsMovSolOn(m,mu,U,w)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.MovingUniqueOn (KAM/Frozen/Planetary/Defs/MovingUniqueOn.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-stopped#StoppedActionBound
KIND: definition
TITLE: Stopped action bound: KAM.Planetary.StoppedActionBound
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-stopped@L477-L484
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.StoppedActionBound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: B a box (AMDBox) for n planets, mu, T, delta in R, z_0 in Ph_{2n}
SOURCE_QUANTIFIERS: n implicit; B, mu, T, delta, z_0; then forall l, r, z
SOURCE_CONCLUSION: defines StoppedBound(B,mu,T,delta,z_0) iff for all l, r in R and z: R -> Ph_{2n} with l <= 0 <= r, l < r, z(0) = z_0, IsMovSolOn(m,mu,[l,r],z) and z(t) in LowAMD(m,l,u,A_1) for all t in [l,r]: ¦Lambda_i(z(t)) - Lambda_i(z_0)¦ <= delta for all t in [l,r] cap [-T,T] and all i
CONSTANT_SCOPE: T, delta arbitrary reals; both one-sided intervals allowed
FROZEN_FILE: KAM/Frozen/Planetary/Defs/StoppedActionBound.lean
FROZEN_DECL: KAM.Planetary.StoppedActionBound
FROZEN_ANCHOR_ID: planetary.d25.StoppedActionBound.v1
FROZEN_ABI_SHA256: ef94c714ed23d3770d24a66f788b1148e53212ce04ca01459f15ca5578f98451
DEPS: bpP:p0:d25-box#AMDBox, bpP:p0:phase#Phase, bpP:p0:d25-movsol#IsMovingSolutionOn, bpP:p0:d25-lowamd#LowAMDRegion, bpP:p0:d25-kepler#keplerAction
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:d25-box#AMDBox | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-stopped@L478-L478 | the box B supplies m, l, u, A_1
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-stopped@L478-L478 | z: R -> Ph_{2n}
EDGE: bpP:p0:d25-movsol#IsMovingSolutionOn | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-stopped@L479-L479 | IsMovSolOn(m,mu,[l,r],z)
EDGE: bpP:p0:d25-lowamd#LowAMDRegion | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-stopped@L479-L479 | z(t) in LowAMD(m,l,u,A_1)
EDGE: bpP:p0:d25-kepler#keplerAction | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-stopped@L480-L480 | Lambda_i(z(t)) - Lambda_i(z_0)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.StoppedActionBound (KAM/Frozen/Planetary/Defs/StoppedActionBound.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-exponents#planetaryTimeExponent
KIND: definition
TITLE: Exponents: KAM.Planetary.planetaryTimeExponent
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-exponents@L486-L490
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.planetaryTimeExponent
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n in N
SOURCE_QUANTIFIERS: n
SOURCE_CONCLUSION: defines alpha_n = 2/(6 n^2 - 3 n + 14) (planetaryTimeExponent; n the number of planets)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlanetaryTimeExponent.lean
FROZEN_DECL: KAM.Planetary.planetaryTimeExponent
FROZEN_ANCHOR_ID: planetary.d25.planetaryTimeExponent.v1
FROZEN_ABI_SHA256: d50f6181d0c0f28b50322ce65b1a9831d2ecd43ad5c2c9e3941105da2d0eb152
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planetaryTimeExponent (KAM/Frozen/Planetary/Defs/PlanetaryTimeExponent.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:d25-exponents#planetaryDriftExponent
KIND: definition
TITLE: Exponents: KAM.Planetary.planetaryDriftExponent
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-exponents@L486-L490
PROOF_SOURCE: -
CONTRACT_ID: planetary.d25.planetaryDriftExponent
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n in N
SOURCE_QUANTIFIERS: n
SOURCE_CONCLUSION: defines beta_n = (3/2) alpha_n (planetaryDriftExponent)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Planetary/Defs/PlanetaryDriftExponent.lean
FROZEN_DECL: KAM.Planetary.planetaryDriftExponent
FROZEN_ANCHOR_ID: planetary.d25.planetaryDriftExponent.v1
FROZEN_ABI_SHA256: 96a0f584827900cd21aa60ad82436d7ab45e5e9ea813426b73f55a4ebc50fb97
DEPS: bpP:p0:d25-exponents#planetaryTimeExponent
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:d25-exponents#planetaryTimeExponent | blueprint-P/parts/p0-conventions.tex#bpP:p0:d25-exponents@L487-L487 | beta_n = (3/2) alpha_n
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0
REVIEWER: sol-review-P-c
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.planetaryDriftExponent (KAM/Frozen/Planetary/Defs/PlanetaryDriftExponent.lean)
LEAN_NOTE: sealed frozen definition; formalized, nothing to prove
NOTE: -

NODE: bpP:p0:amd
KIND: theorem
TITLE: P-AMD-CONFINEMENT: deterministic stopped-input helper
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L499-L511
PROOF_SOURCE: blueprint-P/parts/p14a-amd-expsafe.tex#bpP:p14:amd@L129-L133
CONTRACT_ID: planetary.d25.amdConfinement
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 2; B an admissible box; mu, T, delta > 0 with l_i + 2 delta < l^0_i and u^0_i + 2 delta < u_i for all i, and A_0 + 2 n delta < A_1; z_0 in LowAMD(m,l^0,u^0,A_0) with StoppedBound(B,mu,T,delta,z_0); G = m_0 = 1
SOURCE_QUANTIFIERS: forall n >= 2, B (admissible), mu, T, delta (hypotheses above), z_0 (with the stopped bound); exists z: R -> Ph_{2n}
SOURCE_CONCLUSION: there is z: R -> Ph_{2n} with z(0) = z_0 and (a) IsMovSolOn(m,mu,[-T,T],z) and MovUniqueOn(m,mu,[-T,T],z); (b) IsNewtonOn(mass_mu,[-T,T], t -> x(z(t)_1), t -> v(z(t)_2)) with the barycentric reconstructions for G = m_0 = 1; (c) for every t in [-T,T]: z(t) in LowAMD(m,l,u,A_1), J(z(t)) = J(z(0)), for all i: ¦e_i(z(t))¦ < e_*, d <= ¦q_i(t)¦ <= R, and PairBounds(d,2R; x(z(t)_1)); (d) for every t in [-T,T]: A(z(t)) <= A_0 + n delta and ¦Lambda_i(z(t)) - Lambda_i(z_0)¦ <= delta for all i
CONSTANT_SCOPE: order of choice: B, mu, T, delta, then z_0 with the stopped bound; z depends on all of them; no dynamical premise except the stopped bound; no constant is produced
FROZEN_FILE: KAM/Frozen/Planetary/Theorems/AmdConfinement.lean
FROZEN_DECL: KAM.Planetary.amdConfinement
FROZEN_ANCHOR_ID: planetary.d25.amdConfinement.v1
FROZEN_ABI_SHA256: a06de42f8f9b1500dacb7d6458a771df2ac692e555eb951cd1b7f779ec077122
DEPS: bpP:p0:phase#Phase, bpP:p0:d25-box#AMDBox, bpP:p0:d25-box#Admissible, bpP:p0:d25-lowamd#LowAMDRegion, bpP:p0:d25-stopped#StoppedActionBound, bpP:p0:d25-movsol#IsMovingSolutionOn, bpP:p0:d25-unique#MovingUniqueOn, bpP:p0:d25-newton#IsNewtonSolutionOn, bpP:p0:barycentric#actualMasses, bpP:p0:barycentric#barycentricPositions, bpP:p0:barycentric#barycentricVelocities, bpP:p0:d25-amd#totalMomentum, bpP:p0:d25-kepler#keplerEccVector, bpP:p0:plane#planeLength, bpP:p0:body#bodyVector, bpP:p0:nocoll#PairBounds, bpP:p0:d25-amd#physicalAMD, bpP:p0:d25-kepler#keplerAction, bpP:p14:amd
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L501-L501 | z_0 in Ph_{2n}
EDGE: bpP:p0:d25-box#AMDBox | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L500-L500 | B a box with fields l, l^0, u^0, u, A_0, A_1
EDGE: bpP:p0:d25-box#Admissible | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L500-L500 | B is admissible
EDGE: bpP:p0:d25-lowamd#LowAMDRegion | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L501-L501 | z_0 in LowAMD(m,l^0,u^0,A_0)
EDGE: bpP:p0:d25-stopped#StoppedActionBound | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L501-L501 | StoppedBound(B,mu,T,delta,z_0)
EDGE: bpP:p0:d25-movsol#IsMovingSolutionOn | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L503-L503 | IsMovSolOn in (a)
EDGE: bpP:p0:d25-unique#MovingUniqueOn | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L503-L503 | MovUniqueOn in (a)
EDGE: bpP:p0:d25-newton#IsNewtonSolutionOn | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L504-L504 | IsNewtonOn in (b)
EDGE: bpP:p0:barycentric#actualMasses | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L504-L504 | mass_mu in (b)
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L504-L504 | x in (b), (c)
EDGE: bpP:p0:barycentric#barycentricVelocities | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L504-L504 | v in (b)
EDGE: bpP:p0:d25-amd#totalMomentum | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L505-L505 | J(z(t)) = J(z(0)) in (c)
EDGE: bpP:p0:d25-kepler#keplerEccVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L505-L505 | e_i(z(t)) in (c)
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L505-L505 | ¦e_i¦ and the distance bounds in (c)
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L505-L505 | q_i(t) in (c)
EDGE: bpP:p0:nocoll#PairBounds | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L505-L505 | PairBounds in (c)
EDGE: bpP:p0:d25-amd#physicalAMD | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L506-L506 | A(z(t)) in (d)
EDGE: bpP:p0:d25-kepler#keplerAction | blueprint-P/parts/p0-conventions.tex#bpP:p0:amd@L506-L506 | Lambda_i in (d)
EDGE: bpP:p14:amd | blueprint-P/parts/p14a-amd-expsafe.tex#bpP:p14:amd@L129-L129 | this result carries \frozen{KAM.Planetary.amdConfinement}: it proves the anchor
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: PROVED
LEAN_REF: KAM.Planetary.amdConfinement (KAM/Frozen/Planetary/Theorems/AmdConfinement.lean)
LEAN_NOTE: P-AMD anchor SEALED (manifest planetary.d25.amdConfinement.v1); provider audit A6-audit-1 PASS WITH NOTES (seal-ready)
NOTE: root anchor. Proof: Theorem bpP:p14:amd (Part 14a), which carries the \frozen tag.

NODE: bpP:p0:expsafe
KIND: theorem
TITLE: P-EXP-SAFE: planar moving-Sun exponential safety for every low-AMD datum
STATEMENT_SOURCE: blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L513-L522
PROOF_SOURCE: blueprint-P/parts/p14a-amd-expsafe.tex#bpP:p14:expsafe@L295-L299
CONTRACT_ID: planetary.d25.planetaryExponentialSafety
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 2; B an admissible box; G = m_0 = 1
SOURCE_QUANTIFIERS: forall n >= 2, B (admissible); exists mu_*, c, C > 0; forall mu in (0,mu_*), forall z_0 in LowAMD(m,l^0,u^0,A_0); exists z: R -> Ph_{2n}
SOURCE_CONCLUSION: there are mu_*, c, C > 0 such that for every mu in (0,mu_*) and every z_0 in LowAMD(m,l^0,u^0,A_0) there is z: R -> Ph_{2n} with z(0) = z_0 such that, with T = exp(c mu^{-alpha_n}): (a) the clauses (a), (b), (c) of P-AMD-CONFINEMENT hold on [-T,T] (existence, uniqueness, Newton equations, outer region, conservation of J, eccentricity, radius, pair bounds); (b) ¦a_i(z(t)) - a_i(z_0)¦ <= C mu^{beta_n} for all ¦t¦ <= T and all i
CONSTANT_SCOPE: mu_*, c, C depend on (n, B) only (before mu and z_0); z depends on (mu, z_0); exponents alpha_n, beta_n of the D25 definition
FROZEN_FILE: KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean
FROZEN_DECL: KAM.Planetary.planetaryExponentialSafety
FROZEN_ANCHOR_ID: planetary.d25.planetaryExponentialSafety.v1
FROZEN_ABI_SHA256: 2e161e3b644712a64211734b4208c2425542c31bf0a43de3857c3cceb1a2a14a
DEPS: bpP:p0:phase#Phase, bpP:p0:d25-box#AMDBox, bpP:p0:d25-box#Admissible, bpP:p0:d25-lowamd#LowAMDRegion, bpP:p0:d25-exponents#planetaryTimeExponent, bpP:p0:amd, bpP:p0:d25-kepler#keplerAxis, bpP:p0:d25-exponents#planetaryDriftExponent, bpP:p14:expsafe, bpP:p0:d25-movsol#IsMovingSolutionOn, bpP:p0:d25-unique#MovingUniqueOn, bpP:p0:d25-newton#IsNewtonSolutionOn, bpP:p0:barycentric#actualMasses, bpP:p0:barycentric#barycentricPositions, bpP:p0:barycentric#barycentricVelocities, bpP:p0:d25-amd#totalMomentum, bpP:p0:d25-kepler#keplerEccVector, bpP:p0:plane#planeLength, bpP:p0:body#bodyVector, bpP:p0:nocoll#PairBounds
ROUTES: -
ROUTE_FOR: -
EDGE: bpP:p0:phase#Phase | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L514-L514 | z: R -> Ph_{2n}
EDGE: bpP:p0:d25-box#AMDBox | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L514-L514 | B a box
EDGE: bpP:p0:d25-box#Admissible | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L514-L514 | B is admissible
EDGE: bpP:p0:d25-lowamd#LowAMDRegion | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L514-L514 | z_0 in LowAMD(m,l^0,u^0,A_0)
EDGE: bpP:p0:d25-exponents#planetaryTimeExponent | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L514-L514 | T = exp(c mu^{-alpha_n})
EDGE: bpP:p0:amd | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L516-L516 | clauses (a), (b), (c) of P-AMD-CONFINEMENT are part of this statement; its proof reaches them through the helper bpP:p14:amd (step es-amd)
EDGE: bpP:p0:d25-kepler#keplerAxis | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L517-L517 | a_i(z(t)) in (b)
EDGE: bpP:p0:d25-exponents#planetaryDriftExponent | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L517-L517 | C mu^{beta_n}
EDGE: bpP:p14:expsafe | blueprint-P/parts/p14a-amd-expsafe.tex#bpP:p14:expsafe@L295-L295 | this result carries \frozen{KAM.Planetary.planetaryExponentialSafety}: it proves the anchor
EDGE: bpP:p0:d25-movsol#IsMovingSolutionOn | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L516-L516 | clause (a) incorporates AMD clauses (a)-(c), which explicitly use IsMovingSolutionOn; the frozen conclusion expands that use
EDGE: bpP:p0:d25-unique#MovingUniqueOn | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L516-L516 | clause (a) incorporates AMD clauses (a)-(c), which explicitly use MovingUniqueOn; the frozen conclusion expands that use
EDGE: bpP:p0:d25-newton#IsNewtonSolutionOn | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L516-L516 | clause (a) incorporates AMD clauses (a)-(c), which explicitly use IsNewtonSolutionOn; the frozen conclusion expands that use
EDGE: bpP:p0:barycentric#actualMasses | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L516-L516 | clause (a) incorporates AMD clauses (a)-(c), which explicitly use actualMasses; the frozen conclusion expands that use
EDGE: bpP:p0:barycentric#barycentricPositions | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L516-L516 | clause (a) incorporates AMD clauses (a)-(c), which explicitly use barycentricPositions; the frozen conclusion expands that use
EDGE: bpP:p0:barycentric#barycentricVelocities | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L516-L516 | clause (a) incorporates AMD clauses (a)-(c), which explicitly use barycentricVelocities; the frozen conclusion expands that use
EDGE: bpP:p0:d25-amd#totalMomentum | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L516-L516 | clause (a) incorporates AMD clauses (a)-(c), which explicitly use totalMomentum; the frozen conclusion expands that use
EDGE: bpP:p0:d25-kepler#keplerEccVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L516-L516 | clause (a) incorporates AMD clauses (a)-(c), which explicitly use keplerEccVector; the frozen conclusion expands that use
EDGE: bpP:p0:plane#planeLength | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L516-L516 | clause (a) incorporates AMD clauses (a)-(c), which explicitly use planeLength; the frozen conclusion expands that use
EDGE: bpP:p0:body#bodyVector | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L516-L516 | clause (a) incorporates AMD clauses (a)-(c), which explicitly use bodyVector; the frozen conclusion expands that use
EDGE: bpP:p0:nocoll#PairBounds | blueprint-P/parts/p0-conventions.tex#bpP:p0:expsafe@L516-L516 | clause (a) incorporates AMD clauses (a)-(c), which explicitly use PairBounds; the frozen conclusion expands that use
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: sonnet-extract-P-p0+sol-review-P-c
REVIEWER: sol-delta-P-b
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: root anchor. Proof: Theorem bpP:p14:expsafe (Part 14a). The edge to bpP:p0:amd is kept because the statement incorporates clauses (a)-(c) of P-AMD-CONFINEMENT by reference (statement-level use); the proof applies the helper bpP:p14:amd (step es-amd).
