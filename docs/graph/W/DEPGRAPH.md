# Track W proof dependency database

GRAPH_VERSION: 4
ROOTS: bpW:wh:nlw2
CORPUS: blueprint-W/parts/{w0-conventions,w0-normalization,w1-sequences,w2-reconstruction,w3-birkhoff,w-headline}.tex pinned by SHA-256 in docs/graph/W/CORPUS.sha256 (KAM-inp branch inp, fa002b43, 2026-10-30; wave 1 = accepted parts W0-W3 and the headline; W4-W8 pending)
CONVENTIONS: docs/graph/W/SPEC.md "Conventions to watch": weighted coordinates (WaveSpace = l2 x l2, coefficients q = coeff y = y_j/(j e^j), kappa/tau transports of W1); N_+ (PNat) mode indexing, tangential i : Fin 2 is mode j = i+1, normal modes j >= 3; period-one torus angles phi = 2 pi theta, nu = omega/(2 pi), linear flow dz/dt = -i lambda z; max norm on WaveSpace (sqrt 2 factors where the source uses a Hilbert product norm); two-sided weights <l>^{2s} e^{2a|l|}, K_s = 2^s (1+2 zeta(2s))^{1/2}, C_m = 8(1+2 zeta(3))/pi independent of m; corrected normal-form coefficients E-PDE-W-1/2 (A_ii = 9/(8 pi lambda_i^2), A_12 = B_ji = 3/(2 pi lambda lambda), prefactor 1/16, I_j = |z_j|^2, q = sqrt2 Re z); positive carriers hm : 0 < m, hI : forall i, 0 < I i; headline constants r0, C, tau, eta, Gamma, nu, K after m and before I, theta0, gamma_I per I, C common to (3) and (5)
STANDING_ASSUMPTIONS: bpW:w0:mass
EXTERNAL_POLICY: track-W external inputs are the labelled items of the parts' external-fact lists (bpW:w1:ext-*, bpW:w2:ext-*, bpW:w3:ext-*, all Mathlib-level; an item that only restates another external is excluded as an alias) plus the one unlabelled W0-ledger fact bpW:w0n:ledger#ext-lindstedt; track-K results that a W proof uses (cited by \texttt{bp:p1:...}; blueprint-W has no \Kref) are IMPORTED nodes K:<K graph node> (KIND external, LEAN_STATUS EXTERNAL, STATEMENT_SOURCE in blueprint/, NOTE IMPORTED: proved in the track-K graph, node <label>; shared Lean provider); any other unproved fact is a step node with NOTE SOURCE_GAP
FROZEN_ANCHORS: bpW:w0:nlw#IsClassicalSolution, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:ellap#ellWeight, bpW:w0:ellap#WaveSpace, bpW:w0:ellap#coeff, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:Gq#cubicGrad, bpW:w0:periodone#linearTorus, bpW:wh:embedding#IsAnalyticTorusEmbedding, bpW:wh:dioph#IsDiophantine, bpW:wh:nlw2
FROZEN_MANIFEST: manifest/frozen-anchors.json | sha256:674c73210fe8aeef703101ebe014dbc3e8569cb12f54a14dba1a7ff418d76aab
WRITER: claude-suborch-W
GLOBAL_REVIEWER: -
GLOBAL_REVIEW_REF: -

The dependency direction is `NODE -> prerequisite`. Node blocks are assembled from `docs/graph/W/packets/<slice>.nodes.md`; edit those, then re-run `inp_depgraph_assemble.py` (orchestrator-tools).

## Nodes

NODE: bpW:w0:mass
KIND: assumption
TITLE: Mass
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:mass@L24-L27
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0:mass
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: m fixed
SOURCE_CONCLUSION: m > 0 is fixed; all constants may depend on m unless stated otherwise; no uniformity as m -> 0 or m -> infinity is claimed
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c
LEAN_STATUS: ASSUMED
LEAN_REF: -
LEAN_NOTE: -
NOTE: STANDING_ASSUMPTIONS: the only standing assumption of track W (m > 0 fixed). In the frozen anchors it is the carrier hm : 0 < m of lam, reconU, reconV, cubicGrad, IsClassicalSolution, nlw2 (SPEC).

NODE: bpW:w0:nlw#IsClassicalSolution
KIND: definition
TITLE: Cubic Dirichlet wave equation: KAM.Wave.IsClassicalSolution
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:nlw@L29-L35
PROOF_SOURCE: -
CONTRACT_ID: wave.IsClassicalSolution
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: m in R with m > 0 (frozen carrier hm); u : R -> R -> R (frozen: on the whole time line I = R)
SOURCE_QUANTIFIERS: m, hm, u
SOURCE_CONCLUSION: defines: u is a classical solution of u_tt = u_xx - m u - u^3 on I x [0,pi] with u(t,0) = u(t,pi) = 0: u, u_t, u_x, u_tt, u_xx exist (x-derivatives one-sided at the endpoints, i.e. within [0,pi]) and are continuous on I x [0,pi], and the equation and boundary conditions hold (KAM.Wave.IsClassicalSolution m hm u, I = R, derivatives as witnesses ut, ux, utt, uxx)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Wave/Defs/IsClassicalSolution.lean
FROZEN_DECL: KAM.Wave.IsClassicalSolution
FROZEN_ANCHOR_ID: wave.IsClassicalSolution.v1
FROZEN_ABI_SHA256: c112724c82953ce66a9ba83f63f985c0793ca440135cd273a98078a9f1fc51b9
DEPS: bpW:w0:mass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:mass | blueprint-W/parts/w0-conventions.tex#bpW:w0:nlw@L33-L33 | the mass m of the equation is the fixed m > 0 (carrier hm)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:basis#lam
KIND: definition
TITLE: Dirichlet basis and linear frequencies: KAM.Wave.lam
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L39-L42
PROOF_SOURCE: -
CONTRACT_ID: wave.lam
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: m > 0 (carrier hm); j in N_+
SOURCE_QUANTIFIERS: m, hm, j
SOURCE_CONCLUSION: defines lambda_j = sqrt(j^2 + m) > 0 (KAM.Wave.lam m hm j); the definition also records -phi_j'' + m phi_j = lambda_j^2 phi_j
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Wave/Defs/Lam.lean
FROZEN_DECL: KAM.Wave.lam
FROZEN_ANCHOR_ID: wave.lam.v1
FROZEN_ABI_SHA256: c2dc54857edbf03f207980ed747cb4e478b4d85f0483e098f1ff44890df32263
DEPS: bpW:w0:mass, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:mass | blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L40-L40 | lambda_j = sqrt(j^2+m) > 0 uses the fixed m > 0
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L41-L41 | the recorded eigenfunction equation uses phi_j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:basis#sineMode
KIND: definition
TITLE: Dirichlet basis and linear frequencies: KAM.Wave.sineMode
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L39-L42
PROOF_SOURCE: -
CONTRACT_ID: wave.sineMode
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: j in N_+, x in R
SOURCE_QUANTIFIERS: j, x
SOURCE_CONCLUSION: defines phi_j(x) = sqrt(2/pi) sin(j x) (KAM.Wave.sineMode j x); the definition also records int_0^pi phi_i phi_j = delta_ij and phi_j(0) = phi_j(pi) = 0
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Wave/Defs/SineMode.lean
FROZEN_DECL: KAM.Wave.sineMode
FROZEN_ANCHOR_ID: wave.sineMode.v1
FROZEN_ABI_SHA256: 9999834f0d6cf8a9dd64263840d0c7e18929af6de976bba57cf67619d16412f5
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:ellap#ellWeight
KIND: definition
TITLE: Weighted sequence spaces: KAM.Wave.ellWeight
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L51-L57
PROOF_SOURCE: -
CONTRACT_ID: wave.ellWeight
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a, p in R; j in N_+
SOURCE_QUANTIFIERS: a, p, j
SOURCE_CONCLUSION: defines the weight j^p e^{a j} of the norm ¦¦w¦¦_{a,p}^2 = sum_{j>=1} ¦w_j¦^2 j^{2p} e^{2aj} of l^{a,p} (KAM.Wave.ellWeight a p j = j^p exp(a j))
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Wave/Defs/EllWeight.lean
FROZEN_DECL: KAM.Wave.ellWeight
FROZEN_ANCHOR_ID: wave.ellWeight.v1
FROZEN_ABI_SHA256: 590e6d1efbbbe2957abb244fe99539598f35982ec67bf9e3b33f322bf8391b64
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:ellap#WaveSpace
KIND: definition
TITLE: Weighted sequence spaces: KAM.Wave.WaveSpace
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L51-L57
PROOF_SOURCE: -
CONTRACT_ID: wave.WaveSpace
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (the headline weights a = p = 1, Convention bpW:w0:weights)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines the phase space E_{1,1} = l^{1,1} x l^{1,1} with ¦¦(q,p)¦¦_E = max(¦¦q¦¦_{1,1}, ¦¦p¦¦_{1,1}); frozen in weighted coordinates as KAM.Wave.WaveSpace = l^2(N_+;R) x l^2(N_+;R) with the product (max) norm, a point (y, y') standing for q = coeff y, p = coeff y'
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Wave/Defs/WaveSpace.lean
FROZEN_DECL: KAM.Wave.WaveSpace
FROZEN_ANCHOR_ID: wave.WaveSpace.v1
FROZEN_ABI_SHA256: bdfca9327ef9225b058b7139a28cf63e78ee8ff99fca5ffa6a0be04af472bb09
DEPS: bpW:w0:ellap#ellWeight, bpW:w0:ellap#spaces, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L53-L53 | the norm of l^{a,p} is weighted by j^p e^{aj}, at a = p = 1 the weight of the weighted coordinates
EDGE: bpW:w0:ellap#spaces | blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L54-L55 | E_{1,1} specializes the general product space and its max norm
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L53-L55 | frozen weighted-coordinate dictionary reads q and momentum through coeff (WaveSpace docstring)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:ellap#coeff
KIND: definition
TITLE: Weighted sequence spaces: KAM.Wave.coeff
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L51-L57
PROOF_SOURCE: -
CONTRACT_ID: wave.coeff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: y in l^2(N_+;R); j in N_+
SOURCE_QUANTIFIERS: y, j
SOURCE_CONCLUSION: defines the coefficient q_j = y_j / (j e^j) of the point of l^{1,1} represented by y (KAM.Wave.coeff y j = y j / ellWeight 1 1 j)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Wave/Defs/Coeff.lean
FROZEN_DECL: KAM.Wave.coeff
FROZEN_ANCHOR_ID: wave.coeff.v1
FROZEN_ABI_SHA256: 8a44d865337bca1cc70cfffe2d67bc4af13f70bc64861843a785bcf8d4b4747d
DEPS: bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L53-L53 | the coefficient divides by the weight j^p e^{aj} at a = p = 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:twosided
KIND: definition
TITLE: Two-sided spaces
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:twosided@L66-L71
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0:twosided
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a >= 0, s in R
SOURCE_QUANTIFIERS: a, s
SOURCE_CONCLUSION: defines l^{a,s}_b, complex sequences (c_l)_{l in Z} with ¦¦c¦¦_{a,s}^2 = sum_l <l>^{2s} e^{2a¦l¦} ¦c_l¦^2 < infinity, <l> = max(1,¦l¦), and the convolution (c*d)_l = sum_i c_i d_{l-i}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:reconstruction#reconU
KIND: definition
TITLE: Reconstruction: KAM.Wave.reconU
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L75-L81
PROOF_SOURCE: -
CONTRACT_ID: wave.reconU
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: m > 0 (carrier hm); (q,p) in E_{a,p} with a > 0 (frozen: a = 1, q = coeff y for y in l^2(N_+;R)); x in R
SOURCE_QUANTIFIERS: m, hm, y, x
SOURCE_CONCLUSION: defines U_m(q)(x) = sum_{j>=1} q_j / sqrt(lambda_j) phi_j(x) (KAM.Wave.reconU m hm y x, a tsum over j in N_+ with q = coeff y); intended dictionary u = U_m(q)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Wave/Defs/ReconU.lean
FROZEN_DECL: KAM.Wave.reconU
FROZEN_ANCHOR_ID: wave.reconU.v1
FROZEN_ABI_SHA256: afecc78929f2434f1c43fd73388bfed906c707c14f209552209f0da3ace2e155
DEPS: bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L77-L77 | the weight 1/sqrt(lambda_j)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L77-L77 | the modes phi_j
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L76-L76 | q is the coefficient sequence of a point of E (frozen: q = coeff y)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:reconstruction#reconV
KIND: definition
TITLE: Reconstruction: KAM.Wave.reconV
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L75-L81
PROOF_SOURCE: -
CONTRACT_ID: wave.reconV
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: m > 0 (carrier hm); (q,p) in E_{a,p} with a > 0 (frozen: a = 1, p = coeff y for y in l^2(N_+;R)); x in R
SOURCE_QUANTIFIERS: m, hm, y, x
SOURCE_CONCLUSION: defines V_m(p)(x) = sum_{j>=1} sqrt(lambda_j) p_j phi_j(x) (KAM.Wave.reconV m hm y x with p = coeff y); intended dictionary u_t = V_m(p)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Wave/Defs/ReconV.lean
FROZEN_DECL: KAM.Wave.reconV
FROZEN_ANCHOR_ID: wave.reconV.v1
FROZEN_ABI_SHA256: 5b3a45c2e7dd82cb415595bda752e0518964fda80deb44200323523b5a0a35a6
DEPS: bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L77-L77 | the weight sqrt(lambda_j)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L77-L77 | the modes phi_j
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L76-L76 | p is the coefficient sequence of a point of E (frozen: p = coeff y)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:H
KIND: definition
TITLE: Hamiltonian
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:H@L87-L92
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0:H
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: (q,p) in E_{1,1}
SOURCE_QUANTIFIERS: (q,p)
SOURCE_CONCLUSION: defines H_m(q,p) = Lambda(q,p) + G(q), Lambda(q,p) = (1/2) sum_j lambda_j (q_j^2 + p_j^2), G(q) = (1/4) int_0^pi U_m(q)(x)^4 dx; and states that Lambda is finite on E_{a,p} for p >= 1/2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lam, bpW:w0:reconstruction#reconU, bpW:w0:ellap#WaveSpace, bpW:w0:ellap#spaces
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:H@L89-L89 | Lambda is weighted by lambda_j
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-conventions.tex#bpW:w0:H@L90-L90 | G integrates U_m(q)^4
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w0-conventions.tex#bpW:w0:H@L88-L88 | H is defined on E_{1,1}
EDGE: bpW:w0:ellap#spaces | blueprint-W/parts/w0-conventions.tex#bpW:w0:H@L91-L91 | finiteness is stated on the general coefficient space E_{a,p}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:Gq#cubicGrad
KIND: definition
TITLE: Cubic gradient: KAM.Wave.cubicGrad
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L96-L101
PROOF_SOURCE: -
CONTRACT_ID: wave.cubicGrad
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: m > 0 (carrier hm); q in l^{1,1} (frozen: q = coeff y, y in l^2(N_+;R)); l in N_+
SOURCE_QUANTIFIERS: m, hm, y, l
SOURCE_CONCLUSION: defines G_q(q)_l = (1/sqrt(lambda_l)) int_0^pi U_m(q)(x)^3 phi_l(x) dx (KAM.Wave.cubicGrad m hm y l); the remarks that G_q(q)_l = dG/dq_l and G_q(q) in l^{1,2} are forward pointers to Lemma bpW:w0n:gradient and Theorem bpW:w0n:cubic-bound, not part of the definition
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Wave/Defs/CubicGrad.lean
FROZEN_DECL: KAM.Wave.cubicGrad
FROZEN_ANCHOR_ID: wave.cubicGrad.v1
FROZEN_ABI_SHA256: b43284c7493204aa6da9c006fdc338b3d48c53e243ae7cdbb6383dd7d4028600
DEPS: bpW:w0:reconstruction#reconU, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L98-L98 | the integrand U_m(q)^3
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L98-L98 | the factor 1/sqrt(lambda_l)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L98-L98 | the test mode phi_l
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L97-L98 | q in ell^{1,1} is read as coeff y in the frozen carrier dictionary
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The \ref{bpW:w0n:gradient} and \ref{bpW:w0n:cubic-bound} of L99-L100 are forward pointers (they would close the cycle cubicGrad -> gradient -> cubicGrad); not edges.

NODE: bpW:w0:eqmotion
KIND: definition
TITLE: Symplectic form and equations of motion
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L103-L112
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0:eqmotion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: (q,p) in E_{1,1}
SOURCE_QUANTIFIERS: (q,p), j >= 1
SOURCE_CONCLUSION: defines the symplectic form sum_j dq_j ^ dp_j and the Hamiltonian equations, i.e. the coefficient system (bpW:w0:coeffsys) dq_j/dt = lambda_j p_j, dp_j/dt = -lambda_j q_j - G_q(q)_j (j >= 1), read in l^{1,0} for (q,p) in E_{1,1} or coordinatewise; records that q -> (lambda_j q_j) is bounded l^{a,p+1} -> l^{a,p} (norm <= sqrt(1+m)) but not l^{a,p} -> l^{a,p}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:H, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:mass, bpW:w0:ellap#WaveSpace, bpW:w0:ellap#spaces
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:H | blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L104-L104 | the equations are Hamilton's equations of H
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L107-L107 | the linear part lambda_j
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L107-L107 | the nonlinear part G_q(q)_j
EDGE: bpW:w0:mass | blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L109-L109 | the operator norm bound explicitly uses the fixed positive mass through sqrt(1+m)
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L110-L110 | the equation is read for points of E_{1,1}
EDGE: bpW:w0:ellap#spaces | blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L109-L110 | linear multiplier maps ell^{a,p+1} to ell^{a,p}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The \ref{bpW:w0n:cubic-bound} of L111 (smoothing of order one) is a forward pointer, not an edge.

NODE: bpW:w0:z
KIND: definition
TITLE: Complex coordinates
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:z@L118-L123
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0:z
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: (q,p), j >= 1
SOURCE_CONCLUSION: defines z_j = (q_j + i p_j)/sqrt 2, zbar_j = (q_j - i p_j)/sqrt 2, so q_j = sqrt2 Re z_j, p_j = sqrt2 Im z_j, ¦z_j¦^2 = (q_j^2+p_j^2)/2, sum dq ^ dp = i sum dz ^ dzbar, Lambda = sum lambda_j ¦z_j¦^2; under the linear flow dz_j/dt = -i lambda_j z_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:H, bpW:w0:eqmotion, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:H | blueprint-W/parts/w0-conventions.tex#bpW:w0:z@L121-L121 | Lambda = sum lambda_j ¦z_j¦^2 rewrites the quadratic part of H
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w0-conventions.tex#bpW:w0:z@L122-L122 | the linear flow dq_j = lambda_j p_j, dp_j = -lambda_j q_j and the form sum dq ^ dp
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:z@L121-L122 | Lambda and the complex linear flow directly use lambda_j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:actions
KIND: definition
TITLE: Actions and radian angles
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:actions@L127-L134
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0:actions
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: (q,p) in E_{a,p}; on {I_j > 0} for the angle
SOURCE_QUANTIFIERS: (q,p), j >= 1
SOURCE_CONCLUSION: defines I_j = (q_j^2+p_j^2)/2 = ¦z_j¦^2 and, on {I_j > 0}, the radian angle phi_j by q_j = sqrt(2I_j) cos phi_j, p_j = -sqrt(2I_j) sin phi_j, z_j = sqrt(I_j) e^{-i phi_j}; dq_j ^ dp_j = dphi_j ^ dI_j, Lambda = sum lambda_j I_j, linear flow dphi_j/dt = lambda_j, dI_j/dt = 0; I = (I_1,I_2) tangential (J = {1,2}), Z_j = I_j normal (j >= 3)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:z, bpW:w0:eqmotion, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:z | blueprint-W/parts/w0-conventions.tex#bpW:w0:actions@L128-L128 | I_j = ¦z_j¦^2 and z_j = sqrt(I_j) e^{-i phi_j}
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w0-conventions.tex#bpW:w0:actions@L132-L132 | the linear flow in action-angle form
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:actions@L131-L132 | Lambda = sum lambda_j I_j and angular velocity lambda_j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:periodone#linearTorus
KIND: definition
TITLE: Period-one torus angles and frequencies: KAM.Wave.linearTorus
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:periodone@L136-L144
PROOF_SOURCE: -
CONTRACT_ID: wave.linearTorus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: I in (0,infinity)^2 (frozen carrier hI : forall i, 0 < I i); theta in R^2
SOURCE_QUANTIFIERS: I, hI, theta
SOURCE_CONCLUSION: convention: torus angles have period one, phi_j = 2 pi theta_j, campaign frequency nu = omega/(2 pi), (theta, Y = 2 pi I) canonical, small divisors 2 pi k.nu + l.Omega; defines the linear torus K^0_I(theta) = (Q^0,P^0) with Q^0_j = sqrt(2I_j) cos(2 pi theta_j), P^0_j = -sqrt(2I_j) sin(2 pi theta_j) for j = 1,2 and Q^0_j = P^0_j = 0 for j >= 3 (KAM.Wave.linearTorus I hI theta, stored in weighted coordinates ellWeight 1 1 j * Q^0_j; tangential i : Fin 2 is mode j = i+1); records invariance under the linear flow with nu = (lambda_1, lambda_2)/(2 pi)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Wave/Defs/LinearTorus.lean
FROZEN_DECL: KAM.Wave.linearTorus
FROZEN_ANCHOR_ID: wave.linearTorus.v1
FROZEN_ABI_SHA256: 3826f3c033910de266a3363c9baadc5ea96c76e6d2b8678a2407cda0b1235bd6
DEPS: bpW:w0:actions, bpW:w0:ellap#WaveSpace, bpW:w0:ellap#ellWeight, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:actions | blueprint-W/parts/w0-conventions.tex#bpW:w0:periodone@L141-L141 | the formula is the action-angle map with phi_j = 2 pi theta_j
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w0-conventions.tex#bpW:w0:periodone@L141-L141 | K^0_I takes values in E (frozen: WaveSpace, weighted coordinates)
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w0-conventions.tex#bpW:w0:periodone@L141-L141 | frozen weighted coordinates ellWeight 1 1 j * Q^0_j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:periodone@L143-L143 | linear invariance frequency is (lambda_1,lambda_2)/(2 pi)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:basis#lambda-facts
KIND: claim
TITLE: Elementary facts about lambda_j
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L45-L47
PROOF_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L45-L47
CONTRACT_ID: bpW:w0:basis#lambda-facts
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; lambda_j = sqrt(j^2+m)
SOURCE_QUANTIFIERS: j >= 1; s in R
SOURCE_CONCLUSION: j < lambda_j < j + sqrt m; j/lambda_j < 1; j -> lambda_j strictly increasing; f(s) = sqrt(s^2+m) strictly convex on R with 0 < f'(s) = s/f(s) < 1 for s > 0 and f' strictly increasing; lambda_{j+1} - lambda_j = (2j+1)/(lambda_{j+1}+lambda_j) < 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lam, bpW:w0:mass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L45-L45 | facts about lambda_j = sqrt(j^2+m)
EDGE: bpW:w0:mass | blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L46-L46 | strict convexity and j < lambda_j use m > 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0c
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose (L45-L47) stating facts that later proofs consume (SPEC section-data rule); justification is elementary and inline.

NODE: bpW:w0:ellap#spaces
KIND: definition
TITLE: General weighted coefficient spaces and their product norm
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L51-L57
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0:ellap#spaces
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a >= 0, p in R; scalar field R or C
SOURCE_QUANTIFIERS: a >= 0, p in R
SOURCE_CONCLUSION: defines ell^{a,p} as real sequences w with sum_{j>=1} |w_j|^2 j^{2p} exp(2aj) < infinity, its complex analogue, and E_{a,p} = ell^{a,p} x ell^{a,p} with max product norm; the exponent p and momentum p are distinguished by context
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L53-L53 | norm uses the square of ellWeight a p j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: new+sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0:reconstruction#rescaling
KIND: definition
TITLE: Inverse coefficient dictionary and symplectic rescaling
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L78-L80
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0:reconstruction#rescaling
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0 through lambda; coefficient data (q,p) in E_{a,p}, a > 0; u = U_m(q), u_t = V_m(p), u = sum x_j phi_j, u_t = sum y_j phi_j
SOURCE_QUANTIFIERS: j >= 1
SOURCE_CONCLUSION: records the equivalent coefficient dictionary q_j = sqrt(lambda_j) x_j, p_j = y_j/sqrt(lambda_j), and the coordinatewise symplectic identity dq_j wedge dp_j = dx_j wedge dy_j; x_j,y_j here are sine coefficients, not the frozen weighted coordinates
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L78-L79 | u = U_m(q) gives the displacement coefficient rescaling
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L78-L79 | u_t = V_m(p) gives the momentum coefficient rescaling
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L79-L80 | reciprocal sqrt(lambda_j) factors give the symplectic rescaling
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: new+sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:recon-bounded
KIND: lemma
TITLE: Reconstruction is bounded into $C^k$
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L18-L27
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L29-L35
CONTRACT_ID: bpW:w0n:recon-bounded
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a > 0, p in R, k in N; c in l^{a,p}_C (also the standing m > 0 for the U_m, V_m clause)
SOURCE_QUANTIFIERS: for all a > 0, p, k; for all c
SOURCE_CONCLUSION: sum_j ¦c_j¦ j^k <= M_{a,p,k} ¦¦c¦¦_{a,p} with M_{a,p,k}^2 = sum_j j^{2k-2p} e^{-2aj} < infinity; the series sum c_j phi_j and its termwise x-derivatives of order <= k converge absolutely and uniformly on [0,pi]; c -> sum c_j phi_j is bounded linear l^{a,p} -> C^k([0,pi]) with norm <= sqrt(2/pi) M_{a,p,k}, vanishes at x = 0, pi, and int_0^pi (sum c_j phi_j) phi_l = c_l; U_m, V_m and q -> U_m(lambda q) are bounded linear l^{a,p} -> C^k([0,pi]) for every p, since lambda_j^{+-1/2} <= (1+m)^{1/4} j^{1/2} and multiplication by lambda^r maps l^{a,p} into l^{a,p-¦r¦} (0 <= r <= 2) with norm <= (1+m)^{r/2}
CONSTANT_SCOPE: M_{a,p,k} depends only on a, p, k; the multiplier norms on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:ellap#ellWeight, bpW:w0:basis#sineMode, bpW:w1:ext-unifderiv, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:basis#lam, bpW:w0:mass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L30-L30 | the norm ¦¦c¦¦_{a,p} with weight j^p e^{aj} in Cauchy-Schwarz
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L31-L31 | ¦d_x^r phi_j¦ <= sqrt(2/pi) j^r; phi_j(0) = phi_j(pi) = 0; orthonormality
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L32-L32 | Weierstrass M-test and termwise differentiation of uniformly convergent derivative series
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L24-L24 | U_m is a series of this form with c_j = q_j/sqrt(lambda_j)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L24-L24 | V_m is a series of this form with c_j = sqrt(lambda_j) p_j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L25-L25 | the multiplier lambda^r and the bound lambda_j^{+-1/2} <= (1+m)^{1/4} j^{1/2}
EDGE: bpW:w0:mass | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L34-L34 | j^2 + m <= (1+m) j^2 uses m >= 0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:quartic-coeff
KIND: lemma
TITLE: Closed form, (c)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L40-L51
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L53-L69
CONTRACT_ID: bpW:w0n:quartic-coeff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: i, j, k, l >= 1; g_ijkl = int_0^pi phi_i phi_j phi_k phi_l dx
SOURCE_QUANTIFIERS: for all i, j, k, l >= 1
SOURCE_CONCLUSION: g_ijkl = (1/(2pi)) ([i+l=j+k] + [i+k=j+l] + [i+j=k+l] - [i=j+k+l] - [j=i+k+l] - [k=i+j+l] - [l=i+j+k]); g is symmetric; g_ijkl = 0 unless +-i+-j+-k+-l = 0; g_iiii = 3/(2pi); g_iijj = 1/pi (i != j); equivalently (bpW:w0n:g-signed) g_ijkl = (1/(2pi)) sum_{eps in {+-1}^3} s(eps) [l = eps_1 i + eps_2 j + eps_3 k], s(eps) = (-1)^{1+#{t: eps_t = -1}}, so ¦g_ijkl¦ <= (1/(2pi)) sum_eps [l = eps_1 i + eps_2 j + eps_3 k]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#sineMode, stepW:w0n:prod, stepW:w0n:cos, stepW:w0n:signed
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L41-L41 | g is the integral of a product of four modes phi
EDGE: stepW:w0n:prod | blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L54-L54 | proof step
EDGE: stepW:w0n:cos | blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L57-L57 | proof step
EDGE: stepW:w0n:signed | blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L65-L65 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:prod
KIND: step
TITLE: Product to sum
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:prod@L54-L56
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:prod@L54-L56
CONTRACT_ID: stepW:w0n:prod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: i, j, k, l >= 1
SOURCE_QUANTIFIERS: for all x
SOURCE_CONCLUSION: phi_i phi_j phi_k phi_l = (1/pi^2)(cos(i-j)x - cos(i+j)x)(cos(k-l)x - cos(k+l)x)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#stepW:w0n:prod@L56-L56 | phi_j = sqrt(2/pi) sin(jx) and the product-to-sum formula
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:cos
KIND: step
TITLE: Cosine integrals
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:cos@L57-L64
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:cos@L57-L64
CONTRACT_ID: stepW:w0n:cos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: i,j,k,l >= 1; A,B in Z (auxiliary integration variables)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: int_0^pi cos Ax cos Bx dx = (pi/2)([A=B] + [A=-B]); hence the eight-bracket formula for g_ijkl, which reduces to the stated closed form, with g_iiii = 3/(2pi) and g_iijj = 1/pi (i != j)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:prod
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:prod | blueprint-W/parts/w0-normalization.tex#stepW:w0n:cos@L60-L60 | integrates the product-to-sum expansion termwise
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:signed
KIND: step
TITLE: Signed form
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:signed@L65-L68
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:signed@L65-L68
CONTRACT_ID: stepW:w0n:signed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: i,j,k,l >= 1
SOURCE_QUANTIFIERS: for all i, j, k, l >= 1
SOURCE_CONCLUSION: the seven bracket relations solved for l give the signed form (bpW:w0n:g-signed) (the eighth pattern l = -i-j-k is impossible for l >= 1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:cos
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:cos | blueprint-W/parts/w0-normalization.tex#stepW:w0n:signed@L66-L66 | rewrites the seven relations of the closed form
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:gradient
KIND: lemma
TITLE: $G$ and its gradient as absolutely convergent sums
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L76-L82
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L84-L92
CONTRACT_ID: bpW:w0n:gradient
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a > 0, p >= 0, q in l^{a,p}; hat q_j = q_j/sqrt(lambda_j)
SOURCE_QUANTIFIERS: for all a > 0, p >= 0, q
SOURCE_CONCLUSION: G(q) = (1/4) sum_{i,j,k,l} g_ijkl hat q_i hat q_j hat q_k hat q_l and G_q(q)_l = (1/sqrt(lambda_l)) sum_{i,j,k} g_ijkl hat q_i hat q_j hat q_k, both absolutely convergent; G is Gateaux differentiable along every coordinate with dG/dq_l = G_q(q)_l; int_0^pi U_m(q)^3 phi_l dx = sqrt(lambda_l) G_q(q)_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:recon-bounded, bpW:w0:reconstruction#reconU, bpW:w0:H, bpW:w0n:quartic-coeff, bpW:w1:ext-integral, bpW:w0:Gq#cubicGrad, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L85-L85 | k = 0: sum ¦hat q_j¦ < infinity and U_m(q) = sum hat q_j phi_j uniformly
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L85-L85 | U_m(q) = sum hat q_j phi_j
EDGE: bpW:w0:H | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L88-L88 | G(q) = (1/4) int U_m(q)^4
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L86-L86 | the coefficients g_ijkl of the termwise-integrated quadruple series
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L87-L87 | termwise integration (dominated convergence for series) and differentiation under the integral
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L90-L90 | identifies int U_m(q)^3 phi_l / sqrt(lambda_l) with G_q(q)_l
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L77-L77 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L86-L86 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:algebra
KIND: lemma
TITLE: Weighted convolution algebra
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L94-L98
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L100-L113
CONTRACT_ID: bpW:w0n:algebra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, s >= 1; c, d in l^{a,s}_b
SOURCE_QUANTIFIERS: for all a >= 0, s >= 1, c, d
SOURCE_CONCLUSION: ¦¦c*d¦¦_{a,s} <= K_s ¦¦c¦¦_{a,s} ¦¦d¦¦_{a,s} with K_s = 2^s (1+2 zeta(2s))^{1/2}; K_{3/2}^2 = 8(1+2 zeta(3)); each convolution sum converges absolutely
CONSTANT_SCOPE: K_s depends only on s
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:twosided, stepW:w0n:weight, stepW:w0n:young
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:twosided | blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L95-L95 | the two-sided spaces and the convolution
EDGE: stepW:w0n:weight | blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L102-L102 | proof step
EDGE: stepW:w0n:young | blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L107-L107 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:weight
KIND: step
TITLE: Weight inequality
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:weight@L102-L106
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:weight@L102-L106
CONTRACT_ID: stepW:w0n:weight
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, s >= 1; w_l = <l>^s e^{a¦l¦}
SOURCE_QUANTIFIERS: for all i, l in Z
SOURCE_CONCLUSION: e^{a¦l¦} <= e^{a¦i¦} e^{a¦l-i¦}, <l> <= <i> + <l-i>, and w_l <= 2^{s-1}(w_i w_{l-i}/<l-i>^s + w_i w_{l-i}/<i>^s)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:twosided
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:twosided | blueprint-W/parts/w0-normalization.tex#stepW:w0n:weight@L103-L103 | the weight <l> = max(1,¦l¦) of l^{a,s}_b
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:young
KIND: step
TITLE: Young and Cauchy--Schwarz
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L107-L112
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L107-L112
CONTRACT_ID: stepW:w0n:young
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, s >= 1; c,d in l_b^{a,s}; w_l = <l>^s exp(a abs(l)); C_l = w_l abs(c_l), D_l = w_l abs(d_l); C'_l=C_l/<l>^s, D'_l=D_l/<l>^s
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: w_l ¦(c*d)_l¦ <= 2^{s-1}((C*D')_l + (C'*D)_l); with Young ¦¦X*Y¦¦_2 <= ¦¦X¦¦_2 ¦¦Y¦¦_1 and ¦¦D'¦¦_1 <= ¦¦D¦¦_2 (1+2 zeta(2s))^{1/2} this gives the bound with K_s and the absolute convergence
CONSTANT_SCOPE: K_s depends only on s
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:weight, bpW:w1:young
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:weight | blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L108-L108 | inserts the weight inequality
EDGE: bpW:w1:young | blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L109-L109 | Young's inequality (i) and the l^1 control with 1+2 zeta(2s) (ii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:cubic-bound
KIND: theorem
TITLE: Cubic gradient, (b)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L118-L129
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L131-L155
CONTRACT_ID: bpW:w0n:cubic-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; T(q,q',q'')_l = (1/sqrt(lambda_l)) sum_{i,j,k} g_ijkl hat q_i hat q'_j hat q''_k on (l^{a,p}_C)^3, hat q_j = q_j/sqrt(lambda_j)
SOURCE_QUANTIFIERS: for all a >= 0, p >= 1/2; for all q, q', q''
SOURCE_CONCLUSION: the sums converge absolutely; T is a bounded symmetric trilinear map into l^{a,p+1}_C, real on real arguments, with ¦¦T(q,q',q'')¦¦_{a,p+1} <= C_* ¦¦q¦¦ ¦¦q'¦¦ ¦¦q''¦¦, C_* = K_{p+1/2}^2/pi; for a > 0, G_q(q) = T(q,q,q); for a = p = 1, G_q : l^{1,1} -> l^{1,2} is real analytic (a continuous cubic polynomial) with ¦¦G_q(q)¦¦_{1,2} <= C_m ¦¦q¦¦_{1,1}^3, C_m = 8(1+2 zeta(3))/pi (about 8.67)
CONSTANT_SCOPE: C_* depends only on p; C_m is independent of m > 0 (only lambda_j >= j is used)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient, bpW:w0n:algebra, bpW:w0n:quartic-coeff, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, stepW:w0n:majorant, stepW:w0n:selection, stepW:w0n:smoothing, stepW:w0n:analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L120-L120 | the coefficients g_ijkl of T
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L120-L120 | the weights 1/sqrt(lambda)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L125-L125 | the identification G_q(q) = T(q,q,q)
EDGE: stepW:w0n:majorant | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L132-L132 | proof step
EDGE: stepW:w0n:selection | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L136-L136 | proof step
EDGE: stepW:w0n:smoothing | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L142-L142 | proof step
EDGE: stepW:w0n:analytic | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L149-L149 | proof step
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L125-L125 | explicit citation identifying G_q with the diagonal T
EDGE: bpW:w0n:algebra | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L124-L124 | K_{p+1/2} is the algebra constant, with p >= 1/2 ensuring s >= 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:majorant
KIND: step
TITLE: Even majorants
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L132-L135
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L132-L135
CONTRACT_ID: stepW:w0n:majorant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; q,q',q'' in l_C^{a,p}; define x_i=abs(q_abs(i))/sqrt(lambda_abs(i)) for i != 0 and x_0=0, and similarly x',x''
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: x is even and ¦¦x¦¦_{a,p+1/2}^2 = 2 sum_i (i/lambda_i) i^{2p} e^{2ai} ¦q_i¦^2 <= 2 ¦¦q¦¦_{a,p}^2 (the corrected constant sqrt 2, errata N-1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:twosided, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:twosided | blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L135-L135 | the two-sided norm of the majorant
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L134-L134 | lambda_i >= i (i/lambda_i < 1)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L133-L133 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:selection
KIND: step
TITLE: Selection rule bound
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L136-L141
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L136-L141
CONTRACT_ID: stepW:w0n:selection
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; q,q',q'' in l_C^{a,p}; l >= 1; hat q and even majorants are the explicit sequences defined at L120-L121 and L133-L134
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: sum_{i,j,k} ¦g_ijkl¦ ¦hat q_i hat q'_j hat q''_k¦ <= (1/(2pi)) (x*x'*x'')_l, so the sum defining T converges absolutely
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, stepW:w0n:majorant, bpW:w0n:algebra
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L137-L137 | the signed form (bpW:w0n:g-signed) and its bound
EDGE: stepW:w0n:majorant | blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L139-L139 | the even majorants x, x', x''
EDGE: bpW:w0n:algebra | blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L141-L141 | finiteness of the triple convolution: apply the algebra estimate twice, s=p+1/2 >= 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:smoothing
KIND: step
TITLE: Smoothing
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L142-L148
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L142-L148
CONTRACT_ID: stepW:w0n:smoothing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; q,q',q'' in l_C^{a,p}; s=p+1/2; X=x*x'*x'' with the explicit majorants of L133-L134
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: ¦¦T¦¦_{a,p+1}^2 <= (1/(8 pi^2)) ¦¦X¦¦_{a,p+1/2}^2 and ¦¦X¦¦ <= K_s^2 2^{3/2} prod ¦¦q¦¦, hence ¦¦T¦¦_{a,p+1} <= (K_s^2/pi) prod ¦¦q¦¦
CONSTANT_SCOPE: K_s depends only on s = p + 1/2
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:selection, bpW:w0:basis#lambda-facts, bpW:w0n:algebra, stepW:w0n:majorant, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:selection | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L143-L143 | the pointwise bound by X_l/(2pi)
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L143-L143 | l/lambda_l <= 1
EDGE: bpW:w0n:algebra | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L146-L146 | the algebra bound with s = p + 1/2 >= 1, applied twice
EDGE: stepW:w0n:majorant | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L147-L147 | ¦¦x¦¦ <= sqrt 2 ¦¦q¦¦
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L143-L143 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:analytic
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L149-L154
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L149-L154
CONTRACT_ID: stepW:w0n:analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; q in l_C^{a,p}; T is the series formula of L120-L121 (boundedness and symmetry are proved, not assumed)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: T is trilinear and symmetric; q -> T(q,q,q) is a continuous homogeneous cubic polynomial, analytic on the whole space, real on real sequences; for a > 0 it is G_q (Lemma bpW:w0n:gradient)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, bpW:w1:ext-analytic, bpW:w0n:gradient, bpW:w0:Gq#cubicGrad, stepW:w0n:smoothing
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L150-L150 | symmetry of g
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L152-L152 | a continuous multilinear map (its diagonal) is analytic
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L154-L154 | identification with G_q for a > 0
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L154-L154 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: stepW:w0n:smoothing | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L151-L151 | boundedness of the trilinear formula is supplied by the preceding smoothing estimate
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:pde-equiv
KIND: proposition
TITLE: Equivalence, (a)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L165-L183
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L185-L209
CONTRACT_ID: bpW:w0n:pde-equiv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I subset R open interval; q, p : I -> l^{1,1}; (i): q, p continuous into l^{1,1}, continuously differentiable into l^{1,0}, satisfying (bpW:w0:coeffsys) in l^{1,0}; (ii): u(t,x) = U_m(q(t))(x) is a classical solution of (bpW:w0:eq) on I and u_t(t,.) = V_m(p(t)) for every t
SOURCE_QUANTIFIERS: for every open I and q, p as stated; (force identity) for every q in l^{1,1}
SOURCE_CONCLUSION: (i) u = U_m(q(t)) is a classical solution of (bpW:w0:eq) on I with u_t = V_m(p(t)); (ii) every q_j, p_j is C^1 on I and (bpW:w0:coeffsys) holds coordinatewise; and (bpW:w0n:force): U_m(q)^3 = sum_l sqrt(lambda_l) G_q(q)_l phi_l uniformly on [0,pi] and -d_x^2 U_m(q) + m U_m(q) = U_m(lambda^2 q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:eqmotion, bpW:w0:nlw#IsClassicalSolution, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, stepW:w0n:force, stepW:w0n:time, stepW:w0n:ident, stepW:w0n:converse, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L169-L169 | the coefficient system (bpW:w0:coeffsys)
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L170-L170 | classical solution of (bpW:w0:eq)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L170-L170 | u = U_m(q(t))
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L171-L171 | u_t = V_m(p(t))
EDGE: stepW:w0n:force | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L186-L186 | proof step
EDGE: stepW:w0n:time | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L193-L193 | proof step
EDGE: stepW:w0n:ident | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L199-L199 | proof step
EDGE: stepW:w0n:converse | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L202-L202 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L178-L178 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L178-L178 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L178-L178 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:force
KIND: step
TITLE: Force identity
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L186-L192
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L186-L192
CONTRACT_ID: stepW:w0n:force
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q in l^{1,1}; f = U_m(q)^3 in C([0,pi])
SOURCE_QUANTIFIERS: for q
SOURCE_CONCLUSION: (bpW:w0n:force): U_m(q)^3 = sum_l sqrt(lambda_l) G_q(q)_l phi_l uniformly on [0,pi], and -d_x^2 U_m(q) + m U_m(q) = U_m(lambda^2 q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient, bpW:w0n:cubic-bound, bpW:w0n:recon-bounded, bpW:w1:sine-completeness, bpW:w0:basis#sineMode, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L187-L187 | int f phi_l = sqrt(lambda_l) G_q(q)_l
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L188-L188 | (sqrt(lambda_l) G_q(q)_l) lies in l^{1,1}
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L188-L188 | uniform convergence of S (k = 0) and termwise differentiation (k = 2)
EDGE: bpW:w1:sine-completeness | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L190-L190 | (phi_l) is a complete orthonormal system of L^2(0,pi)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L192-L192 | -phi_j'' + m phi_j = lambda_j^2 phi_j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L192-L192 | the eigenvalue lambda_j^2 = j^2 + m
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L187-L187 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L187-L187 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:time
KIND: step
TITLE: Time regularity
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L193-L198
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L193-L198
CONTRACT_ID: stepW:w0n:time
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the hypotheses of (i)
SOURCE_QUANTIFIERS: t in I
SOURCE_CONCLUSION: dot q is C^1 into l^{1,-1}, hence q is C^2 there, with ddot q = -lambda^2 q - lambda G_q(q); t -> u(t,.) is C^2 into C^2([0,pi]); u,u_t,u_tt,u_x,u_xx exist and are jointly continuous; u_t=U_m(lambda p)=V_m(p), u_tt=U_m(ddot q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:eqmotion, bpW:w0n:recon-bounded, bpW:w0:reconstruction#reconV, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L194-L194 | dot q = lambda p and dot p = -lambda q - G_q(q)
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L196-L196 | lambda bounded l^{1,0} -> l^{1,-1}; U_m : l^{1,-1} -> C^2([0,pi]) bounded linear
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L198-L198 | U_m(lambda p) = V_m(p)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L194-L194 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L196-L196 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L196-L196 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:ident
KIND: step
TITLE: Identification
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L199-L201
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L199-L201
CONTRACT_ID: stepW:w0n:ident
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I subset R open interval; q,p:I -> l^{1,1}, continuous there and C^1 into l^{1,0}, satisfying the coefficient system in l^{1,0}; u(t,x)=U_m(q(t))(x)
SOURCE_QUANTIFIERS: t in I
SOURCE_CONCLUSION: u_tt = u_xx - m u - u^3 and u(t,0) = u(t,pi) = 0, so u is a classical solution with u_t = V_m(p)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:force, stepW:w0n:time, bpW:w0n:recon-bounded, bpW:w0:nlw#IsClassicalSolution, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:force | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L200-L200 | U_m(lambda^2 q) = -u_xx + m u and U_m(lambda G_q(q)) = u^3
EDGE: stepW:w0n:time | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L200-L200 | u_tt = U_m(ddot q)
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L201-L201 | boundary values vanish
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L201-L201 | the definition of classical solution being verified
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L200-L200 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L200-L200 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L200-L200 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:converse
KIND: step
TITLE: Converse
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L202-L208
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L202-L208
CONTRACT_ID: stepW:w0n:converse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the hypotheses of (ii)
SOURCE_QUANTIFIERS: t in I, l >= 1
SOURCE_CONCLUSION: int u phi_l = q_l/sqrt(lambda_l), int u_t phi_l = sqrt(lambda_l) p_l; dot q_l = lambda_l p_l and sqrt(lambda_l) dot p_l = int u_tt phi_l = -lambda_l^2 q_l/sqrt(lambda_l) - sqrt(lambda_l) G_q(q)_l, i.e. (bpW:w0:coeffsys) coordinatewise with q_l, p_l in C^1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:nlw#IsClassicalSolution, bpW:w0n:recon-bounded, bpW:w1:ext-integral, bpW:w0:basis#sineMode, bpW:w0n:gradient, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L204-L204 | u_t, u_tt continuous; the equation and boundary values
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L203-L203 | the coefficient formula int (sum c_j phi_j) phi_l = c_l
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L204-L204 | differentiation under the integral sign
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L206-L206 | phi_l(0) = phi_l(pi) = 0 and phi_l'' = -l^2 phi_l (integration by parts)
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L207-L207 | int u^3 phi_l = sqrt(lambda_l) G_q(q)_l
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L203-L203 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L203-L203 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L203-L203 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L207-L207 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:nonres
KIND: lemma
TITLE: Qualitative nonresonance of all quartic terms
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L220-L224
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L226-L247
CONTRACT_ID: bpW:w0n:nonres
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; a, b, c, d >= 1 with g_abcd != 0; sigma in {+-1}^4 with sigma_1 lambda_a + sigma_2 lambda_b + sigma_3 lambda_c + sigma_4 lambda_d = 0
SOURCE_QUANTIFIERS: for all m > 0, a, b, c, d, sigma
SOURCE_CONCLUSION: the indices with sigma = +1 and those with sigma = -1 form equal multisets (two of each)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lam, bpW:w0n:quartic-coeff, stepW:w0n:31, stepW:w0n:22
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L222-L222 | the frequencies lambda
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L227-L227 | g_abcd != 0 implies a signed relation +-a+-b+-c+-d = 0
EDGE: stepW:w0n:31 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L229-L229 | proof step
EDGE: stepW:w0n:22 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L233-L233 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:31
KIND: step
TITLE: Four or three equal signs
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L229-L232
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L229-L232
CONTRACT_ID: stepW:w0n:31
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; a,b,c,d >= 1 with g_abcd != 0; sigma in {+1,-1}^4; sum sigma_r lambda_index(r)=0; consider the cases of four or three equal signs
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: all four signs equal is impossible; three equal signs are impossible since lambda_x + lambda_y > lambda_{x+y} and lambda_d <= lambda_{a+b+c} < lambda_a + lambda_b + lambda_c
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:mass, bpW:w0:basis#lam, bpW:w0n:quartic-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L231-L231 | lambda > 0 and j -> lambda_j increasing
EDGE: bpW:w0:mass | blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L232-L232 | squaring: 2 sqrt((x^2+m)(y^2+m)) > 2xy - m uses m > 0
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L231-L231 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L231-L231 | g_abcd != 0 supplies d <= a+b+c via the selection rule at L227-L228
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:22
KIND: step
TITLE: Two against two
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L233-L246
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L233-L246
CONTRACT_ID: stepW:w0n:22
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; a,b,c,d >= 1 with g_abcd != 0; lambda_a+lambda_b=lambda_c+lambda_d; {a,b} != {c,d} as multisets (contradiction case); f(s)=sqrt(s^2+m)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: case (1) a+b = c+d, case (2) a+c = b+d, case (3) a = b+c+d each lead to a contradiction; the cases are exhaustive
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, bpW:w0n:quartic-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L236-L236 | strict convexity of f, f' > 0 increasing
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L234-L234 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L235-L235 | the signed index relation used in the exhaustive cases comes from L227-L228
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:Qdef
KIND: definition
TITLE: Partial quartic normal form
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:Qdef@L270-L273
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0n:Qdef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: G^tan, G^nor and resonance as in bpW:w0n:birkhoff#data
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines bar G = the sum of the resonant monomials of G^tan (with coefficients) and the partial quartic normal form Lambda + bar G + G^nor
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:birkhoff#data, bpW:w0:H
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:birkhoff#data | blueprint-W/parts/w0-normalization.tex#bpW:w0n:Qdef@L271-L271 | resonant monomials of G^tan; G^nor
EDGE: bpW:w0:H | blueprint-W/parts/w0-normalization.tex#bpW:w0n:Qdef@L272-L272 | Lambda, the quadratic part of H
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:AB
KIND: theorem
TITLE: Action coefficients, (d)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L275-L286
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L288-L305
CONTRACT_ID: bpW:w0n:AB
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J = {1,2}; m > 0; I = (I_1,I_2), Z = (I_j)_{j>=3}, I_j = ¦z_j¦^2
SOURCE_QUANTIFIERS: for every m > 0
SOURCE_CONCLUSION: bar G = (1/2)<AI,I> + <BI,Z> with A_ii = 9/(8 pi lambda_i^2), A_12 = A_21 = 3/(2 pi lambda_1 lambda_2), B_ji = 3/(2 pi lambda_j lambda_i) (j >= 3, i in J); equivalently A = (3/(8pi)) D(4 11^T - Id)D, D = diag(1/lambda_1, 1/lambda_2), (BI)_j = (3/(2 pi lambda_j))(I_1/lambda_1 + I_2/lambda_2); and (bpW:w0n:avgG) <G> = (3/(16 pi))(4 (sum_j I_j/lambda_j)^2 - sum_j I_j^2/lambda_j^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:Qdef, bpW:w0:actions, bpW:w0:basis#lam, stepW:w0n:resavg, stepW:w0n:moments, stepW:w0n:sum
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:Qdef | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L277-L277 | bar G is the resonant tangential part
EDGE: bpW:w0:actions | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L276-L276 | I_j = ¦z_j¦^2, tangential I, normal Z
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L278-L278 | lambda in A and B
EDGE: stepW:w0n:resavg | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L289-L289 | proof step
EDGE: stepW:w0n:moments | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L295-L295 | proof step
EDGE: stepW:w0n:sum | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L299-L299 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:resavg
KIND: step
TITLE: Resonant equals averaged
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L289-L294
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L289-L294
CONTRACT_ID: stepW:w0n:resavg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the monomials of (bpW:w0n:Gz) with nonzero coefficient
SOURCE_QUANTIFIERS: monomials z^alpha zbar^beta
SOURCE_CONCLUSION: a monomial is resonant iff alpha = beta (it is I_a I_b); the angle average of z^alpha zbar^beta is delta_{alpha beta} I^alpha; hence bar G is the part of <G> (extended from finitely supported q by the absolutely convergent formula) with at least one tangential action
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:nonres, bpW:w0n:birkhoff#data, bpW:w0:actions, bpW:w0n:Qdef, bpW:w0n:gradient
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:nonres | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L290-L290 | resonance with nonzero coefficient forces alpha = beta
EDGE: bpW:w0n:birkhoff#data | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L290-L290 | the monomials of (bpW:w0n:Gz)
EDGE: bpW:w0:actions | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L291-L291 | z_j = sqrt(I_j) e^{-i phi_j}
EDGE: bpW:w0n:Qdef | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L292-L292 | bar G as the resonant tangential monomials
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L294-L294 | absolute convergence justifies extension of the finite-support average
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:moments
KIND: step
TITLE: Averages of monomials
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:moments@L295-L298
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:moments@L295-L298
CONTRACT_ID: stepW:w0n:moments
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q_j = sqrt(2 I_j) cos phi_j, independent angles
SOURCE_QUANTIFIERS: indices i, j, k, l
SOURCE_CONCLUSION: <q_i q_j q_k q_l> = 0 unless the indices pair up; <q_i^4> = (3/2) I_i^2; <q_i^2 q_j^2> = I_i I_j (i != j); (i,i,i,i) occurs once and {i,i,j,j} six times among ordered quadruples
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:actions
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:actions | blueprint-W/parts/w0-normalization.tex#stepW:w0n:moments@L296-L296 | q_j = sqrt(2 I_j) cos phi_j
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:sum
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L299-L304
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L299-L304
CONTRACT_ID: stepW:w0n:sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; oscillator actions I_j=abs(z_j)^2; y_j=I_j/lambda_j; first compute on finite support and extend as at L293-L294
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: <G> = (9/(16pi)) sum y_i^2 + (3/(2pi)) sum_{i<j} y_i y_j, which is (bpW:w0n:avgG); matching gives A and B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient, bpW:w0n:quartic-coeff, stepW:w0n:moments, stepW:w0n:resavg, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L300-L300 | G = (1/4) sum g_ijkl hat q^4 with hat q = q/sqrt(lambda)
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L300-L300 | g_iiii = 3/(2pi), g_iijj = 1/pi
EDGE: stepW:w0n:moments | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L301-L301 | the moments 3/2 I^2, I_i I_j and the multiplicities
EDGE: stepW:w0n:resavg | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L303-L303 | bar G = the part of <G> with a tangential action
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L300-L300 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:formal-birkhoff
KIND: proposition
TITLE: Formal partial Birkhoff transformation
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L307-L315
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L317-L323
CONTRACT_ID: bpW:w0n:formal-birkhoff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F the quartic polynomial with coefficient c_ab/(-i<alpha-beta,hat lambda>) on each nonresonant monomial z^alpha zbar^beta of G^tan (coefficient c_ab) and zero otherwise
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: F is real; X_Lambda F = G^tan - bar G (X_Lambda F = dF/dt along the linear flow); formally H o Phi^1_F = Lambda + bar G + G^nor + (terms of degree >= 6); the quartic part of the normal form is independent of the choice of F among solutions of X_Lambda F = G^tan - bar G
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:birkhoff#data, bpW:w0n:Qdef, bpW:w0n:nonres, bpW:w0:z, bpW:w0:H, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:birkhoff#data | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L308-L308 | monomials of G^tan, resonance, divisors <alpha-beta,hat lambda>
EDGE: bpW:w0n:Qdef | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L310-L310 | bar G and the normal form
EDGE: bpW:w0n:nonres | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L318-L318 | the divisors of nonresonant monomials are nonzero
EDGE: bpW:w0:z | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L318-L318 | X_Lambda (z^alpha zbar^beta) = -i<alpha-beta,hat lambda> z^alpha zbar^beta along dz = -i lambda z
EDGE: bpW:w0:H | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L321-L321 | H = Lambda + G in the Lie series
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L309-L309 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:nondeg
KIND: theorem
TITLE: Nondegeneracy, (e)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L346-L353
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L355-L377
CONTRACT_ID: bpW:w0n:nondeg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J = {1,2}; m > 0; A, B of Theorem bpW:w0n:AB; (A1)-(A3) as in bpW:w0n:nondeg-sec#data
SOURCE_QUANTIFIERS: for every m > 0
SOURCE_CONCLUSION: (i) det A = -63/(64 pi^2 lambda_1^2 lambda_2^2) = -63/(64 pi^2 (1+m)(4+m)) != 0; (ii) <l,lambda_N> != 0 for 1 <= ¦l¦ <= 2; (iii) (A3) holds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:nondeg-sec#data, bpW:w0n:AB, stepW:w0n:det, stepW:w0n:A2, stepW:w0n:A3red, stepW:w0n:l1, stepW:w0n:l2, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:nondeg-sec#data | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L351-L351 | the conditions (A2), (A3)
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L349-L349 | the matrix A
EDGE: stepW:w0n:det | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L356-L356 | proof step
EDGE: stepW:w0n:A2 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L360-L360 | proof step
EDGE: stepW:w0n:A3red | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L363-L363 | proof step
EDGE: stepW:w0n:l1 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L369-L369 | proof step
EDGE: stepW:w0n:l2 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L373-L373 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L349-L349 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:det
KIND: step
TITLE: Determinant
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L356-L359
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L356-L359
CONTRACT_ID: stepW:w0n:det
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A of Theorem bpW:w0n:AB
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: det A = (3/(8pi))^2 lambda_1^{-2} lambda_2^{-2} det((3,4),(4,3)) = -63/(64 pi^2) lambda_1^{-2} lambda_2^{-2}; also for general n >= 1, det(4 11^T - Id_n)=(-1)^{n-1}(4n-1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L357-L357 | A = (3/(8pi)) D(4 11^T - Id) D
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L357-L357 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:A2
KIND: step
TITLE: Pure normal
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L360-L362
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L360-L362
CONTRACT_ID: stepW:w0n:A2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: l in Z^N, 1 <= ¦l¦ <= 2
SOURCE_QUANTIFIERS: l
SOURCE_CONCLUSION: <l,lambda_N> is +-lambda_a, +-2 lambda_a, +-(lambda_a+lambda_b) or +-(lambda_a-lambda_b), a != b in N, all nonzero
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L362-L362 | lambda > 0 strictly increasing
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L361-L361 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:A3red
KIND: step
TITLE: Reduction of (A$_3$)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L363-L368
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L363-L368
CONTRACT_ID: stepW:w0n:A3red
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: b = (1/lambda_1, 1/lambda_2), s = sum_{j>=3} l_j/lambda_j
SOURCE_QUANTIFIERS: (k,l)
SOURCE_CONCLUSION: A = (3/(8pi))(4bb^T - D^2), B^T l = (3/(2pi)) s b; the linear part (3/(8pi))(4(<b,k>+s)b - D^2 k) vanishes iff k_i/lambda_i = c (i = 1,2) with c = 4(<b,k>+s), then <b,k> = 2c, s = -(7/4)c; the constant part is c(lambda_1^2+lambda_2^2) + <l,lambda_N>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w0n:nondeg-sec#data, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L365-L365 | A and B
EDGE: bpW:w0n:nondeg-sec#data | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L366-L366 | the affine map of (A3)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L364-L364 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:l1
KIND: step
TITLE: The case $\abs l=1$
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L369-L372
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L369-L372
CONTRACT_ID: stepW:w0n:l1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; k in Z^2, l in Z^N finitely supported with abs(l)=1; l=sigma e_nu, sigma in {+1,-1}, nu >= 3; consider vanishing of the affine map in (A3)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: the constant part vanishes iff 7 lambda_nu^2 = 4(lambda_1^2+lambda_2^2), and then k_i^2 in (0,4/7) is not the square of an integer; so (A3) holds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:A3red, bpW:w0:basis#lam, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:A3red | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L370-L370 | the vanishing conditions of the reduction
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L370-L370 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L372-L372 | strict positivity of lambda makes k_i^2 strictly between zero and 4/7
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w0n:l2
KIND: step
TITLE: The case $\abs l=2$
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L373-L376
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L373-L376
CONTRACT_ID: stepW:w0n:l2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; k in Z^2, l in Z^N finitely supported with abs(l)=2; consider vanishing of the linear part of the affine map in (A3)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: ¦s¦ <= 2/lambda_3 < 2/3, ¦c¦ < 8/21, k_2 - k_1 = c(lambda_2 - lambda_1) with 0 < lambda_2 - lambda_1 < 1 forces k_1 = k_2, c = 0, s = 0, impossible for ¦l¦ = 2; so the linear part does not vanish
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:A3red, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:A3red | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L374-L374 | the vanishing conditions of the reduction
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L375-L375 | lambda_3 > 3, 0 < lambda_2 - lambda_1 < 1, lambda injective
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L374-L374 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w0n:duffing
KIND: proposition
TITLE: One-mode frequency shift, (f)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L391-L400
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L402-L407
CONTRACT_ID: bpW:w0n:duffing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: restriction of (bpW:w0:eq) to u = x(t) phi_j(x), only mode j excited, forcing of other modes dropped
SOURCE_QUANTIFIERS: j >= 1; amplitude a
SOURCE_CONCLUSION: the projected one-mode equation is ddot x+lambda_j^2 x+eps x^3=0, eps=g_jjjj=3/(2pi); its frequency at small amplitude a is lambda_j+3 eps a^2/(8 lambda_j)+O(a^4)=lambda_j+9 a^2/(16pi lambda_j)+O(a^4); setting I_j=lambda_j a^2/2 to leading order gives lambda_j+9 I_j/(8pi lambda_j^2)+O(a^4), agreeing with the normal-form first-order shift A_jj I_j (for the tangential diagonal in AB); the printed coefficient would give a shift 16 times larger
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:nlw#IsClassicalSolution, bpW:w0n:quartic-coeff, bpW:w0n:ledger#ext-lindstedt, bpW:w0:actions, bpW:w0n:AB, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L392-L392 | restriction of the equation (bpW:w0:eq)
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L403-L403 | int (x phi_j)^3 phi_j = x^3 g_jjjj, g_jjjj = 3/(2pi)
EDGE: bpW:w0n:ledger#ext-lindstedt | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L403-L403 | the classical Lindstedt shift 3 eps a^2/(8 omega_0)
EDGE: bpW:w0:actions | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L406-L406 | I_j = (q_j^2+p_j^2)/2 = lambda_j a^2/2 to leading order
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L397-L397 | A_jj = 9/(8 pi lambda_j^2)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L394-L394 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L392-L392 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Consistency check (f) of W0; no later proof consumes it so far (decide at W8, SPEC Reachability).

NODE: bpW:w0n:birkhoff#data
KIND: definition
TITLE: Quartic part in complex coordinates; resonance; tangential/normal split
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:birkhoff@L258-L268
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0n:birkhoff#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J = {1,2}, N = {j >= 3}; complex coordinates z of Definition bpW:w0:z
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines (with the identity (bpW:w0n:Gz)) G = (1/16) sum g_ijkl (lambda_i lambda_j lambda_k lambda_l)^{-1/2} prod (z + zbar) as a sum of monomials z^alpha zbar^beta, ¦alpha¦+¦beta¦ = 4, evolving by e^{-i<alpha-beta,hat lambda>t} along the linear flow; resonant iff <alpha-beta,hat lambda> = 0; the split G = G^tan + G^nor, G^nor the monomials with all indices in N
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:z, bpW:w0n:gradient, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:z | blueprint-W/parts/w0-normalization.tex#bpW:w0n:birkhoff@L259-L259 | q_j = (z_j + zbar_j)/sqrt 2 and the linear flow dz_j = -i lambda_j z_j
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#bpW:w0n:birkhoff@L261-L261 | G = (1/4) sum g_ijkl q-hat^4 (quartic series)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:birkhoff@L261-L261 | the weights (lambda_i lambda_j lambda_k lambda_l)^{-1/2}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L258-L268 (with the display bpW:w0n:Gz) that fixes data consumed by Qdef, AB and formal-birkhoff (SPEC section-data rule).

NODE: bpW:w0n:nondeg-sec#data
KIND: definition
TITLE: Nondegeneracy conditions (A1)-(A3) of the Cantor Manifold Theorem
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg-sec@L341-L344
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0n:nondeg-sec#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A, B of Theorem bpW:w0n:AB
SOURCE_QUANTIFIERS: (k,l) in Z^2 x Z^N with 1 <= ¦l¦ <= 2
SOURCE_CONCLUSION: defines omega(I) = lambda_J + A I, Omega(I) = lambda_N + B I and the conditions (A1) det A != 0, (A2) <l,lambda_N> != 0, (A3) <k,omega(I)> + <l,Omega(I)> not identically 0 as an affine function of I, for all (k,l) with 1 <= ¦l¦ <= 2 (¦l¦ = sum ¦l_j¦)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg-sec@L341-L341 | omega(I) = lambda_J + A I and Omega(I) = lambda_N + B I
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg-sec@L341-L341 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w0n
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L341-L344 defining the conditions stated in Theorem bpW:w0n:nondeg (SPEC section-data rule).

NODE: bpW:w0n:ledger#ext-lindstedt
KIND: external
TITLE: Classical Lindstedt frequency shift (unlabelled W0 external)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:ledger@L422-L423
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0n:ledger#ext-lindstedt
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the Duffing equation ddot x + omega_0^2 x + eps x^3 = 0
SOURCE_QUANTIFIERS: amplitude a -> 0
SOURCE_CONCLUSION: its Lindstedt-Poincare frequency at amplitude a is omega_0 + 3 eps a^2/(8 omega_0) + O(a^4) ("the classical Lindstedt shift", W0 ledger "External standard facts")
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w0n
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled external of the W0 ledger (SPEC External inputs); used only by bpW:w0n:duffing.

NODE: bpW:w1:transport
KIND: definition
TITLE: Weights, transport and coefficient maps
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:transport@L30-L39
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a, p in R; K in {R, C}; a >= 0 for l^{a,p}_K
SOURCE_QUANTIFIERS: a, p, K
SOURCE_CONCLUSION: defines omega_{a,p}(j) = j^p e^{aj} > 0 (frozen ellWeight a p j), l^2_K = l^2(N_+;K), tau_{a,p} : l^{a,p}_K -> l^2_K, (tau w)_j = omega_{a,p}(j) w_j, kappa_{a,p} : l^2_K -> l^{a,p}_K, (kappa y)_j = y_j/omega_{a,p}(j); y represents w = kappa y (weighted coordinates); a map A : l^{a,p} -> l^{a',p'} is represented by hat A = tau_{a',p'} o A o kappa_{a,p}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:ellap#ellWeight, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w1-sequences.tex#bpW:w1:transport@L31-L31 | omega_{a,p}(j) is the frozen ellWeight a p j
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:transport@L33-L33 | the spaces l^{a,p}_K of Definition bpW:w0:ellap; kappa_{1,1} is the frozen coeff (realization table L51)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-lp
KIND: external
TITLE: $\ell^2$ spaces
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-lp@L72-L77
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-lp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: l^2(iota;K) is a Hilbert space for every index type (lp.instInnerProductSpace, lp.completeSpace) with <f,g> = sum conj(f_i) g_i; ¦f_i¦ <= ¦¦f¦¦; membership and norm bounds follow from bounds on finite partial sums; f = sum_i f_i e_i, e_i = lp.single 2 i 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-series
KIND: external
TITLE: Series
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-series@L78-L80
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-series
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: sum_{k>=1} k^{-2} = pi^2/6; sum_{k>=1} k^{-sigma} < infinity for sigma > 1; Tonelli for nonnegative double series and Fubini for absolutely summable ones
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-analytic
KIND: external
TITLE: Analytic maps
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-analytic@L81-L88
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: a continuous multilinear map is analytic (a continuous polynomial) everywhere; continuous linear and bilinear maps are analytic; compositions and pairs of analytic maps are analytic; a continuous bilinear map applied to two analytic maps is analytic; C-analytic maps are R-analytic; analytic maps are Frechet differentiable
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-onevar
KIND: external
TITLE: One complex variable, Banach values
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-onevar@L89-L98
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-onevar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: for a complete complex normed space F: the Cauchy estimate (phi continuous on the closed disc of radius R > 0, holomorphic inside, ¦¦phi¦¦ <= B on the circle implies ¦¦phi'(c)¦¦ <= B/R); the Cauchy integral formula (valid for complete F; K's bp:p1:ext-cauchy, provenance), in particular the formula for phi'(c); continuous linear maps commute with Bochner integrals; the norm is attained by norm-one functionals; holomorphic maps on open subsets of C are analytic; a locally uniform limit of holomorphic maps on an open subset of C is holomorphic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-unifderiv
KIND: external
TITLE: Uniform limits and derivatives
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-unifderiv@L99-L102
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-unifderiv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: if f_k -> f pointwise on an open set U of a normed space over K, each f_k is differentiable on U and Df_k -> g uniformly on U, then f is differentiable on U with Df = g; the mean value inequality on convex sets (K's bp:p1:ext-mvt, provenance)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-integral
KIND: external
TITLE: Integrals
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-integral@L103-L108
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-integral
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: Bochner integrals of continuous maps of a compact interval or box into a complete space; ¦¦int F¦¦ <= int ¦¦F¦¦; differentiation under the integral sign with a dominating bound on the derivative (a.e.-strongly measurable integrand and derivative, measurability from continuity); dominated convergence (K's bp:p1:ext-integral, provenance)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-ode
KIND: external
TITLE: ODE
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-ode@L109-L111
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-ode
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: Picard-Lindelof existence and uniqueness for Lipschitz fields in a Banach space; Gronwall's inequality
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:ext-fourier
KIND: external
TITLE: Fourier analysis
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:ext-fourier@L112-L116
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:ext-fourier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: the characters e^{inx}, n in Z, form a Hilbert basis of L^2 of R/2piZ with normalized Haar measure, and e^{2 pi i k.x}, k in Z^n, one of L^2(R^n/Z^n); Parseval; continuous periodic functions with absolutely summable coefficients are the sums of their Fourier series (K's bp:p1:ext-fourier, provenance)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:space
KIND: lemma
TITLE: The weighted spaces
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L122-L136
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L138-L154
CONTRACT_ID: bpW:w1:space
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p in R, K in {R, C}
SOURCE_QUANTIFIERS: for all a >= 0, p
SOURCE_CONCLUSION: (i) tau_{a,p}, kappa_{a,p} are mutually inverse K-linear bijections, ¦¦tau w¦¦_{l^2} = ¦¦w¦¦_{a,p}; l^{a,p}_K with <w,w'>_{a,p} = sum omega^2 conj(w_j) w'_j is a Hilbert space isometric to l^2_K, complete and separable; (ii) ¦(kappa y)_j¦ <= ¦¦y¦¦/omega_{a,p}(j) and y -> (kappa y)_j is the continuous linear functional omega^{-1} ev_j; (iii) ¦¦y - P_N y¦¦ -> 0 for the truncations P_N; (iv) for K = R, a = p = 1, kappa_{1,1} is the frozen coeff, and WaveSpace = l^2_R x l^2_R with its product (max) norm is isometric to E_{1,1} with ¦¦(q,p)¦¦_E = max(¦¦q¦¦_{1,1}, ¦¦p¦¦_{1,1}) via kappa_{1,1} x kappa_{1,1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, stepW:w1:iso, stepW:w1:sep, stepW:w1:coord, stepW:w1:frozen, bpW:w0:ellap#coeff, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L125-L125 | tau, kappa and the weights
EDGE: stepW:w1:iso | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L139-L139 | proof step
EDGE: stepW:w1:sep | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L144-L144 | proof step
EDGE: stepW:w1:coord | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L148-L148 | proof step
EDGE: stepW:w1:frozen | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L151-L151 | proof step
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L132-L132 | the frozen coeff occurs directly here
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#bpW:w1:space@L132-L132 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:iso
KIND: step
TITLE: Isometry
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L139-L143
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L139-L143
CONTRACT_ID: stepW:w1:iso
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:space: a >= 0, p in R, K in {R, C}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:space (for all a >= 0, p); within the step: w in l^{a,p}_K; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦tau w¦¦^2 = ¦¦w¦¦_{a,p}^2; tau, kappa are mutually inverse; the inner product and completeness transport from l^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, bpW:w0:ellap#ellWeight, bpW:w1:ext-lp
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L140-L140 | tau, kappa, omega
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L140-L140 | the norm of Definition bpW:w0:ellap
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:iso@L143-L143 | inner product and completeness of l^2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:sep
KIND: step
TITLE: Separability
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sep@L144-L147
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sep@L144-L147
CONTRACT_ID: stepW:w1:sep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:space: a >= 0, p in R, K in {R, C}; local data: (iii) of the lemma
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:space (for all a >= 0, p); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: finitely supported sequences with rational (Gaussian rational) entries form a countable dense set, so l^{a,p}_K is separable (not consumed by later milestones)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:coord
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:coord | blueprint-W/parts/w1-sequences.tex#stepW:w1:sep@L146-L146 | density by the truncation statement (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:coord
KIND: step
TITLE: Coordinates and truncation
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L148-L150
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L148-L150
CONTRACT_ID: stepW:w1:coord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:space: a >= 0, p in R, K in {R, C}; local data: y in l^2_K
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:space (for all a >= 0, p); within the step: j, N; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) ¦(kappa y)_j¦ <= ¦¦y¦¦/omega(j); (iii) ¦¦y - P_N y¦¦^2 = sum_{j>N} ¦y_j¦^2 -> 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-lp, bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L149-L149 | ¦y_j¦ <= ¦¦y¦¦
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:coord@L149-L149 | kappa divides by omega(j)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:frozen
KIND: step
TITLE: Frozen case
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L151-L153
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L151-L153
CONTRACT_ID: stepW:w1:frozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:space: a >= 0, p in R, K in {R, C}; local data: K = R, a = p = 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:space (for all a >= 0, p); within the step: y, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: coeff y j = y_j/omega_{1,1}(j) by the frozen definition, and Mathlib's product norm is the max norm, giving (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:ellap#coeff, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L152-L152 | unfolds the frozen coeff
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#stepW:w1:frozen@L153-L153 | the frozen WaveSpace with the product (max) norm
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:coordinatewise
KIND: lemma
TITLE: Derivatives of coordinates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L158-L168
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L170-L180
CONTRACT_ID: bpW:w1:coordinatewise
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: c : R -> l^2_K differentiable at t; weights (a,p), (a',p') with a >= a', p >= p'; iota the inclusion of Lemma bpW:w1:embed, represented by hat iota; v in l^2_K
SOURCE_QUANTIFIERS: for all such c, t, v
SOURCE_CONCLUSION: (a) for every j, t -> (kappa_{a,p} c(t))_j has derivative (kappa_{a',p'} v)_j at t iff (b) hat iota c'(t) = v; in particular for differentiable K : R^2 -> WaveSpace and X^w of Proposition bpW:w1:hamfield(v), the frozen conclusion (4) of KAM.Wave.nlw2 at (I,theta) (the HasDerivAt of t -> coeff (K(theta + t nu)).i j at 0) is equivalent to hat iota(DK(theta) nu) = X^w(K(theta)), hat iota representing E_{1,1} subset E_{1,0}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:embed, bpW:w1:hamfield, bpW:w0:ellap#coeff, stepW:w1:coordder, stepW:w1:coordcomp, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L160-L160 | the inclusion iota and its representative
EDGE: bpW:w1:hamfield | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L165-L165 | the field X^w of (v)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L165-L165 | the coefficients coeff in the frozen conclusion (4)
EDGE: stepW:w1:coordder | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L171-L171 | proof step
EDGE: stepW:w1:coordcomp | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L175-L175 | proof step
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#bpW:w1:coordinatewise@L164-L164 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The statement speaks of the *form* of the frozen conclusion (4) of nlw2; that is not a use of the root (no edge to bpW:wh:nlw2, which would create a cycle once W8 is added).

NODE: stepW:w1:coordder
KIND: step
TITLE: Coordinates of the derivative
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L171-L174
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L171-L174
CONTRACT_ID: stepW:w1:coordder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:coordinatewise: c : R -> l^2_K differentiable at t; weights (a,p), (a',p') with a >= a', p >= p'; iota the inclusion of Lemma bpW:w1:embed, represented by hat iota; v in l^2_K; local data: c differentiable at t
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:coordinatewise (for all such c, t, v); within the step: j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the coordinate curve t -> (kappa_{a,p} c(t))_j has derivative (kappa_{a,p} c'(t))_j = (kappa_{a',p'} hat iota c'(t))_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:space, bpW:w1:embed
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L172-L172 | (ii): the coordinate is a continuous linear functional
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordder@L174-L174 | (iii): the inclusion does not change coefficients
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:coordcomp
KIND: step
TITLE: Comparison
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L175-L179
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L175-L179
CONTRACT_ID: stepW:w1:coordcomp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:coordinatewise: c : R -> l^2_K differentiable at t; weights (a,p), (a',p') with a >= a', p >= p'; iota the inclusion of Lemma bpW:w1:embed, represented by hat iota; v in l^2_K
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:coordinatewise (for all such c, t, v); within the step: j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (a) iff (b) by injectivity of kappa_{a',p'}; for the frozen statement, c(t) = K(theta + t nu) componentwise at t = 0 with (a,p) = (1,1), (a',p') = (1,0), compared with Proposition bpW:w1:hamfield(v)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:coordder, bpW:w1:space, bpW:w1:hamfield
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:coordder | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L176-L176 | the derivative of the coordinates
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L177-L177 | injectivity of kappa ((i))
EDGE: bpW:w1:hamfield | blueprint-W/parts/w1-sequences.tex#stepW:w1:coordcomp@L179-L179 | (v): the coordinates of X^w are the right sides of (4)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:multiplier
KIND: lemma
TITLE: Diagonal multipliers
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L183-L189
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L191-L195
CONTRACT_ID: bpW:w1:multiplier
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: mu : N_+ -> K and M >= 0 with ¦mu_j¦ <= M for all j
SOURCE_QUANTIFIERS: for all mu, M
SOURCE_CONCLUSION: D_mu y = (mu_j y_j) is bounded linear on l^2_K with ¦¦D_mu¦¦ <= M and ¦¦D_mu¦¦ >= ¦mu_j¦ for every j; a diagonal map w -> (m_j w_j) from l^{a,p}_K to l^{a',p'}_K has representative D_mu with mu_j = m_j omega_{a',p'}(j)/omega_{a,p}(j); it is bounded with norm <= M when ¦mu_j¦ <= M, and unbounded if (mu_j) is unbounded
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-lp, bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L193-L193 | norm bounds from finite partial sums
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:multiplier@L194-L194 | the representative tau o (m .) o kappa
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:embed
KIND: lemma
TITLE: Embeddings
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L198-L207
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L209-L214
CONTRACT_ID: bpW:w1:embed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= a' >= 0, p, p' in R
SOURCE_QUANTIFIERS: for all such weights; w
SOURCE_CONCLUSION: (i) if p >= p', l^{a,p}_K subset l^{a',p'}_K with ¦¦w¦¦_{a',p'} <= ¦¦w¦¦_{a,p}, representative D_mu, mu_j = j^{p'-p} e^{(a'-a)j} in (0,1]; (ii) if a > a' and sigma = p' - p > 0, ¦¦w¦¦_{a',p'} <= (sigma/(e(a-a')))^sigma ¦¦w¦¦_{a,p}; (iii) the inclusions do not change coefficients (kappa_{a',p'} D_mu = kappa_{a,p}), are injective and compose
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:multiplier, bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L210-L210 | m_j = 1, mu_j = omega_{a',p'}(j)/omega_{a,p}(j)
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:embed@L213-L213 | the identity mu_j/omega_{a',p'}(j) = 1/omega_{a,p}(j)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:diag
KIND: lemma
TITLE: Frequency multipliers and the linear flow
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L217-L232
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L234-L249
CONTRACT_ID: bpW:w1:diag
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p in R, r in R; lambda^r the multiplier w -> (lambda_j^r w_j)
SOURCE_QUANTIFIERS: for all a, p, r; t, s in R
SOURCE_CONCLUSION: (i) lambda^r is bounded l^{a,p+r}_K -> l^{a,p}_K, norm (1+m)^{r/2} for r >= 0 (attained at j = 1), at most 1 for r < 0, representative D_mu with mu_j = (lambda_j/j)^r, an isomorphism with inverse lambda^{-r}; (ii) for r > 0 it is not bounded l^{a,p} -> l^{a,p}; (iii) R_t z = (e^{-i lambda_j t} z_j) is a linear isometry of l^{a,p}_C, R_{t+s} = R_t R_s, t -> R_t z continuous; (iv) the real linear flow L_t(q,p) = (cos(lambda t)q + sin(lambda t)p, -sin(lambda t)q + cos(lambda t)p) preserves ¦¦q¦¦^2 + ¦¦p¦¦^2, ¦¦L_t(q,p)¦¦_E <= sqrt2 ¦¦(q,p)¦¦_E, L_{t+s} = L_t L_s, every coordinate solves dq_j = lambda_j p_j, dp_j = -lambda_j q_j, and in the coordinates z of Definition bpW:w0:z, L_t is R_t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lam, bpW:w0:z, stepW:w1:ratio, stepW:w1:rot, stepW:w1:realflow
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L218-L218 | the multiplier lambda^r
EDGE: bpW:w0:z | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L230-L230 | the complex coordinates z
EDGE: stepW:w1:ratio | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L235-L235 | proof step
EDGE: stepW:w1:rot | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L240-L240 | proof step
EDGE: stepW:w1:realflow | blueprint-W/parts/w1-sequences.tex#bpW:w1:diag@L244-L244 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:ratio
KIND: step
TITLE: Ratio
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L235-L239
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L235-L239
CONTRACT_ID: stepW:w1:ratio
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:diag: a >= 0, p in R, r in R; lambda^r the multiplier w -> (lambda_j^r w_j)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:diag (for all a, p, r; t, s in R); within the step: j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: mu_j = (lambda_j/j)^r with 1 < lambda_j/j <= sqrt(1+m), equality at j = 1; so ¦mu_j¦ <= (1+m)^{r/2} = mu_1 (r >= 0), ¦mu_j¦ <= 1 (r < 0); the inverse is the same with -r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:multiplier, bpW:w0:basis#lambda-facts, bpW:w0:mass, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L236-L236 | the representative and its norm
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L237-L237 | j < lambda_j
EDGE: bpW:w0:mass | blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L237-L237 | lambda_j^2 = j^2 + m <= (1+m) j^2
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:ratio@L236-L236 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:rot
KIND: step
TITLE: Unboundedness and rotations
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L240-L243
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L240-L243
CONTRACT_ID: stepW:w1:rot
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:diag: a >= 0, p in R, r in R; lambda^r the multiplier w -> (lambda_j^r w_j); local data: t, s in R; z in l^{a,p}_C
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:diag (for all a, p, r; t, s in R); within the step: t, s; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) lambda_j^r -> infinity; (iii) R_t = D_mu with ¦mu_j¦ = 1 is an isometry, group law coordinatewise, and t -> R_t z continuous by dominated convergence for series
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:multiplier, bpW:w1:ext-series, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L241-L241 | R_t is a multiplier D_mu with ¦mu_j¦ = 1
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L243-L243 | dominated convergence for series (Tonelli/Fubini for series)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:rot@L241-L241 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:realflow
KIND: step
TITLE: Real flow
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L244-L248
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L244-L248
CONTRACT_ID: stepW:w1:realflow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:diag: a >= 0, p in R, r in R; lambda^r the multiplier w -> (lambda_j^r w_j); local data: (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:diag (for all a, p, r; t, s in R); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: coordinatewise rotation: q_j(t)^2 + p_j(t)^2 = q_j^2 + p_j^2, hence the norm identity and max(¦¦q(t)¦¦,¦¦p(t)¦¦)^2 <= ¦¦q¦¦^2 + ¦¦p¦¦^2 <= 2¦¦(q,p)¦¦_E^2; derivatives and group law by trigonometry; z_j(t) = e^{-i lambda_j t} z_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:z, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:z | blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L248-L248 | z_j = (q_j + i p_j)/sqrt 2
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:realflow@L248-L248 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:linfty
KIND: definition
TITLE: Sup-weighted sequences
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:linfty@L254-L261
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:linfty
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: p in R; Pi subset R^2; L >= 0
SOURCE_QUANTIFIERS: p, Pi, L
SOURCE_CONCLUSION: defines l^p_infty (real sequences with ¦w¦_p = sup_j ¦w_j¦ j^p < infinity, realized as lp infinity by w -> (j^p w_j)) and L-Lipschitz maps Pi -> l^p_infty (max norm on R^2); P96-K's Lipschitz semi-norm is the least such L
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:tails
KIND: lemma
TITLE: Spectral asymptotics of the wave normal frequencies
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L264-L273
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L275-L280
CONTRACT_ID: bpW:w1:tails
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: b = (1/lambda_1, 1/lambda_2); Omega_j(xi) = lambda_j + (3/(2 pi lambda_j))<b,xi> (j >= 3, xi in R^2); bar Omega_j = j; tilde Omega_j = Omega_j - bar Omega_j
SOURCE_QUANTIFIERS: for all xi, zeta in R^2; i, j >= 3
SOURCE_CONCLUSION: ¦tilde Omega(xi)¦_1 <= m/2 + (3/(2pi))¦<b,xi>¦ and ¦tilde Omega(xi) - tilde Omega(zeta)¦_1 <= (3/(2pi))(1/lambda_1 + 1/lambda_2)¦xi - zeta¦; so P96-K Assumption B holds with d = 1, delta = -1, and p - bar p <= delta holds with equality for bar p = p + 1; ¦Omega_i(xi) - Omega_j(xi) - (i-j)¦ <= (m + (3/pi)¦<b,xi>¦)/min(i,j)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w1:linfty, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L266-L266 | Omega = lambda_N + B xi with the corrected B
EDGE: bpW:w1:linfty | blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L268-L268 | the norm ¦.¦_1 of l^1_infty and the Lipschitz condition
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L276-L276 | lambda_j - j = m/(lambda_j + j) in (0, m/(2j)]; lambda_j > j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:tails@L265-L265 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:twosided-transport
KIND: definition
TITLE: Two-sided transport
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-transport@L288-L294
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:twosided-transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a >= 0, s in R
SOURCE_QUANTIFIERS: a, s
SOURCE_CONCLUSION: defines omega^b_{a,s}(l) = <l>^s e^{a¦l¦} and the realization of l^{a,s}_b as lp (Int -> C) 2 via c -> (omega^b(l) c_l) (an isometry as in Lemma bpW:w1:space); (c*d)_l = sum_i c_i d_{l-i} when sum_i ¦c_i¦¦d_{l-i}¦ < infinity for all l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:twosided, bpW:w1:space
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:twosided | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-transport@L290-L290 | the space l^{a,s}_b and the convolution
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided-transport@L291-L291 | the isometry argument
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:twosided
KIND: lemma
TITLE: Passage between one- and two-sided sequences
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L297-L313
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L315-L325
CONTRACT_ID: bpW:w1:twosided
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p in R
SOURCE_QUANTIFIERS: for all a, p; q; X; z, zbar
SOURCE_CONCLUSION: (i) (E^+- q)_l = (+-1)^{[l<0]} q_¦l¦/sqrt(lambda_¦l¦) (l != 0), 0 at l = 0, is linear l^{a,p}_C -> l^{a,p+1/2}_b with norm <= sqrt2 ¦¦q¦¦_{a,p}, also for the majorant ¦E^+ q¦; the even x_l = ¦q_¦l¦¦/sqrt(¦l¦) has ¦¦x¦¦_{a,p+1/2}^2 = 2¦¦q¦¦_{a,p}^2; (ii) for X in l^{a,p+1/2}_b, (X_l/sqrt(lambda_l))_{l>=1} lies in l^{a,p+1}_C with norm <= (sum_{l>=1} l^{2p+1} e^{2al} ¦X_l¦^2)^{1/2} <= ¦¦X¦¦_{a,p+1/2}, and <= ¦¦X¦¦/sqrt2 if ¦X¦ is even; (iii) J(z,zbar) (z on j >= 1, zbar on -j, 0 at 0) is a linear isometry from l^{a,p}_C x l^{a,p}_C with (¦¦z¦¦^2 + ¦¦zbar¦¦^2)^{1/2} onto {w in l^{a,p}_b : w_0 = 0}, ¦¦J(z,zbar)¦¦ <= sqrt2 max(¦¦z¦¦,¦¦zbar¦¦)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:twosided-transport, bpW:w0:basis#lam, stepW:w1:ext, stepW:w1:restr, stepW:w1:pair
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:twosided-transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L302-L302 | the two-sided weights
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L300-L300 | the factor 1/sqrt(lambda_¦l¦)
EDGE: stepW:w1:ext | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L316-L316 | proof step
EDGE: stepW:w1:restr | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L320-L320 | proof step
EDGE: stepW:w1:pair | blueprint-W/parts/w1-sequences.tex#bpW:w1:twosided@L323-L323 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:ext
KIND: step
TITLE: Extensions
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L316-L319
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L316-L319
CONTRACT_ID: stepW:w1:ext
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:twosided: a >= 0, p in R; local data: q in l^{a,p}_C
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:twosided (for all a, p; q; X; z, zbar); within the step: q; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦E^+- q¦¦^2 = 2 sum j^{2p+1} e^{2aj} ¦q_j¦^2/lambda_j <= 2¦¦q¦¦^2; the majorant has the same norm; with sqrt(¦l¦) the factor j/lambda_j becomes 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, stepW:w0n:majorant, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L318-L318 | j/lambda_j < 1
EDGE: stepW:w0n:majorant | blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L319-L319 | this is the majorant step of W0
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:ext@L317-L317 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:restr
KIND: step
TITLE: Restriction
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L320-L322
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L320-L322
CONTRACT_ID: stepW:w1:restr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:twosided: a >= 0, p in R; local data: X in l^{a,p+1/2}_b
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:twosided (for all a, p; q; X; z, zbar); within the step: X; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum_{l>=1} l^{2p+2} e^{2al} ¦X_l¦^2/lambda_l <= sum_{l>=1} l^{2p+1} e^{2al} ¦X_l¦^2; for even ¦X¦ at most half the full sum
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, stepW:w0n:smoothing, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L321-L321 | l/lambda_l < 1
EDGE: stepW:w0n:smoothing | blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L322-L322 | this is the smoothing step of W0
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:restr@L321-L321 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:pair
KIND: step
TITLE: Pairing
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:pair@L323-L324
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:pair@L323-L324
CONTRACT_ID: stepW:w1:pair
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:twosided: a >= 0, p in R; local data: z, zbar in l^{a,p}_C
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:twosided (for all a, p; q; X; z, zbar); within the step: z, zbar; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦J(z,zbar)¦¦^2 = sum_{j>=1} omega_{a,p}(j)^2 (¦z_j¦^2 + ¦zbar_j¦^2) since <+-j> = j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:twosided-transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:twosided-transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:pair@L324-L324 | the two-sided weight <l>
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:young
KIND: lemma
TITLE: Young and $\ell^1$ control
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L329-L339
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L341-L357
CONTRACT_ID: bpW:w1:young
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (i) X in l^2(Z), Y in l^1(Z); (ii) s > 1/2, a >= 0, Y in l^{a,s}_b; (iii) nonnegative X, Y, Z in l^{0,s}_b with s > 1/2; complex c, d
SOURCE_QUANTIFIERS: for all such sequences
SOURCE_CONCLUSION: (i) each sum_i ¦X_i¦¦Y_{l-i}¦ converges and ¦¦X*Y¦¦_{l^2} <= ¦¦X¦¦_{l^2} ¦¦Y¦¦_{l^1}; (ii) sum_l <l>^{-2s} = 1 + 2 zeta(2s) < infinity and ¦¦Y¦¦_{l^1} <= (1+2zeta(2s))^{1/2} ¦¦Y¦¦_{0,s} <= (1+2zeta(2s))^{1/2} ¦¦Y¦¦_{a,s}; (iii) convolution of nonnegative sequences is commutative, associative and monotone; ¦c*d¦ <= ¦c¦*¦d¦ pointwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:twosided-transport, stepW:w1:cs, stepW:w1:youngsum, stepW:w1:l1, stepW:w1:rules
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:twosided-transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L333-L333 | the norms ¦¦.¦¦_{a,s} and the convolution
EDGE: stepW:w1:cs | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L342-L342 | proof step
EDGE: stepW:w1:youngsum | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L346-L346 | proof step
EDGE: stepW:w1:l1 | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L349-L349 | proof step
EDGE: stepW:w1:rules | blueprint-W/parts/w1-sequences.tex#bpW:w1:young@L353-L353 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:cs
KIND: step
TITLE: Weighted Cauchy--Schwarz
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cs@L342-L345
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cs@L342-L345
CONTRACT_ID: stepW:w1:cs
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:young: (i) X in l^2(Z), Y in l^1(Z); (ii) s > 1/2, a >= 0, Y in l^{a,s}_b; (iii) nonnegative X, Y, Z in l^{0,s}_b with s > 1/2; complex c, d; local data: X in l^2, Y in l^1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:young (for all such sequences); within the step: l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (sum_i ¦X_i¦¦Y_{l-i}¦)^2 <= ¦¦Y¦¦_1 sum_i ¦X_i¦^2 ¦Y_{l-i}¦, finite
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:youngsum
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L346-L348
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L346-L348
CONTRACT_ID: stepW:w1:youngsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:young: (i) X in l^2(Z), Y in l^1(Z); (ii) s > 1/2, a >= 0, Y in l^{a,s}_b; (iii) nonnegative X, Y, Z in l^{0,s}_b with s > 1/2; complex c, d
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:young (for all such sequences); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum_l ¦(X*Y)_l¦^2 <= ¦¦Y¦¦_1^2 ¦¦X¦¦_2^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:cs, bpW:w1:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:cs | blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L348-L348 | sums the pointwise bound over l
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:youngsum@L347-L347 | exchange of the nonnegative double sum (Tonelli)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:l1
KIND: step
TITLE: $\ell^1$ control
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:l1@L349-L352
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:l1@L349-L352
CONTRACT_ID: stepW:w1:l1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:young: (i) X in l^2(Z), Y in l^1(Z); (ii) s > 1/2, a >= 0, Y in l^{a,s}_b; (iii) nonnegative X, Y, Z in l^{0,s}_b with s > 1/2; complex c, d
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:young (for all such sequences); within the step: Y; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum_l <l>^{-2s} = 1 + 2 sum_{l>=1} l^{-2s} < infinity and ¦¦Y¦¦_1 <= (1+2zeta(2s))^{1/2} ¦¦Y¦¦_{0,s} <= (1+2zeta(2s))^{1/2} ¦¦Y¦¦_{a,s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:l1@L350-L350 | sum k^{-sigma} < infinity for sigma = 2s > 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:rules
KIND: step
TITLE: Algebraic rules
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L353-L356
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L353-L356
CONTRACT_ID: stepW:w1:rules
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:young: (i) X in l^2(Z), Y in l^1(Z); (ii) s > 1/2, a >= 0, Y in l^{a,s}_b; (iii) nonnegative X, Y, Z in l^{0,s}_b with s > 1/2; complex c, d; local data: sequences in l^1 cap l^2 by (ii)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:young (for all such sequences); within the step: X, Y, Z; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: absolute convergence of the double series allows rearrangement (associativity); commutativity by i -> l - i; monotonicity and ¦c*d¦ <= ¦c¦*¦d¦ termwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:l1, bpW:w1:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:l1 | blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L354-L354 | (ii) puts the sequences in l^1 cap l^2
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:rules@L355-L355 | Fubini for absolutely summable double series
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:algebra
KIND: lemma
TITLE: Convolution algebra
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L360-L363
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L365-L369
CONTRACT_ID: bpW:w1:algebra
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, s >= 1, c, d (, e) in l^{a,s}_b
SOURCE_QUANTIFIERS: for all such a, s, c, d, e
SOURCE_CONCLUSION: ¦¦c*d¦¦_{a,s} <= K_s ¦¦c¦¦ ¦¦d¦¦ with K_s = 2^s(1+2zeta(2s))^{1/2}, and ¦¦c*d*e¦¦_{a,s} <= K_s^2 ¦¦c¦¦ ¦¦d¦¦ ¦¦e¦¦
CONSTANT_SCOPE: K_s depends only on s
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:algebra, bpW:w1:young
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:algebra | blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L366-L366 | the two-factor bound is Lemma bpW:w0n:algebra
EDGE: bpW:w1:young | blueprint-W/parts/w1-sequences.tex#bpW:w1:algebra@L367-L367 | (iii): associativity for the three-factor form
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:selection
KIND: lemma
TITLE: Selection-rule trilinear maps
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L386-L400
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L402-L427
CONTRACT_ID: bpW:w1:selection
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b
SOURCE_QUANTIFIERS: for all such a, p, M, c and arguments
SOURCE_CONCLUSION: (a) T_c(q,q',q'')_l = sum c_ijkl q_i q'_j q''_k converge absolutely and ¦¦T_c¦¦_{a,p+1} <= 2 M K_s^2 prod ¦¦q¦¦_{a,p}; (b) T_c(w,w',w'')_l (l != 0) converge absolutely, T_c(.)_0 = 0, ¦¦T_c¦¦_{a,p+1} <= 64 M K_s^2 prod ¦¦w¦¦_{a,p}; T_c is trilinear, symmetric if c is symmetric in its first three indices
CONSTANT_SCOPE: the bounds depend only on M and s (through K_s)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:maj1, stepW:w1:sel1, stepW:w1:smooth1, stepW:w1:maj2, stepW:w1:sel2, stepW:w1:smooth2
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:maj1 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L403-L403 | proof step
EDGE: stepW:w1:sel1 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L406-L406 | proof step
EDGE: stepW:w1:smooth1 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L412-L412 | proof step
EDGE: stepW:w1:maj2 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L415-L415 | proof step
EDGE: stepW:w1:sel2 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L419-L419 | proof step
EDGE: stepW:w1:smooth2 | blueprint-W/parts/w1-sequences.tex#bpW:w1:selection@L423-L423 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:maj1
KIND: step
TITLE: One-sided majorant
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj1@L403-L405
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj1@L403-L405
CONTRACT_ID: stepW:w1:maj1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:selection: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b; local data: x_i = ¦q_¦i¦¦/sqrt(¦i¦), x_0 = 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:selection (for all such a, p, M, c and arguments); within the step: q, q', q''; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: x is even with ¦¦x¦¦_{a,s} = sqrt2 ¦¦q¦¦_{a,p}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:twosided
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:twosided | blueprint-W/parts/w1-sequences.tex#stepW:w1:maj1@L405-L405 | (i): the even sequence x
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:sel1
KIND: step
TITLE: One-sided selection
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L406-L411
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L406-L411
CONTRACT_ID: stepW:w1:sel1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:selection: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:selection (for all such a, p, M, c and arguments); within the step: l >= 1; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum_{i,j,k} ¦c_ijkl q_i q'_j q''_k¦ <= M l^{-1/2} X_l with X = x*x'*x'', finite and even
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:maj1, stepW:w0n:selection, bpW:w1:young, bpW:w1:algebra
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:maj1 | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L408-L408 | the even majorants
EDGE: stepW:w0n:selection | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L410-L410 | the injectivity argument of the W0 selection step
EDGE: bpW:w1:young | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L410-L410 | X is finite (Young, l^1 control)
EDGE: bpW:w1:algebra | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel1@L411-L411 | X lies in l^{a,s}_b
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:smooth1
KIND: step
TITLE: One-sided smoothing
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L412-L414
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L412-L414
CONTRACT_ID: stepW:w1:smooth1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:selection: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:selection (for all such a, p, M, c and arguments); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦T_c¦¦_{a,p+1}^2 <= (M^2/2) ¦¦X¦¦_{a,s}^2 and ¦¦X¦¦_{a,s} <= K_s^2 ¦¦x¦¦ ¦¦x'¦¦ ¦¦x''¦¦ = 2^{3/2} K_s^2 prod ¦¦q¦¦; hence ¦¦T_c¦¦ <= 2 M K_s^2 prod ¦¦q¦¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:sel1, bpW:w1:algebra, stepW:w1:maj1
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:sel1 | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L413-L413 | the pointwise bound by M l^{-1/2} X_l
EDGE: bpW:w1:algebra | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L414-L414 | three-factor algebra bound
EDGE: stepW:w1:maj1 | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth1@L414-L414 | ¦¦x¦¦ = sqrt2 ¦¦q¦¦
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:maj2
KIND: step
TITLE: Two-sided majorant
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj2@L415-L418
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:maj2@L415-L418
CONTRACT_ID: stepW:w1:maj2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:selection: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b; local data: tilde x_i = (¦w_i¦ + ¦w_{-i}¦)/sqrt(¦i¦), tilde x_0 = 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:selection (for all such a, p, M, c and arguments); within the step: w, w', w''; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: tilde x is even with ¦¦tilde x¦¦_{a,s}^2 <= 4 ¦¦w¦¦_{a,p}^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:twosided-transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:twosided-transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:maj2@L417-L417 | the two-sided weights
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:sel2
KIND: step
TITLE: Two-sided selection
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel2@L419-L422
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sel2@L419-L422
CONTRACT_ID: stepW:w1:sel2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:selection: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:selection (for all such a, p, M, c and arguments); within the step: l != 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: each of the eight eps-terms is at most (tilde x*tilde x'*tilde x'')_l =: tilde X_l, so ¦T_c(w,w',w'')_l¦ <= 8 M ¦l¦^{-1/2} tilde X_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:maj2
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:maj2 | blueprint-W/parts/w1-sequences.tex#stepW:w1:sel2@L421-L421 | ¦w_i¦/sqrt(¦i¦) <= tilde x_{i'}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:smooth2
KIND: step
TITLE: Two-sided smoothing
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L423-L426
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L423-L426
CONTRACT_ID: stepW:w1:smooth2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:selection: a >= 0, p >= 1/2, s = p + 1/2, M >= 0; (a) c : N_+^4 -> C with ¦c_ijkl¦ <= M (ijkl)^{-1/2} sum_eps [l = eps_1 i + eps_2 j + eps_3 k], q, q', q'' in l^{a,p}_C; (b) c : (Z\0)^4 -> C with the same bound in ¦ijkl¦, w, w', w'' in l^{a,p}_b
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:selection (for all such a, p, M, c and arguments); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦T_c¦¦_{a,p+1}^2 <= 64 M^2 ¦¦tilde X¦¦_{a,s}^2, ¦¦tilde X¦¦ <= 8 K_s^2 prod ¦¦w¦¦, so ¦¦T_c¦¦ <= 64 M K_s^2 prod ¦¦w¦¦; trilinearity and symmetry termwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:sel2, bpW:w1:algebra, stepW:w1:maj2
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:sel2 | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L424-L424 | the pointwise bound
EDGE: bpW:w1:algebra | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L425-L425 | three-factor algebra bound
EDGE: stepW:w1:maj2 | blueprint-W/parts/w1-sequences.tex#stepW:w1:smooth2@L425-L425 | ¦¦tilde x¦¦ <= 2 ¦¦w¦¦
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:trilinear
KIND: theorem
TITLE: The cubic map as a continuous trilinear map
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L431-L450
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L452-L472
CONTRACT_ID: bpW:w1:trilinear
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2, C_* = K_{p+1/2}^2/pi, K in {R, C}; for (iii) a >= a' >= 0, p >= p' >= 1/2; for (iv) y in l^2_R, l >= 1 (and a > 0 for the general case)
SOURCE_QUANTIFIERS: for all such a, p, K
SOURCE_CONCLUSION: (i) there is a unique continuous symmetric K-trilinear map T^{a,p}_K : (l^2_K)^3 -> l^2_K with kappa_{a,p+1} T^{a,p}_K(y,y',y'') = T(kappa y, kappa y', kappa y'') (T of Theorem bpW:w0n:cubic-bound) and ¦¦T^{a,p}_K¦¦ <= C_*; (ii) T_C(iota y, ...) = iota T_R(y, ...) and conj(T_C(z,z',z'')) = T_C(conj z, ...); (iii) T^{a',p'}(hat iota y, ...) = hat iota' T^{a,p}(y, ...); (iv) cubicGrad m hm y l = T^{1,1}_R(y,y,y)_l/omega_{1,2}(l), i.e. G_q(kappa_{1,1} y) = kappa_{1,2} T^{1,1}_R(y,y,y); for a > 0, p >= 1/2 likewise G_q(kappa_{a,p} y) = kappa_{a,p+1} T^{a,p}_R(y,y,y)
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, bpW:w1:complexification, bpW:w0:Gq#cubicGrad, stepW:w1:tricoord, stepW:w1:tricont, stepW:w1:trireal, stepW:w1:trifrozen, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L437-L437 | kappa, omega
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L439-L439 | iota and conjugation
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L446-L446 | the frozen cubicGrad in (iv)
EDGE: stepW:w1:tricoord | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L453-L453 | proof step
EDGE: stepW:w1:tricont | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L459-L459 | proof step
EDGE: stepW:w1:trireal | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L463-L463 | proof step
EDGE: stepW:w1:trifrozen | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L467-L467 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L455-L455 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#bpW:w1:trilinear@L468-L468 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:tricoord
KIND: step
TITLE: Coordinates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L453-L458
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L453-L458
CONTRACT_ID: stepW:w1:tricoord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:trilinear: a >= 0, p >= 1/2, C_* = K_{p+1/2}^2/pi, K in {R, C}; for (iii) a >= a' >= 0, p >= p' >= 1/2; for (iv) y in l^2_R, l >= 1 (and a > 0 for the general case); local data: y, y', y'' in l^2_K; q = kappa_{a,p} y etc.
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:trilinear (for all such a, p, K); within the step: y, y', y''; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: each T(q,q',q'')_l is an absolutely convergent tsum over N_+^3, T(q,q',q'') in l^{a,p+1}_K with norm <= C_* prod ¦¦y¦¦; define T(y,y',y'') = tau_{a,p+1} T(q,q',q'')
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, bpW:w0:basis#lam
ROUTES: stepW:w1:tricoord#via-cubic-bound, stepW:w1:tricoord#via-selection
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L458-L458 | tau_{a,p+1} and the weighted coordinates
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L455-L455 | lambda occurs directly here (frozen lam)
EDGE: stepW:w1:tricoord#via-cubic-bound | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L454-L454 | first derivation: Theorem bpW:w0n:cubic-bound
EDGE: stepW:w1:tricoord#via-selection | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L455-L455 | equivalent derivation: Lemma bpW:w1:selection(a)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:tricont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L459-L462
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L459-L462
CONTRACT_ID: stepW:w1:tricont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:trilinear: a >= 0, p >= 1/2, C_* = K_{p+1/2}^2/pi, K in {R, C}; for (iii) a >= a' >= 0, p >= p' >= 1/2; for (iv) y in l^2_R, l >= 1 (and a > 0 for the general case)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:trilinear (for all such a, p, K); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: trilinear and symmetric termwise; continuous with norm <= C_* (MultilinearMap.mkContinuous); unique since kappa_{a,p+1} is injective
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:tricoord, bpW:w0n:quartic-coeff, bpW:w1:space
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:tricoord | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L461-L461 | the bound C_* prod ¦¦y¦¦
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L460-L460 | symmetry of g
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricont@L462-L462 | kappa is injective ((i))
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:trireal
KIND: step
TITLE: Real structure and compatibility
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L463-L466
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L463-L466
CONTRACT_ID: stepW:w1:trireal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:trilinear: a >= 0, p >= 1/2, C_* = K_{p+1/2}^2/pi, K in {R, C}; for (iii) a >= a' >= 0, p >= p' >= 1/2; for (iv) y in l^2_R, l >= 1 (and a > 0 for the general case)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:trilinear (for all such a, p, K); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) real coefficients commute with iota and conjugation; (iii) both sides have coefficients T(q,q',q'')
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:complexification, bpW:w1:embed, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L465-L465 | iota and conjugation
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L466-L466 | (iii): inclusions do not change coefficients
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:trireal@L464-L464 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:trifrozen
KIND: step
TITLE: Frozen identification
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L467-L471
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L467-L471
CONTRACT_ID: stepW:w1:trifrozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:trilinear: a >= 0, p >= 1/2, C_* = K_{p+1/2}^2/pi, K in {R, C}; for (iii) a >= a' >= 0, p >= p' >= 1/2; for (iv) y in l^2_R, l >= 1 (and a > 0 for the general case); local data: y in l^2_R, a = p = 1 (or a > 0)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:trilinear (for all such a, p, K); within the step: y, l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: reconU m hm y = U_m(kappa_{1,1} y) (absolutely convergent tsum), the interval integral is that of Definition bpW:w0:Gq, so cubicGrad m hm y l = G_q(kappa_{1,1} y)_l = T(q,q,q)_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:reconstruction#reconU, bpW:w0n:recon-bounded, bpW:w0:Gq#cubicGrad, bpW:w0n:gradient, bpW:w0:ellap#coeff, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L468-L468 | unfolds the frozen reconU
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L469-L469 | the tsum converges absolutely
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L470-L470 | unfolds the frozen cubicGrad
EDGE: bpW:w0n:gradient | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L471-L471 | G_q(q)_l = T(q,q,q)_l for a > 0
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L468-L468 | kappa_{1,1} = coeff
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:trifrozen@L470-L470 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:cubic-analytic
KIND: corollary
TITLE: Analyticity and Lipschitz bounds of the cubic gradient
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L475-L489
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L491-L505
CONTRACT_ID: bpW:w1:cubic-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y)
SOURCE_QUANTIFIERS: for all y, y', h, k
SOURCE_CONCLUSION: (i) N is K-analytic on l^2_K, ¦¦N(y)¦¦ <= C_* ¦¦y¦¦^3; (ii) DN(y)h = 3T(y,y,h), D^2N(y)(h,k) = 6T(y,h,k), D^3N = 6T, ¦¦DN(y)¦¦ <= 3C_*¦¦y¦¦^2, ¦¦D^2N(y)¦¦ <= 6C_*¦¦y¦¦; (iii) ¦¦N(y) - N(y')¦¦ <= 3C_* ¦¦y-y'¦¦ max(¦¦y¦¦,¦¦y'¦¦)^2; (iv) G^w(y)_l = omega_{1,2}(l) cubicGrad m hm y l is N for (a,p) = (1,1), K = R, real analytic with ¦¦G^w(y)¦¦ <= C_m ¦¦y¦¦^3, C_m = 8(1+2zeta(3))/pi; G_q(kappa_{1,1} y) has weighted coordinates G^w(y) at (1,2), (l^{-1} G^w(y)_l) at (1,1), (l^{-2} G^w(y)_l) at (1,0)
CONSTANT_SCOPE: C_* depends only on p; C_m independent of m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:trilinear, bpW:w0:Gq#cubicGrad, stepW:w1:can, stepW:w1:cder, stepW:w1:clip, stepW:w1:cfrozen
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L476-L476 | T and C_*
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L484-L484 | the frozen cubicGrad in (iv)
EDGE: stepW:w1:can | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L492-L492 | proof step
EDGE: stepW:w1:cder | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L494-L494 | proof step
EDGE: stepW:w1:clip | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L499-L499 | proof step
EDGE: stepW:w1:cfrozen | blueprint-W/parts/w1-sequences.tex#bpW:w1:cubic-analytic@L502-L502 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:can
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:can@L492-L493
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:can@L492-L493
CONTRACT_ID: stepW:w1:can
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cubic-analytic: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y); local data: T continuous trilinear
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cubic-analytic (for all y, y', h, k); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: N = T o Delta, Delta(y) = (y,y,y) continuous linear, is analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:can@L493-L493 | continuous multilinear maps and compositions are analytic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:cder
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cder@L494-L498
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cder@L494-L498
CONTRACT_ID: stepW:w1:cder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cubic-analytic: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y); local data: T symmetric trilinear with ¦¦T¦¦ <= C_*
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cubic-analytic (for all y, y', h, k); within the step: y, h; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: DN(y)h = 3T(y,y,h), the higher derivatives likewise, with the stated bounds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:trilinear
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:cder@L496-L496 | symmetry and the bound C_* ((i))
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:clip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:clip@L499-L501
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:clip@L499-L501
CONTRACT_ID: stepW:w1:clip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cubic-analytic: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y); local data: T trilinear
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cubic-analytic (for all y, y', h, k); within the step: y, y'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: N(y) - N(y') = T(y-y',y,y) + T(y',y-y',y) + T(y',y',y-y'), so the Lipschitz bound 3C_* ¦¦y-y'¦¦ max^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:trilinear
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:clip@L501-L501 | the bound C_*
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:cfrozen
KIND: step
TITLE: Frozen form
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L502-L504
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L502-L504
CONTRACT_ID: stepW:w1:cfrozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cubic-analytic: a >= 0, p >= 1/2, T = T^{a,p}_K, C_* as in Theorem bpW:w1:trilinear, N(y) = T(y,y,y); local data: (a,p) = (1,1), K = R
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cubic-analytic (for all y, y', h, k); within the step: y, l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) from Theorem bpW:w1:trilinear(iv), omega_{1,1}/omega_{1,2} = l^{-1}, omega_{1,0}/omega_{1,2} = l^{-2}, and C_* = K_{3/2}^2/pi = C_m
CONSTANT_SCOPE: C_m independent of m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:trilinear, bpW:w0n:cubic-bound, bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L503-L503 | (iv) frozen identification
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L504-L504 | C_m = K_{3/2}^2/pi
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:cfrozen@L503-L503 | the weight ratios
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:gradient-identity
KIND: proposition
TITLE: Gradient identity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L509-L522
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L524-L540
CONTRACT_ID: bpW:w1:gradient-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a > 0, p >= 1/2; G(q) = (1/4) int_0^pi U_m(q)^4 for q in l^{a,p}; <u,v>_0 = sum_j u_j v_j (unweighted), absolutely convergent for u in l^{a,p+1}, v in l^{a,p}
SOURCE_QUANTIFIERS: for all a > 0, p >= 1/2; q, h in l^{a,p}; y, h in l^2_R for (iii)
SOURCE_CONCLUSION: (i) G(q) = (1/4)<G_q(q),q>_0 = (1/4) Q(q,q,q,q), Q(q_1,..,q_4) = <T(q_1,q_2,q_3),q_4>_0 symmetric continuous 4-linear with ¦Q¦ <= C_* prod ¦¦q_i¦¦; (ii) G is real analytic on l^{a,p} and DG(q)h = <G_q(q),h>_0; (iii) G_q(q) is not the Riesz gradient of G for l^{a,p} (that is (omega^{-2} G_q(q)_j)); in frozen coordinates, G^w(y) = G(kappa_{1,1} y), DG^w(y)h = sum_j cubicGrad m hm y j . coeff h j and nabla^{l^2} G^w(y) = (G^w(y)_j/(omega_{1,1}(j) omega_{1,2}(j)))_j
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:H, bpW:w0n:cubic-bound, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff, stepW:w1:quartic, stepW:w1:gradder, stepW:w1:gradw, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:H | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L510-L510 | G(q) = (1/4) int U_m(q)^4
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L515-L515 | the trilinear map T
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L519-L519 | frozen cubicGrad in (iii)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L519-L519 | frozen coeff in (iii)
EDGE: stepW:w1:quartic | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L525-L525 | proof step
EDGE: stepW:w1:gradder | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L531-L531 | proof step
EDGE: stepW:w1:gradw | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L535-L535 | proof step
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#bpW:w1:gradient-identity@L510-L510 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:quartic
KIND: step
TITLE: Quartic form
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L525-L530
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L525-L530
CONTRACT_ID: stepW:w1:quartic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:gradient-identity: a > 0, p >= 1/2; G(q) = (1/4) int_0^pi U_m(q)^4 for q in l^{a,p}; <u,v>_0 = sum_j u_j v_j (unweighted), absolutely convergent for u in l^{a,p+1}, v in l^{a,p}; local data: q in l^{a,p}, a > 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:gradient-identity (for all a > 0, p >= 1/2; q, h in l^{a,p}; y, h in l^2_R for (iii)); within the step: q_1, ..., q_4; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: G(q) = (1/4) sum_l q_l T(q,q,q)_l; Q is well defined, symmetric, and ¦Q¦ <= C_* prod ¦¦q_i¦¦
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient, bpW:w0n:quartic-coeff, bpW:w1:embed, bpW:w0n:cubic-bound
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:gradient | blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L526-L526 | G as an absolutely convergent quartic sum
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L528-L528 | symmetry of g
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L529-L529 | ¦¦u¦¦_{0,0} <= ¦¦u¦¦_{a,p+1}, ¦¦v¦¦_{0,0} <= ¦¦v¦¦_{a,p}
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w1-sequences.tex#stepW:w1:quartic@L530-L530 | the bound on T
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:gradder
KIND: step
TITLE: Derivative
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L531-L534
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L531-L534
CONTRACT_ID: stepW:w1:gradder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:gradient-identity: a > 0, p >= 1/2; G(q) = (1/4) int_0^pi U_m(q)^4 for q in l^{a,p}; <u,v>_0 = sum_j u_j v_j (unweighted), absolutely convergent for u in l^{a,p+1}, v in l^{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:gradient-identity (for all a > 0, p >= 1/2; q, h in l^{a,p}; y, h in l^2_R for (iii)); within the step: q, h; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: G = (1/4) Q o (q -> (q,q,q,q)) is analytic and DG(q)h = Q(q,q,q,h) = <T(q,q,q),h>_0 = <G_q(q),h>_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:quartic, bpW:w1:ext-analytic, bpW:w1:trilinear, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:quartic | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L532-L532 | the quartic form Q
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L532-L532 | continuous multilinear maps are analytic
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L534-L534 | (iv): T(q,q,q) = G_q(q)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradder@L533-L533 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:gradw
KIND: step
TITLE: Weighted coordinates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L535-L539
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L535-L539
CONTRACT_ID: stepW:w1:gradw
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:gradient-identity: a > 0, p >= 1/2; G(q) = (1/4) int_0^pi U_m(q)^4 for q in l^{a,p}; <u,v>_0 = sum_j u_j v_j (unweighted), absolutely convergent for u in l^{a,p+1}, v in l^{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:gradient-identity (for all a > 0, p >= 1/2; q, h in l^{a,p}; y, h in l^2_R for (iii)); within the step: y, h; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the Riesz gradient is (omega^{-2} G_q(q)_j); in frozen coordinates DG^w(y)h and nabla^{l^2} G^w(y) as stated
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:gradder, bpW:w1:cubic-analytic, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:gradder | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L536-L536 | DG(q)h = <G_q(q),h>_0
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L538-L538 | (iv): G^w and the weighted coordinates of G_q(kappa y)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#stepW:w1:gradw@L536-L536 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:hamfield
KIND: proposition
TITLE: The Hamiltonian field
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L543-L563
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L565-L586
CONTRACT_ID: bpW:w1:hamfield
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a > 0, p >= 1/2
SOURCE_QUANTIFIERS: for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j
SOURCE_CONCLUSION: (i) X_Lambda(q,p) = (lambda p, -lambda q) is bounded E_{a,p} -> E_{a,p-1} with norm <= sqrt(1+m), not bounded E_{a,p} -> E_{a,p}; (ii) X_G(q,p) = (0, -G_q(q)) is real analytic E_{a,p} -> E_{a,p+1}, ¦¦X_G¦¦ <= C_* ¦¦q¦¦^3, with the bounds of Corollary bpW:w1:cubic-analytic; its complex extension is C-analytic E^C_{a,p} -> E^C_{a,p+1}; (iii) X_H = X_Lambda + X_G is real analytic E_{a,p} -> E_{a,p-1}; (iv) H = Lambda + G is real analytic on E_{a,p}, DH(q,p)(0,e_j) = lambda_j p_j, DH(q,p)(e_j,0) = lambda_j q_j + G_q(q)_j, i.e. X_H = (d_p H, -d_q H), the system (bpW:w0:coeffsys); (v) for a = p = 1, with D = D_mu, mu_j = lambda_j/j, S = D_{(1/j)}, X^w(y,y') = (D y', -D y - S^2 G^w(y)) on WaveSpace represents X_H : E_{1,1} -> E_{1,0}, is real analytic on WaveSpace, and has j-th coordinates omega_{1,0}(j)(lambda_j coeff y' j, -lambda_j coeff y j - cubicGrad m hm y j)
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:H, bpW:w0:eqmotion, bpW:w1:cubic-analytic, bpW:w0:ellap#WaveSpace, bpW:w0:ellap#coeff, bpW:w0:Gq#cubicGrad, stepW:w1:hlin, stepW:w1:hnonlin, stepW:w1:hsum, stepW:w1:hham, stepW:w1:hfrozen, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:H | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L553-L553 | H = Lambda + G
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L555-L555 | the system (bpW:w0:coeffsys)
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L550-L550 | the bounds of the cubic gradient
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L557-L557 | X^w : WaveSpace -> WaveSpace
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L560-L560 | the coordinates in terms of coeff
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L560-L560 | the coordinates in terms of cubicGrad
EDGE: stepW:w1:hlin | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L566-L566 | proof step
EDGE: stepW:w1:hnonlin | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L568-L568 | proof step
EDGE: stepW:w1:hsum | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L571-L571 | proof step
EDGE: stepW:w1:hham | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L574-L574 | proof step
EDGE: stepW:w1:hfrozen | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L581-L581 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:hamfield@L546-L546 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hlin
KIND: step
TITLE: Linear part
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hlin@L566-L567
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hlin@L566-L567
CONTRACT_ID: stepW:w1:hlin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:hamfield: a > 0, p >= 1/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:hamfield (for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i) from Lemma bpW:w1:diag(i)-(ii) with r = 1 componentwise; the max norm is preserved under componentwise bounds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:diag
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:diag | blueprint-W/parts/w1-sequences.tex#stepW:w1:hlin@L567-L567 | (i)-(ii) with r = 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hnonlin
KIND: step
TITLE: Nonlinear part
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L568-L570
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L568-L570
CONTRACT_ID: stepW:w1:hnonlin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:hamfield: a > 0, p >= 1/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:hamfield (for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) from Corollary bpW:w1:cubic-analytic and Theorem bpW:w1:trilinear(iv) in the second component, composed with the projection (q,p) -> q; complex version from (ii) of the theorem
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cubic-analytic, bpW:w1:trilinear
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L569-L569 | analyticity and bounds of N
EDGE: bpW:w1:trilinear | blueprint-W/parts/w1-sequences.tex#stepW:w1:hnonlin@L569-L569 | (iv) identification with G_q and (ii) complex version
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hsum
KIND: step
TITLE: Sum
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L571-L573
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L571-L573
CONTRACT_ID: stepW:w1:hsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:hamfield: a > 0, p >= 1/2; local data: (i), (ii)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:hamfield (for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: X_G maps into E_{a,p+1} subset E_{a,p-1}; a bounded linear plus an analytic map is analytic, giving (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:embed, stepW:w1:hlin, stepW:w1:hnonlin, bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L572-L572 | E_{a,p+1} subset E_{a,p-1}
EDGE: stepW:w1:hlin | blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L573-L573 | X_Lambda bounded linear
EDGE: stepW:w1:hnonlin | blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L573-L573 | X_G analytic
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hsum@L573-L573 | sums of analytic maps
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hham
KIND: step
TITLE: Hamiltonian
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L574-L580
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L574-L580
CONTRACT_ID: stepW:w1:hham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:hamfield: a > 0, p >= 1/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:hamfield (for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j); within the step: (q,p), j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Lambda is the diagonal of beta(q,q') = sum lambda_j q_j q'_j with ¦beta¦ <= sqrt(1+m) ¦¦q¦¦ ¦¦q'¦¦, a bounded quadratic form on E_{a,p}; DLambda(q,p)(h,k) = <lambda q,h>_0 + <lambda p,k>_0; with Proposition bpW:w1:gradient-identity(ii), evaluation at (e_j,0), (0,e_j) gives (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w1:embed, bpW:w1:gradient-identity, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L576-L576 | lambda_j <= sqrt(1+m) j
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L577-L577 | ¦¦q¦¦_{0,1/2} <= ¦¦q¦¦_{a,p} for p >= 1/2
EDGE: bpW:w1:gradient-identity | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L579-L579 | (ii): DG(q)h = <G_q(q),h>_0
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:hham@L575-L575 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hfrozen
KIND: step
TITLE: Frozen form
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L581-L585
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L581-L585
CONTRACT_ID: stepW:w1:hfrozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:hamfield: a > 0, p >= 1/2; local data: a = p = 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:hamfield (for all a > 0, p >= 1/2; (q,p) in E_{a,p}; j); within the step: y, y', j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the coordinates of X_H(kappa y, kappa y') times omega_{1,0}(j) = e^j are (lambda_j/j) y'_j and -(lambda_j/j) y_j - j^{-2} G^w(y)_j; D, S bounded, so X^w is a polynomial map on WaveSpace, analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cubic-analytic, bpW:w1:multiplier, bpW:w0:basis#lambda-facts, bpW:w1:ext-analytic, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L583-L583 | (iv): e^j cubicGrad_j = j^{-2} G^w(y)_j
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L584-L584 | D and S are bounded
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L584-L584 | lambda_j/j <= sqrt(1+m)
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L585-L585 | polynomial maps are analytic
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L582-L582 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L583-L583 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#stepW:w1:hfrozen@L585-L585 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:tricoord#via-cubic-bound
KIND: route
TITLE: Coordinates of the trilinear map via Theorem bpW:w0n:cubic-bound
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L454-L458
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L454-L454
CONTRACT_ID: stepW:w1:tricoord#via-cubic-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as in Step stepW:w1:tricoord
SOURCE_QUANTIFIERS: y, y', y''
SOURCE_CONCLUSION: the conclusion of Step stepW:w1:tricoord
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:cubic-bound
ROUTES: -
ROUTE_FOR: stepW:w1:tricoord
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L454-L454 | absolute convergence and the bound C_*
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:tricoord#via-selection
KIND: route
TITLE: Coordinates of the trilinear map via Lemma bpW:w1:selection(a)
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L454-L458
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L455-L456
CONTRACT_ID: stepW:w1:tricoord#via-selection
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: as in Step stepW:w1:tricoord
SOURCE_QUANTIFIERS: y, y', y''
SOURCE_CONCLUSION: the conclusion of Step stepW:w1:tricoord
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:selection, bpW:w0n:quartic-coeff, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: stepW:w1:tricoord
EDGE: bpW:w1:selection | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L455-L455 | (a) with M = 1/(2pi)
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L456-L456 | the bound after (bpW:w0n:g-signed) gives the hypothesis on c
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:tricoord@L456-L456 | lambda >= j gives the (ijkl)^{-1/2} decay
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: "equivalently Lemma bpW:w1:selection(a) with c_ijkl = g_ijkl (lambda lambda lambda lambda)^{-1/2}, M = 1/(2pi)": the text offers it as a sufficient alternative to cubic-bound.

NODE: bpW:w1:sine-completeness
KIND: lemma
TITLE: Completeness of the sine system
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L593-L596
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L598-L613
CONTRACT_ID: bpW:w1:sine-completeness
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (i) f in L^2(0,pi) with int_0^pi f phi_l = 0 for all l >= 1; (ii) moreover f continuous on [0,pi]
SOURCE_QUANTIFIERS: for all f
SOURCE_CONCLUSION: (i) f = 0 a.e. on (0,pi); (ii) f = 0 on [0,pi]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#sineMode, stepW:w1:odd, stepW:w1:coeffs, stepW:w1:basis, stepW:w1:cont
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L594-L594 | the sine modes phi_l
EDGE: stepW:w1:odd | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L599-L599 | proof step
EDGE: stepW:w1:coeffs | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L602-L602 | proof step
EDGE: stepW:w1:basis | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L606-L606 | proof step
EDGE: stepW:w1:cont | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-completeness@L610-L610 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:odd
KIND: step
TITLE: Odd extension
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:odd@L599-L601
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:odd@L599-L601
CONTRACT_ID: stepW:w1:odd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-completeness: (i) f in L^2(0,pi) with int_0^pi f phi_l = 0 for all l >= 1; (ii) moreover f continuous on [0,pi]
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-completeness (for all f); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the odd extension g of f to R/2piZ lies in L^2 with ¦¦g¦¦^2 = 2¦¦f¦¦^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:coeffs
KIND: step
TITLE: Fourier coefficients vanish
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coeffs@L602-L605
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:coeffs@L602-L605
CONTRACT_ID: stepW:w1:coeffs
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-completeness: (i) f in L^2(0,pi) with int_0^pi f phi_l = 0 for all l >= 1; (ii) moreover f continuous on [0,pi]; local data: the hypothesis of (i)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-completeness (for all f); within the step: n in Z; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: int_{-pi}^{pi} g e^{-inx} = -2i int_0^pi f sin(nx) = 0 for all n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:odd, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:odd | blueprint-W/parts/w1-sequences.tex#stepW:w1:coeffs@L603-L603 | the odd extension g
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#stepW:w1:coeffs@L605-L605 | sin(nx) = sqrt(pi/2) phi_n(x)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:basis
KIND: step
TITLE: Hilbert basis
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L606-L609
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L606-L609
CONTRACT_ID: stepW:w1:basis
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-completeness: (i) f in L^2(0,pi) with int_0^pi f phi_l = 0 for all l >= 1; (ii) moreover f continuous on [0,pi]
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-completeness (for all f); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the Fourier coefficients of g for the normalized Haar measure vanish, so g = 0 in L^2 and f = 0 a.e. on (0,pi)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:coeffs, bpW:w1:ext-fourier
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:coeffs | blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L607-L607 | the vanishing integrals
EDGE: bpW:w1:ext-fourier | blueprint-W/parts/w1-sequences.tex#stepW:w1:basis@L608-L608 | the characters form a Hilbert basis (injective coefficient map)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cont@L610-L612
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:cont@L610-L612
CONTRACT_ID: stepW:w1:cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-completeness: (i) f in L^2(0,pi) with int_0^pi f phi_l = 0 for all l >= 1; (ii) moreover f continuous on [0,pi]
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-completeness (for all f); within the step: x_0 in [0,pi]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: f(x_0) != 0 would give ¦f¦ > ¦f(x_0)¦/2 on a subinterval of positive length, contradicting (i); so f = 0 on [0,pi]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:basis
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:basis | blueprint-W/parts/w1-sequences.tex#stepW:w1:cont@L612-L612 | (i): f = 0 a.e.
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:sine-feature
KIND: lemma
TITLE: Analytic sine features
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L617-L629
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L631-L645
CONTRACT_ID: bpW:w1:sine-feature
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a > 0, p in R, k in N; beta : N_+ -> R with ¦beta_j¦ <= B j^nu for some B, nu >= 0; Psi(x)_j = beta_j phi_j^(k)(x)/omega_{a,p}(j), phi_j^(k)(x) = sqrt(2/pi) j^k sin^(k)(jx), for x in C with ¦Im x¦ < a
SOURCE_QUANTIFIERS: for all a > 0, p, k, beta, B, nu; (i) for 0 < a' < a; (iii) for real x, y in l^2_R
SOURCE_CONCLUSION: (i) with b_j = sqrt(2/pi) B j^{nu+k-p} e^{-(a-a')j}, ¦Psi(x)_j¦ <= b_j for ¦Im x¦ <= a' and sum b_j < infinity; (ii) Psi is holomorphic on {¦Im x¦ < a}, hence C-analytic there, real for real x, and Psi_R = re o Psi¦_R : R -> l^2_R is real analytic; (iii) <Psi_R(x),y> = sum_j beta_j (kappa_{a,p} y)_j phi_j^(k)(x), absolutely convergent
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#sineMode, bpW:w1:transport, stepW:w1:growth, stepW:w1:normal, stepW:w1:sinereal
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L620-L620 | the modes phi_j and their derivatives
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L620-L620 | the weights omega_{a,p} and kappa_{a,p}
EDGE: stepW:w1:growth | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L632-L632 | proof step
EDGE: stepW:w1:normal | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L636-L636 | proof step
EDGE: stepW:w1:sinereal | blueprint-W/parts/w1-sequences.tex#bpW:w1:sine-feature@L641-L641 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:growth
KIND: step
TITLE: Growth on the strip
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:growth@L632-L635
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:growth@L632-L635
CONTRACT_ID: stepW:w1:growth
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-feature: a > 0, p in R, k in N; beta : N_+ -> R with ¦beta_j¦ <= B j^nu for some B, nu >= 0; Psi(x)_j = beta_j phi_j^(k)(x)/omega_{a,p}(j), phi_j^(k)(x) = sqrt(2/pi) j^k sin^(k)(jx), for x in C with ¦Im x¦ < a; local data: ¦Im x¦ <= a' < a
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-feature (for all a > 0, p, k, beta, B, nu; (i) for 0 < a' < a; (iii) for real x, y in l^2_R); within the step: j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦sin^(k)(jx)¦ <= e^{j¦Im x¦}, so ¦Psi(x)_j¦ <= b_j, and sum b_j < infinity since a - a' > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:normal
KIND: step
TITLE: Normal convergence
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L636-L640
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L636-L640
CONTRACT_ID: stepW:w1:normal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-feature: a > 0, p in R, k in N; beta : N_+ -> R with ¦beta_j¦ <= B j^nu for some B, nu >= 0; Psi(x)_j = beta_j phi_j^(k)(x)/omega_{a,p}(j), phi_j^(k)(x) = sqrt(2/pi) j^k sin^(k)(jx), for x in C with ¦Im x¦ < a
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-feature (for all a > 0, p, k, beta, B, nu; (i) for 0 < a' < a; (iii) for real x, y in l^2_R); within the step: N; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the partial sums Psi^N are holomorphic and converge to Psi uniformly on ¦Im x¦ <= a', hence locally uniformly on the strip; Psi is holomorphic and analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:growth, bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:growth | blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L638-L638 | the tail bound sum_{j>N} b_j
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:normal@L640-L640 | locally uniform limits of holomorphic maps are holomorphic; holomorphic on open subsets of C implies analytic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:sinereal
KIND: step
TITLE: Real restriction
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L641-L644
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L641-L644
CONTRACT_ID: stepW:w1:sinereal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:sine-feature: a > 0, p in R, k in N; beta : N_+ -> R with ¦beta_j¦ <= B j^nu for some B, nu >= 0; Psi(x)_j = beta_j phi_j^(k)(x)/omega_{a,p}(j), phi_j^(k)(x) = sqrt(2/pi) j^k sin^(k)(jx), for x in C with ¦Im x¦ < a
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:sine-feature (for all a > 0, p, k, beta, B, nu; (i) for 0 < a' < a; (iii) for real x, y in l^2_R); within the step: real x, y; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Psi(x) = iota Psi_R(x) for real x and Psi_R = re o Psi o (R -> C) is real analytic; (iii) by lp.inner_eq_tsum and y_j/omega(j) = (kappa y)_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:complexification-lemma, bpW:w1:ext-lp, bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:complexification-lemma | blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L643-L643 | (ii): R-analyticity of re o f o l
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L643-L643 | the inner product of l^2 as a tsum
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:sinereal@L644-L644 | kappa_{a,p}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:recon-analytic
KIND: corollary
TITLE: Analytic reconstruction
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L648-L670
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L672-L692
CONTRACT_ID: bpW:w1:recon-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: k in N; Psi^{U,k}_R, Psi^{V,k}_R the real feature maps of Lemma bpW:w1:sine-feature with a = p = 1 and beta_j = lambda_j^{-1/2}, resp. lambda_j^{1/2}; U^(k)_y(x) = <Psi^{U,k}_R(x),y> = sum coeff y j/sqrt(lambda_j) phi_j^(k)(x), V^(k)_y(x) = sum sqrt(lambda_j) coeff y j phi_j^(k)(x) for y in l^2_R, x in R; (iii) S a real normed space and Y : S -> l^2_R real analytic at s_0
SOURCE_QUANTIFIERS: for all k, y, real x; (iii) for all S, Y, s_0, x_0
SOURCE_CONCLUSION: the series converge absolutely; (i) U^(0)_y(x) = reconU m hm y x and V^(0)_y(x) = reconV m hm y x; (ii) x -> U^(k)_y(x) has derivative U^(k+1)_y(x) (HasDerivAt), likewise V; U^(k)_y is the k-th derivative of reconU m hm y (iteratedDeriv k), and derivWithin (reconU m hm y) (Icc 0 pi) x = U^(1)_y(x) for x in [0,pi]; (iii) (s,x) -> U^(k)_{Y(s)}(x) and V^(k)_{Y(s)}(x) are real analytic on S x R at (s_0,x_0); in particular for S = R^n the iterated x-derivatives of reconU m hm (Y s) and reconV m hm (Y s) are real analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, bpW:w0:basis#lam, bpW:w0:ellap#coeff, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, stepW:w1:bil, stepW:w1:recanalytic, stepW:w1:recder, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L650-L650 | the feature maps
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L650-L650 | beta_j = lambda_j^{+-1/2}
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L652-L652 | coeff y j in the series
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L656-L656 | the frozen reconU in (i), (ii)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L656-L656 | the frozen reconV in (i)
EDGE: stepW:w1:bil | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L673-L673 | proof step
EDGE: stepW:w1:recanalytic | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L677-L677 | proof step
EDGE: stepW:w1:recder | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L683-L683 | proof step
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#bpW:w1:recon-analytic@L652-L652 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:bil
KIND: step
TITLE: Bilinear form
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L673-L676
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L673-L676
CONTRACT_ID: stepW:w1:bil
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:recon-analytic: k in N; Psi^{U,k}_R, Psi^{V,k}_R the real feature maps of Lemma bpW:w1:sine-feature with a = p = 1 and beta_j = lambda_j^{-1/2}, resp. lambda_j^{1/2}; U^(k)_y(x) = <Psi^{U,k}_R(x),y> = sum coeff y j/sqrt(lambda_j) phi_j^(k)(x), V^(k)_y(x) = sum sqrt(lambda_j) coeff y j phi_j^(k)(x) for y in l^2_R, x in R; (iii) S a real normed space and Y : S -> l^2_R real analytic at s_0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:recon-analytic (for all k, y, real x; (iii) for all S, Y, s_0, x_0); within the step: y, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦beta_j¦ <= (1+m)^{1/4} j^{1/2}, so Lemma bpW:w1:sine-feature applies; (iii) gives the series forms and absolute convergence; for k = 0 the series is the frozen tsum termwise, which is (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, bpW:w0:basis#lambda-facts, bpW:w0:ellap#coeff, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L674-L674 | (iii) and its hypothesis ¦beta_j¦ <= B j^nu
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L674-L674 | lambda_j^{+-1/2} <= (1+m)^{1/4} j^{1/2}
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L675-L675 | coeff y j = (kappa_{1,1} y)_j
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L676-L676 | the frozen tsum of reconU
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w1-sequences.tex#stepW:w1:bil@L676-L676 | the frozen tsum of reconV
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:recanalytic
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L677-L682
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L677-L682
CONTRACT_ID: stepW:w1:recanalytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:recon-analytic: k in N; Psi^{U,k}_R, Psi^{V,k}_R the real feature maps of Lemma bpW:w1:sine-feature with a = p = 1 and beta_j = lambda_j^{-1/2}, resp. lambda_j^{1/2}; U^(k)_y(x) = <Psi^{U,k}_R(x),y> = sum coeff y j/sqrt(lambda_j) phi_j^(k)(x), V^(k)_y(x) = sum sqrt(lambda_j) coeff y j phi_j^(k)(x) for y in l^2_R, x in R; (iii) S a real normed space and Y : S -> l^2_R real analytic at s_0; local data: Y analytic at s_0; Psi^{U,k}_R analytic
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:recon-analytic (for all k, y, real x; (iii) for all S, Y, s_0, x_0); within the step: (s_0,x_0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the composite of the continuous bilinear inner product with the analytic pair (Psi^{U,k}_R(x), Y(s)) is analytic at (s_0,x_0); this is (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L680-L680 | (ii): Psi_R is analytic
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:recanalytic@L679-L679 | bilinear maps, pairs and compositions of analytic maps are analytic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:recder
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L683-L691
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L683-L691
CONTRACT_ID: stepW:w1:recder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:recon-analytic: k in N; Psi^{U,k}_R, Psi^{V,k}_R the real feature maps of Lemma bpW:w1:sine-feature with a = p = 1 and beta_j = lambda_j^{-1/2}, resp. lambda_j^{1/2}; U^(k)_y(x) = <Psi^{U,k}_R(x),y> = sum coeff y j/sqrt(lambda_j) phi_j^(k)(x), V^(k)_y(x) = sum sqrt(lambda_j) coeff y j phi_j^(k)(x) for y in l^2_R, x in R; (iii) S a real normed space and Y : S -> l^2_R real analytic at s_0; local data: Psi^{U,k}_R analytic
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:recon-analytic (for all k, y, real x; (iii) for all S, Y, s_0, x_0); within the step: k, y, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (Psi^{U,k}_R)' = Psi^{U,k+1}_R coordinatewise, so d/dx U^(k)_y = U^(k+1)_y; iterating from (i) gives the iterated derivatives of reconU m hm y; at x in [0,pi] the derivative within [0,pi] equals the two-sided derivative (uniqueDiffOn_Icc); the same for V; this is (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, bpW:w1:ext-analytic, bpW:w1:space, stepW:w1:bil, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L684-L684 | (ii): Psi_R analytic, hence differentiable
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L684-L684 | analytic maps are differentiable
EDGE: bpW:w1:space | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L686-L686 | (ii): coordinate evaluation is continuous linear
EDGE: stepW:w1:bil | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L689-L689 | (i): U^(0)_y = reconU m hm y
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L687-L687 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w1-sequences.tex#stepW:w1:recder@L688-L688 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:complexification
KIND: definition
TITLE: Complexification
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification@L698-L703
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:complexification
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: l^2_R, l^2_C and products
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines iota : l^2_R -> l^2_C, re : l^2_C -> l^2_R, conjugation, componentwise on products (E^C_{a,p} represented by (l^2_C)^2), and: f is real on reals if f(iota y) in iota(l^2_R) whenever defined
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:complexification-lemma
KIND: lemma
TITLE: Complexification and real analyticity
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L707-L718
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L720-L725
CONTRACT_ID: bpW:w1:complexification-lemma
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: (ii) F_1, F_2 complex Banach, V real normed, l : V -> F_1 and pi : F_2 -> W continuous R-linear, f C-analytic at l(x); (iii) f defined near iota y, C-analytic at iota y and real on reals near iota y
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: (i) iota, re are continuous R-linear, ¦¦iota y¦¦ = ¦¦y¦¦, ¦¦re z¦¦ <= ¦¦z¦¦, re o iota = id, ¦¦iota y + i iota y'¦¦^2 = ¦¦y¦¦^2 + ¦¦y'¦¦^2, conjugation is a conjugate-linear isometry, and all commute with tau, kappa and real multipliers; (ii) pi o f o l is R-analytic at x; (iii) g = re o f o iota is R-analytic at y, iota o g = f o iota near y, and Dg(y)h = re Df(iota y) iota h
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:complexification, bpW:w1:transport, bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L709-L709 | iota, re, conjugation
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L711-L711 | commutation with tau, kappa
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#bpW:w1:complexification-lemma@L722-L722 | C-analytic is R-analytic; composition with continuous linear maps
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:holomorphic
KIND: definition
TITLE: Holomorphic maps on Banach domains
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holomorphic@L728-L734
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:holomorphic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: F_1, F_2 complex Banach spaces, U subset F_1 open
SOURCE_QUANTIFIERS: f : U -> F_2
SOURCE_CONCLUSION: defines: f is holomorphic iff complex Frechet differentiable at every point of U (DifferentiableOn C f U); bounds are hypotheses ¦¦f(z)¦¦ <= M for z in U, never an unguarded supremum
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:cauchy
KIND: lemma
TITLE: Cauchy estimate
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L737-L742
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L744-L752
CONTRACT_ID: bpW:w1:cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r > 0, M >= 0, f holomorphic on B(v,r) subset F_1 with ¦¦f(z)¦¦ <= M there; for the consequences delta > 0, f holomorphic on open V with ¦¦f¦¦ <= M, B(w,delta) subset V, C convex with C + B(0,delta) subset V
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: ¦¦Df(v)¦¦ <= M/r; ¦¦Df(w)¦¦ <= M/delta; f is (M/delta)-Lipschitz on C
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, stepW:w1:lines, stepW:w1:onevar, stepW:w1:margins
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L738-L738 | holomorphic maps on Banach domains
EDGE: stepW:w1:lines | blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L745-L745 | proof step
EDGE: stepW:w1:onevar | blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L748-L748 | proof step
EDGE: stepW:w1:margins | blueprint-W/parts/w1-sequences.tex#bpW:w1:cauchy@L750-L750 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:lines
KIND: step
TITLE: Complex lines
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:lines@L745-L747
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:lines@L745-L747
CONTRACT_ID: stepW:w1:lines
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cauchy: r > 0, M >= 0, f holomorphic on B(v,r) subset F_1 with ¦¦f(z)¦¦ <= M there; for the consequences delta > 0, f holomorphic on open V with ¦¦f¦¦ <= M, B(w,delta) subset V, C convex with C + B(0,delta) subset V; local data: u in F_1, ¦¦u¦¦ = 1, 0 < r' < r
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cauchy (for all such data); within the step: u, r'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: phi(zeta) = f(v + zeta u) is holomorphic on ¦zeta¦ < r', continuous on ¦zeta¦ <= r', phi'(0) = Df(v)u, ¦¦phi¦¦ <= M
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:onevar
KIND: step
TITLE: One-variable estimate
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L748-L749
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L748-L749
CONTRACT_ID: stepW:w1:onevar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cauchy: r > 0, M >= 0, f holomorphic on B(v,r) subset F_1 with ¦¦f(z)¦¦ <= M there; for the consequences delta > 0, f holomorphic on open V with ¦¦f¦¦ <= M, B(w,delta) subset V, C convex with C + B(0,delta) subset V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cauchy (for all such data); within the step: u; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦Df(v)u¦¦ <= M/r'; letting r' -> r and taking sup over u, ¦¦Df(v)¦¦ <= M/r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:lines, bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:lines | blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L749-L749 | the one-variable function phi
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:onevar@L749-L749 | the Cauchy estimate in one variable
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:margins
KIND: step
TITLE: Margins
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L750-L751
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L750-L751
CONTRACT_ID: stepW:w1:margins
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:cauchy: r > 0, M >= 0, f holomorphic on B(v,r) subset F_1 with ¦¦f(z)¦¦ <= M there; for the consequences delta > 0, f holomorphic on open V with ¦¦f¦¦ <= M, B(w,delta) subset V, C convex with C + B(0,delta) subset V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:cauchy (for all such data); within the step: w, C; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: apply on B(w,delta) for ¦¦Df(w)¦¦ <= M/delta; the Lipschitz bound on C by the mean value inequality
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:onevar, bpW:w1:ext-unifderiv
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L751-L751 | the estimate on balls
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w1-sequences.tex#stepW:w1:margins@L751-L751 | the mean value inequality on convex sets
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:deriv-continuous
KIND: lemma
TITLE: Derivatives of holomorphic maps are continuous
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L755-L760
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L762-L775
CONTRACT_ID: bpW:w1:deriv-continuous
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset F_1 open, f : U -> F_2 holomorphic; w_0 in U, rho > 0, B >= 0 with B(w_0,2rho) subset U and ¦¦f¦¦ <= B on B(w_0,2rho)
SOURCE_QUANTIFIERS: for all such data; w, w' in B(w_0,rho/2)
SOURCE_CONCLUSION: ¦¦Df(w) - Df(w')¦¦ <= 2 B rho^{-2} ¦¦w - w'¦¦; such rho, B exist for every w_0, so Df : U -> L(F_1,F_2) is continuous (ContinuousOn (fderiv C f) U)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, stepW:w1:dcbound, stepW:w1:dcintegral, stepW:w1:dclip
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L756-L756 | holomorphic maps
EDGE: stepW:w1:dcbound | blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L763-L763 | proof step
EDGE: stepW:w1:dcintegral | blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L765-L765 | proof step
EDGE: stepW:w1:dclip | blueprint-W/parts/w1-sequences.tex#bpW:w1:deriv-continuous@L769-L769 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:dcbound
KIND: step
TITLE: Existence of $\rho$, $B$
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcbound@L763-L764
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcbound@L763-L764
CONTRACT_ID: stepW:w1:dcbound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:deriv-continuous: U subset F_1 open, f : U -> F_2 holomorphic; w_0 in U, rho > 0, B >= 0 with B(w_0,2rho) subset U and ¦¦f¦¦ <= B on B(w_0,2rho); local data: f continuous at w_0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:deriv-continuous (for all such data; w, w' in B(w_0,rho/2)); within the step: w_0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦f(z)¦¦ <= ¦¦f(w_0)¦¦ + 1 =: B on some ball B(w_0,2rho) subset U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:dcintegral
KIND: step
TITLE: Cauchy integral along lines
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcintegral@L765-L768
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dcintegral@L765-L768
CONTRACT_ID: stepW:w1:dcintegral
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:deriv-continuous: U subset F_1 open, f : U -> F_2 holomorphic; w_0 in U, rho > 0, B >= 0 with B(w_0,2rho) subset U and ¦¦f¦¦ <= B on B(w_0,2rho); local data: w in B(w_0,rho/2), ¦¦u¦¦ = 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:deriv-continuous (for all such data; w, w' in B(w_0,rho/2)); within the step: w, u; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: phi(zeta) = f(w + zeta u) is holomorphic for ¦zeta¦ < 3rho/2 and Df(w)u = (1/(2 pi i)) oint_{¦zeta¦=rho/2} f(w + zeta u) zeta^{-2} dzeta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:dcintegral@L767-L767 | the Cauchy integral formula for phi'(0)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:dclip
KIND: step
TITLE: Lipschitz difference
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L769-L774
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L769-L774
CONTRACT_ID: stepW:w1:dclip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:deriv-continuous: U subset F_1 open, f : U -> F_2 holomorphic; w_0 in U, rho > 0, B >= 0 with B(w_0,2rho) subset U and ¦¦f¦¦ <= B on B(w_0,2rho)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:deriv-continuous (for all such data; w, w' in B(w_0,rho/2)); within the step: w, w', u; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦Df¦¦ <= B/rho on B(w_0,rho), so the integrands differ by at most (B/rho)¦¦w - w'¦¦; subtracting the Cauchy integrals gives ¦¦(Df(w) - Df(w'))u¦¦ <= 2 B rho^{-2} ¦¦w - w'¦¦; sup over u
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cauchy, stepW:w1:dcintegral, stepW:w1:dcbound
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L771-L771 | margin rho inside B(w_0,2rho)
EDGE: stepW:w1:dcintegral | blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L772-L772 | the two Cauchy integrals
EDGE: stepW:w1:dcbound | blueprint-W/parts/w1-sequences.tex#stepW:w1:dclip@L771-L771 | the bound B on B(w_0,2rho)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:uniform-limit
KIND: lemma
TITLE: Uniform limits
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L778-L786
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L788-L798
CONTRACT_ID: bpW:w1:uniform-limit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset F_1 open, f_k : U -> F_2 holomorphic, f_k -> f uniformly on U; (ii) moreover M >= 0 with ¦¦f(z)¦¦ <= M on U
SOURCE_QUANTIFIERS: for all such data; (i) balls B(w,delta), delta > 0, B(w,2delta) subset U; (ii) delta > 0 with B(w,delta) subset U
SOURCE_CONCLUSION: (i) f is holomorphic on U and Df_k -> Df uniformly on every such B(w,delta); if every f_k is real on reals, so is f; no boundedness of f assumed; (ii) ¦¦Df(w)¦¦ <= M/delta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, bpW:w1:complexification, stepW:w1:ulcauchy, stepW:w1:ullimit
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L779-L779 | holomorphic maps
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L782-L782 | real on reals
EDGE: stepW:w1:ulcauchy | blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L789-L789 | proof step
EDGE: stepW:w1:ullimit | blueprint-W/parts/w1-sequences.tex#bpW:w1:uniform-limit@L794-L794 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:ulcauchy
KIND: step
TITLE: Cauchy in derivatives
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ulcauchy@L789-L793
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ulcauchy@L789-L793
CONTRACT_ID: stepW:w1:ulcauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:uniform-limit: U subset F_1 open, f_k : U -> F_2 holomorphic, f_k -> f uniformly on U; (ii) moreover M >= 0 with ¦¦f(z)¦¦ <= M on U; local data: eps > 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:uniform-limit (for all such data; (i) balls B(w,delta), delta > 0, B(w,2delta) subset U; (ii) delta > 0 with B(w,delta) subset U); within the step: w' in B(w,delta); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (Df_k) is uniformly Cauchy on B(w,delta) in the complete space of bounded C-linear maps, with a uniform limit g
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:ulcauchy@L791-L791 | applied to f_k - f_l with bound eps
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:ullimit
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L794-L797
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L794-L797
CONTRACT_ID: stepW:w1:ullimit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:uniform-limit: U subset F_1 open, f_k : U -> F_2 holomorphic, f_k -> f uniformly on U; (ii) moreover M >= 0 with ¦¦f(z)¦¦ <= M on U
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:uniform-limit (for all such data; (i) balls B(w,delta), delta > 0, B(w,2delta) subset U; (ii) delta > 0 with B(w,delta) subset U); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: f is C-differentiable on the ball with Df = g, hence holomorphic on U; real on reals since iota(l^2_R) is closed; (ii) is the Cauchy estimate for f
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:ulcauchy, bpW:w1:ext-unifderiv, bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:ulcauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L795-L795 | the uniform limit g of Df_k
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L795-L795 | uniform limits of derivatives
EDGE: bpW:w1:cauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:ullimit@L797-L797 | (ii) applied to f itself
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:holo-analytic-fd
KIND: lemma
TITLE: Holomorphic maps of finitely many variables are analytic
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L801-L811
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L813-L836
CONTRACT_ID: bpW:w1:holo-analytic-fd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: U subset C^n open (max norm), F complex Banach, f : U -> F holomorphic; for the quantitative part n >= 1, r > 0 with bar P(z_0,r) subset U; for the real part F = E^C_{a,p} and f real on reals at the real points of U
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: f is C-analytic on U (AnalyticOnNhd C f U; n = 0 trivial); there are r_1 > r and M_1 >= 0 with bar P(z_0,r_1) subset U, ¦¦f¦¦ <= M_1 there, and f = sum_alpha c_alpha (z - z_0)^alpha absolutely on P(z_0,r_1) with ¦¦c_alpha¦¦ <= M_1 r_1^{-¦alpha¦}; grouped by degree a FormalMultilinearSeries (p_m) with ¦¦p_m¦¦ <= binom(m+n-1,n-1) M_1 r_1^{-m} and HasFPowerSeriesOnBall f p z_0 r_1; re o f¦_{U cap R^n} is real analytic into E_{a,p}
CONSTANT_SCOPE: r_1, M_1 depend on f, z_0, r
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, bpW:w1:complexification, stepW:w1:hamargin, stepW:w1:hacoef, stepW:w1:hagroup, stepW:w1:hareal
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L802-L802 | holomorphic maps
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L809-L809 | real on reals
EDGE: stepW:w1:hamargin | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L814-L814 | proof step
EDGE: stepW:w1:hacoef | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L817-L817 | proof step
EDGE: stepW:w1:hagroup | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L824-L824 | proof step
EDGE: stepW:w1:hareal | blueprint-W/parts/w1-sequences.tex#bpW:w1:holo-analytic-fd@L834-L834 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hamargin
KIND: step
TITLE: Margin
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hamargin@L814-L816
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hamargin@L814-L816
CONTRACT_ID: stepW:w1:hamargin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:holo-analytic-fd: U subset C^n open (max norm), F complex Banach, f : U -> F holomorphic; for the quantitative part n >= 1, r > 0 with bar P(z_0,r) subset U; for the real part F = E^C_{a,p} and f real on reals at the real points of U; local data: bar P(z_0,r) subset U compact, U open
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:holo-analytic-fd (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: bar P(z_0,r_1) subset U for some r_1 > r, and f is bounded by some M_1 on the compact bar P(z_0,r_1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hacoef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L817-L823
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L817-L823
CONTRACT_ID: stepW:w1:hacoef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:holo-analytic-fd: U subset C^n open (max norm), F complex Banach, f : U -> F holomorphic; for the quantitative part n >= 1, r > 0 with bar P(z_0,r) subset U; for the real part F = E^C_{a,p} and f real on reals at the real points of U; local data: F complete
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:holo-analytic-fd (for all such data); within the step: alpha in N^n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: there are c_alpha in F with ¦¦c_alpha¦¦ <= M_1 r_1^{-¦alpha¦} and f(z) = sum_alpha c_alpha (z - z_0)^alpha absolutely on P(z_0,r_1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:hamargin, K:bp:p1:holomorphic-analytic, bpW:w1:ext-onevar, bpW:w1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:hamargin | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L819-L819 | the radius r_1 and the bound M_1
EDGE: K:bp:p1:holomorphic-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L818-L818 | K's Cauchy-coefficient argument (steps han-cauchy..han-bounds), applied with W replaced by the complete F
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L821-L821 | the one-variable Cauchy formula for complete F
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L823-L823 | Fubini and termwise integration of Bochner integrals on the torus
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Uses the proof of track K's Lemma bp:p1:holomorphic-analytic (steps han-cauchy to han-bounds) with radius r_1 and K's target W replaced by the complete space F (a carrier change); the text justifies the transfer (L821-L823: only the one-variable Cauchy formula for complete F and Bochner integration on the domain torus are used). Reviewer: check that the import and the two externals cover the transfer.

NODE: stepW:w1:hagroup
KIND: step
TITLE: Degree grouping
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L824-L833
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L824-L833
CONTRACT_ID: stepW:w1:hagroup
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:holo-analytic-fd: U subset C^n open (max norm), F complex Banach, f : U -> F holomorphic; for the quantitative part n >= 1, r > 0 with bar P(z_0,r) subset U; for the real part F = E^C_{a,p} and f real on reals at the real points of U
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:holo-analytic-fd (for all such data); within the step: m >= 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: p_m(h_1..h_m) = sum_{¦alpha¦=m} (prod (h_l)_{iota_alpha(l)}) c_alpha is a continuous m-linear map with ¦¦p_m¦¦ <= binom(m+n-1,n-1) M_1 r_1^{-m}; sum ¦¦p_m¦¦ rho^m < infinity for rho < r_1; regrouping gives HasFPowerSeriesOnBall f p z_0 r_1; f is analytic at every point of U
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:hacoef, bpW:w3:ext-tsum, bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:hacoef | blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L829-L829 | the coefficients c_alpha and their bounds
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L831-L831 | regrouping an absolutely convergent multi-index series by degree
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w1-sequences.tex#stepW:w1:hagroup@L832-L832 | a power series with positive radius gives analyticity (HasFPowerSeriesOnBall)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:hareal
KIND: step
TITLE: Real points
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hareal@L834-L835
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:hareal@L834-L835
CONTRACT_ID: stepW:w1:hareal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:holo-analytic-fd: U subset C^n open (max norm), F complex Banach, f : U -> F holomorphic; for the quantitative part n >= 1, r > 0 with bar P(z_0,r) subset U; for the real part F = E^C_{a,p} and f real on reals at the real points of U; local data: F = E^C_{a,p}, f real on reals
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:holo-analytic-fd (for all such data); within the step: real points; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: re o f¦_{U cap R^n} is real analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:complexification-lemma
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:complexification-lemma | blueprint-W/parts/w1-sequences.tex#stepW:w1:hareal@L835-L835 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:torus-analytic
KIND: corollary
TITLE: Real-analytic tori from complex strips
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L839-L844
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L846-L849
CONTRACT_ID: bpW:w1:torus-analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: s > 0, T_s = {theta in C^2 : max_i ¦Im theta_i¦ < s}; tilde K : T_s -> E^C_{1,1} holomorphic, real on reals, 1-periodic
SOURCE_QUANTIFIERS: for all such s, tilde K
SOURCE_CONCLUSION: K = re o tilde K¦_{R^2} : R^2 -> WaveSpace satisfies AnalyticOnNhd R K univ, is Z^2-periodic, and fderiv R K theta h = re D tilde K(theta) h for h in R^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holo-analytic-fd, bpW:w1:complexification-lemma, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holo-analytic-fd | blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L847-L847 | with U = T_s
EDGE: bpW:w1:complexification-lemma | blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L847-L847 | (iii): real restriction and its derivative
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w1-sequences.tex#bpW:w1:torus-analytic@L841-L841 | K takes values in WaveSpace (E_{1,1})
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:flow
KIND: lemma
TITLE: Holomorphic flows
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L852-L866
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L868-L902
CONTRACT_ID: bpW:w1:flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for all such data; w in U, t in [-1,1]
SOURCE_CONCLUSION: (i) a unique C^1 curve t -> phi^t(w), t in [-1,1], phi^0(w) = w, d/dt phi^t = X(phi^t), values in V, with ¦¦phi^t(w) - w¦¦ <= ¦t¦M <= M; (ii) w -> phi^t(w) is holomorphic on U with ¦¦D phi^t(w)¦¦ <= e^{L¦t¦}; (iii) phi^t is real on reals; (iv) ¦¦phi^t(w,xi) - phi^t(w,zeta)¦¦ <= ¦t¦ e^{L¦t¦} N
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, bpW:w1:complexification, stepW:w1:flowlip, stepW:w1:picard, stepW:w1:picardholo, stepW:w1:flowlim, stepW:w1:flowreal, stepW:w1:flowpar, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L853-L853 | holomorphic fields
EDGE: bpW:w1:complexification | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L861-L861 | real on reals
EDGE: stepW:w1:flowlip | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L869-L869 | proof step
EDGE: stepW:w1:picard | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L872-L872 | proof step
EDGE: stepW:w1:picardholo | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L876-L876 | proof step
EDGE: stepW:w1:flowlim | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L889-L889 | proof step
EDGE: stepW:w1:flowreal | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L895-L895 | proof step
EDGE: stepW:w1:flowpar | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L897-L897 | proof step
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#bpW:w1:flow@L857-L857 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:flowlip
KIND: step
TITLE: Lipschitz region
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlip@L869-L871
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlip@L869-L871
CONTRACT_ID: stepW:w1:flowlip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V; local data: w in U, w' in B(w,delta)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); within the step: w, w'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦DX(w')¦¦ <= L and X is L-Lipschitz on the convex ball B(w,delta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cauchy | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlip@L871-L871 | margin delta inside B(w,2delta) subset V
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:picard
KIND: step
TITLE: Picard iterates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L872-L875
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L872-L875
CONTRACT_ID: stepW:w1:picard
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); within the step: k, w, t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the Picard iterates phi_k stay in B(w,delta) (¦¦phi_k - w¦¦ <= ¦t¦M < delta), are continuous in (w,t), and ¦¦phi_{k+1} - phi_k¦¦ <= M L^k ¦t¦^{k+1}/(k+1)! uniformly in w
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:flowlip, bpW:w1:ext-integral, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:flowlip | blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L875-L875 | L-Lipschitz on B(w,delta)
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L873-L873 | the integral equation (Bochner integral)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#stepW:w1:picard@L873-L873 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:picardholo
KIND: step
TITLE: Holomorphy of the iterates
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L876-L888
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L876-L888
CONTRACT_ID: stepW:w1:picardholo
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: by induction w -> phi_k(w,t) is holomorphic on U, ¦¦D_w phi_k¦¦ <= sum_{i<=k} (L¦t¦)^i/i! <= e^{L¦t¦}, t -> D_w phi_k continuous; differentiation under the integral with domination L e^L
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:deriv-continuous, bpW:w1:ext-integral, stepW:w1:flowlip, stepW:w1:picard, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:deriv-continuous | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L881-L881 | DX is continuous on V
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L883-L883 | differentiation under the integral (hasFDerivAt_integral_of_dominated_of_fderiv_le)
EDGE: stepW:w1:flowlip | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L884-L884 | ¦¦DX¦¦ <= L on B(w,delta)
EDGE: stepW:w1:picard | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L879-L879 | the iterates and their continuity
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#stepW:w1:picardholo@L877-L877 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:flowlim
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L889-L894
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L889-L894
CONTRACT_ID: stepW:w1:flowlim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); within the step: w, t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the iterates converge uniformly to phi, a C^1 solution of the integral equation; uniqueness among solutions in V; phi^t holomorphic with the derivative bound; this proves (i), (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:picard, bpW:w1:ext-ode, bpW:w1:uniform-limit, stepW:w1:picardholo, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:picard | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L890-L890 | geometric convergence of the iterates
EDGE: bpW:w1:ext-ode | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L891-L891 | uniqueness of ODE solutions for Lipschitz fields
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L893-L893 | holomorphy of the uniform limit
EDGE: stepW:w1:picardholo | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L893-L893 | holomorphy and bounds of the iterates
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowlim@L893-L893 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:flowreal
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowreal@L895-L896
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowreal@L895-L896
CONTRACT_ID: stepW:w1:flowreal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: every Picard iterate of a real point is real and the real subspace is closed, so phi^t is real on reals
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:picard, stepW:w1:flowlim
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:picard | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowreal@L896-L896 | the Picard iterates
EDGE: stepW:w1:flowlim | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowreal@L896-L896 | phi is their limit
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:flowpar
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L897-L901
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L897-L901
CONTRACT_ID: stepW:w1:flowpar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:flow: F complex Banach, V subset F open, X : V -> F holomorphic with ¦¦X(z)¦¦ <= M on V; U subset V open with B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with ¦¦X(z,xi) - X(z,zeta)¦¦ <= N on V
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:flow (for all such data; w in U, t in [-1,1]); within the step: w, t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: psi^t = phi^t(w,xi) - phi^t(w,zeta) satisfies ¦¦dpsi/dt¦¦ <= N + L¦¦psi¦¦, psi^0 = 0, so ¦¦psi^t¦¦ <= N(e^{L¦t¦} - 1)/L <= ¦t¦ e^{L¦t¦} N (both curves stay in the convex ball B(w,delta))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:flowlip, stepW:w1:flowlim, bpW:w1:ext-ode, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:flowlip | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L899-L899 | X(.,zeta) is L-Lipschitz on B(w,delta)
EDGE: stepW:w1:flowlim | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L898-L898 | both trajectories lie in B(w,delta) by (i)
EDGE: bpW:w1:ext-ode | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L900-L900 | Gronwall's inequality
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w1-sequences.tex#stepW:w1:flowpar@L898-L898 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:kam-space
KIND: definition
TITLE: KAM phase space, domains, norms
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-space@L916-L928
PROOF_SOURCE: -
CONTRACT_ID: bpW:w1:kam-space
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a >= 0, p in R, bar p; s, r > 0
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines P^{a,p}_C = C^2 x C^2 x l^{a,p}_C x l^{a,p}_C (points (theta,y,u,v), weighted coordinates, max norm on C^2), D(s,r) = {max ¦Im theta_i¦ < s, ¦y¦ < r^2, ¦¦u¦¦_{a,p} + ¦¦v¦¦_{a,p} < r}, ¦W¦_{bar p,r} = ¦Theta¦ + ¦Y¦/r^2 + ¦¦U¦¦_{a,bar p}/r + ¦¦V¦¦_{a,bar p}/r, the operator norm ¦L¦_{r,s}, and period one: x = 2 pi theta is P96-K's angle, a strip ¦Im x¦ < s_K is ¦Im theta¦ < s_K/(2pi), theta-components are (2pi)^{-1} times x-components
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-space@L918-L918 | weighted coordinates of l^{a,p}_C
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:kam-domain
KIND: lemma
TITLE: Domains
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L939-L943
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L945-L951
CONTRACT_ID: bpW:w1:kam-domain
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: 0 < sigma <= 1, 0 < 2sigma < s, r > 0
SOURCE_QUANTIFIERS: for all such sigma, s, r; W_0, W
SOURCE_CONCLUSION: D(s,r) is open and convex; D(s',r') subset D(s,r) for s' <= s, r' <= r; every W_0 in D(s-2sigma,r/2) has W_0 + W in D(s-sigma,r) whenever ¦W¦_{p,r} < sigma/2; ¦W¦_{bar p,r} <= ¦W¦_{p,r} for bar p <= p and ¦W¦_{p,r} <= ¦W¦_{p,r'} for r' <= r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:kam-space, bpW:w1:embed
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:kam-space | blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L940-L940 | D(s,r) and the norms
EDGE: bpW:w1:embed | blueprint-W/parts/w1-sequences.tex#bpW:w1:kam-domain@L950-L950 | (i): norm comparison for bar p <= p
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:fourier-l2
KIND: lemma
TITLE: Hilbert-valued Fourier series on strips
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L955-L966
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L968-L990
CONTRACT_ID: bpW:w1:fourier-l2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: H complex Hilbert space, n >= 1, s > 0, T_s = {max ¦Im theta_i¦ < s}, u : T_s -> H holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s (M >= 0); hat u_k = int_{[0,1]^n} u(x) e^{-2 pi i k.x} dx; (ii) c_k in H with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 s} < infinity
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: (i) sum_k ¦¦hat u_k¦¦^2 e^{4 pi ¦k¦_1 s} <= 2^n M^2; (ii) v(theta) = sum c_k e^{2 pi i k.theta} converges absolutely and uniformly on T_s, is holomorphic and 1-periodic, hat v_k = c_k, ¦¦v¦¦ <= sum ¦¦c_k¦¦ e^{2pi¦k¦_1 s}; (iii) u is the sum of its Fourier series on T_{s'} for s' < s
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, stepW:w1:shift, stepW:w1:parseval, stepW:w1:orthants, stepW:w1:fsum
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L957-L957 | holomorphic maps
EDGE: stepW:w1:shift | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L969-L969 | proof step
EDGE: stepW:w1:parseval | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L975-L975 | proof step
EDGE: stepW:w1:orthants | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L980-L980 | proof step
EDGE: stepW:w1:fsum | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-l2@L984-L984 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:shift
KIND: step
TITLE: Shifted coefficients
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L969-L974
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L969-L974
CONTRACT_ID: stepW:w1:shift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-l2: H complex Hilbert space, n >= 1, s > 0, T_s = {max ¦Im theta_i¦ < s}, u : T_s -> H holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s (M >= 0); hat u_k = int_{[0,1]^n} u(x) e^{-2 pi i k.x} dx; (ii) c_k in H with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 s} < infinity; local data: eta in R^n, max ¦eta_i¦ < s
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-l2 (for all such data); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: hat u_k e^{-2 pi k.eta} is the k-th Fourier coefficient of the continuous periodic x -> u(x + i eta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: K:step:p1:dec-shift, bpW:w1:ext-lp
ROUTES: -
ROUTE_FOR: -
EDGE: K:step:p1:dec-shift | blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L973-L973 | the contour shift (cited as fourier-basic) applied to the scalar holomorphic functions <e,u>
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:shift@L974-L974 | vectors of H are determined by the functionals <e,.>
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The text cites "the contour shift of track K's bp:p1:fourier-basic" (L973); fourier-basic contains no contour shift. The shift is K's step:p1:dec-shift (in the proof of bp:p1:decay), used here with an arbitrary shift eta instead of K's t_j = -rho' sgn(k_j). Suspected blueprint misreference (reported).

NODE: stepW:w1:parseval
KIND: step
TITLE: Parseval
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L975-L979
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L975-L979
CONTRACT_ID: stepW:w1:parseval
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-l2: H complex Hilbert space, n >= 1, s > 0, T_s = {max ¦Im theta_i¦ < s}, u : T_s -> H holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s (M >= 0); hat u_k = int_{[0,1]^n} u(x) e^{-2 pi i k.x} dx; (ii) c_k in H with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 s} < infinity; local data: g continuous periodic H-valued with ¦¦g¦¦ <= M
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-l2 (for all such data); within the step: eta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum_k ¦¦hat g_k¦¦^2 = int ¦¦g¦¦^2 <= M^2; hence sum_k ¦¦hat u_k¦¦^2 e^{-4 pi k.eta} <= M^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-fourier, bpW:w1:ext-series, stepW:w1:shift
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-fourier | blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L978-L978 | scalar Parseval
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L978-L978 | Tonelli over the orthonormal basis
EDGE: stepW:w1:shift | blueprint-W/parts/w1-sequences.tex#stepW:w1:parseval@L979-L979 | the shifted coefficients
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:orthants
KIND: step
TITLE: Orthants
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:orthants@L980-L983
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:orthants@L980-L983
CONTRACT_ID: stepW:w1:orthants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-l2: H complex Hilbert space, n >= 1, s > 0, T_s = {max ¦Im theta_i¦ < s}, u : T_s -> H holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s (M >= 0); hat u_k = int_{[0,1]^n} u(x) e^{-2 pi i k.x} dx; (ii) c_k in H with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 s} < infinity; local data: s' < s
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-l2 (for all such data); within the step: eps in {+-1}^n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: e^{4 pi s' ¦k¦_1} <= sum_eps e^{4 pi s' eps.k}; summing the 2^n shifts eta = -s' eps gives (i) with s', and monotone convergence gives s
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:parseval
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:parseval | blueprint-W/parts/w1-sequences.tex#stepW:w1:orthants@L981-L981 | the bound for each eta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fsum
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L984-L989
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L984-L989
CONTRACT_ID: stepW:w1:fsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-l2: H complex Hilbert space, n >= 1, s > 0, T_s = {max ¦Im theta_i¦ < s}, u : T_s -> H holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s (M >= 0); hat u_k = int_{[0,1]^n} u(x) e^{-2 pi i k.x} dx; (ii) c_k in H with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 s} < infinity; local data: (ii): sum ¦¦c_k¦¦ e^{2 pi ¦k¦_1 s} < infinity; (iii): u as in (i), s' < s
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-l2 (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) uniform convergence of holomorphic partial sums, holomorphy of the limit, coefficients termwise; (iii) sum ¦¦hat u_k¦¦ e^{2pi¦k¦_1 s'} <= 2^{n/2} M (sum e^{-4pi¦k¦_1(s-s')})^{1/2} < infinity, and the sum v of (ii) equals u on R^n (scalar uniqueness) and on T_{s'} (identity theorem)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:uniform-limit, bpW:w1:ext-integral, stepW:w1:orthants, K:bp:p1:fourier-basic, K:bp:p1:strip-identity
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L986-L986 | holomorphy of the uniform limit
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L986-L986 | term-by-term integration of the coefficients
EDGE: stepW:w1:orthants | blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L987-L987 | (i) in the Cauchy-Schwarz bound
EDGE: K:bp:p1:fourier-basic | blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L989-L989 | (b): a continuous periodic function with vanishing coefficients is 0
EDGE: K:bp:p1:strip-identity | blueprint-W/parts/w1-sequences.tex#stepW:w1:fsum@L989-L989 | identity theorem on strips
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:fourier-banach
KIND: lemma
TITLE: Banach-valued Fourier coefficients on strips
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L996-L1012
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1014-L1029
CONTRACT_ID: bpW:w1:fourier-banach
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F complex Banach, n >= 1, s > 0, M >= 0, u : T_s -> F holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s; hat u_k (Bochner integral); (ii) 0 < sigma < s, c >= 0; (iii) c_k in F with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 rho} < infinity for some rho > 0
SOURCE_QUANTIFIERS: for all such data; k in Z^n
SOURCE_CONCLUSION: (i) ¦¦hat u_k¦¦ <= M e^{-2 pi ¦k¦_1 s}; (ii) sum_k ¦¦hat u_k¦¦ e^{2pi¦k¦_1(s-sigma)} <= M coth(pi sigma)^n and sum_k (1+¦k¦_1)^c ¦¦hat u_k¦¦ e^{2pi¦k¦_1(s-sigma)} <= M S_{n,c}(sigma); (iii) v = sum c_k e^{2pi i k.theta} converges absolutely and uniformly on T_rho, is holomorphic and 1-periodic, hat v_k = c_k, ¦¦v¦¦ <= sum ¦¦c_k¦¦ e^{2pi¦k¦_1 rho}; (iv) everything is linear in u (parameter-difference versions)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holomorphic, bpW:w1:lattice, stepW:w1:fbdual, stepW:w1:fbdecay, stepW:w1:fbsum, stepW:w1:fbconv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L999-L999 | holomorphic maps
EDGE: bpW:w1:lattice | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1005-L1005 | S_{n,c}
EDGE: stepW:w1:fbdual | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1015-L1015 | proof step
EDGE: stepW:w1:fbdecay | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1019-L1019 | proof step
EDGE: stepW:w1:fbsum | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1023-L1023 | proof step
EDGE: stepW:w1:fbconv | blueprint-W/parts/w1-sequences.tex#bpW:w1:fourier-banach@L1025-L1025 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fbdual
KIND: step
TITLE: Scalar reduction
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdual@L1015-L1018
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdual@L1015-L1018
CONTRACT_ID: stepW:w1:fbdual
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-banach: F complex Banach, n >= 1, s > 0, M >= 0, u : T_s -> F holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s; hat u_k (Bochner integral); (ii) 0 < sigma < s, c >= 0; (iii) c_k in F with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 rho} < infinity for some rho > 0; local data: phi in F*, ¦¦phi¦¦ <= 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-banach (for all such data; k in Z^n); within the step: phi; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: phi o u is holomorphic, 1-periodic, bounded by M, and phi(hat u_k) = (phi o u)^_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdual@L1018-L1018 | continuous linear maps commute with Bochner integrals
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fbdecay
KIND: step
TITLE: Scalar decay
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1019-L1022
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1019-L1022
CONTRACT_ID: stepW:w1:fbdecay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-banach: F complex Banach, n >= 1, s > 0, M >= 0, u : T_s -> F holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s; hat u_k (Bochner integral); (ii) 0 < sigma < s, c >= 0; (iii) c_k in F with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 rho} < infinity for some rho > 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-banach (for all such data; k in Z^n); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦(phi o u)^_k¦ <= e^{-2pi¦k¦_1 s'} M for 0 <= s' < s; s' -> s; for all norm-one phi, ¦¦hat u_k¦¦ <= M e^{-2pi¦k¦_1 s}; this is (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:fbdual, K:bp:p1:decay, bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:fbdual | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1020-L1020 | the scalar functions phi o u
EDGE: K:bp:p1:decay | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1020-L1020 | scalar coefficient decay
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbdecay@L1022-L1022 | the norm is attained by norm-one functionals
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fbsum
KIND: step
TITLE: Lattice sum
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1023-L1024
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1023-L1024
CONTRACT_ID: stepW:w1:fbsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-banach: F complex Banach, n >= 1, s > 0, M >= 0, u : T_s -> F holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s; hat u_k (Bochner integral); (ii) 0 < sigma < s, c >= 0; (iii) c_k in F with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 rho} < infinity for some rho > 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-banach (for all such data; k in Z^n); within the step: sigma; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦hat u_k¦¦ e^{2pi¦k¦_1(s-sigma)} <= M e^{-2pi¦k¦_1 sigma}, summed with Lemma bpW:w1:lattice; this is (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:fbdecay, bpW:w1:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:fbdecay | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1024-L1024 | (i)
EDGE: bpW:w1:lattice | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbsum@L1024-L1024 | (i), (iii): the lattice sums
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:fbconv
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1025-L1028
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1025-L1028
CONTRACT_ID: stepW:w1:fbconv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:fourier-banach: F complex Banach, n >= 1, s > 0, M >= 0, u : T_s -> F holomorphic, 1-periodic, ¦¦u¦¦ <= M on T_s; hat u_k (Bochner integral); (ii) 0 < sigma < s, c >= 0; (iii) c_k in F with sum ¦¦c_k¦¦ e^{2pi¦k¦_1 rho} < infinity for some rho > 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:fourier-banach (for all such data; k in Z^n); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the partial sums converge uniformly on T_rho; the limit is holomorphic; coefficients by term-by-term integration; (iv) by linearity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:uniform-limit, bpW:w1:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1027-L1027 | (i): holomorphy of the uniform limit
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w1-sequences.tex#stepW:w1:fbconv@L1028-L1028 | term-by-term integration
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:lattice
KIND: lemma
TITLE: Weighted lattice sums
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1033-L1047
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1049-L1065
CONTRACT_ID: bpW:w1:lattice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 1, sigma > 0, eps = 2 pi sigma, ¦k¦_1 = sum ¦k_i¦; (iii) c >= 0, b = c + n - 1; (iv) tau >= 1, gamma, beta >= 0
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: (i) sum_k e^{-eps¦k¦_1} = coth(eps/2)^n = coth(pi sigma)^n; (ii) #{k : ¦k¦_1 = m} <= 2^n binom(m+n-1,n-1) <= 2^n (m+1)^{n-1}; (iii) sum_k (1+¦k¦_1)^c e^{-eps¦k¦_1} <= S_{n,c}(sigma) := 2^n (2b/(e eps))^b e^{eps/2} (1 + 2/eps) ((2b/(e eps))^b := 1 for b = 0); (iv) A_k = 1 + ¦k¦_1^tau <= (1+¦k¦_1)^tau, so sum A_k^gamma (1+¦k¦_1)^beta e^{-eps¦k¦_1} <= S_{n,gamma tau + beta}(sigma), and P96-K's B_sigma^2 <= 2^n S_{n,4tau+2}(sigma/pi) in period-one units
CONSTANT_SCOPE: S_{n,c}(sigma) explicit in n, c, sigma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:latprod, stepW:w1:latcount, stepW:w1:latweight, stepW:w1:latdiv
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:latprod | blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1050-L1050 | proof step
EDGE: stepW:w1:latcount | blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1054-L1054 | proof step
EDGE: stepW:w1:latweight | blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1057-L1057 | proof step
EDGE: stepW:w1:latdiv | blueprint-W/parts/w1-sequences.tex#bpW:w1:lattice@L1062-L1062 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:latprod
KIND: step
TITLE: Product
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latprod@L1050-L1053
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latprod@L1050-L1053
CONTRACT_ID: stepW:w1:latprod
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:lattice: n >= 1, sigma > 0, eps = 2 pi sigma, ¦k¦_1 = sum ¦k_i¦; (iii) c >= 0, b = c + n - 1; (iv) tau >= 1, gamma, beta >= 0; local data: eps > 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:lattice (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the sum factorizes and sum_{m in Z} e^{-eps¦m¦} = coth(eps/2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:latprod@L1052-L1052 | Tonelli for the product sum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:latcount
KIND: step
TITLE: Counting
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latcount@L1054-L1056
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latcount@L1054-L1056
CONTRACT_ID: stepW:w1:latcount
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:lattice: n >= 1, sigma > 0, eps = 2 pi sigma, ¦k¦_1 = sum ¦k_i¦; (iii) c >= 0, b = c + n - 1; (iv) tau >= 1, gamma, beta >= 0; local data: m >= 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:lattice (for all such data); within the step: m; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: #{k : ¦k¦_1 = m} <= 2^n binom(m+n-1,n-1) <= 2^n (m+1)^{n-1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:latweight
KIND: step
TITLE: Weighted sum
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latweight@L1057-L1061
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latweight@L1057-L1061
CONTRACT_ID: stepW:w1:latweight
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:lattice: n >= 1, sigma > 0, eps = 2 pi sigma, ¦k¦_1 = sum ¦k_i¦; (iii) c >= 0, b = c + n - 1; (iv) tau >= 1, gamma, beta >= 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:lattice (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the sum in (iii) is at most 2^n sum_m (m+1)^b e^{-eps m} <= S_{n,c}(sigma), using t^b e^{-eps t/2} <= (2b/(e eps))^b and 1 - e^{-x} >= x/(1+x)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:latcount
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:latcount | blueprint-W/parts/w1-sequences.tex#stepW:w1:latweight@L1058-L1058 | (ii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:latdiv
KIND: step
TITLE: Divisor weights
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latdiv@L1062-L1064
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:latdiv@L1062-L1064
CONTRACT_ID: stepW:w1:latdiv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:lattice: n >= 1, sigma > 0, eps = 2 pi sigma, ¦k¦_1 = sum ¦k_i¦; (iii) c >= 0, b = c + n - 1; (iv) tau >= 1, gamma, beta >= 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:lattice (for all such data); within the step: x >= 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: 1 + x^tau <= (1+x)^tau; the B_sigma statement by the substitution ¦k¦ = ¦k¦_1, e^{-2¦k¦sigma_K} = e^{-2pi¦k¦_1(sigma_K/pi)}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:latweight
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:latweight | blueprint-W/parts/w1-sequences.tex#stepW:w1:latdiv@L1064-L1064 | (iii) with c = gamma tau + beta
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w1:schur
KIND: lemma
TITLE: Hilbert-matrix bound
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1110-L1121
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1123-L1138
CONTRACT_ID: bpW:w1:schur
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A bounded on l^2_K with matrix A_ij = (A e_j)_i; (iii) F_ij with ¦F_ij¦ <= c¦A_ij¦/¦i-j¦ (i != j), ¦F_ii¦ <= c¦A_ii¦; (iv) A : l^{a,p}_K -> l^{a,bar p}_K via its representative
SOURCE_QUANTIFIERS: for all such A, F, c
SOURCE_CONCLUSION: (i) B_ij = ¦A_ij¦/¦i-j¦ (i != j), B_ii = 0 defines a bounded operator with absolutely convergent rows and ¦¦B¦¦ <= (pi/sqrt3)¦¦A¦¦; (ii) the diagonal (A_ii) is a multiplier with norm <= ¦¦A¦¦; (iii) ¦¦F¦¦ <= c(1 + pi/sqrt3)¦¦A¦¦ <= 3c¦¦A¦¦; (iv) the same for weighted spaces via the representative hat A (ratios unchanged by the weights)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, stepW:w1:rows, stepW:w1:schurtest, stepW:w1:diagcomb, stepW:w1:schurweights
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1119-L1119 | the representative hat A
EDGE: stepW:w1:rows | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1124-L1124 | proof step
EDGE: stepW:w1:schurtest | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1128-L1128 | proof step
EDGE: stepW:w1:diagcomb | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1131-L1131 | proof step
EDGE: stepW:w1:schurweights | blueprint-W/parts/w1-sequences.tex#bpW:w1:schur@L1136-L1136 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:rows
KIND: step
TITLE: Row and column sums
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rows@L1124-L1127
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:rows@L1124-L1127
CONTRACT_ID: stepW:w1:rows
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:schur: A bounded on l^2_K with matrix A_ij = (A e_j)_i; (iii) F_ij with ¦F_ij¦ <= c¦A_ij¦/¦i-j¦ (i != j), ¦F_ii¦ <= c¦A_ii¦; (iv) A : l^{a,p}_K -> l^{a,bar p}_K via its representative
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:schur (for all such A, F, c); within the step: i, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum_j ¦A_ij¦^2 <= ¦¦A¦¦^2, sum_i ¦A_ij¦^2 <= ¦¦A¦¦^2; row and column sums of B at most (pi/sqrt3)¦¦A¦¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-series | blueprint-W/parts/w1-sequences.tex#stepW:w1:rows@L1126-L1126 | sum_{k != 0} k^{-2} = pi^2/3
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:schurtest
KIND: step
TITLE: Schur test
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1128-L1130
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1128-L1130
CONTRACT_ID: stepW:w1:schurtest
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:schur: A bounded on l^2_K with matrix A_ij = (A e_j)_i; (iii) F_ij with ¦F_ij¦ <= c¦A_ij¦/¦i-j¦ (i != j), ¦F_ii¦ <= c¦A_ii¦; (iv) A : l^{a,p}_K -> l^{a,bar p}_K via its representative
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:schur (for all such A, F, c); within the step: v; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦Bv¦¦^2 <= Lambda^2 ¦¦A¦¦^2 ¦¦v¦¦^2 (Schur test)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:rows, bpW:w1:ext-lp
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:rows | blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1129-L1129 | row and column sums
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w1-sequences.tex#stepW:w1:schurtest@L1130-L1130 | norm bounds via finite partial sums
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:diagcomb
KIND: step
TITLE: Diagonal and combination
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1131-L1135
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1131-L1135
CONTRACT_ID: stepW:w1:diagcomb
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:schur: A bounded on l^2_K with matrix A_ij = (A e_j)_i; (iii) F_ij with ¦F_ij¦ <= c¦A_ij¦/¦i-j¦ (i != j), ¦F_ii¦ <= c¦A_ii¦; (iv) A : l^{a,p}_K -> l^{a,bar p}_K via its representative
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:schur (for all such A, F, c); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦A_ii¦ <= ¦¦A¦¦; the diagonal is a multiplier; F is dominated entrywise by cB + c diag(¦A_ii¦), so ¦¦F¦¦ <= c(1 + pi/sqrt3)¦¦A¦¦ < 3c¦¦A¦¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:multiplier, stepW:w1:schurtest
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:multiplier | blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1132-L1132 | diagonal multipliers
EDGE: stepW:w1:schurtest | blueprint-W/parts/w1-sequences.tex#stepW:w1:diagcomb@L1133-L1133 | the bound on B
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w1:schurweights
KIND: step
TITLE: Weights
STATEMENT_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurweights@L1136-L1137
PROOF_SOURCE: blueprint-W/parts/w1-sequences.tex#stepW:w1:schurweights@L1136-L1137
CONTRACT_ID: stepW:w1:schurweights
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w1:schur: A bounded on l^2_K with matrix A_ij = (A e_j)_i; (iii) F_ij with ¦F_ij¦ <= c¦A_ij¦/¦i-j¦ (i != j), ¦F_ii¦ <= c¦A_ii¦; (iv) A : l^{a,p}_K -> l^{a,bar p}_K via its representative; local data: A : l^{a,p} -> l^{a,bar p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w1:schur (for all such A, F, c); within the step: i, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: hat A_ij = omega_{a,bar p}(i) A_ij/omega_{a,p}(j), likewise for F, so the hypotheses of (iii) transfer
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w1-sequences.tex#stepW:w1:schurweights@L1137-L1137 | the representative
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:ext-deriv
KIND: external
TITLE: One-variable calculus
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-deriv@L40-L48
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: a continuous linear map composed with a curve differentiable at t is differentiable at t with the image derivative; d/ds <Psi(s),y> = <Psi'(s),y>; derivatives are unique; translation: if F has derivative d at 0 then s -> F(s-t) has derivative d at t; a two-sided derivative is a derivative within any set; on [0,pi] (pi > 0) derivatives within are unique, so derivWithin f (Icc 0 pi) x equals any f' with HasDerivWithinAt f f' (Icc 0 pi) x
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:ext-an
KIND: external
TITLE: Analytic maps on $\R\times\R$
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-an@L49-L54
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: the projections of R x R and the affine maps t -> theta_0 + t nu are analytic; sums, products and powers of real analytic functions are analytic; analytic maps are differentiable and continuous; continuity at every point of a set gives ContinuousOn
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:ext-sums
KIND: external
TITLE: Series and norms
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-sums@L55-L60
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-sums
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: tsum_congr (termwise equal series have equal tsum, no summability needed); Summable.tsum_sub, Summable.tsum_add, tsum_mul_left for summable series; tsum_zero; comparison; summability of j e^{-j}, e^{-j} (geometric); Cauchy-Schwarz ¦<Psi,y>¦ <= ¦¦Psi¦¦ ¦¦y¦¦; on a product norm_fst_le, norm_snd_le
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:ext-trig
KIND: external
TITLE: Trigonometry
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-trig@L61-L64
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-trig
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: sin 0 = 0, sin(n pi) = 0 for n in N; ¦sin¦, ¦cos¦ <= 1; d/dx sin(jx) = j cos(jx), d/dx cos(jx) = -j sin(jx); sqrt(lambda) sqrt(lambda) = lambda and lambda/sqrt(lambda) = sqrt(lambda) for lambda > 0; lambda_j^2 = j^2 + m
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:derived
KIND: definition
TITLE: Derived reconstructions
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:derived@L70-L76
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:derived
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: y in l^2_R, x in R (standing data a = p = 1, kappa = kappa_{1,1})
SOURCE_QUANTIFIERS: y, x
SOURCE_CONCLUSION: defines D^0 y(x) = U_m(y)(x) (frozen reconU m hm y x), D^1 y(x) = sum_j kappa(y)_j/sqrt(lambda_j) sqrt(2/pi) j cos(jx), D^2 y(x) = -sum_j kappa(y)_j/sqrt(lambda_j) sqrt(2/pi) j^2 sin(jx) as tsums over N_+ (non-frozen helpers)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:ellap#coeff, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:derived@L72-L72 | kappa(y)_j = coeff y j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:derived@L72-L72 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:derived@L71-L71 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:functionals
KIND: lemma
TITLE: Reconstruction functionals
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L81-L92
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L94-L124
CONTRACT_ID: bpW:w2:functionals
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}
SOURCE_QUANTIFIERS: there exist Psi^0, Psi^1, Psi^2, Psi^V; then for all y in l^2_R and x in R
SOURCE_CONCLUSION: there are real analytic Psi^0, Psi^1, Psi^2, Psi^V : R -> l^2_R (AnalyticOnNhd R Psi univ) such that (i) D^k y(x) = <Psi^k(x),y> (k = 0,1,2) and V_m(y)(x) = <Psi^V(x),y>, the four series absolutely convergent; (ii) ¦¦Psi^0(x)¦¦, ¦¦Psi^1(x)¦¦ <= c_0, ¦¦Psi^V(x)¦¦ <= (1+m)^{1/4} c_0, hence ¦D^0y(x)¦, ¦D^1y(x)¦ <= c_0 ¦¦y¦¦ and ¦V_m(y)(x)¦ <= (1+m)^{1/4} c_0 ¦¦y¦¦; (iii) D^k y has derivative D^{k+1} y(x) at x (k = 0,1); (iv) D^0 y(0) = D^0 y(pi) = 0
CONSTANT_SCOPE: c_0 absolute; Psi^k independent of y and x
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:derived, stepW:w2:features, stepW:w2:pairing, stepW:w2:norms, stepW:w2:xder, stepW:w2:bdry, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L85-L85 | D^k y
EDGE: stepW:w2:features | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L95-L95 | proof step
EDGE: stepW:w2:pairing | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L103-L103 | proof step
EDGE: stepW:w2:norms | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L108-L108 | proof step
EDGE: stepW:w2:xder | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L114-L114 | proof step
EDGE: stepW:w2:bdry | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L120-L120 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L96-L96 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L101-L101 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L88-L88 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L85-L85 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L107-L107 | the frozen coeff occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:features
KIND: step
TITLE: Choice of the features
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L95-L102
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L95-L102
CONTRACT_ID: stepW:w2:features
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:functionals: standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:functionals (there exist Psi^0, Psi^1, Psi^2, Psi^V; then for all y in l^2_R and x in R); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Lemma bpW:w1:sine-feature with a = p = 1 applies to beta_j = lambda_j^{-1/2} (B = 1, nu = 0) and beta_j = lambda_j^{1/2} (B = (1+m)^{1/4}, nu = 1/2); the real restrictions Psi^k, Psi^V are real analytic with coordinates Psi^k(x)_j = lambda_j^{-1/2} phi_j^(k)(x)/omega(j), Psi^V(x)_j = lambda_j^{1/2} phi_j(x)/omega(j)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, bpW:w0:basis#lambda-facts, bpW:w0:mass, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L96-L96 | with a = p = 1 and the two choices of beta; (ii) real analyticity
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L97-L97 | lambda_j > j >= 1
EDGE: bpW:w0:mass | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L98-L98 | lambda_j^2 = j^2 + m <= (1+m) j^2
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L96-L96 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L101-L101 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:pairing
KIND: step
TITLE: Pairings
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L103-L107
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L103-L107
CONTRACT_ID: stepW:w2:pairing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:functionals: standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:functionals (there exist Psi^0, Psi^1, Psi^2, Psi^V; then for all y in l^2_R and x in R); within the step: y, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: <Psi^k(x),y> and <Psi^V(x),y> equal termwise the summands of reconU, of D^1, D^2 and of reconV, so the tsums agree; this is (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, stepW:w2:features, bpW:w2:derived, bpW:w2:ext-sums, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L104-L104 | (iii): the pairings as absolutely convergent series
EDGE: stepW:w2:features | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L104-L104 | the feature maps Psi^k, Psi^V
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L106-L106 | the summands of D^1, D^2
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L107-L107 | tsum_congr
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L104-L104 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L104-L104 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L106-L106 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L106-L106 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L107-L107 | the frozen coeff occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:norms
KIND: step
TITLE: Norms
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L108-L113
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L108-L113
CONTRACT_ID: stepW:w2:norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:functionals: standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:functionals (there exist Psi^0, Psi^1, Psi^2, Psi^V; then for all y in l^2_R and x in R); within the step: x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦Psi^k(x)¦¦^2 <= (2/pi) sum_j lambda_j^{-1} j^{2k-2} e^{-2j} <= c_0^2 for k = 0,1, and ¦¦Psi^V(x)¦¦^2 <= (1+m)^{1/2} c_0^2; with Cauchy-Schwarz this gives (ii)
CONSTANT_SCOPE: c_0 absolute
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:features, bpW:w0:basis#lambda-facts, bpW:w1:ext-lp, bpW:w2:ext-sums, stepW:w2:pairing, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:features | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L109-L109 | the coordinates of Psi^k, Psi^V
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L110-L110 | lambda_j^{-1} < 1 and lambda_j j^{-2} <= (1+m)^{1/2} j^{-1}
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L113-L113 | norm bounds from finite partial sums
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L113-L113 | Cauchy-Schwarz
EDGE: stepW:w2:pairing | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L113-L113 | (i) for the pointwise bounds
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L109-L109 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L109-L109 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:xder
KIND: step
TITLE: $x$-derivatives
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L114-L119
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L114-L119
CONTRACT_ID: stepW:w2:xder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:functionals: standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:functionals (there exist Psi^0, Psi^1, Psi^2, Psi^V; then for all y in l^2_R and x in R); within the step: x, y; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (Psi^k)'(x) = Psi^{k+1}(x) for k = 0,1, and x -> <Psi^k(x),y> has derivative <Psi^{k+1}(x),y>; with (i) this is (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:recder, bpW:w2:ext-trig, bpW:w2:ext-deriv, stepW:w2:pairing, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:recder | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L115-L115 | the derivative of the analytic feature map has the coordinatewise derivatives
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L116-L116 | derivatives of sin(jx), cos(jx)
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L119-L119 | derivative of the pairing with fixed y
EDGE: stepW:w2:pairing | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L119-L119 | (i)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L117-L117 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L117-L117 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:bdry
KIND: step
TITLE: Boundary values
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L120-L123
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L120-L123
CONTRACT_ID: stepW:w2:bdry
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:functionals: standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:functionals (there exist Psi^0, Psi^1, Psi^2, Psi^V; then for all y in l^2_R and x in R); within the step: y; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: phi_j(0) = phi_j(pi) = 0 for j in N_+, so every summand of reconU m hm y 0 and reconU m hm y pi vanishes and the tsum is 0; this is (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-trig, bpW:w2:ext-sums, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L121-L121 | sin 0 = 0, sin(j pi) = 0
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L123-L123 | tsum_zero
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L121-L121 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L122-L122 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:force
KIND: lemma
TITLE: Force identity in frozen form
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L128-L137
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L139-L160
CONTRACT_ID: bpW:w2:force
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j
SOURCE_QUANTIFIERS: for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))
SOURCE_CONCLUSION: both series converge absolutely; (i) Sigma_lin(x) = -D^2 y(x) + m D^0 y(x) for every x in R; (ii) Sigma_cub(x) = U_m(y)(x)^3 for every x in [0,pi]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:derived, stepW:w2:fsum, stepW:w2:flin, stepW:w2:fcub, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L134-L134 | D^0 y and D^2 y
EDGE: stepW:w2:fsum | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L140-L140 | proof step
EDGE: stepW:w2:flin | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L148-L148 | proof step
EDGE: stepW:w2:fcub | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L154-L154 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L130-L130 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L130-L130 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L134-L134 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L131-L131 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:fsum
KIND: step
TITLE: Summability
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L140-L147
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L140-L147
CONTRACT_ID: stepW:w2:fsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:force: standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:force (for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))); within the step: y, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the summands of Sigma_lin are at most sqrt(2/pi)(1+m)^{3/4} ¦¦y¦¦ j e^{-j}, those of Sigma_cub at most sqrt(2/pi)(1+m)^{1/4} ¦¦G^w(y)¦¦ e^{-j}; both majorants are summable; D^0 y(x), D^2 y(x) converge absolutely
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-lp, bpW:w0:basis#lambda-facts, bpW:w1:cubic-analytic, bpW:w2:ext-sums, bpW:w2:functionals, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L141-L141 | ¦kappa(y)_j¦ <= ¦¦y¦¦/(j e^j)
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L141-L141 | sqrt(lambda_j) lambda_j <= (1+m)^{3/4} j^{3/2}
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L143-L143 | (iv): G(y)_j = G^w(y)_j/omega_{1,2}(j), G^w(y) in l^2_R
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L146-L146 | comparison and summability of the majorants
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L147-L147 | (i): absolute convergence of D^0 y(x), D^2 y(x)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L141-L141 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L142-L142 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L146-L146 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L143-L143 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:flin
KIND: step
TITLE: Linear part
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L148-L153
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L148-L153
CONTRACT_ID: stepW:w2:flin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:force: standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:force (for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))); within the step: y, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: termwise sqrt(lambda_j) lambda_j = (j^2+m)/sqrt(lambda_j), so the j-th summand of Sigma_lin is minus that of D^2 y plus m times that of D^0 y; summing gives (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-trig, bpW:w2:derived, stepW:w2:fsum, bpW:w2:ext-sums, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L149-L149 | lambda/sqrt(lambda) identities and lambda_j^2 = j^2 + m
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L151-L151 | the summands of D^0, D^2
EDGE: stepW:w2:fsum | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L151-L151 | absolute convergence of both series
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L152-L152 | Summable.tsum_add, tsum_mul_left
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L149-L149 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L150-L150 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L151-L151 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:fcub
KIND: step
TITLE: Cubic part
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L154-L159
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L154-L159
CONTRACT_ID: stepW:w2:fcub
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:force: standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:force (for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))); within the step: y, x in [0,pi]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: U_m(y) = U_m(q) and G(y) = G_q(q) for q = kappa(y) in l^{1,1}; the first identity of (bpW:w0n:force) gives U_m(q)^3 = sum_l sqrt(lambda_l) G_q(q)_l phi_l on [0,pi], which is (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:trifrozen, stepW:w0n:force, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:trifrozen | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L155-L155 | the frozen reconU and cubicGrad are U_m and G_q of q = kappa(y)
EDGE: stepW:w0n:force | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L157-L157 | the force identity U_m(q)^3 = sum sqrt(lambda_l) G_q(q)_l phi_l
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L158-L158 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L158-L158 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L155-L155 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L155-L155 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:coeffsol
KIND: definition
TITLE: Analytic coefficient solution
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L166-L174
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:coeffsol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: Y : R -> WaveSpace (standing data)
SOURCE_QUANTIFIERS: Y
SOURCE_CONCLUSION: defines: Y is an analytic coefficient solution iff (C1) Y is real analytic at every t (forall t, AnalyticAt R Y t) and (C2) for all t and j in N_+, s -> coeff (Y s).1 j has derivative lambda_j coeff (Y t).2 j at t and s -> coeff (Y s).2 j has derivative -lambda_j coeff (Y t).1 j - cubicGrad m hm (Y t).1 j at t (HasDerivAt)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:eqmotion, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L176-L176 | (C2) is the coefficient system (bpW:w0:coeffsys) read coordinatewise
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L171-L171 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L172-L172 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L170-L170 | the frozen coeff occurs directly here
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L167-L167 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:orbit
KIND: lemma
TITLE: Torus orbits are analytic coefficient solutions
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L178-L190
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L192-L202
CONTRACT_ID: bpW:w2:orbit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K : (Fin 2 -> R) -> WaveSpace with AnalyticOnNhd R K univ; nu : Fin 2 -> R such that for all theta and j in N_+ the invariance (bpW:w2:inv) holds, each as a HasDerivAt at 0 of t -> coeff (K(theta + t nu)).i j (the frozen conclusion (4) of nlw2 for one I)
SOURCE_QUANTIFIERS: for all K, nu as stated; for every theta_0
SOURCE_CONCLUSION: Y(t) = K(theta_0 + t nu) is an analytic coefficient solution
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:coeffsol, stepW:w2:oan, stepW:w2:oshift, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L189-L189 | the notion of analytic coefficient solution
EDGE: stepW:w2:oan | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L193-L193 | proof step
EDGE: stepW:w2:oshift | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L196-L196 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L183-L183 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L184-L184 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L197-L197 | the frozen coeff occurs directly here
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L179-L179 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:oan
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oan@L193-L195
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oan@L193-L195
CONTRACT_ID: stepW:w2:oan
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:orbit: K : (Fin 2 -> R) -> WaveSpace with AnalyticOnNhd R K univ; nu : Fin 2 -> R such that for all theta and j in N_+ the invariance (bpW:w2:inv) holds, each as a HasDerivAt at 0 of t -> coeff (K(theta + t nu)).i j (the frozen conclusion (4) of nlw2 for one I)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:orbit (for all K, nu as stated; for every theta_0); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: t -> theta_0 + t nu is analytic and K is analytic at its value, so Y is analytic at t ((C1))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-an
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oan@L195-L195 | affine maps are analytic; AnalyticAt.comp
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:oshift
KIND: step
TITLE: Shift
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L196-L201
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L196-L201
CONTRACT_ID: stepW:w2:oshift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:orbit: K : (Fin 2 -> R) -> WaveSpace with AnalyticOnNhd R K univ; nu : Fin 2 -> R such that for all theta and j in N_+ the invariance (bpW:w2:inv) holds, each as a HasDerivAt at 0 of t -> coeff (K(theta + t nu)).i j (the frozen conclusion (4) of nlw2 for one I)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:orbit (for all K, nu as stated; for every theta_0); within the step: t, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: applying (bpW:w2:inv) at theta = theta_0 + t nu and translating, s -> coeff (Y s).i j has the derivative required by (C2) at t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-deriv, bpW:w0:basis#lam, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L198-L198 | the translation rule for derivatives
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L201-L201 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L197-L197 | the frozen coeff occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:curve-deriv
KIND: lemma
TITLE: Coefficients of the curve derivative
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L206-L210
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L212-L220
CONTRACT_ID: bpW:w2:curve-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Y an analytic coefficient solution; t in R
SOURCE_QUANTIFIERS: for all Y, t; j in N_+
SOURCE_CONCLUSION: Y_1 = (Y .).1 and Y_2 = (Y .).2 are differentiable at t as maps R -> l^2_R and, with Y_i'(t) their derivatives, kappa(Y_1'(t))_j = lambda_j kappa(Y_2(t))_j and kappa(Y_2'(t))_j = -lambda_j kappa(Y_1(t))_j - G(Y_1(t))_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:coeffsol, stepW:w2:cdiff, stepW:w2:ccoord, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L207-L207 | analytic coefficient solution
EDGE: stepW:w2:cdiff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L213-L213 | proof step
EDGE: stepW:w2:ccoord | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L216-L216 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L209-L209 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L209-L209 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:cdiff
KIND: step
TITLE: Differentiability
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L213-L215
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L213-L215
CONTRACT_ID: stepW:w2:cdiff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve-deriv: Y an analytic coefficient solution; t in R
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve-deriv (for all Y, t; j in N_+); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Y_i is analytic at t (composite with the continuous linear projection), hence differentiable
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-an
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L215-L215 | analytic maps are differentiable
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:ccoord
KIND: step
TITLE: Coordinates
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L216-L219
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L216-L219
CONTRACT_ID: stepW:w2:ccoord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve-deriv: Y an analytic coefficient solution; t in R
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve-deriv (for all Y, t; j in N_+); within the step: t, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: s -> kappa(Y_i(s))_j has derivative kappa(Y_i'(t))_j and, by (C2), the derivative stated there; uniqueness gives the identities
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:coordinatewise, stepW:w2:cdiff, bpW:w2:ext-deriv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:coordinatewise | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L217-L217 | with (a,p) = (a',p') = (1,1), hat iota = id, v = Y_i'(t)
EDGE: stepW:w2:cdiff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L217-L217 | Y_i differentiable at t
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L219-L219 | uniqueness of derivatives
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:curve
KIND: theorem
TITLE: P96-W Lemma~1 in frozen form
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L233-L249
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L251-L296
CONTRACT_ID: bpW:w2:curve
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]
SOURCE_CONCLUSION: (i) each of the five functions, uncurried, is real analytic at every point of R x R; (ii) s -> u(s,x) has derivative u_t(t,x) at t; (iii) for x in [0,pi], s -> u_t(s,x) has derivative u_tt(t,x) at t; (iv) u(t,.) has derivative u_x(t,x) and u_x(t,.) has derivative u_xx(t,x) at x; (v) IsClassicalSolution m hm u with witnesses (u_t,u_x,u_tt,u_xx); (vi) for x in [0,pi], derivWithin (u t) (Icc 0 pi) x = u_x(t,x) and ¦u(t,x)¦ + ¦derivWithin (u t) (Icc 0 pi) x¦ + ¦V_m(Y_2(t))(x)¦ <= M_m ¦¦Y(t)¦¦
CONSTANT_SCOPE: M_m depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:coeffsol, bpW:w2:derived, bpW:w2:functionals, stepW:w2:joint, stepW:w2:t1, stepW:w2:t2, stepW:w2:x, stepW:w2:frozen, stepW:w2:bound, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:Gq#cubicGrad, bpW:w0:nlw#IsClassicalSolution
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L234-L234 | analytic coefficient solution
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L236-L236 | u_x = D^1 Y_1(t), u_xx = D^2 Y_1(t)
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L238-L238 | c_0
EDGE: stepW:w2:joint | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L252-L252 | proof step
EDGE: stepW:w2:t1 | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L263-L263 | proof step
EDGE: stepW:w2:t2 | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L271-L271 | proof step
EDGE: stepW:w2:x | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L279-L279 | proof step
EDGE: stepW:w2:frozen | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L281-L281 | proof step
EDGE: stepW:w2:bound | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L290-L290 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L267-L267 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L268-L268 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L235-L235 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L235-L235 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L274-L274 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L245-L245 | the frozen IsClassicalSolution occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:joint
KIND: step
TITLE: Joint analyticity
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L252-L262
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L252-L262
CONTRACT_ID: stepW:w2:joint
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: (s_0,x_0) in R^2; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (s,x) -> <Psi(x),Y_i(s)> are real analytic at every point; by (i) of Lemma bpW:w2:functionals these are u, u_x, u_xx, u_t; u_tt is a polynomial in u, u_xx; this is (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:cdiff, bpW:w1:recon-analytic, bpW:w2:ext-an, bpW:w1:ext-analytic, bpW:w2:functionals, bpW:w0:reconstruction#reconV
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:cdiff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L253-L253 | Y_1, Y_2 analytic at every t
EDGE: bpW:w1:recon-analytic | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L253-L253 | (iii) with parameter domain R
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L257-L257 | pairs, projections and polynomials of analytic maps
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L259-L259 | the continuous bilinear inner product is analytic
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L259-L259 | (i): the functions are the pairings
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L254-L254 | V_m occurs directly here (frozen reconV)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:t1
KIND: step
TITLE: First time derivative
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L263-L270
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L263-L270
CONTRACT_ID: stepW:w2:t1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: t, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: s -> u(s,x) has derivative <Psi^0(x),Y_1'(t)> = U_m(Y_1'(t))(x) = V_m(Y_2(t))(x) = u_t(t,x); this is (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:functionals, bpW:w2:ext-deriv, bpW:w2:curve-deriv, bpW:w2:ext-trig, bpW:w2:ext-sums, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L265-L265 | (i): D^0 y(x) = <Psi^0(x),y> continuous linear in y
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L266-L266 | derivative of a continuous linear image of a curve
EDGE: bpW:w2:curve-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L267-L267 | kappa(Y_1'(t))_j = lambda_j kappa(Y_2(t))_j
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L267-L267 | lambda/sqrt(lambda) = sqrt(lambda)
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L270-L270 | tsum_congr
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L267-L267 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L268-L268 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L264-L264 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L270-L270 | V_m occurs directly here (frozen reconV)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:t2
KIND: step
TITLE: Second time derivative
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L271-L278
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L271-L278
CONTRACT_ID: stepW:w2:t2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: t, x in [0,pi]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: s -> u_t(s,x) has derivative V_m(Y_2'(t))(x) = -Sigma_lin(x) - Sigma_cub(x) = u_tt(t,x) for x in [0,pi]; this is (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:functionals, bpW:w2:ext-deriv, bpW:w2:curve-deriv, stepW:w2:fsum, bpW:w2:ext-sums, bpW:w2:force, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconV, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L272-L272 | (i): V_m(y)(x) = <Psi^V(x),y>
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L272-L272 | derivative of a continuous linear image of a curve
EDGE: bpW:w2:curve-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L273-L273 | the coordinates of Y_2'(t)
EDGE: stepW:w2:fsum | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L275-L275 | absolute convergence of Sigma_lin, Sigma_cub with y = Y_1(t)
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L276-L276 | Summable.tsum_sub
EDGE: bpW:w2:force | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L277-L277 | (i), (ii) on [0,pi]
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L274-L274 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L274-L274 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L272-L272 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L274-L274 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:x
KIND: step
TITLE: Space derivatives
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:x@L279-L280
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:x@L279-L280
CONTRACT_ID: stepW:w2:x
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: t, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) is (iii) of Lemma bpW:w2:functionals with y = Y_1(t)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:functionals
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:x@L280-L280 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:frozen
KIND: step
TITLE: The frozen definition
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L281-L289
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L281-L289
CONTRACT_ID: stepW:w2:frozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: t, x in [0,pi]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: unfolding IsClassicalSolution m hm u with witnesses (u_t,u_x,u_tt,u_xx): continuity on univ x Icc 0 pi from (i), the two time derivatives from (ii), (iii), the two x-derivatives within [0,pi] from (iv), the equation by definition of u_tt, the boundary values from (iv) of Lemma bpW:w2:functionals; this is (v)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:joint, bpW:w2:ext-an, stepW:w2:t1, stepW:w2:t2, stepW:w2:x, bpW:w2:ext-deriv, bpW:w2:functionals, bpW:w0:nlw#IsClassicalSolution
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:joint | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L283-L283 | (i): analyticity, hence continuity
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L283-L283 | analytic implies continuous; ContinuousOn
EDGE: stepW:w2:t1 | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L286-L286 | (ii)
EDGE: stepW:w2:t2 | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L286-L286 | (iii)
EDGE: stepW:w2:x | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L287-L287 | (iv)
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L287-L287 | HasDerivAt.hasDerivWithinAt
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L289-L289 | (iv): boundary values
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L282-L282 | the frozen IsClassicalSolution occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:bound
KIND: step
TITLE: Bound
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L290-L295
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L290-L295
CONTRACT_ID: stepW:w2:bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: t, x in [0,pi]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: derivWithin (u t) (Icc 0 pi) x = u_x(t,x) (endpoints included) and ¦u¦ + ¦u_x¦ + ¦V_m(Y_2(t))(x)¦ <= M_m ¦¦Y(t)¦¦; this is (vi)
CONSTANT_SCOPE: M_m depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:frozen, bpW:w2:ext-deriv, bpW:w2:functionals, bpW:w2:ext-sums, bpW:w0:reconstruction#reconV
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:frozen | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L291-L291 | the derivative within [0,pi]
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L292-L292 | uniqueness of derivatives within [0,pi]
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L293-L293 | (ii): the pointwise bounds
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L295-L295 | norm_fst_le, norm_snd_le
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L294-L294 | V_m occurs directly here (frozen reconV)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:main
KIND: theorem
TITLE: PDE solutions on invariant tori
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L303-L321
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L323-L332
CONTRACT_ID: bpW:w2:main
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; M_m as in Theorem bpW:w2:curve; K : (Fin 2 -> R) -> WaveSpace, nu : Fin 2 -> R, B in R with (H1) IsAnalyticTorusEmbedding K, (H2) the invariance (bpW:w2:inv) for every theta and j in N_+, (H3) ¦¦K(theta)¦¦ <= B for every theta
SOURCE_QUANTIFIERS: for all m > 0, K, nu, B as stated; for every theta_0; (a) for every z in univ x Icc 0 pi; (c), (d) for all t in R, x in [0,pi]
SOURCE_CONCLUSION: with u(t,x) = reconU m hm (K(theta_0 + t nu)).1 x: (a) AnalyticAt R (z -> reconU m hm (K(theta_0 + z.1 nu)).1 z.2) z; (b) IsClassicalSolution m hm u; (c) HasDerivAt (s -> reconU m hm (K(theta_0 + s nu)).1 x) (reconV m hm (K(theta_0 + t nu)).2 x) t; (d) ¦u(t,x)¦ + ¦derivWithin (u t) (Icc 0 pi) x¦ + ¦V_m(K(theta_0 + t nu).2)(x)¦ <= M_m B
CONSTANT_SCOPE: M_m depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:curve, bpW:w2:orbit, stepW:w2:mred, stepW:w2:mconc, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:ellap#WaveSpace, bpW:w0:nlw#IsClassicalSolution, bpW:wh:embedding#IsAnalyticTorusEmbedding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:curve | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L304-L304 | M_m
EDGE: bpW:w2:orbit | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L308-L308 | (H2) is its invariance hypothesis (bpW:w2:inv)
EDGE: stepW:w2:mred | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L324-L324 | proof step
EDGE: stepW:w2:mconc | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L328-L328 | proof step
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L311-L311 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L319-L319 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L304-L304 | the frozen WaveSpace occurs directly here
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L315-L315 | the frozen IsClassicalSolution occurs directly here
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L307-L307 | the frozen IsAnalyticTorusEmbedding occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:mred
KIND: step
TITLE: Reduction to a curve
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L324-L327
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L324-L327
CONTRACT_ID: stepW:w2:mred
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:main: m > 0; M_m as in Theorem bpW:w2:curve; K : (Fin 2 -> R) -> WaveSpace, nu : Fin 2 -> R, B in R with (H1) IsAnalyticTorusEmbedding K, (H2) the invariance (bpW:w2:inv) for every theta and j in N_+, (H3) ¦¦K(theta)¦¦ <= B for every theta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:main (for all m > 0, K, nu, B as stated; for every theta_0; (a) for every z in univ x Icc 0 pi; (c), (d) for all t in R, x in [0,pi]); within the step: theta_0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: from the analyticity conjunct of (H1) and (H2), Y(t) = K(theta_0 + t nu) is an analytic coefficient solution, and the u of the two theorems coincide
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:orbit
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:orbit | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L326-L326 | torus orbits are analytic coefficient solutions
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w2:mconc
KIND: step
TITLE: Conclusions
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L328-L331
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L328-L331
CONTRACT_ID: stepW:w2:mconc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:main: m > 0; M_m as in Theorem bpW:w2:curve; K : (Fin 2 -> R) -> WaveSpace, nu : Fin 2 -> R, B in R with (H1) IsAnalyticTorusEmbedding K, (H2) the invariance (bpW:w2:inv) for every theta and j in N_+, (H3) ¦¦K(theta)¦¦ <= B for every theta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:main (for all m > 0, K, nu, B as stated; for every theta_0; (a) for every z in univ x Icc 0 pi; (c), (d) for all t in R, x in [0,pi]); within the step: theta_0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (a) is (i) of Theorem bpW:w2:curve restricted to R x [0,pi]; (b) is (v); (c) is (ii) restricted to [0,pi]; (d) is (vi) with ¦¦Y(t)¦¦ <= B by (H3) and M_m > 0
CONSTANT_SCOPE: M_m depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:curve, stepW:w2:mred, bpW:w0:reconstruction#reconV
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:curve | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L329-L329 | (i), (ii), (v), (vi)
EDGE: stepW:w2:mred | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L329-L329 | Y is an analytic coefficient solution
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L330-L330 | V_m occurs directly here (frozen reconV)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:clause5
KIND: corollary
TITLE: Clause (5) with the common constant
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L347-L353
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L355-L360
CONTRACT_ID: bpW:w2:clause5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0, C_3 > 0, Gamma subset Fin 2 -> R, nu : (Fin 2 -> R) -> Fin 2 -> R, K : (Fin 2 -> R) -> (Fin 2 -> R) -> WaveSpace; for every I in Gamma: K_I satisfies IsAnalyticTorusEmbedding, ¦¦K_I(theta)¦¦ <= C_3 sqrt(I_0+I_1) for all theta, and the invariance (4) of nlw2 holds; C = max(1,M_m) C_3
SOURCE_QUANTIFIERS: for all such m, C_3, Gamma, nu, K
SOURCE_CONCLUSION: C > 0, C >= C_3, ¦¦K_I(theta)¦¦ <= C sqrt(I_0+I_1), and conclusion (5) of nlw2 holds verbatim with this C
CONSTANT_SCOPE: C depends only on m and C_3 (C = max(1,M_m) C_3)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:main, bpW:w2:curve, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:nlw#IsClassicalSolution, bpW:w0:ellap#WaveSpace, bpW:wh:embedding#IsAnalyticTorusEmbedding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:main | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L358-L358 | applied with K = K_I, nu = nu(I), B = C_3 sqrt(I_0+I_1)
EDGE: bpW:w2:curve | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L351-L351 | the constant M_m
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L351-L351 | (4) of nlw2 involves lambda_j
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L351-L351 | (4) of nlw2 involves cubicGrad
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L351-L351 | (4) of nlw2 involves coeff
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L352-L352 | (5) of nlw2 involves reconU
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L352-L352 | (5) of nlw2 involves reconV
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L352-L352 | (5) of nlw2 involves IsClassicalSolution
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L349-L349 | the frozen WaveSpace occurs directly here
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L350-L350 | the frozen IsAnalyticTorusEmbedding occurs directly here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Consumer: the W8 assembly (later wave) for the root bpW:wh:nlw2. The statement speaks of the form of conclusions (4)-(5) of nlw2; that is not a use of the root.

NODE: bpW:w3:ext-multilinear
KIND: external
TITLE: Multilinear maps
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-multilinear@L42-L48
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:ext-multilinear
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: continuous multilinear maps between Banach spaces form a Banach space under the operator norm; inserting a continuous multilinear map into a slot of another, or composing with continuous linear maps, gives a continuous multilinear map of norm at most the product; the diagonal P(w) = M(w,...,w) of a continuous d-linear M is C^infinity with DP(w)v = sum_i M(w,..,v (slot i),..,w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:ext-series
KIND: external
TITLE: Power series
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-series@L49-L59
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:ext-series
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: if (M_n) are continuous n-linear with sum ¦¦M_n¦¦ r^n < infinity then f(w) = sum M_n(w,..,w) has this power series on the open ball of radius r, is analytic there, derivative termwise; finite sums, compositions and continuous multilinear images of analytic maps are analytic; A -> A^{-1} is analytic on the units of a Banach algebra; the derivative of an analytic map is analytic; C-analytic implies R-analytic; a FormalMultilinearSeries carries explicit zero coefficients
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:ext-tsum
KIND: external
TITLE: Termwise differentiation
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-tsum@L60-L68
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:ext-tsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: termwise differentiation of sum f_k on an open convex set under sum sup ¦¦Df_k¦¦ < infinity and convergence at a point; absolutely summable families may be regrouped along any partition; for a continuous multilinear B and absolutely summable families, B(sum a^1,..,sum a^r) = sum B(a^1_{i_1},..,a^r_{i_r}) absolutely (Cauchy products)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:ext-mvt
KIND: external
TITLE: Mean value inequality; zero derivative
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-mvt@L69-L72
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:ext-mvt
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: mean value inequality ¦¦f(y) - f(x)¦¦ <= M ¦¦y - x¦¦ on a convex set with ¦¦Df¦¦ <= M; a differentiable function on an interval with vanishing derivative is constant
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:ext-integral
KIND: external
TITLE: Integrals in a parameter
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-integral@L73-L82
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:ext-integral
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: for Y : [0,1] x U -> V continuous, differentiable in w with D_w Y continuous and bounded, w -> int_0^1 Y(t,w) dt is differentiable with derivative int D_w Y (complex differentiable over C); the fundamental theorem of calculus for C^1 maps [0,1] -> V; continuous linear maps commute with the Bochner integral; ¦¦int Y¦¦ <= int ¦¦Y¦¦; termwise integration of sum g_j with sup ¦¦g_j¦¦ <= c_j, sum c_j < infinity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:ext-neumann
KIND: external
TITLE: Neumann series
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:ext-neumann@L83-L86
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:ext-neumann
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: if A is a bounded operator on a Banach space with ¦¦A - I¦¦ <= 1/2 then A is invertible, ¦¦A^{-1}¦¦ <= 2, ¦¦A^{-1} - I¦¦ <= 2¦¦A - I¦¦, and A^{-1} = sum_{n>=0} (I - A)^n absolutely
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:space
KIND: definition
TITLE: Two-sided coordinate space
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:space@L108-L116
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:space
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; typing data a >= 0, r in R
SOURCE_QUANTIFIERS: a, r
SOURCE_CONCLUSION: defines W_{a,r} = complex families (w_l)_{l in Z\0} with ¦¦w¦¦_{a,r}^2 = sum_{l != 0} ¦l¦^{2r} e^{2a¦l¦} ¦w_l¦^2 < infinity; W = W_{a,p}, W+ = W_{a,p+1} (norms ¦¦.¦¦, ¦¦.¦¦_+); tilde w (¦l¦ <= 2) and hat w (¦l¦ >= 3); lambda'_l = sgn(l) lambda_¦l¦; Lean carrier lp (Bool x PNat -> C) 2 in weighted coordinates
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3#data, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:space@L111-L111 | W = W_{a,p} with the standing a, p
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:space@L113-L113 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:coords
KIND: lemma
TITLE: Complex coordinates and real structure
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L119-L128
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L130-L136
CONTRACT_ID: bpW:w3:coords
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; E^C = l^{a,p}_C x l^{a,p}_C with the max norm; Z : E^C -> W, (Zx)_j = (q_j + i p_j)/sqrt2, (Zx)_{-j} = (q_j - i p_j)/sqrt2
SOURCE_QUANTIFIERS: for all x in E^C, w in W
SOURCE_CONCLUSION: Z is a C-linear bijection with ¦¦x¦¦_E <= ¦¦Zx¦¦ <= sqrt2 ¦¦x¦¦_E, mapping E^C_{a,p+1} onto W+ with the same bounds; rho(w)_l = conj(w_{-l}) is a conjugate-linear isometric involution of W and W+; Z maps the real E_{a,p} bijectively onto W_R = {rho w = w}; on real points w_j = z_j, w_{-j} = zbar_j, w_j w_{-j} = ¦z_j¦^2 = I_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:space, bpW:w0:z, bpW:w0:actions
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:space | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L121-L121 | the space W
EDGE: bpW:w0:z | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L127-L127 | the complex coordinates z_j
EDGE: bpW:w0:actions | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:coords@L127-L127 | I_j = ¦z_j¦^2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:omega
KIND: lemma
TITLE: Symplectic form
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L139-L145
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L147-L151
CONTRACT_ID: bpW:w3:omega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}
SOURCE_QUANTIFIERS: for all w, w' in W; x, x' real in E
SOURCE_CONCLUSION: Omega(w,w') = i sum_{l != 0} sgn(l) w_l w'_{-l} is continuous antisymmetric bilinear on W, ¦Omega(w,w')¦ <= ¦¦w¦¦ ¦¦w'¦¦, nondegenerate (Omega(zeta,e_{-l}) = i sgn(l) zeta_l); Omega(Zx,Zx') = sum (q_j p'_j - p_j q'_j) (the form sum dq ^ dp); Omega(rho w, rho w') = conj Omega(w,w')
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:space, bpW:w3:coords, bpW:w0:eqmotion
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:space | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L140-L140 | the space W and its norm
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L149-L149 | the inverse formulas of Z
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:omega@L144-L144 | the symplectic form sum dq_j ^ dp_j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:hamfield-def
KIND: definition
TITLE: Hamiltonian field; one-smoothing holomorphic class
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L154-L162
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:hamfield-def
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; U subset W open, P : U -> C complex differentiable
SOURCE_QUANTIFIERS: U, P
SOURCE_CONCLUSION: defines X_P as the map with DP(w)v = Omega(X_P(w),v) for all w in U, v in W (unique, X_P(w)_l = -i sgn(l) DP(w) e_{-l}); P real iff P(rho w) = conj P(w) on U = rho U (then X_P o rho = rho o X_P); the class A(U) of real P analytic on U whose Hamiltonian field exists, takes values in W+, and is analytic U -> W+; analytic maps are holomorphic (Definition bpW:w1:holomorphic)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:omega, bpW:w3:coords, bpW:w1:holomorphic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L157-L157 | uniqueness by nondegeneracy; the formula for X_P
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L158-L158 | the involution rho
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L161-L161 | holomorphic maps
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:real-restrict
KIND: lemma
TITLE: Real restrictions
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L171-L177
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L179-L186
CONTRACT_ID: bpW:w3:real-restrict
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; U subset W open with rho U = U; V in {W, W+} with real form E_V in {E_{a,p}, E_{a,p+1}}; f : U -> V analytic with f o rho = rho o f; (second claim) P : U -> C analytic and real
SOURCE_QUANTIFIERS: for all such U, V, f, P
SOURCE_CONCLUSION: f^R(x) = Z^{-1} f(Zx), x in Z^{-1}(U) cap E_{a,p}, takes values in E_V and is real analytic; x -> P(Zx) is real valued and real analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:coords, bpW:w3:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L182-L182 | Z and the projection Pi are continuous R-linear
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:real-restrict@L180-L180 | C-analytic is R-analytic; compositions
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:forms
KIND: definition
TITLE: Smoothing symmetric forms
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L189-L197
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:forms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; d >= 2; P a continuous symmetric d-linear form on W
SOURCE_QUANTIFIERS: P, c
SOURCE_CONCLUSION: defines: P is smoothing with constant c if there is a continuous (d-1)-linear nabla P : W^{d-1} -> W+ with P(w^1,..,w^{d-1},v) = Omega(nabla P(w^1,..),v) and ¦¦nabla P(..)¦¦_+ <= c prod ¦¦w^i¦¦; and records that then X_P(w) = d nabla P(w,..,w), ¦P(w)¦ <= c¦¦w¦¦^d, ¦¦X_P(w)¦¦_+ <= dc¦¦w¦¦^{d-1}, ¦¦X_P(y) - X_P(w)¦¦_+ <= d(d-1)c max(¦¦y¦¦,¦¦w¦¦)^{d-2} ¦¦y - w¦¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:omega, bpW:w3:hamfield-def, bpW:w3:ext-multilinear
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L192-L192 | the symplectic form
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L194-L194 | the Hamiltonian field X_P
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:forms@L194-L194 | derivative of the diagonal of a multilinear map
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:Lambda
KIND: lemma
TITLE: The linear part
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L200-L206
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L208-L212
CONTRACT_ID: bpW:w3:Lambda
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}
SOURCE_QUANTIFIERS: for all w, v in W; w in W+ for the field; real x
SOURCE_CONCLUSION: Lambda(w) = sum_{j>=1} lambda_j w_j w_{-j} is a continuous quadratic form on W with ¦Lambda(w)¦ <= sqrt(1+m) ¦¦w¦¦^2, Lambda(Zx) = (1/2) sum lambda_j (q_j^2 + p_j^2) for real x; DLambda(w)v = sum_{l != 0} lambda_¦l¦ w_{-l} v_l; for w in W+ its Hamiltonian field is X_Lambda(w)_l = -i lambda'_l w_l, bounded linear W+ -> W of norm <= sqrt(1+m); X_Lambda does not map W into itself
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:space, bpW:w0:H, bpW:w3:coords, bpW:w0:basis#lambda-facts, bpW:w3:hamfield-def, bpW:w1:diag, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:space | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L201-L201 | W, W+ and lambda'
EDGE: bpW:w0:H | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L203-L203 | the quadratic part of H
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L202-L202 | Z on real points
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L209-L209 | lambda_j <= sqrt(1+m) j
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L210-L210 | the field from Definition bpW:w3:hamfield-def
EDGE: bpW:w1:diag | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L211-L211 | (i) with r = 1: the operator bound
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Lambda@L201-L201 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:majorant
KIND: lemma
TITLE: Majorant for the cubic sums
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L232-L239
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L241-L245
CONTRACT_ID: bpW:w3:majorant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; nonnegative u, u', u'' in l^{a,p}; M(u,u',u'')_l = lambda_l^{-1/2} sum_{i,j,k} ¦g_ijkl¦ u_i u'_j u''_k/sqrt(lambda_i lambda_j lambda_k)
SOURCE_QUANTIFIERS: for all such u, u', u''
SOURCE_CONCLUSION: the sums converge and ¦¦M(u,u',u'')¦¦_{a,p+1} <= C_* ¦¦u¦¦ ¦¦u'¦¦ ¦¦u''¦¦, C_* = K_{p+1/2}^2/pi; C_* does not depend on m; for a = p = 1, C_* = 8(1+2 zeta(3))/pi
CONSTANT_SCOPE: C_* depends only on p (not on m, not on a)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, bpW:w0n:algebra, stepW:w0n:majorant, stepW:w0n:selection, stepW:w0n:smoothing, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L234-L234 | the coefficients g_ijkl
EDGE: bpW:w0n:algebra | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L237-L237 | K_s
EDGE: stepW:w0n:majorant | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L242-L242 | the W0 majorant step applied to q = u
EDGE: stepW:w0n:selection | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L242-L242 | the W0 selection step
EDGE: stepW:w0n:smoothing | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L242-L242 | the W0 smoothing step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:majorant@L234-L234 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:quartic
KIND: lemma
TITLE: Quartic forms
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L248-L259
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L261-L278
CONTRACT_ID: bpW:w3:quartic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; S subset (Z\0)^4 invariant under permutations and x -> -x; c_x with c_x = c_{sigma x} = conj(c_{-x}) and ¦c_x¦ <= ¦frak g_x¦; P(w^1..w^4) = (1/16) sum_{x in S} c_x w^1_{x_1} w^2_{x_2} w^3_{x_3} w^4_{x_4}
SOURCE_QUANTIFIERS: for all such S, c
SOURCE_CONCLUSION: P converges absolutely, is continuous, symmetric, smoothing with constant C_*/4, with nabla P(w^1,w^2,w^3)_l = -(i sgn(l)/16) sum_{y : (y,-l) in S} c_{(y,-l)} w^1_{y_1} w^2_{y_2} w^3_{y_3}; its diagonal P is real; with c = frak g on (Z\0)^4, T, T cap paired, T^c one obtains frak G, frak G^tan, bar frak G, frak G^nor and G, G^tan, bar G, G^nor; G = G^tan + G^nor; ¦¦X_P(w)¦¦_+ <= C_* ¦¦w¦¦^3, ¦P(w)¦ <= (C_*/4)¦¦w¦¦^4 for these P
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic-sec#data, bpW:w3:forms, stepW:w3:maj, stepW:w3:gradbound, stepW:w3:identify
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic-sec#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L250-L250 | frak g, pairing and T
EDGE: bpW:w3:forms | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L252-L252 | smoothing forms
EDGE: stepW:w3:maj | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L262-L262 | proof step
EDGE: stepW:w3:gradbound | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L266-L266 | proof step
EDGE: stepW:w3:identify | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic@L270-L270 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:maj
KIND: step
TITLE: Majorize
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L262-L265
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L262-L265
CONTRACT_ID: stepW:w3:maj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; S subset (Z\0)^4 invariant under permutations and x -> -x; c_x with c_x = c_{sigma x} = conj(c_{-x}) and ¦c_x¦ <= ¦frak g_x¦; P(w^1..w^4) = (1/16) sum_{x in S} c_x w^1_{x_1} w^2_{x_2} w^3_{x_3} w^4_{x_4}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic (for all such S, c); within the step: w^1, w^2, w^3; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: with u^t_i = ¦w^t_i¦ + ¦w^t_{-i}¦, ¦¦u^t¦¦_{a,p} <= sqrt2 ¦¦w^t¦¦ and sum_y ¦frak g_{(y,-l)}¦ ¦w^1_{y_1} w^2_{y_2} w^3_{y_3}¦ <= M(u^1,u^2,u^3)_¦l¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:majorant, bpW:w3:quartic-sec#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:majorant | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L265-L265 | the majorant M
EDGE: bpW:w3:quartic-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:maj@L265-L265 | frak g
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:gradbound
KIND: step
TITLE: Bound the gradient
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L266-L269
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L266-L269
CONTRACT_ID: stepW:w3:gradbound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; S subset (Z\0)^4 invariant under permutations and x -> -x; c_x with c_x = c_{sigma x} = conj(c_{-x}) and ¦c_x¦ <= ¦frak g_x¦; P(w^1..w^4) = (1/16) sum_{x in S} c_x w^1_{x_1} w^2_{x_2} w^3_{x_3} w^4_{x_4}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic (for all such S, c); within the step: w^1, w^2, w^3; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦nabla P¦¦_+ <= (C_*/4) prod ¦¦w^t¦¦
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:majorant, stepW:w3:maj
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:majorant | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L267-L267 | the bound C_*
EDGE: stepW:w3:maj | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradbound@L268-L268 | the majorization
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:identify
KIND: step
TITLE: Identify
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L270-L277
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L270-L277
CONTRACT_ID: stepW:w3:identify
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; S subset (Z\0)^4 invariant under permutations and x -> -x; c_x with c_x = c_{sigma x} = conj(c_{-x}) and ¦c_x¦ <= ¦frak g_x¦; P(w^1..w^4) = (1/16) sum_{x in S} c_x w^1_{x_1} w^2_{x_2} w^3_{x_3} w^4_{x_4}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic (for all such S, c); within the step: w^1, w^2, w^3, v; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Omega(nabla P(w^1,w^2,w^3),v) = P(w^1,w^2,w^3,v); symmetry; reality P(rho w) = conj P(w); the bounds by Definition bpW:w3:forms with d = 4, c = C_*/4; frak g and the four sets are invariant; (Z\0)^4 = T disjoint union T^c
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:omega, stepW:w3:maj, bpW:w3:forms, stepW:w3:gradbound, bpW:w3:coords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L271-L271 | the form Omega
EDGE: stepW:w3:maj | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L274-L274 | absolute convergence
EDGE: bpW:w3:forms | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L276-L276 | the bounds for d = 4
EDGE: stepW:w3:gradbound | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L276-L276 | c = C_*/4
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:identify@L275-L275 | the involution rho
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:quartic-ident
KIND: lemma
TITLE: Identification with Part~0
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L282-L291
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L293-L312
CONTRACT_ID: bpW:w3:quartic-ident
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for all real x; for all w in W; for x in T
SOURCE_CONCLUSION: G(Zx) = G(q) of Definition bpW:w0:H for a > 0 (definition of G on E_{0,p} for a = 0); Z^{-1} X_G(Zx) = (0,-T(q,q,q)), which is (0,-G_q(q)) for a > 0; G^nor(w) = G^nor(hat w), X_{G^nor} has vanishing tangential components, ¦G^nor(w)¦ <= (C_*/4)¦¦hat w¦¦^4, ¦¦X_{G^nor}(w)¦¦_+ <= C_*¦¦hat w¦¦^3; with I_j := w_j w_{-j}, bar G(w) = (1/2) sum_{i,j in J} A_ij I_i I_j + sum_{j>=3, i in J} B_ji I_i I_j (corrected A, B); x in T with frak g_x != 0 has delta_x = 0 iff x is paired
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic, bpW:w0:H, bpW:w0n:cubic-bound, bpW:w0n:AB, stepW:w3:Gz, stepW:w3:XG, stepW:w3:Gnor, stepW:w3:count, stepW:w3:res, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L283-L283 | the forms G, G^nor, bar G
EDGE: bpW:w0:H | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L283-L283 | G(q) of Definition bpW:w0:H
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L284-L284 | the trilinear T
EDGE: bpW:w0n:AB | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L289-L289 | the corrected A, B
EDGE: stepW:w3:Gz | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L294-L294 | proof step
EDGE: stepW:w3:XG | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L298-L298 | proof step
EDGE: stepW:w3:Gnor | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L302-L302 | proof step
EDGE: stepW:w3:count | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L304-L304 | proof step
EDGE: stepW:w3:res | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L309-L309 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L305-L305 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-ident@L285-L285 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:Gz
KIND: step
TITLE: The quartic
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L294-L297
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L294-L297
CONTRACT_ID: stepW:w3:Gz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: real x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: expanding prod (z + zbar) in (bpW:w0n:Gz) gives G(Zx) = (1/16) sum frak g_x w_x, absolutely convergent, and G(q) agrees with (bpW:w0n:Gz)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:birkhoff#data, bpW:w3:quartic, bpW:w0n:gradient
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:birkhoff#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L295-L295 | the identity (bpW:w0n:Gz)
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L296-L296 | absolute convergence
EDGE: bpW:w0n:gradient | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L297-L297 | G(q) as the quartic sum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:XG
KIND: step
TITLE: The field
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L301
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L301
CONTRACT_ID: stepW:w3:XG
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: real points; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Z^{-1} X_G = (d_p G, -d_q G) with d_p G = 0 and d_{q_l} G = T(q,q,q)_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:hamfield-def#hamilton, bpW:w0n:gradient, bpW:w0n:cubic-bound
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:hamfield-def#hamilton | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L299-L299 | on real points Z^{-1} X_P = (d_p P, -d_q P)
EDGE: bpW:w0n:gradient | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L301-L301 | d_{q_l} G = G_q(q)_l = T(q,q,q)_l
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L301-L301 | the trilinear T
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:Gnor
KIND: step
TITLE: Normal part
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L302-L303
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L302-L303
CONTRACT_ID: stepW:w3:Gnor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: x in T^c; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: every x in T^c has all ¦x_t¦ >= 3, whence the normal-part claims
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic-sec#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L303-L303 | the set T
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:count
KIND: step
TITLE: Count the paired terms
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L304-L308
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L304-L308
CONTRACT_ID: stepW:w3:count
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: 1 <= r <= s, r in J; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the paired terms contribute (3/(2 pi lambda_r lambda_s)) I_r I_s (r < s, 24 orderings) and (1/2) A_rr I_r^2 (r = s, 6 orderings): the coefficients of Theorem bpW:w0n:AB
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, bpW:w0n:AB, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L305-L305 | g_rrss = 1/pi, g_rrrr = 3/(2pi)
EDGE: bpW:w0n:AB | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L308-L308 | A and B
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:count@L305-L305 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:res
KIND: step
TITLE: Resonance
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L309-L311
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L309-L311
CONTRACT_ID: stepW:w3:res
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: frak g_x != 0 and delta_x = 0 force pairing
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:nonres
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:nonres | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:res@L310-L310 | applied to the indices ¦x¦ with signs sgn x_t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:divisor
KIND: lemma
TITLE: Divisor lower bound; P96-W Lemma~4
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L317-L323
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L325-L364
CONTRACT_ID: bpW:w3:divisor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦
SOURCE_QUANTIFIERS: for all such x
SOURCE_CONCLUSION: ¦delta_x¦ >= m/(27 (n^2+m)^{3/2}); consequently, if x in T, frak g_x != 0 and x is not paired, ¦delta_x¦ >= delta_*(m) := m/(27 (4+m)^{3/2})
CONSTANT_SCOPE: delta_* depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic-sec#data, bpW:w0:basis#lambda-facts, stepW:w3:sel, stepW:w3:signs, stepW:w3:s0, stepW:w3:s1, stepW:w3:s23, stepW:w3:s1inner, stepW:w3:divconcl, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic-sec#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L318-L318 | delta_x, pairing, T
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L327 | f'(s) = s/f(s) increasing, f'' = m/f^3 > 0 decreasing
EDGE: stepW:w3:sel | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L329-L329 | proof step
EDGE: stepW:w3:signs | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L333-L333 | proof step
EDGE: stepW:w3:s0 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L337-L337 | proof step
EDGE: stepW:w3:s1 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L339-L339 | proof step
EDGE: stepW:w3:s23 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L344-L344 | proof step
EDGE: stepW:w3:s1inner | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L349-L349 | proof step
EDGE: stepW:w3:divconcl | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L360-L360 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L327-L327 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:sel
KIND: step
TITLE: Selection rule
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:sel@L329-L332
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:sel@L329-L332
CONTRACT_ID: stepW:w3:sel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L326-L328)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); within the step: a <= b <= c <= d sorted ¦x_t¦; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: d = a+b+c or d = b+c-a
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:signs
KIND: step
TITLE: Signs
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:signs@L333-L336
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:signs@L333-L336
CONTRACT_ID: stepW:w3:signs
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L326-L328)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); within the step: sign patterns; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: WLOG at most two x_t negative; it suffices to bound the divisor of each sign pattern on (a,b,c,d)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:s0
KIND: step
TITLE: No minus sign
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L337-L338
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L337-L338
CONTRACT_ID: stepW:w3:s0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L326-L328)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: with no minus sign delta >= 4 > beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L338-L338 | lambda_k > k >= 1
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L338-L338 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:s1
KIND: step
TITLE: One minus sign
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L339-L343
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L339-L343
CONTRACT_ID: stepW:w3:s1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L326-L328)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: with one minus sign the divisor is >= m/(2 lambda_a) >= beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:sel, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:sel | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L343-L343 | a + b + c >= d
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L340-L340 | f(k) - k = m/(f(k)+k); lambda_c + c <= lambda_d + d
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L340-L340 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:s23
KIND: step
TITLE: Two minus signs, outer pairs
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L344-L348
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L344-L348
CONTRACT_ID: stepW:w3:s23
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L326-L328)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: delta_3 = lambda_c + lambda_d - lambda_a - lambda_b and delta_2 = (lambda_b - lambda_a) + (lambda_d - lambda_c) vanish identically iff paired, and otherwise are >= a/lambda_a >= beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L346-L346 | lambda_{k+1} - lambda_k >= f'(k) >= f'(a)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L345-L345 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:s1inner
KIND: step
TITLE: Two minus signs, inner pair
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L349-L359
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L349-L359
CONTRACT_ID: stepW:w3:s1inner
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L326-L328)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); within the step: cases (i), (ii); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: delta_1 = lambda_a + lambda_d - lambda_b - lambda_c is paired iff a = b, c = d, and otherwise >= beta: (i) d = b+c-a via f'' >= m/(27 lambda_a^3); (ii) d = a+b+c via 2a f'(b) >= 2/sqrt(1+m) >= beta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:sel, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:sel | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L352-L352 | the two cases d = b+c-a, d = a+b+c
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L353-L353 | f' increasing, f'' = m/f^3
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L350-L350 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:divconcl
KIND: step
TITLE: Conclusion
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L360-L363
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L360-L363
CONTRACT_ID: stepW:w3:divconcl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:divisor: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; n general in this lemma; x in (Z\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦; local data: a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); beta = m/(27 lambda_a^3) (proof preamble L326-L328)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:divisor (for all such x); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: two-minus patterns are +-delta_1, +-delta_2, +-delta_3 and pairing coincides with identical vanishing; the corollary follows since frak g_x != 0 implies the selection rule, n <= 2 on T, and n -> m/(n^2+m)^{3/2} is decreasing
CONSTANT_SCOPE: delta_* depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:s0, stepW:w3:s1, stepW:w3:s23, stepW:w3:s1inner, bpW:w0n:quartic-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:s0 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L361-L361 | no minus sign
EDGE: stepW:w3:s1 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L361-L361 | one minus sign
EDGE: stepW:w3:s23 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L361-L361 | delta_2, delta_3
EDGE: stepW:w3:s1inner | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L361-L361 | delta_1
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divconcl@L363-L363 | frak g_x != 0 implies the selection rule
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:Fdef
KIND: definition
TITLE: Generating Hamiltonian
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Fdef@L385-L391
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:Fdef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}
SOURCE_QUANTIFIERS: x; w^1..w^4
SOURCE_CONCLUSION: defines f_x = frak g_x/delta_x for x in T not paired, f_x = 0 otherwise (Lean: division by 0 is 0; Lemma bpW:w3:divisor guarantees delta_x != 0 where frak g_x != 0); frak F(w^1..w^4) = (i/16) sum_x f_x w^1_{x_1} .. w^4_{x_4}, F(w) = frak F(w,w,w,w), S = 4 nabla frak F : W^3 -> W+, X_F(w) = S(w,w,w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic-sec#data, bpW:w3:forms
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic-sec#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Fdef@L386-L386 | frak g, delta, pairing, T
EDGE: bpW:w3:forms | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Fdef@L390-L390 | nabla of a form
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:F
KIND: theorem
TITLE: $F$ is bounded and one-smoothing
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L396-L403
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L405-L414
CONTRACT_ID: bpW:w3:F
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; frak F, F, S of Definition bpW:w3:Fdef
SOURCE_QUANTIFIERS: for all w, w^i, v
SOURCE_CONCLUSION: frak F is a continuous symmetric 4-linear form, smoothing with constant C_*/(4 delta_*), F real; S is a continuous symmetric trilinear W^3 -> W+ with ¦¦S(w^1,w^2,w^3)¦¦_+ <= C_F prod ¦¦w^i¦¦, C_F = C_*/delta_*(m) = 27 C_* (4+m)^{3/2}/m; Omega(S(w^1,w^2,w^3),v) = 4 frak F(w^1,w^2,w^3,v) symmetric in all four; S commutes with rho; ¦F(w)¦ <= (C_F/4)¦¦w¦¦^4; X_F is a cubic polynomial, analytic W -> W+
CONSTANT_SCOPE: C_F depends on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Fdef, stepW:w3:fcoef, stepW:w3:Fconcl
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Fdef | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L397-L397 | frak F, F, S
EDGE: stepW:w3:fcoef | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L406-L406 | proof step
EDGE: stepW:w3:Fconcl | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:F@L410-L410 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:fcoef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L406-L409
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L406-L409
CONTRACT_ID: stepW:w3:fcoef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:F: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; frak F, F, S of Definition bpW:w3:Fdef
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:F (for all w, w^i, v); within the step: x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: f is permutation invariant, f_{-x} = -f_x, ¦f_x¦ <= ¦frak g_x¦/delta_*; c_x := i delta_* f_x satisfies the hypotheses of Lemma bpW:w3:quartic and frak F = delta_*^{-1} P_c
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:divisor, bpW:w3:quartic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:divisor | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L408-L408 | ¦delta_x¦ >= delta_*
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:fcoef@L408-L408 | its coefficient hypotheses
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:Fconcl
KIND: step
TITLE: Conclusions
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L410-L413
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L410-L413
CONTRACT_ID: stepW:w3:Fconcl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:F: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; frak F, F, S of Definition bpW:w3:Fdef
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:F (for all w, w^i, v); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: smoothing with constant C_*/(4 delta_*) and reality; S = 4 nabla frak F gives C_F; reality of S; analyticity of X_F
CONSTANT_SCOPE: C_F depends on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic, stepW:w3:fcoef, bpW:w3:hamfield-def, bpW:w3:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L411-L411 | smoothing and reality of P_c
EDGE: stepW:w3:fcoef | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L411-L411 | frak F = P_c/delta_*
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L413-L413 | reality of the field from reality of the form
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Fconcl@L413-L413 | polynomials are analytic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:homological
KIND: proposition
TITLE: Homological identity
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L417-L422
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L424-L439
CONTRACT_ID: bpW:w3:homological
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Z' = bar G - G^tan, the diagonal of frak z = bar frak G - frak G^tan
SOURCE_QUANTIFIERS: for every w in W
SOURCE_CONCLUSION: frak z is a form as in Lemma bpW:w3:quartic, smoothing with constant C_*/4, ¦¦X_{Z'}(w)¦¦_+ <= C_*¦¦w¦¦^3; DLambda(w) X_F(w) = Z'(w), equivalently G + DLambda . X_F = bar G + G^nor
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic, stepW:w3:Xfcoord, stepW:w3:euler, stepW:w3:divide, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L418-L418 | the forms bar frak G, frak G^tan and their bounds
EDGE: stepW:w3:Xfcoord | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L425-L425 | proof step
EDGE: stepW:w3:euler | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L428-L428 | proof step
EDGE: stepW:w3:divide | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L434-L434 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:homological@L429-L429 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:Xfcoord
KIND: step
TITLE: Field coordinates
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L425-L427
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L425-L427
CONTRACT_ID: stepW:w3:Xfcoord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:homological: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Z' = bar G - G^tan, the diagonal of frak z = bar frak G - frak G^tan
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:homological (for every w in W); within the step: w, l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: X_F(w)_l = 4 nabla frak F(w,w,w)_l = (sgn(l)/4) sum_y f_{(y,-l)} w_y
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Fdef, bpW:w3:quartic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Fdef | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L426-L426 | S = 4 nabla frak F
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Xfcoord@L426-L426 | the formula for nabla
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:euler
KIND: step
TITLE: Euler identity
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L428-L433
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L428-L433
CONTRACT_ID: stepW:w3:euler
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:homological: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Z' = bar G - G^tan, the diagonal of frak z = bar frak G - frak G^tan
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:homological (for every w in W); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: DLambda(w) X_F(w) = -(1/16) sum_x delta_x f_x w_x, all series absolutely convergent
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Lambda, stepW:w3:Xfcoord, bpW:w3:F, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L429-L429 | DLambda(w)v
EDGE: stepW:w3:Xfcoord | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L429-L429 | the coordinates of X_F
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L433-L433 | ¦¦X_F(w)¦¦_+ < infinity
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L432-L432 | lambda_¦l¦ <= sqrt(1+m) ¦l¦^{p+1} e^{a¦l¦}
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:euler@L429-L429 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:divide
KIND: step
TITLE: Divide
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L434-L438
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L434-L438
CONTRACT_ID: stepW:w3:divide
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:homological: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Z' = bar G - G^tan, the diagonal of frak z = bar frak G - frak G^tan
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:homological (for every w in W); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: delta_x f_x = frak g_x on T \ paired and 0 else, so the sum is bar G - G^tan; with G = G^tan + G^nor the second form
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:euler, bpW:w3:divisor, bpW:w3:quartic
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:euler | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L436-L436 | the sum
EDGE: bpW:w3:divisor | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L436-L436 | delta_x != 0 where frak g_x != 0
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:divide@L437-L437 | the forms and G = G^tan + G^nor
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:lie-coeff
KIND: definition
TITLE: Lie coefficients
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L451-L456
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:lie-coeff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; S of Definition bpW:w3:Fdef
SOURCE_QUANTIFIERS: k >= 0
SOURCE_CONCLUSION: defines the continuous (2k+1)-linear Phi_k : W^{2k+1} -> W by Phi_0(w) = w and the recursion Phi_{k+1}(w^1..w^{2k+3}) = (1/(k+1)) sum_{i=1}^{2k+1} Phi_k(w^1,..,w^{i-1},S(w^i,w^{i+1},w^{i+2}),w^{i+3},..), phi_k(w) = Phi_k(w,..,w), and (LQ)(w) = DQ(w) X_F(w) for C^1 maps Q
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Fdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Fdef | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L453-L453 | S and X_F
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:leibniz
KIND: lemma
TITLE: Coefficient bounds and the Leibniz identity
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L460-L470
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L472-L491
CONTRACT_ID: bpW:w3:leibniz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff
SOURCE_QUANTIFIERS: for all k >= 0
SOURCE_CONCLUSION: (i) phi_{k+1} = L phi_k/(k+1), phi_k = L^k(id)/k!; (ii) ¦¦Phi_k¦¦ <= (2C_F)^k and for k >= 1 Phi_k takes values in W+ with ¦¦Phi_k¦¦_{W^{2k+1} -> W+} <= (2C_F)^k; (iii) Phi_k commutes with rho; (iv) (k+1) phi_{k+1} = sum_{a+b+c=k} S(phi_a,phi_b,phi_c) and (k+1) D phi_{k+1}(w)v = sum_{a+b+c=k} 3 S(D phi_a(w)v, phi_b(w), phi_c(w))
CONSTANT_SCOPE: C_F depends on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:lie-coeff, stepW:w3:rec, stepW:w3:norms, stepW:w3:Phireal, stepW:w3:leib, stepW:w3:leibid
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:lie-coeff | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L463-L463 | Phi_k, phi_k, L
EDGE: stepW:w3:rec | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L473-L473 | proof step
EDGE: stepW:w3:norms | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L476-L476 | proof step
EDGE: stepW:w3:Phireal | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L481-L481 | proof step
EDGE: stepW:w3:leib | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L483-L483 | proof step
EDGE: stepW:w3:leibid | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:leibniz@L487-L487 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:rec
KIND: step
TITLE: Recursion
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L473-L475
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L473-L475
CONTRACT_ID: stepW:w3:rec
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:leibniz: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:leibniz (for all k >= 0); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i): D phi_k(w)v = sum_i Phi_k(w,..,v,..,w) with v = S(w,w,w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-multilinear, bpW:w3:lie-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L474-L474 | derivative of the diagonal
EDGE: bpW:w3:lie-coeff | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:rec@L475-L475 | the recursion
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:norms
KIND: step
TITLE: Norms
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L476-L480
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L476-L480
CONTRACT_ID: stepW:w3:norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:leibniz: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:leibniz (for all k >= 0); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii): ¦¦Phi_{k+1}¦¦ <= 2 C_F ¦¦Phi_k¦¦ in W and in W+
CONSTANT_SCOPE: C_F depends on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-multilinear, bpW:w3:F, bpW:w3:lie-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L477-L477 | norms of inserted multilinear maps
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L477-L477 | ¦¦S¦¦ <= C_F
EDGE: bpW:w3:lie-coeff | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:norms@L479-L479 | Phi_1 = S and the recursion
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:Phireal
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L481-L482
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L481-L482
CONTRACT_ID: stepW:w3:Phireal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:leibniz: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:leibniz (for all k >= 0); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) by induction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:F
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Phireal@L482-L482 | S commutes with rho
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:leib
KIND: step
TITLE: Leibniz rule
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L483-L486
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L483-L486
CONTRACT_ID: stepW:w3:leib
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:leibniz: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:leibniz (for all k >= 0); within the step: n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: for continuous multilinear B and C^infinity Q_i, L B(Q_1..Q_r) = sum_i B(..,LQ_i,..) and the multinomial formula for L^n B(Q_1..Q_r)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-multilinear
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leib@L484-L484 | product and chain rules for multilinear maps
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:leibid
KIND: step
TITLE: The identity
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L487-L490
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L487-L490
CONTRACT_ID: stepW:w3:leibid
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:leibniz: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:leibniz (for all k >= 0); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): (k+1)! phi_{k+1} = L^k(S(id,id,id)) = sum_{a+b+c=k} (k!/(a!b!c!)) S(a! phi_a, b! phi_b, c! phi_c), and the derivative identity by symmetry of S
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:rec, stepW:w3:leib, bpW:w3:F
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:rec | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L489-L489 | (i)
EDGE: stepW:w3:leib | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L489-L489 | the Leibniz rule
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:leibid@L490-L490 | symmetry of S
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:flow
KIND: theorem
TITLE: The flow of $X_F$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L494-L517
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L519-L556
CONTRACT_ID: bpW:w3:flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2 <= 1/10; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})
SOURCE_CONCLUSION: (i) the series converges absolutely, w -> Gamma_t(w) has the power series (t^k Phi_k) on B_{rho_0} and is analytic, Gamma_t - id is analytic B_{rho_0} -> W+, (t,w) -> Gamma_t(w) is C^1; (ii) Gamma_0 = id, d_t Gamma_t = X_F(Gamma_t) and d_t Gamma_t = D Gamma_t X_F; (iii) ¦¦Gamma_t(w)¦¦ <= (10/9)¦¦w¦¦, ¦¦Gamma_t(w) - w¦¦_+ <= 3¦t¦C_F¦¦w¦¦^3, ¦¦D Gamma_t(w) - I¦¦_{W -> W+} <= 10¦t¦C_F¦¦w¦¦^2 <= 1/2, D Gamma_t(w) maps W+ into itself, is invertible on W and W+ with inverses of norm <= 2 and ¦¦D Gamma_t^{-1} - I¦¦_{W -> W+} <= 20¦t¦C_F¦¦w¦¦^2; (iv) Gamma_t(rho w) = rho Gamma_t(w); (v) d_t D Gamma_t(w)v = DX_F(Gamma_t(w)) D Gamma_t(w)v, DX_F(y)xi = 3S(y,y,xi); (vi) Gamma_{-t}(Gamma_t(w)) = w, Gamma = Gamma_1 is injective on B_{rho_1}, Gamma(B_{rho_1}) subset B_{10 rho_1/9} and Gamma(B_{rho_1}) contains B_{9 rho_1/10}
CONSTANT_SCOPE: rho_0, rho_1 depend on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:lie-coeff, bpW:w3:F, stepW:w3:conv, stepW:w3:floweq, stepW:w3:transport, stepW:w3:est, stepW:w3:Greal, stepW:w3:var, stepW:w3:inv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:lie-coeff | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L497-L497 | phi_k
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L495-L495 | C_F
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L520-L520 | proof step
EDGE: stepW:w3:floweq | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L528-L528 | proof step
EDGE: stepW:w3:transport | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L532-L532 | proof step
EDGE: stepW:w3:est | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L535-L535 | proof step
EDGE: stepW:w3:Greal | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L542-L542 | proof step
EDGE: stepW:w3:var | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L544-L544 | proof step
EDGE: stepW:w3:inv | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L548-L548 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:conv
KIND: step
TITLE: Convergence and analyticity
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L520-L527
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L520-L527
CONTRACT_ID: stepW:w3:conv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2 <= 1/10; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦t¦^k ¦¦phi_k(w)¦¦ <= r^k ¦¦w¦¦, r <= 1/10; the formal series with coefficients t^k Phi_k gives analyticity in W and (k >= 1) in W+; termwise derivatives in (t,w) are summable, giving joint C^1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3:ext-series, bpW:w3:ext-tsum
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L521-L521 | (ii) the coefficient bounds
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L524-L524 | power series give analyticity
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L527-L527 | termwise differentiation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:floweq
KIND: step
TITLE: Flow equation
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L528-L531
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L528-L531
CONTRACT_ID: stepW:w3:floweq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2 <= 1/10; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: d_t Gamma_t = S(Gamma_t,Gamma_t,Gamma_t) = X_F(Gamma_t)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3:ext-tsum, stepW:w3:conv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L530-L530 | (iv)
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L531-L531 | Cauchy product
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L529-L529 | termwise derivative
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:transport
KIND: step
TITLE: Transport equation
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L532-L534
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L532-L534
CONTRACT_ID: stepW:w3:transport
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2 <= 1/10; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: d_t Gamma_t = D Gamma_t X_F
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, stepW:w3:conv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L534-L534 | (i)
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L534-L534 | termwise derivatives
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:est
KIND: step
TITLE: Estimates
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L535-L541
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L535-L541
CONTRACT_ID: stepW:w3:est
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2 <= 1/10; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the bounds of (iii) and the inverses
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3:ext-neumann, stepW:w3:conv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L537-L537 | (ii)
EDGE: bpW:w3:ext-neumann | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L540-L540 | Neumann series
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L536-L536 | r <= 1/10
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:Greal
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L542-L543
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L542-L543
CONTRACT_ID: stepW:w3:Greal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2 <= 1/10; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t real; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) termwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L543-L543 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:var
KIND: step
TITLE: Variational equation
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L544-L547
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L544-L547
CONTRACT_ID: stepW:w3:var
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2 <= 1/10; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: t, w, v; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: d_t D Gamma_t v = 3S(D Gamma_t v, Gamma_t, Gamma_t)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, bpW:w3:ext-tsum, stepW:w3:conv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L545-L545 | (iv)
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L545-L545 | Cauchy product
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L546-L546 | termwise derivative
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:inv
KIND: step
TITLE: Inverse
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L548-L555
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L548-L555
CONTRACT_ID: stepW:w3:inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:flow: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ¦¦w¦¦ < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real ¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ¦¦w¦¦^2 <= 1/10; (vi) rho_1 = rho_0/2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:flow (for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})); within the step: ¦t¦ <= 1, w in B_{rho_1}; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: psi(s) = Gamma_{-s}(Gamma_s(w)) is C^1 with derivative 0, so Gamma_{-t}(Gamma_t(w)) = w; injectivity and the image inclusions
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:est, stepW:w3:conv, stepW:w3:transport, stepW:w3:floweq, bpW:w3:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:est | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L549-L549 | ¦¦Gamma_s(w)¦¦ <= (10/9)¦¦w¦¦
EDGE: stepW:w3:conv | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L550-L550 | C^1
EDGE: stepW:w3:transport | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L552-L552 | transport equation
EDGE: stepW:w3:floweq | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L552-L552 | flow equation
EDGE: bpW:w3:ext-mvt | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L553-L553 | zero derivative implies constant
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:symplectic
KIND: theorem
TITLE: Symplecticity and gradient transport
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L569-L576
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L578-L593
CONTRACT_ID: bpW:w3:symplectic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; ¦t¦ < 2, w in B_{rho_0}, xi, eta in W; (consequence) P complex differentiable near Gamma_t(B_rho), rho <= rho_0, with Hamiltonian field X_P
SOURCE_QUANTIFIERS: for all such t, w, xi, eta; P; w in B_rho
SOURCE_CONCLUSION: Omega(D Gamma_t(w) xi, D Gamma_t(w) eta) = Omega(xi,eta); P o Gamma_t has Hamiltonian field X_{P o Gamma_t}(w) = D Gamma_t(w)^{-1} X_P(Gamma_t(w)), with values in W+ when X_P has
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:hamfield-def, stepW:w3:skew, stepW:w3:constform, stepW:w3:gradtrans
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L570-L570 | Gamma_t and rho_0
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L573-L573 | Hamiltonian fields
EDGE: stepW:w3:skew | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L579-L579 | proof step
EDGE: stepW:w3:constform | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L583-L583 | proof step
EDGE: stepW:w3:gradtrans | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:symplectic@L588-L588 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:skew
KIND: step
TITLE: Skewness of $DX_F$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L579-L582
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L579-L582
CONTRACT_ID: stepW:w3:skew
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:symplectic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; ¦t¦ < 2, w in B_{rho_0}, xi, eta in W; (consequence) P complex differentiable near Gamma_t(B_rho), rho <= rho_0, with Hamiltonian field X_P
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:symplectic (for all such t, w, xi, eta; P; w in B_rho); within the step: y, xi, eta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Omega(DX_F(y)xi,eta) + Omega(xi,DX_F(y)eta) = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:F, bpW:w3:omega, bpW:w3:flow
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:F | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L581-L581 | Omega(S(.),v) = 4 frak F symmetric
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L582-L582 | antisymmetry
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:skew@L580-L580 | (v): DX_F(y) xi = 3 S(y,y,xi)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:constform
KIND: step
TITLE: Constant form
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L583-L587
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L583-L587
CONTRACT_ID: stepW:w3:constform
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:symplectic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; ¦t¦ < 2, w in B_{rho_0}, xi, eta in W; (consequence) P complex differentiable near Gamma_t(B_rho), rho <= rho_0, with Hamiltonian field X_P
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:symplectic (for all such t, w, xi, eta; P; w in B_rho); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: g(t) = Omega(D Gamma_t xi, D Gamma_t eta) has g' = 0 and g(0) = Omega(xi,eta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, stepW:w3:skew, bpW:w3:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L586-L586 | (v) variational equation; D Gamma_0 = I
EDGE: stepW:w3:skew | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L586-L586 | skewness
EDGE: bpW:w3:ext-mvt | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L587-L587 | zero derivative
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:gradtrans
KIND: step
TITLE: Gradient transport
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L588-L592
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L588-L592
CONTRACT_ID: stepW:w3:gradtrans
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:symplectic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; ¦t¦ < 2, w in B_{rho_0}, xi, eta in W; (consequence) P complex differentiable near Gamma_t(B_rho), rho <= rho_0, with Hamiltonian field X_P
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:symplectic (for all such t, w, xi, eta; P; w in B_rho); within the step: w, v; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: D(P o Gamma_t)(w)v = Omega(D Gamma_t^{-1} X_P(Gamma_t w), v); values in W+ by invertibility on W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, stepW:w3:constform
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L591-L591 | (iii) invertibility on W and W+
EDGE: stepW:w3:constform | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L592-L592 | constant form
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:Yseries
KIND: lemma
TITLE: Power series of the integrand
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L611-L619
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L621-L673
CONTRACT_ID: bpW:w3:Yseries
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}
SOURCE_QUANTIFIERS: there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}
SOURCE_CONCLUSION: there are continuous (2j+3)-linear Y_j : W^{2j+3} -> W+ with sum ¦¦Y_j¦¦ rho_1^{2j+3} <= 4 C_* rho_1^3 and Y(t,w) = sum t^j Y_j(w,..,w) absolutely; int_0^1 Y(t,w) dt = sum Y_j(w,..,w)/(j+1); w -> int_0^1 Y dt has the formal power series q (q_{2j+3} = Y_j/(j+1), else 0) on B_{rho_1} and is analytic B_{rho_1} -> W+; int_0^1 Y(t,rho w) dt = rho int_0^1 Y(t,w) dt
CONSTANT_SCOPE: C_* depends only on p; rho_1 on m, p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main-sec#data, stepW:w3:majcalc, stepW:w3:majflow, stepW:w3:majA, stepW:w3:majN, stepW:w3:majX, stepW:w3:majY, stepW:w3:majint, stepW:w3:majps, stepW:w3:majreal
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main-sec#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L613-L613 | the integrand Y
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L623-L623 | proof step
EDGE: stepW:w3:majflow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L635-L635 | proof step
EDGE: stepW:w3:majA | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L638-L638 | proof step
EDGE: stepW:w3:majN | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L645-L645 | proof step
EDGE: stepW:w3:majX | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L652-L652 | proof step
EDGE: stepW:w3:majY | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L656-L656 | proof step
EDGE: stepW:w3:majint | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L662-L662 | proof step
EDGE: stepW:w3:majps | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L666-L666 | proof step
EDGE: stepW:w3:majreal | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:Yseries@L669-L669 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majcalc
KIND: step
TITLE: Majorant calculus
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L623-L634
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L623-L634
CONTRACT_ID: stepW:w3:majcalc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 <= 1/80 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: (t,w)-series P^i, multilinear B; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: majorant calculus: composite series have mu_{B(P^1..P^n)} <= ¦¦B¦¦ prod mu_{P^i} and sum to B(P^1(t,w),..); sums add coefficientwise; graded series and shifts
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-multilinear, bpW:w3:ext-tsum
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L630-L630 | norms of composites
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L631-L631 | regrouping
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majflow
KIND: step
TITLE: The flow
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L635-L637
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L635-L637
CONTRACT_ID: stepW:w3:majflow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 <= 1/80 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: s, rho; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the series Gamma (shift 1) sums to Gamma_t(w) with mu_Gamma <= rho/(1-r)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:leibniz, stepW:w3:majcalc
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L636-L636 | Gamma_t
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L637-L637 | (ii)
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L636-L636 | (t,w)-series
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majA
KIND: step
TITLE: The derivative
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L638-L644
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L638-L644
CONTRACT_ID: stepW:w3:majA
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 <= 1/80 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: k >= 1; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: A_{k,2k} with ¦¦A_{k,2k}¦¦ <= (2k+1)(2C_F)^k, mu_A <= 5r <= 1/16, sums to D Gamma_t(w) - I on W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:leibniz, stepW:w3:est, bpW:w3:ext-multilinear, bpW:w3:flow
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L641-L641 | (ii)
EDGE: stepW:w3:est | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L643-L643 | sum (2k+1) r^k <= 5r
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L643-L643 | derivative of the diagonal
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L644-L644 | (i) termwise derivative
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majN
KIND: step
TITLE: The inverse
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L645-L651
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L645-L651
CONTRACT_ID: stepW:w3:majN
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 <= 1/80 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: N = sum_n (-A)^n regrouped is a graded series (shift 0) with mu_N <= 16/15 summing to D Gamma_t(w)^{-1} on W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majA, stepW:w3:majcalc, bpW:w3:ext-tsum, bpW:w3:ext-neumann
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majA | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L647-L647 | mu_A <= 1/16
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L647-L647 | composite series
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L649-L649 | regrouping
EDGE: bpW:w3:ext-neumann | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L650-L650 | Neumann series
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majX
KIND: step
TITLE: The cubic field along the flow
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L652-L655
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L652-L655
CONTRACT_ID: stepW:w3:majX
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 <= 1/80 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: 4 nabla frak z(Gamma,Gamma,Gamma) has majorant <= C_* rho^3 (1-r)^{-3}, sums to X_{Z'}(Gamma_t w), shift 3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic, stepW:w3:majflow, stepW:w3:majcalc
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L653-L653 | 4 nabla frak z trilinear of norm <= C_*
EDGE: stepW:w3:majflow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L654-L654 | the series Gamma
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L654-L654 | composites
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majY
KIND: step
TITLE: The integrand
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L656-L661
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L656-L661
CONTRACT_ID: stepW:w3:majY
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 <= 1/80 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the composite series cal Y sums to Y(t,w), has shift 3 and mu_Y(1,rho_1) <= 4 C_* rho_1^3; Y_j = cal Y_{j,2j+3}
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majN, stepW:w3:majX, bpW:w3:main-sec#data
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majN | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L658-L658 | N
EDGE: stepW:w3:majX | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L658-L658 | the cubic field along the flow
EDGE: bpW:w3:main-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L659-L659 | Y(t,w)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majint
KIND: step
TITLE: Integrate in $t$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L662-L665
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L662-L665
CONTRACT_ID: stepW:w3:majint
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 <= 1/80 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: termwise integration in t: int_0^1 Y dt = sum Y_j(w,..,w)/(j+1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majY, bpW:w3:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majY | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L664-L664 | the bounds on Y_j
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L664-L664 | termwise integration
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majps
KIND: step
TITLE: Power series
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L666-L668
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L666-L668
CONTRACT_ID: stepW:w3:majps
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 <= 1/80 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum ¦¦q_n¦¦ rho_1^n < infinity, so the formal power series and analyticity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majY, bpW:w3:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majY | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L667-L667 | sum ¦¦Y_j¦¦ rho_1^{2j+3}
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L667-L667 | power series give analyticity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:majreal
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L669-L672
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L669-L672
CONTRACT_ID: stepW:w3:majreal
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 <= 1/80 (proof preamble L622)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); within the step: t real; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Y(t, rho w) = rho Y(t,w) and rho commutes with the t-integral
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:hamfield-def, bpW:w3:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L670-L670 | (iv) reality of Gamma_t
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L671-L671 | X_{Z'} commutes with rho
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L672-L672 | continuous R-linear maps commute with the integral
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:main
KIND: theorem
TITLE: Analytic partial Birkhoff normal form; P96-W Main Proposition for $J=\{1,2\}$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L677-L695
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L697-L746
CONTRACT_ID: bpW:w3:main
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}
SOURCE_QUANTIFIERS: for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)
SOURCE_CONCLUSION: (i) K is analytic on B_{rho_1} and real, ¦K(w)¦ <= C_K ¦¦w¦¦^6, C_K = 10 C_* C_F; (ii) K in A(B_{rho_1}): X_K is analytic B_{rho_1} -> W+, real, ¦¦X_K(w)¦¦_+ <= C'_K ¦¦w¦¦^5, C'_K = 66 C_* C_F; X_K^R = Z^{-1} X_K o Z is real analytic B^E_{r_1} -> E_{a,p+1} (r_1 = rho_1/sqrt2) and equals (d_p K^R, -d_q K^R) for K^R = K o Z; (iii) bar G = (1/2)<AI,I> + <BI,Z> with the corrected coefficients, G^nor depends only on hat w, ¦G^nor¦ <= (C_*/4)¦¦hat w¦¦^4, both in A(W) with cubic fields bounded by C_*¦¦w¦¦^3 (C_*¦¦hat w¦¦^3); (iv) for w in B_{rho_1} cap W+, Gamma(w) in W+ and D Gamma(w)[X_Lambda(w) + X_{bar G}(w) + X_{G^nor}(w) + X_K(w)] = X_H(Gamma(w))
CONSTANT_SCOPE: C_K, C'_K, rho_1 depend on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main-sec#data, bpW:w3:flow, bpW:w3:hamfield-def, stepW:w3:Kanalytic, stepW:w3:K1, stepW:w3:K2, stepW:w3:XK1, stepW:w3:XK2, stepW:w3:XKconcl, stepW:w3:iii, stepW:w3:conj
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main-sec#data | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L679-L679 | H = Lambda + G
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L678-L678 | Gamma = Gamma_1
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L683-L683 | the class A
EDGE: stepW:w3:Kanalytic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L700-L700 | proof step
EDGE: stepW:w3:K1 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L704-L704 | proof step
EDGE: stepW:w3:K2 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L708-L708 | proof step
EDGE: stepW:w3:XK1 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L714-L714 | proof step
EDGE: stepW:w3:XK2 | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L722-L722 | proof step
EDGE: stepW:w3:XKconcl | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L732-L732 | proof step
EDGE: stepW:w3:iii | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L737-L737 | proof step
EDGE: stepW:w3:conj | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main@L739-L739 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:Kanalytic
KIND: step
TITLE: Analyticity and reality
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L700-L703
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L700-L703
CONTRACT_ID: stepW:w3:Kanalytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K = K_1 + K_2 with K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: K is analytic on B_{rho_1} and real
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:ext-series, bpW:w3:Lambda, bpW:w3:quartic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L702-L702 | (i) Gamma analytic; (iv) reality
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L702-L702 | compositions
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L701-L701 | Lambda a continuous polynomial
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L701-L701 | G, bar G, G^nor polynomials
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:K1
KIND: step
TITLE: The bound for $K_1$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L704-L707
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L704-L707
CONTRACT_ID: stepW:w3:K1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K = K_1 + K_2 with K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦K_1(w)¦ = ¦G(Gamma w) - G(w)¦ <= 5 C_* C_F ¦¦w¦¦^6
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-mvt, bpW:w3:flow, bpW:w3:quartic, bpW:w3:omega, bpW:w3:homological
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-mvt | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L706-L706 | mean value inequality on the segment
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L707-L707 | (iii) estimates
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L706-L706 | ¦¦X_G(y)¦¦_+ <= C_*¦¦y¦¦^3
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L706-L706 | DG(y)v = Omega(X_G(y),v)
EDGE: bpW:w3:homological | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L698-L698 | Z' = bar G - G^tan in the splitting K = K_1 + K_2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:K2
KIND: step
TITLE: The bound for $K_2$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L708-L713
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L708-L713
CONTRACT_ID: stepW:w3:K2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K = K_1 + K_2 with K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: h(t) = Lambda(Gamma_t w) - Lambda(w) - t Z'(w) has h(0) = 0, h'(t) = Z'(Gamma_t w) - Z'(w), ¦h'(t)¦ <= 5 C_* C_F t ¦¦w¦¦^6, so ¦K_2(w)¦ <= 5 C_* C_F ¦¦w¦¦^6; with K_1, (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:homological, stepW:w3:K1, stepW:w3:Kanalytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L710-L710 | (ii) flow equation
EDGE: bpW:w3:homological | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L710-L710 | DLambda . X_F = Z' at Gamma_t w
EDGE: stepW:w3:K1 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L712-L712 | the same mean value argument
EDGE: stepW:w3:Kanalytic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L713-L713 | (i) analyticity part
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:XK1
KIND: step
TITLE: The field of $K_1$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L714-L721
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L714-L721
CONTRACT_ID: stepW:w3:XK1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K = K_1 + K_2 with K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: X_{K_1}(w) = D Gamma^{-1} X_G(Gamma w) - X_G(w), ¦¦X_{K_1}(w)¦¦_+ <= 44 C_* C_F ¦¦w¦¦^5, analytic into W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:symplectic, bpW:w3:forms, bpW:w3:flow, bpW:w3:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L715-L715 | gradient transport
EDGE: bpW:w3:forms | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L717-L717 | Lipschitz bound d = 4
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L717-L717 | (iii)
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L720-L720 | analyticity of D(Gamma - id), inversion
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:XK2
KIND: step
TITLE: The field of $K_2$
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L722-L731
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L722-L731
CONTRACT_ID: stepW:w3:XK2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K = K_1 + K_2 with K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: K_2(w) = int_0^1 (Z'(Gamma_t w) - Z'(w)) dt, X_{K_2}(w) = int_0^1 Y(t,w) dt with ¦¦X_{K_2}(w)¦¦_+ <= 22 C_* C_F ¦¦w¦¦^5, analytic B_{rho_1} -> W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-integral, stepW:w3:K2, bpW:w3:symplectic, bpW:w3:main-sec#data, stepW:w3:XK1, bpW:w3:Yseries
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L723-L723 | FTC and differentiation under the integral
EDGE: stepW:w3:K2 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L723-L723 | h'(t)
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L725-L725 | gradient transport
EDGE: bpW:w3:main-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L726-L726 | Y of (bpW:w3:Ydef)
EDGE: stepW:w3:XK1 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L726-L726 | the same bound
EDGE: bpW:w3:Yseries | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L727-L727 | D_w Y bounded; analyticity of the integral
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:XKconcl
KIND: step
TITLE: Conclusion of (ii)
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L732-L736
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L732-L736
CONTRACT_ID: stepW:w3:XKconcl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K = K_1 + K_2 with K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii): X_K = X_{K_1} + X_{K_2}, 44 + 22 = 66, analytic; reality; the real restriction and (d_p K^R, -d_q K^R)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:XK1, stepW:w3:XK2, bpW:w3:hamfield-def, bpW:w3:real-restrict, bpW:w3:hamfield-def#hamilton, bpW:w3:coords
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:XK1 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L733-L733 | X_{K_1}
EDGE: stepW:w3:XK2 | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L733-L733 | X_{K_2}
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L734-L734 | reality of the field
EDGE: bpW:w3:real-restrict | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L734-L734 | real restriction
EDGE: bpW:w3:hamfield-def#hamilton | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L735-L735 | Z^{-1} X_K = (d_p K, -d_q K) on real points
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L736-L736 | ¦¦Zx¦¦ <= sqrt2 ¦¦x¦¦_E
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:iii
KIND: step
TITLE: (iii)
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L737-L738
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L737-L738
CONTRACT_ID: stepW:w3:iii
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K = K_1 + K_2 with K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) from Lemmas bpW:w3:quartic and bpW:w3:quartic-ident
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:quartic, bpW:w3:quartic-ident
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L738-L738 | forms and bounds
EDGE: bpW:w3:quartic-ident | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L738-L738 | bar G, G^nor
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w3:conj
KIND: step
TITLE: Conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L739-L745
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L739-L745
CONTRACT_ID: stepW:w3:conj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K = K_1 + K_2 with K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w in B_{rho_1} cap W+; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): Gamma(w) in W+ and D Gamma(w)[X_Lambda + X_{bar G} + X_{G^nor} + X_K](w) = X_H(Gamma(w))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:Lambda, bpW:w3:symplectic, bpW:w3:omega, stepW:w3:XKconcl
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L740-L740 | Gamma - id into W+
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L741-L741 | DH(y)u = Omega(X_H(y),u) on W+
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L742-L742 | gradient transport
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L745-L745 | nondegeneracy
EDGE: stepW:w3:XKconcl | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L744-L744 | X_K
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:gamma-real
KIND: corollary
TITLE: Real change of coordinates
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L770-L784
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L786-L796
CONTRACT_ID: bpW:w3:gamma-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; r_1 = rho_1/sqrt2, B^E_r = {x in E_{a,p} : ¦¦x¦¦_E < r}; Gamma^R = Z^{-1} o Gamma o Z
SOURCE_QUANTIFIERS: x in B^E_{r_1}
SOURCE_CONCLUSION: Gamma^R : B^E_{r_1} -> E_{a,p} is well defined and (i) real analytic with the real power series of terms Z^{-1} Phi_k(Z.,..,Z.); (ii) ¦¦Gamma^R(x) - x¦¦_{E_{a,p+1}} <= 6 sqrt2 C_F ¦¦x¦¦_E^3 and Gamma^R(B^E_{r_1}) subset B^E_{2r_1}; (iii) symplectic for sum dq ^ dp, injective, inverse Z^{-1} Gamma_{-1} Z on its image, image contains B^E_{r_1/2}; (iv) H(Gamma^R x) = Lambda(x) + bar G(x) + G^nor(x) + K(Zx) with bar G = (1/2)<AI,I> + <BI,Z>, I_j = (q_j^2+p_j^2)/2
CONSTANT_SCOPE: C_F, r_1 depend on m and p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:coords, bpW:w3:leibniz, bpW:w3:ext-series, bpW:w3:omega, bpW:w3:symplectic, bpW:w3:main, bpW:w3:quartic-ident
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L787-L787 | (iii), (iv), (vi)
EDGE: bpW:w3:coords | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L788-L788 | Z and real points
EDGE: bpW:w3:leibniz | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L789-L789 | (iii) reality of Phi_k
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L791-L791 | analyticity over R
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L792-L792 | the real form
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L793-L793 | symplecticity
EDGE: bpW:w3:main | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L795-L795 | (iv) the normal form
EDGE: bpW:w3:quartic-ident | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:gamma-real@L795-L795 | bar G on real points
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3:transport-tori
KIND: corollary
TITLE: Invariant tori are transported
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L800-L807
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L809-L813
CONTRACT_ID: bpW:w3:transport-tori
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; nu in R^2; Psi : R^2 -> B_{rho_1} cap W+ differentiable into W with D Psi(theta) nu = X_{H'}(Psi(theta)), X_{H'} = X_Lambda + X_{bar G} + X_{G^nor} + X_K; for the last claim Psi real (rho Psi = Psi)
SOURCE_QUANTIFIERS: for all such nu, Psi; all theta; j >= 1
SOURCE_CONCLUSION: Gamma o Psi takes values in W+ and D(Gamma o Psi)(theta) nu = X_H(Gamma o Psi(theta)); if Psi is real, (Q,P) = Z^{-1} Gamma o Psi satisfies D_nu Q_j = lambda_j P_j, D_nu P_j = -lambda_j Q_j - T(Q,Q,Q)_j, the coefficient system (bpW:w0:coeffsys) (T = G_q for a > 0)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w3:Lambda, bpW:w3:quartic-ident, bpW:w0:eqmotion, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L810-L810 | (iv) conjugacy
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L812-L812 | X_Lambda on real points
EDGE: bpW:w3:quartic-ident | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L812-L812 | Z^{-1} X_G = (0,-T(q,q,q))
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L806-L806 | the coefficient system
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L805-L805 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:transport-tori@L806-L806 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w3#data
KIND: definition
TITLE: W3 standing data (a, p, J)
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3@L23-L27
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: fixes, throughout Part W3, a >= 0 and p >= 1/2 (headline a = p = 1), the tangential modes J = {1,2} and normal modes j >= 3; constants depend on m, a, p as listed in section bpW:w3:constants
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:mass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:mass | blueprint-W/parts/w3-birkhoff.tex#bpW:w3@L23-L23 | Standing assumption m > 0 in force
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled 'Standing data' paragraph (SPEC hypothesis packages): its premise p >= 1/2 is used by Lemma bpW:w3:Lambda and every bound through C_* = K_{p+1/2}^2/pi; it is recorded in the SOURCE_HYPOTHESES of each W3 result.

NODE: bpW:w3:hamfield-def#hamilton
KIND: claim
TITLE: Hamilton's equations and reality of X_P
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L164-L167
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L164-L167
CONTRACT_ID: bpW:w3:hamfield-def#hamilton
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; P as in Definition bpW:w3:hamfield-def
SOURCE_QUANTIFIERS: real points; w, v
SOURCE_CONCLUSION: on real points Z^{-1} X_P = (d_p P, -d_q P), the convention of Definition bpW:w0:eqmotion; if P is real then X_P o rho = rho o X_P
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:hamfield-def, bpW:w3:omega, bpW:w0:eqmotion
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L164-L164 | the Hamiltonian field X_P
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L165-L165 | Omega(Zx,Zx') = sum (q p' - p q') and Omega(rho w, rho w') = conj Omega
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L165-L165 | the sign convention of Hamilton's equations
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled paragraph after Definition bpW:w3:hamfield-def, cited as "paragraph after Definition bpW:w3:hamfield-def" in Steps stepW:w3:XG and stepW:w3:XKconcl.

NODE: bpW:w3:quartic-sec#data
KIND: definition
TITLE: Two-sided quartic coefficients, divisors, pairing, tangential set
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-sec@L224-L230
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:quartic-sec#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; x in (Z\0)^4
SOURCE_QUANTIFIERS: x
SOURCE_CONCLUSION: defines ¦x¦, w_x = w_{x_1} w_{x_2} w_{x_3} w_{x_4}, frak g_x = g_¦x¦/sqrt(lambda_¦x_1¦ .. lambda_¦x_4¦), delta_x = lambda'_{x_1} + .. + lambda'_{x_4}; x paired iff a permutation of (r,-r,s,-s) (then delta_x = 0); T = {x : min_t ¦x_t¦ <= 2} (at least one tangential index)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, bpW:w3:space, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-sec@L228-L228 | g from Lemma bpW:w0n:quartic-coeff
EDGE: bpW:w3:space | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-sec@L227-L227 | lambda'_l = sgn(l) lambda_¦l¦
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:quartic-sec@L226-L226 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L224-L230 fixing notation consumed throughout W3 (SPEC section-data rule).

NODE: bpW:w3:main-sec#data
KIND: definition
TITLE: H = Lambda + G on W and the integrand Y(t,w)
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L598-L609
PROOF_SOURCE: -
CONTRACT_ID: bpW:w3:main-sec#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}
SOURCE_QUANTIFIERS: 0 <= t <= 1, w in B_{rho_1}
SOURCE_CONCLUSION: defines H = Lambda + G on W (on real points the Hamiltonian of Definition bpW:w0:H), X_H = X_Lambda + X_G on W+ with values in W, and (bpW:w3:Ydef) Y(t,w) = D Gamma_t(w)^{-1} X_{Z'}(Gamma_t w) - X_{Z'}(w) in W+, Z' = bar G - G^tan, rho_1 = (1/2)(40 C_F)^{-1/2}, D Gamma_t(w)^{-1} the inverse on W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:Lambda, bpW:w3:quartic, bpW:w0:H, bpW:w3:homological, bpW:w3:flow
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L598-L598 | Lambda finite, X_Lambda on W+
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L598-L598 | G finite, X_G
EDGE: bpW:w0:H | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L599-L599 | the Hamiltonian on real points
EDGE: bpW:w3:homological | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L605-L605 | Z' = bar G - G^tan and X_{Z'}
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:main-sec@L607-L607 | (iii) the inverse of D Gamma_t on W+
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L598-L609 (with the display bpW:w3:Ydef) fixing H, X_H and Y used by Lemma bpW:w3:Yseries and Theorem bpW:w3:main (SPEC section-data rule).

NODE: bpW:wh:embedding#IsAnalyticTorusEmbedding
KIND: definition
TITLE: Analytic torus embedding: KAM.Wave.IsAnalyticTorusEmbedding
STATEMENT_SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:embedding@L22-L27
PROOF_SOURCE: -
CONTRACT_ID: wave.IsAnalyticTorusEmbedding
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a real normed space E (frozen: any NormedSpace R E); K : R^2 -> E
SOURCE_QUANTIFIERS: E, K
SOURCE_CONCLUSION: defines: K is an analytic torus embedding iff K is Z^2-periodic, real analytic (blueprint: locally the restriction of a holomorphic map into E_C; frozen: AnalyticOnNhd R K univ), injective modulo Z^2 (K(theta) = K(theta') implies theta - theta' in Z^2), and DK(theta) is injective at every theta (KAM.Wave.IsAnalyticTorusEmbedding K)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Wave/Defs/IsAnalyticTorusEmbedding.lean
FROZEN_DECL: KAM.Wave.IsAnalyticTorusEmbedding
FROZEN_ANCHOR_ID: wave.IsAnalyticTorusEmbedding.v1
FROZEN_ABI_SHA256: b931ceffaa8574f7dfc635404ea1c87c77d71dfb42d10b3ed63d2744b6c7d53c
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:wh:dioph#IsDiophantine
KIND: definition
TITLE: Diophantine: KAM.IsDiophantine
STATEMENT_SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:dioph@L33-L37
PROOF_SOURCE: -
CONTRACT_ID: kam.IsDiophantine
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: gamma, tau in R; nu in R^2 (frozen: KAM.IsDiophantine for n = 2)
SOURCE_QUANTIFIERS: gamma, tau, nu
SOURCE_CONCLUSION: defines: nu is (gamma,tau)-Diophantine iff ¦k.nu¦ >= gamma ¦k¦_1^{-tau} for all k in Z^2 \ {0}, ¦k¦_1 = ¦k_1¦ + ¦k_2¦ (the frozen track-K definition KAM.IsDiophantine, transcribed here)
CONSTANT_SCOPE: none
FROZEN_FILE: KAM/Frozen/Defs/IsDiophantine.lean
FROZEN_DECL: KAM.IsDiophantine
FROZEN_ANCHOR_ID: kam.IsDiophantine.v1
FROZEN_ABI_SHA256: 24a486c6ccc5648791465ec3577c2e37fd464ecaec8f0dab9c74a5588535e717
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:wh:nlw2
KIND: theorem
TITLE: W-NLW2, proposed
STATEMENT_SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L41-L65
PROOF_SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L41-L65
CONTRACT_ID: wave.nlw2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0 (frozen hm : 0 < m); the data fixed at L13-L16: weights a = p = 1, E = E_{1,1} with the max norm, U_m, V_m, G_q, P = (0,infinity)^2, r(I) = sqrt(I_1+I_2), B_h = {I : max_i ¦I_i¦ < h}
SOURCE_QUANTIFIERS: for every m > 0, there exist r_0 > 0, C > 0, tau > 1, eta : (0,r_0) -> [0,infinity) with eta(r) -> 0 as r -> 0+, a Borel set Gamma subset {I in P : r(I) < r_0}, a continuous nu : Gamma -> R^2 and maps K_I = (Q_I,P_I) : R^2 -> E (I in Gamma) with (I,theta) -> K_I(theta) continuous on Gamma x R^2; then (1)-(6) hold with inner quantifiers: (2) for every I in Gamma there is gamma_I > 0; (3)-(5) for every I in Gamma, theta (resp. theta_0, t, x) and j >= 1; (6) for all I, I' in Gamma and theta, theta'
SOURCE_CONCLUSION: (1) Leb_2(Gamma cap B_h)/Leb_2(P cap B_h) -> 1 as h -> 0+; (2) nu(I) is (gamma_I,tau)-Diophantine and nu(I) -> (lambda_1,lambda_2)/(2 pi) as I -> 0 in Gamma; (3) each K_I is an analytic torus embedding, sup_theta ¦¦K_I(theta) - K^0_I(theta)¦¦_E <= eta(r(I)) r(I) and sup_theta ¦¦K_I(theta)¦¦_E <= C r(I); (4) D_{nu(I)} Q_{I,j} = lambda_j P_{I,j} and D_{nu(I)} P_{I,j} = -lambda_j Q_{I,j} - G_q(Q_I)_j for all theta, j >= 1 (frozen: HasDerivAt of t -> coeff (K I (theta + t nu I)).i j at t = 0); (5) for every theta_0, u(t,x) = U_m(Q_I(theta_0 + t nu(I)))(x) is real analytic near every point of R x [0,pi], is a classical solution of u_tt = u_xx - m u - u^3 on R, u_t(t,.) = V_m(P_I(theta_0 + t nu(I))), and sup_{t, x in [0,pi]} (¦u¦ + ¦u_x¦ + ¦u_t¦) <= C r(I) (frozen: u_x as derivWithin on [0,pi]); (6) K_I(theta) = K_I'(theta') implies I = I' and theta - theta' in Z^2
CONSTANT_SCOPE: r_0, C, tau, eta, Gamma, nu, K are chosen after m and before I, theta, theta_0; they may depend on m; gamma_I is chosen per I (it may degenerate as I -> 0); C is common to (3) and (5); no uniformity in m
FROZEN_FILE: KAM/Frozen/Wave/Theorems/Nlw2.lean
FROZEN_DECL: KAM.Wave.nlw2
FROZEN_ANCHOR_ID: wave.nlw2.v1
FROZEN_ABI_SHA256: eca3aee797e9040ce3fde0e946ce30e10fe8550faa413b6a83fc9abda495ddb7
DEPS: bpW:w0:mass, bpW:w0:ellap#WaveSpace, bpW:wh:dioph#IsDiophantine, bpW:w0:basis#lam, bpW:wh:embedding#IsAnalyticTorusEmbedding, bpW:w0:periodone#linearTorus, bpW:w0:ellap#coeff, bpW:w0:Gq#cubicGrad, bpW:w0:reconstruction#reconU, bpW:w0:nlw#IsClassicalSolution, bpW:w0:reconstruction#reconV
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:mass | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L42-L42 | for every m > 0 (hm)
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L44-L44 | K_I : R^2 -> E, E = E_{1,1} (frozen WaveSpace)
EDGE: bpW:wh:dioph#IsDiophantine | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L50-L50 | (2) nu(I) is (gamma_I,tau)-Diophantine
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L50-L50 | (2) limit (lambda_1,lambda_2)/(2 pi); (4) lambda_j
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L51-L51 | (3) each K_I is an analytic torus embedding
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L52-L52 | (3) closeness to K^0_I
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L54-L54 | (4) the coefficients Q_{I,j}, P_{I,j} (frozen coeff)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L55-L55 | (4) the cubic gradient G_q(Q_I(theta))_j
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L57-L57 | (5) u = U_m(Q_I(theta_0 + t nu(I)))
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L58-L58 | (5) classical solution of (bpW:w0:eq) on R
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L59-L59 | (5) u_t = V_m(P_I(theta_0 + t nu(I)))
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-wh
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root of track W. PROOF_SOURCE is provisionally the statement locator: the proof (the W8 assembly) is not in the wave-1 corpus. Its proof (assembly) is milestone W8, not yet in the corpus (W4-W8 pending); until then DEPS lists only the statement-level definitions. W2 (bpW:w2:clause5) supplies conclusion (5) from (3)-(4) and becomes a dependency when W8 is added. D_nu (bpW:wh:Dnu) is inlined in the frozen statement.

NODE: K:bp:p1:decay
KIND: external
TITLE: [K] Coefficient decay
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:decay@L786-L789
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:decay
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic, bounded and 1-periodic on T_rho
SOURCE_QUANTIFIERS: rho, u; k in Z^n; rho' with 0<=rho'<rho
SOURCE_CONCLUSION: |hat u_k| <= e^{-2 pi |k|_1 rho'} ||u||_rho
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:decay; shared Lean provider. There: KIND lemma, contract bp:p1:decay v1.

NODE: K:bp:p1:fourier-basic
KIND: external
TITLE: [K] Fourier coefficients of periodic functions
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:fourier-basic@L757-L768
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:fourier-basic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: v C-valued (componentwise for vector/matrix); (a) v continuous, 1-periodic, C^1; (b) v continuous, 1-periodic, sum |hat v_k| finite; (c) r>0, v holomorphic and 1-periodic on T_r, not necessarily bounded, all hat v_k=0
SOURCE_QUANTIFIERS: v; k in Z^n; ell; omega in C^n; r
SOURCE_CONCLUSION: (a) hat(d_ell v)_k = 2 pi i k_ell hat v_k and hat(d_omega v)_k = 2 pi i (k.omega) hat v_k; (b) v(x)=sum hat v_k chi_k(x) for all x, so v=0 if all hat v_k=0; (c) v=0 on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:fourier-basic; shared Lean provider. There: KIND lemma, contract bp:p1:fourier-basic v1.

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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:holomorphic-analytic; shared Lean provider. There: KIND lemma, contract bp:p1:holomorphic-analytic v1.

NODE: K:bp:p1:strip-identity
KIND: external
TITLE: [K] Identity theorem on strips
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#bp:p1:strip-identity@L531-L534
PROOF_SOURCE: -
CONTRACT_ID: K:bp:p1:strip-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: r>0; v holomorphic on T_r with values in W; v(x)=0 for all real x
SOURCE_QUANTIFIERS: r>0 ; v
SOURCE_CONCLUSION: v=0 on T_r
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node bp:p1:strip-identity; shared Lean provider. There: KIND lemma, contract bp:p1:strip-identity v1.

NODE: K:step:p1:dec-shift
KIND: external
TITLE: [K] Shifting one variable
STATEMENT_SOURCE: blueprint/parts/p1-analysis.tex#step:p1:dec-shift@L800-L811
PROOF_SOURCE: -
CONTRACT_ID: K:step:p1:dec-shift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: u holomorphic 1-periodic on T_rho, k, rho'<rho, t_j=-rho' sgn(k_j); I_j integrals
SOURCE_QUANTIFIERS: 1<=j<=n; x_l for l!=j
SOURCE_CONCLUSION: I_{j-1}=I_j for 1<=j<=n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: IMPORTED: proved in the track-K graph, node step:p1:dec-shift; shared Lean provider. There: KIND step, contract step:p1:dec-shift v1.

<!-- BEGIN PROOF DEPGRAPH GENERATED -->
Regenerated by `proof_depgraph.py`; do not hand-edit.

### Dashboard

* Total nodes: **309**
* Frozen anchors: **13**
* Versioned statement contracts: **309**
* Total edges: **1029**
* Root-closure nodes: **19**
* Dependency leaves in root closure: **5**
* Assumption boundary leaves: **1**
* External boundary leaves: **0**
* Alternative routes: **2**
* Topology review queue: **286**
* Explicit source gaps: **0**
* Coverage items: **502**; excluded: **184**

### Roots

* `bpW:wh:nlw2` [REVIEWED; frozen] — contract `wave.nlw2@1`

### Topology review queue

* `K:bp:p1:decay` [PROPOSED] — [K] Coefficient decay
* `K:bp:p1:fourier-basic` [PROPOSED] — [K] Fourier coefficients of periodic functions
* `K:bp:p1:holomorphic-analytic` [PROPOSED] — [K] Holomorphic maps are analytic
* `K:bp:p1:strip-identity` [PROPOSED] — [K] Identity theorem on strips
* `K:step:p1:dec-shift` [PROPOSED] — [K] Shifting one variable
* `bpW:w0:Gq#cubicGrad` [PROPOSED] — Cubic gradient: KAM.Wave.cubicGrad
* `bpW:w0:H` [PROPOSED] — Hamiltonian
* `bpW:w0:actions` [PROPOSED] — Actions and radian angles
* `bpW:w0:basis#lam` [PROPOSED] — Dirichlet basis and linear frequencies: KAM.Wave.lam
* `bpW:w0:ellap#WaveSpace` [PROPOSED] — Weighted sequence spaces: KAM.Wave.WaveSpace
* `bpW:w0:ellap#spaces` [PROPOSED] — General weighted coefficient spaces and their product norm
* `bpW:w0:eqmotion` [PROPOSED] — Symplectic form and equations of motion
* `bpW:w0:periodone#linearTorus` [PROPOSED] — Period-one torus angles and frequencies: KAM.Wave.linearTorus
* `bpW:w0:reconstruction#rescaling` [PROPOSED] — Inverse coefficient dictionary and symplectic rescaling
* `bpW:w0:z` [PROPOSED] — Complex coordinates
* `bpW:w0n:cubic-bound` [PROPOSED] — Cubic gradient, (b)
* `bpW:w0n:duffing` [PROPOSED] — One-mode frequency shift, (f)
* `bpW:w0n:formal-birkhoff` [PROPOSED] — Formal partial Birkhoff transformation
* `bpW:w0n:gradient` [PROPOSED] — $G$ and its gradient as absolutely convergent sums
* `bpW:w0n:nondeg` [PROPOSED] — Nondegeneracy, (e)
* `bpW:w0n:nondeg-sec#data` [PROPOSED] — Nondegeneracy conditions (A1)-(A3) of the Cantor Manifold Theorem
* `bpW:w0n:pde-equiv` [PROPOSED] — Equivalence, (a)
* `bpW:w1:algebra` [PROPOSED] — Convolution algebra
* `bpW:w1:cauchy` [PROPOSED] — Cauchy estimate
* `bpW:w1:complexification` [PROPOSED] — Complexification
* `bpW:w1:complexification-lemma` [PROPOSED] — Complexification and real analyticity
* `bpW:w1:coordinatewise` [PROPOSED] — Derivatives of coordinates
* `bpW:w1:cubic-analytic` [PROPOSED] — Analyticity and Lipschitz bounds of the cubic gradient
* `bpW:w1:deriv-continuous` [PROPOSED] — Derivatives of holomorphic maps are continuous
* `bpW:w1:diag` [PROPOSED] — Frequency multipliers and the linear flow
* `bpW:w1:embed` [PROPOSED] — Embeddings
* `bpW:w1:ext-analytic` [PROPOSED] — Analytic maps
* `bpW:w1:ext-fourier` [PROPOSED] — Fourier analysis
* `bpW:w1:ext-integral` [PROPOSED] — Integrals
* `bpW:w1:ext-lp` [PROPOSED] — $\ell^2$ spaces
* `bpW:w1:ext-ode` [PROPOSED] — ODE
* `bpW:w1:ext-onevar` [PROPOSED] — One complex variable, Banach values
* `bpW:w1:ext-series` [PROPOSED] — Series
* `bpW:w1:ext-unifderiv` [PROPOSED] — Uniform limits and derivatives
* `bpW:w1:flow` [PROPOSED] — Holomorphic flows
* `bpW:w1:fourier-banach` [PROPOSED] — Banach-valued Fourier coefficients on strips
* `bpW:w1:fourier-l2` [PROPOSED] — Hilbert-valued Fourier series on strips
* `bpW:w1:gradient-identity` [PROPOSED] — Gradient identity
* `bpW:w1:hamfield` [PROPOSED] — The Hamiltonian field
* `bpW:w1:holo-analytic-fd` [PROPOSED] — Holomorphic maps of finitely many variables are analytic
* `bpW:w1:holomorphic` [PROPOSED] — Holomorphic maps on Banach domains
* `bpW:w1:kam-domain` [PROPOSED] — Domains
* `bpW:w1:kam-space` [PROPOSED] — KAM phase space, domains, norms
* `bpW:w1:lattice` [PROPOSED] — Weighted lattice sums
* `bpW:w1:linfty` [PROPOSED] — Sup-weighted sequences
* `bpW:w1:multiplier` [PROPOSED] — Diagonal multipliers
* `bpW:w1:recon-analytic` [PROPOSED] — Analytic reconstruction
* `bpW:w1:schur` [PROPOSED] — Hilbert-matrix bound
* `bpW:w1:selection` [PROPOSED] — Selection-rule trilinear maps
* `bpW:w1:sine-completeness` [PROPOSED] — Completeness of the sine system
* `bpW:w1:sine-feature` [PROPOSED] — Analytic sine features
* `bpW:w1:space` [PROPOSED] — The weighted spaces
* `bpW:w1:tails` [PROPOSED] — Spectral asymptotics of the wave normal frequencies
* `bpW:w1:torus-analytic` [PROPOSED] — Real-analytic tori from complex strips
* `bpW:w1:transport` [PROPOSED] — Weights, transport and coefficient maps
* `bpW:w1:trilinear` [PROPOSED] — The cubic map as a continuous trilinear map
* `bpW:w1:twosided` [PROPOSED] — Passage between one- and two-sided sequences
* `bpW:w1:twosided-transport` [PROPOSED] — Two-sided transport
* `bpW:w1:uniform-limit` [PROPOSED] — Uniform limits
* `bpW:w1:young` [PROPOSED] — Young and $\ell^1$ control
* `bpW:w2:clause5` [PROPOSED] — Clause (5) with the common constant
* `bpW:w2:coeffsol` [PROPOSED] — Analytic coefficient solution
* `bpW:w2:curve` [PROPOSED] — P96-W Lemma~1 in frozen form
* `bpW:w2:curve-deriv` [PROPOSED] — Coefficients of the curve derivative
* `bpW:w2:derived` [PROPOSED] — Derived reconstructions
* `bpW:w2:ext-an` [PROPOSED] — Analytic maps on $\R\times\R$
* `bpW:w2:ext-deriv` [PROPOSED] — One-variable calculus
* `bpW:w2:ext-sums` [PROPOSED] — Series and norms
* `bpW:w2:ext-trig` [PROPOSED] — Trigonometry
* `bpW:w2:force` [PROPOSED] — Force identity in frozen form
* `bpW:w2:functionals` [PROPOSED] — Reconstruction functionals
* `bpW:w2:main` [PROPOSED] — PDE solutions on invariant tori
* `bpW:w2:orbit` [PROPOSED] — Torus orbits are analytic coefficient solutions
* `bpW:w3#data` [PROPOSED] — W3 standing data (a, p, J)
* `bpW:w3:F` [PROPOSED] — $F$ is bounded and one-smoothing
* `bpW:w3:Fdef` [PROPOSED] — Generating Hamiltonian
* `bpW:w3:Lambda` [PROPOSED] — The linear part
* `bpW:w3:Yseries` [PROPOSED] — Power series of the integrand
* `bpW:w3:coords` [PROPOSED] — Complex coordinates and real structure
* `bpW:w3:divisor` [PROPOSED] — Divisor lower bound; P96-W Lemma~4
* `bpW:w3:ext-integral` [PROPOSED] — Integrals in a parameter
* `bpW:w3:ext-multilinear` [PROPOSED] — Multilinear maps
* `bpW:w3:ext-mvt` [PROPOSED] — Mean value inequality; zero derivative
* `bpW:w3:ext-neumann` [PROPOSED] — Neumann series
* `bpW:w3:ext-series` [PROPOSED] — Power series
* `bpW:w3:ext-tsum` [PROPOSED] — Termwise differentiation
* `bpW:w3:flow` [PROPOSED] — The flow of $X_F$
* `bpW:w3:forms` [PROPOSED] — Smoothing symmetric forms
* `bpW:w3:gamma-real` [PROPOSED] — Real change of coordinates
* `bpW:w3:hamfield-def` [PROPOSED] — Hamiltonian field; one-smoothing holomorphic class
* `bpW:w3:hamfield-def#hamilton` [PROPOSED] — Hamilton's equations and reality of X_P
* `bpW:w3:homological` [PROPOSED] — Homological identity
* `bpW:w3:leibniz` [PROPOSED] — Coefficient bounds and the Leibniz identity
* `bpW:w3:lie-coeff` [PROPOSED] — Lie coefficients
* `bpW:w3:main` [PROPOSED] — Analytic partial Birkhoff normal form; P96-W Main Proposition for $J=\{1,2\}$
* `bpW:w3:main-sec#data` [PROPOSED] — H = Lambda + G on W and the integrand Y(t,w)
* `bpW:w3:majorant` [PROPOSED] — Majorant for the cubic sums
* `bpW:w3:omega` [PROPOSED] — Symplectic form
* `bpW:w3:quartic` [PROPOSED] — Quartic forms
* `bpW:w3:quartic-ident` [PROPOSED] — Identification with Part~0
* `bpW:w3:quartic-sec#data` [PROPOSED] — Two-sided quartic coefficients, divisors, pairing, tangential set
* `bpW:w3:real-restrict` [PROPOSED] — Real restrictions
* `bpW:w3:space` [PROPOSED] — Two-sided coordinate space
* `bpW:w3:symplectic` [PROPOSED] — Symplecticity and gradient transport
* `bpW:w3:transport-tori` [PROPOSED] — Invariant tori are transported
* `stepW:w0n:22` [PROPOSED] — Two against two
* `stepW:w0n:31` [PROPOSED] — Four or three equal signs
* `stepW:w0n:A2` [PROPOSED] — Pure normal
* `stepW:w0n:A3red` [PROPOSED] — Reduction of (A$_3$)
* `stepW:w0n:analytic` [PROPOSED] — Analyticity
* `stepW:w0n:converse` [PROPOSED] — Converse
* `stepW:w0n:cos` [PROPOSED] — Cosine integrals
* `stepW:w0n:det` [PROPOSED] — Determinant
* `stepW:w0n:force` [PROPOSED] — Force identity
* `stepW:w0n:ident` [PROPOSED] — Identification
* `stepW:w0n:l1` [PROPOSED] — The case $\abs l=1$
* `stepW:w0n:l2` [PROPOSED] — The case $\abs l=2$
* `stepW:w0n:majorant` [PROPOSED] — Even majorants
* `stepW:w0n:resavg` [PROPOSED] — Resonant equals averaged
* `stepW:w0n:selection` [PROPOSED] — Selection rule bound
* `stepW:w0n:signed` [PROPOSED] — Signed form
* `stepW:w0n:smoothing` [PROPOSED] — Smoothing
* `stepW:w0n:sum` [PROPOSED] — Summation
* `stepW:w0n:time` [PROPOSED] — Time regularity
* `stepW:w0n:young` [PROPOSED] — Young and Cauchy--Schwarz
* `stepW:w1:basis` [PROPOSED] — Hilbert basis
* `stepW:w1:bil` [PROPOSED] — Bilinear form
* `stepW:w1:can` [PROPOSED] — Analyticity
* `stepW:w1:cder` [PROPOSED] — Derivatives
* `stepW:w1:cfrozen` [PROPOSED] — Frozen form
* `stepW:w1:clip` [PROPOSED] — Lipschitz
* `stepW:w1:coeffs` [PROPOSED] — Fourier coefficients vanish
* `stepW:w1:cont` [PROPOSED] — Continuity
* `stepW:w1:coord` [PROPOSED] — Coordinates and truncation
* `stepW:w1:coordcomp` [PROPOSED] — Comparison
* `stepW:w1:coordder` [PROPOSED] — Coordinates of the derivative
* `stepW:w1:cs` [PROPOSED] — Weighted Cauchy--Schwarz
* `stepW:w1:dcbound` [PROPOSED] — Existence of $\rho$, $B$
* `stepW:w1:dcintegral` [PROPOSED] — Cauchy integral along lines
* `stepW:w1:dclip` [PROPOSED] — Lipschitz difference
* `stepW:w1:diagcomb` [PROPOSED] — Diagonal and combination
* `stepW:w1:ext` [PROPOSED] — Extensions
* `stepW:w1:fbconv` [PROPOSED] — Summation
* `stepW:w1:fbdecay` [PROPOSED] — Scalar decay
* `stepW:w1:fbdual` [PROPOSED] — Scalar reduction
* `stepW:w1:fbsum` [PROPOSED] — Lattice sum
* `stepW:w1:flowlim` [PROPOSED] — Limit
* `stepW:w1:flowlip` [PROPOSED] — Lipschitz region
* `stepW:w1:flowpar` [PROPOSED] — Parameters
* `stepW:w1:flowreal` [PROPOSED] — Reality
* `stepW:w1:frozen` [PROPOSED] — Frozen case
* `stepW:w1:fsum` [PROPOSED] — Summation
* `stepW:w1:gradder` [PROPOSED] — Derivative
* `stepW:w1:gradw` [PROPOSED] — Weighted coordinates
* `stepW:w1:growth` [PROPOSED] — Growth on the strip
* `stepW:w1:hacoef` [PROPOSED] — Coefficients
* `stepW:w1:hagroup` [PROPOSED] — Degree grouping
* `stepW:w1:hamargin` [PROPOSED] — Margin
* `stepW:w1:hareal` [PROPOSED] — Real points
* `stepW:w1:hfrozen` [PROPOSED] — Frozen form
* `stepW:w1:hham` [PROPOSED] — Hamiltonian
* `stepW:w1:hlin` [PROPOSED] — Linear part
* `stepW:w1:hnonlin` [PROPOSED] — Nonlinear part
* `stepW:w1:hsum` [PROPOSED] — Sum
* `stepW:w1:iso` [PROPOSED] — Isometry
* `stepW:w1:l1` [PROPOSED] — $\ell^1$ control
* `stepW:w1:latcount` [PROPOSED] — Counting
* `stepW:w1:latdiv` [PROPOSED] — Divisor weights
* `stepW:w1:latprod` [PROPOSED] — Product
* `stepW:w1:latweight` [PROPOSED] — Weighted sum
* `stepW:w1:lines` [PROPOSED] — Complex lines
* `stepW:w1:maj1` [PROPOSED] — One-sided majorant
* `stepW:w1:maj2` [PROPOSED] — Two-sided majorant
* `stepW:w1:margins` [PROPOSED] — Margins
* `stepW:w1:normal` [PROPOSED] — Normal convergence
* `stepW:w1:odd` [PROPOSED] — Odd extension
* `stepW:w1:onevar` [PROPOSED] — One-variable estimate
* `stepW:w1:orthants` [PROPOSED] — Orthants
* `stepW:w1:pair` [PROPOSED] — Pairing
* `stepW:w1:parseval` [PROPOSED] — Parseval
* `stepW:w1:picard` [PROPOSED] — Picard iterates
* `stepW:w1:picardholo` [PROPOSED] — Holomorphy of the iterates
* `stepW:w1:quartic` [PROPOSED] — Quartic form
* `stepW:w1:ratio` [PROPOSED] — Ratio
* `stepW:w1:realflow` [PROPOSED] — Real flow
* `stepW:w1:recanalytic` [PROPOSED] — Analyticity
* `stepW:w1:recder` [PROPOSED] — Derivatives
* `stepW:w1:restr` [PROPOSED] — Restriction
* `stepW:w1:rot` [PROPOSED] — Unboundedness and rotations
* `stepW:w1:rows` [PROPOSED] — Row and column sums
* `stepW:w1:rules` [PROPOSED] — Algebraic rules
* `stepW:w1:schurtest` [PROPOSED] — Schur test
* `stepW:w1:schurweights` [PROPOSED] — Weights
* `stepW:w1:sel1` [PROPOSED] — One-sided selection
* `stepW:w1:sel2` [PROPOSED] — Two-sided selection
* `stepW:w1:sep` [PROPOSED] — Separability
* `stepW:w1:shift` [PROPOSED] — Shifted coefficients
* `stepW:w1:sinereal` [PROPOSED] — Real restriction
* `stepW:w1:smooth1` [PROPOSED] — One-sided smoothing
* `stepW:w1:smooth2` [PROPOSED] — Two-sided smoothing
* `stepW:w1:tricont` [PROPOSED] — Continuity
* `stepW:w1:tricoord` [PROPOSED] — Coordinates
* `stepW:w1:tricoord#via-cubic-bound` [PROPOSED] — Coordinates of the trilinear map via Theorem bpW:w0n:cubic-bound
* `stepW:w1:tricoord#via-selection` [PROPOSED] — Coordinates of the trilinear map via Lemma bpW:w1:selection(a)
* `stepW:w1:trifrozen` [PROPOSED] — Frozen identification
* `stepW:w1:trireal` [PROPOSED] — Real structure and compatibility
* `stepW:w1:ulcauchy` [PROPOSED] — Cauchy in derivatives
* `stepW:w1:ullimit` [PROPOSED] — Limit
* `stepW:w1:youngsum` [PROPOSED] — Summation
* `stepW:w2:bdry` [PROPOSED] — Boundary values
* `stepW:w2:bound` [PROPOSED] — Bound
* `stepW:w2:ccoord` [PROPOSED] — Coordinates
* `stepW:w2:cdiff` [PROPOSED] — Differentiability
* `stepW:w2:fcub` [PROPOSED] — Cubic part
* `stepW:w2:features` [PROPOSED] — Choice of the features
* `stepW:w2:flin` [PROPOSED] — Linear part
* `stepW:w2:frozen` [PROPOSED] — The frozen definition
* `stepW:w2:fsum` [PROPOSED] — Summability
* `stepW:w2:joint` [PROPOSED] — Joint analyticity
* `stepW:w2:mconc` [PROPOSED] — Conclusions
* `stepW:w2:mred` [PROPOSED] — Reduction to a curve
* `stepW:w2:norms` [PROPOSED] — Norms
* `stepW:w2:oan` [PROPOSED] — Analyticity
* `stepW:w2:oshift` [PROPOSED] — Shift
* `stepW:w2:pairing` [PROPOSED] — Pairings
* `stepW:w2:t1` [PROPOSED] — First time derivative
* `stepW:w2:t2` [PROPOSED] — Second time derivative
* `stepW:w2:x` [PROPOSED] — Space derivatives
* `stepW:w2:xder` [PROPOSED] — $x$-derivatives
* `stepW:w3:Fconcl` [PROPOSED] — Conclusions
* `stepW:w3:Gnor` [PROPOSED] — Normal part
* `stepW:w3:Greal` [PROPOSED] — Reality
* `stepW:w3:Gz` [PROPOSED] — The quartic
* `stepW:w3:K1` [PROPOSED] — The bound for $K_1$
* `stepW:w3:K2` [PROPOSED] — The bound for $K_2$
* `stepW:w3:Kanalytic` [PROPOSED] — Analyticity and reality
* `stepW:w3:Phireal` [PROPOSED] — Reality
* `stepW:w3:XG` [PROPOSED] — The field
* `stepW:w3:XK1` [PROPOSED] — The field of $K_1$
* `stepW:w3:XK2` [PROPOSED] — The field of $K_2$
* `stepW:w3:XKconcl` [PROPOSED] — Conclusion of (ii)
* `stepW:w3:Xfcoord` [PROPOSED] — Field coordinates
* `stepW:w3:conj` [PROPOSED] — Conjugacy
* `stepW:w3:constform` [PROPOSED] — Constant form
* `stepW:w3:conv` [PROPOSED] — Convergence and analyticity
* `stepW:w3:count` [PROPOSED] — Count the paired terms
* `stepW:w3:divconcl` [PROPOSED] — Conclusion
* `stepW:w3:divide` [PROPOSED] — Divide
* `stepW:w3:est` [PROPOSED] — Estimates
* `stepW:w3:euler` [PROPOSED] — Euler identity
* `stepW:w3:fcoef` [PROPOSED] — Coefficients
* `stepW:w3:floweq` [PROPOSED] — Flow equation
* `stepW:w3:gradbound` [PROPOSED] — Bound the gradient
* `stepW:w3:gradtrans` [PROPOSED] — Gradient transport
* `stepW:w3:identify` [PROPOSED] — Identify
* `stepW:w3:iii` [PROPOSED] — (iii)
* `stepW:w3:inv` [PROPOSED] — Inverse
* `stepW:w3:leib` [PROPOSED] — Leibniz rule
* `stepW:w3:leibid` [PROPOSED] — The identity
* `stepW:w3:maj` [PROPOSED] — Majorize
* `stepW:w3:majA` [PROPOSED] — The derivative
* `stepW:w3:majN` [PROPOSED] — The inverse
* `stepW:w3:majX` [PROPOSED] — The cubic field along the flow
* `stepW:w3:majY` [PROPOSED] — The integrand
* `stepW:w3:majcalc` [PROPOSED] — Majorant calculus
* `stepW:w3:majflow` [PROPOSED] — The flow
* `stepW:w3:majint` [PROPOSED] — Integrate in $t$
* `stepW:w3:majps` [PROPOSED] — Power series
* `stepW:w3:majreal` [PROPOSED] — Reality
* `stepW:w3:norms` [PROPOSED] — Norms
* `stepW:w3:rec` [PROPOSED] — Recursion
* `stepW:w3:res` [PROPOSED] — Resonance
* `stepW:w3:s0` [PROPOSED] — No minus sign
* `stepW:w3:s1` [PROPOSED] — One minus sign
* `stepW:w3:s1inner` [PROPOSED] — Two minus signs, inner pair
* `stepW:w3:s23` [PROPOSED] — Two minus signs, outer pairs
* `stepW:w3:sel` [PROPOSED] — Selection rule
* `stepW:w3:signs` [PROPOSED] — Signs
* `stepW:w3:skew` [PROPOSED] — Skewness of $DX_F$
* `stepW:w3:transport` [PROPOSED] — Transport equation
* `stepW:w3:var` [PROPOSED] — Variational equation

### Dependency leaves in root closure

* `bpW:w0:basis#sineMode` [REVIEWED] — Dirichlet basis and linear frequencies: KAM.Wave.sineMode
* `bpW:w0:ellap#ellWeight` [REVIEWED] — Weighted sequence spaces: KAM.Wave.ellWeight
* `bpW:w0:mass` [REVIEWED] — Mass
* `bpW:wh:dioph#IsDiophantine` [REVIEWED] — Diophantine: KAM.IsDiophantine
* `bpW:wh:embedding#IsAnalyticTorusEmbedding` [REVIEWED] — Analytic torus embedding: KAM.Wave.IsAnalyticTorusEmbedding

### Assumption boundary leaves

* `bpW:w0:mass` [REVIEWED] — Mass

### External boundary leaves

* _(none)_

### Uncovered graph nodes

* _(none)_

### Nodes outside every root closure

* `K:bp:p1:decay` [PROPOSED] — [K] Coefficient decay
* `K:bp:p1:fourier-basic` [PROPOSED] — [K] Fourier coefficients of periodic functions
* `K:bp:p1:holomorphic-analytic` [PROPOSED] — [K] Holomorphic maps are analytic
* `K:bp:p1:strip-identity` [PROPOSED] — [K] Identity theorem on strips
* `K:step:p1:dec-shift` [PROPOSED] — [K] Shifting one variable
* `bpW:w0:basis#lambda-facts` [REVIEWED] — Elementary facts about lambda_j
* `bpW:w0:reconstruction#rescaling` [PROPOSED] — Inverse coefficient dictionary and symplectic rescaling
* `bpW:w0:twosided` [REVIEWED] — Two-sided spaces
* `bpW:w0n:AB` [REVIEWED] — Action coefficients, (d)
* `bpW:w0n:Qdef` [REVIEWED] — Partial quartic normal form
* `bpW:w0n:algebra` [REVIEWED] — Weighted convolution algebra
* `bpW:w0n:birkhoff#data` [REVIEWED] — Quartic part in complex coordinates; resonance; tangential/normal split
* `bpW:w0n:cubic-bound` [PROPOSED] — Cubic gradient, (b)
* `bpW:w0n:duffing` [PROPOSED] — One-mode frequency shift, (f)
* `bpW:w0n:formal-birkhoff` [PROPOSED] — Formal partial Birkhoff transformation
* `bpW:w0n:gradient` [PROPOSED] — $G$ and its gradient as absolutely convergent sums
* `bpW:w0n:ledger#ext-lindstedt` [REVIEWED] — Classical Lindstedt frequency shift (unlabelled W0 external)
* `bpW:w0n:nondeg` [PROPOSED] — Nondegeneracy, (e)
* `bpW:w0n:nondeg-sec#data` [PROPOSED] — Nondegeneracy conditions (A1)-(A3) of the Cantor Manifold Theorem
* `bpW:w0n:nonres` [REVIEWED] — Qualitative nonresonance of all quartic terms
* `bpW:w0n:pde-equiv` [PROPOSED] — Equivalence, (a)
* `bpW:w0n:quartic-coeff` [REVIEWED] — Closed form, (c)
* `bpW:w0n:recon-bounded` [REVIEWED] — Reconstruction is bounded into $C^k$
* `bpW:w1:algebra` [PROPOSED] — Convolution algebra
* `bpW:w1:cauchy` [PROPOSED] — Cauchy estimate
* `bpW:w1:complexification` [PROPOSED] — Complexification
* `bpW:w1:complexification-lemma` [PROPOSED] — Complexification and real analyticity
* `bpW:w1:coordinatewise` [PROPOSED] — Derivatives of coordinates
* `bpW:w1:cubic-analytic` [PROPOSED] — Analyticity and Lipschitz bounds of the cubic gradient
* `bpW:w1:deriv-continuous` [PROPOSED] — Derivatives of holomorphic maps are continuous
* `bpW:w1:diag` [PROPOSED] — Frequency multipliers and the linear flow
* `bpW:w1:embed` [PROPOSED] — Embeddings
* `bpW:w1:ext-analytic` [PROPOSED] — Analytic maps
* `bpW:w1:ext-fourier` [PROPOSED] — Fourier analysis
* `bpW:w1:ext-integral` [PROPOSED] — Integrals
* `bpW:w1:ext-lp` [PROPOSED] — $\ell^2$ spaces
* `bpW:w1:ext-ode` [PROPOSED] — ODE
* `bpW:w1:ext-onevar` [PROPOSED] — One complex variable, Banach values
* `bpW:w1:ext-series` [PROPOSED] — Series
* `bpW:w1:ext-unifderiv` [PROPOSED] — Uniform limits and derivatives
* `bpW:w1:flow` [PROPOSED] — Holomorphic flows
* `bpW:w1:fourier-banach` [PROPOSED] — Banach-valued Fourier coefficients on strips
* `bpW:w1:fourier-l2` [PROPOSED] — Hilbert-valued Fourier series on strips
* `bpW:w1:gradient-identity` [PROPOSED] — Gradient identity
* `bpW:w1:hamfield` [PROPOSED] — The Hamiltonian field
* `bpW:w1:holo-analytic-fd` [PROPOSED] — Holomorphic maps of finitely many variables are analytic
* `bpW:w1:holomorphic` [PROPOSED] — Holomorphic maps on Banach domains
* `bpW:w1:kam-domain` [PROPOSED] — Domains
* `bpW:w1:kam-space` [PROPOSED] — KAM phase space, domains, norms
* `bpW:w1:lattice` [PROPOSED] — Weighted lattice sums
* `bpW:w1:linfty` [PROPOSED] — Sup-weighted sequences
* `bpW:w1:multiplier` [PROPOSED] — Diagonal multipliers
* `bpW:w1:recon-analytic` [PROPOSED] — Analytic reconstruction
* `bpW:w1:schur` [PROPOSED] — Hilbert-matrix bound
* `bpW:w1:selection` [PROPOSED] — Selection-rule trilinear maps
* `bpW:w1:sine-completeness` [PROPOSED] — Completeness of the sine system
* `bpW:w1:sine-feature` [PROPOSED] — Analytic sine features
* `bpW:w1:space` [PROPOSED] — The weighted spaces
* `bpW:w1:tails` [PROPOSED] — Spectral asymptotics of the wave normal frequencies
* `bpW:w1:torus-analytic` [PROPOSED] — Real-analytic tori from complex strips
* `bpW:w1:transport` [PROPOSED] — Weights, transport and coefficient maps
* `bpW:w1:trilinear` [PROPOSED] — The cubic map as a continuous trilinear map
* `bpW:w1:twosided` [PROPOSED] — Passage between one- and two-sided sequences
* `bpW:w1:twosided-transport` [PROPOSED] — Two-sided transport
* `bpW:w1:uniform-limit` [PROPOSED] — Uniform limits
* `bpW:w1:young` [PROPOSED] — Young and $\ell^1$ control
* `bpW:w2:clause5` [PROPOSED] — Clause (5) with the common constant
* `bpW:w2:coeffsol` [PROPOSED] — Analytic coefficient solution
* `bpW:w2:curve` [PROPOSED] — P96-W Lemma~1 in frozen form
* `bpW:w2:curve-deriv` [PROPOSED] — Coefficients of the curve derivative
* `bpW:w2:derived` [PROPOSED] — Derived reconstructions
* `bpW:w2:ext-an` [PROPOSED] — Analytic maps on $\R\times\R$
* `bpW:w2:ext-deriv` [PROPOSED] — One-variable calculus
* `bpW:w2:ext-sums` [PROPOSED] — Series and norms
* `bpW:w2:ext-trig` [PROPOSED] — Trigonometry
* `bpW:w2:force` [PROPOSED] — Force identity in frozen form
* `bpW:w2:functionals` [PROPOSED] — Reconstruction functionals
* `bpW:w2:main` [PROPOSED] — PDE solutions on invariant tori
* `bpW:w2:orbit` [PROPOSED] — Torus orbits are analytic coefficient solutions
* `bpW:w3#data` [PROPOSED] — W3 standing data (a, p, J)
* `bpW:w3:F` [PROPOSED] — $F$ is bounded and one-smoothing
* `bpW:w3:Fdef` [PROPOSED] — Generating Hamiltonian
* `bpW:w3:Lambda` [PROPOSED] — The linear part
* `bpW:w3:Yseries` [PROPOSED] — Power series of the integrand
* `bpW:w3:coords` [PROPOSED] — Complex coordinates and real structure
* `bpW:w3:divisor` [PROPOSED] — Divisor lower bound; P96-W Lemma~4
* `bpW:w3:ext-integral` [PROPOSED] — Integrals in a parameter
* `bpW:w3:ext-multilinear` [PROPOSED] — Multilinear maps
* `bpW:w3:ext-mvt` [PROPOSED] — Mean value inequality; zero derivative
* `bpW:w3:ext-neumann` [PROPOSED] — Neumann series
* `bpW:w3:ext-series` [PROPOSED] — Power series
* `bpW:w3:ext-tsum` [PROPOSED] — Termwise differentiation
* `bpW:w3:flow` [PROPOSED] — The flow of $X_F$
* `bpW:w3:forms` [PROPOSED] — Smoothing symmetric forms
* `bpW:w3:gamma-real` [PROPOSED] — Real change of coordinates
* `bpW:w3:hamfield-def` [PROPOSED] — Hamiltonian field; one-smoothing holomorphic class
* `bpW:w3:hamfield-def#hamilton` [PROPOSED] — Hamilton's equations and reality of X_P
* `bpW:w3:homological` [PROPOSED] — Homological identity
* `bpW:w3:leibniz` [PROPOSED] — Coefficient bounds and the Leibniz identity
* `bpW:w3:lie-coeff` [PROPOSED] — Lie coefficients
* `bpW:w3:main` [PROPOSED] — Analytic partial Birkhoff normal form; P96-W Main Proposition for $J=\{1,2\}$
* `bpW:w3:main-sec#data` [PROPOSED] — H = Lambda + G on W and the integrand Y(t,w)
* `bpW:w3:majorant` [PROPOSED] — Majorant for the cubic sums
* `bpW:w3:omega` [PROPOSED] — Symplectic form
* `bpW:w3:quartic` [PROPOSED] — Quartic forms
* `bpW:w3:quartic-ident` [PROPOSED] — Identification with Part~0
* `bpW:w3:quartic-sec#data` [PROPOSED] — Two-sided quartic coefficients, divisors, pairing, tangential set
* `bpW:w3:real-restrict` [PROPOSED] — Real restrictions
* `bpW:w3:space` [PROPOSED] — Two-sided coordinate space
* `bpW:w3:symplectic` [PROPOSED] — Symplecticity and gradient transport
* `bpW:w3:transport-tori` [PROPOSED] — Invariant tori are transported
* `stepW:w0n:22` [PROPOSED] — Two against two
* `stepW:w0n:31` [PROPOSED] — Four or three equal signs
* `stepW:w0n:A2` [PROPOSED] — Pure normal
* `stepW:w0n:A3red` [PROPOSED] — Reduction of (A$_3$)
* `stepW:w0n:analytic` [PROPOSED] — Analyticity
* `stepW:w0n:converse` [PROPOSED] — Converse
* `stepW:w0n:cos` [PROPOSED] — Cosine integrals
* `stepW:w0n:det` [PROPOSED] — Determinant
* `stepW:w0n:force` [PROPOSED] — Force identity
* `stepW:w0n:ident` [PROPOSED] — Identification
* `stepW:w0n:l1` [PROPOSED] — The case $\abs l=1$
* `stepW:w0n:l2` [PROPOSED] — The case $\abs l=2$
* `stepW:w0n:majorant` [PROPOSED] — Even majorants
* `stepW:w0n:moments` [REVIEWED] — Averages of monomials
* `stepW:w0n:prod` [REVIEWED] — Product to sum
* `stepW:w0n:resavg` [PROPOSED] — Resonant equals averaged
* `stepW:w0n:selection` [PROPOSED] — Selection rule bound
* `stepW:w0n:signed` [PROPOSED] — Signed form
* `stepW:w0n:smoothing` [PROPOSED] — Smoothing
* `stepW:w0n:sum` [PROPOSED] — Summation
* `stepW:w0n:time` [PROPOSED] — Time regularity
* `stepW:w0n:weight` [REVIEWED] — Weight inequality
* `stepW:w0n:young` [PROPOSED] — Young and Cauchy--Schwarz
* `stepW:w1:basis` [PROPOSED] — Hilbert basis
* `stepW:w1:bil` [PROPOSED] — Bilinear form
* `stepW:w1:can` [PROPOSED] — Analyticity
* `stepW:w1:cder` [PROPOSED] — Derivatives
* `stepW:w1:cfrozen` [PROPOSED] — Frozen form
* `stepW:w1:clip` [PROPOSED] — Lipschitz
* `stepW:w1:coeffs` [PROPOSED] — Fourier coefficients vanish
* `stepW:w1:cont` [PROPOSED] — Continuity
* `stepW:w1:coord` [PROPOSED] — Coordinates and truncation
* `stepW:w1:coordcomp` [PROPOSED] — Comparison
* `stepW:w1:coordder` [PROPOSED] — Coordinates of the derivative
* `stepW:w1:cs` [PROPOSED] — Weighted Cauchy--Schwarz
* `stepW:w1:dcbound` [PROPOSED] — Existence of $\rho$, $B$
* `stepW:w1:dcintegral` [PROPOSED] — Cauchy integral along lines
* `stepW:w1:dclip` [PROPOSED] — Lipschitz difference
* `stepW:w1:diagcomb` [PROPOSED] — Diagonal and combination
* `stepW:w1:ext` [PROPOSED] — Extensions
* `stepW:w1:fbconv` [PROPOSED] — Summation
* `stepW:w1:fbdecay` [PROPOSED] — Scalar decay
* `stepW:w1:fbdual` [PROPOSED] — Scalar reduction
* `stepW:w1:fbsum` [PROPOSED] — Lattice sum
* `stepW:w1:flowlim` [PROPOSED] — Limit
* `stepW:w1:flowlip` [PROPOSED] — Lipschitz region
* `stepW:w1:flowpar` [PROPOSED] — Parameters
* `stepW:w1:flowreal` [PROPOSED] — Reality
* `stepW:w1:frozen` [PROPOSED] — Frozen case
* `stepW:w1:fsum` [PROPOSED] — Summation
* `stepW:w1:gradder` [PROPOSED] — Derivative
* `stepW:w1:gradw` [PROPOSED] — Weighted coordinates
* `stepW:w1:growth` [PROPOSED] — Growth on the strip
* `stepW:w1:hacoef` [PROPOSED] — Coefficients
* `stepW:w1:hagroup` [PROPOSED] — Degree grouping
* `stepW:w1:hamargin` [PROPOSED] — Margin
* `stepW:w1:hareal` [PROPOSED] — Real points
* `stepW:w1:hfrozen` [PROPOSED] — Frozen form
* `stepW:w1:hham` [PROPOSED] — Hamiltonian
* `stepW:w1:hlin` [PROPOSED] — Linear part
* `stepW:w1:hnonlin` [PROPOSED] — Nonlinear part
* `stepW:w1:hsum` [PROPOSED] — Sum
* `stepW:w1:iso` [PROPOSED] — Isometry
* `stepW:w1:l1` [PROPOSED] — $\ell^1$ control
* `stepW:w1:latcount` [PROPOSED] — Counting
* `stepW:w1:latdiv` [PROPOSED] — Divisor weights
* `stepW:w1:latprod` [PROPOSED] — Product
* `stepW:w1:latweight` [PROPOSED] — Weighted sum
* `stepW:w1:lines` [PROPOSED] — Complex lines
* `stepW:w1:maj1` [PROPOSED] — One-sided majorant
* `stepW:w1:maj2` [PROPOSED] — Two-sided majorant
* `stepW:w1:margins` [PROPOSED] — Margins
* `stepW:w1:normal` [PROPOSED] — Normal convergence
* `stepW:w1:odd` [PROPOSED] — Odd extension
* `stepW:w1:onevar` [PROPOSED] — One-variable estimate
* `stepW:w1:orthants` [PROPOSED] — Orthants
* `stepW:w1:pair` [PROPOSED] — Pairing
* `stepW:w1:parseval` [PROPOSED] — Parseval
* `stepW:w1:picard` [PROPOSED] — Picard iterates
* `stepW:w1:picardholo` [PROPOSED] — Holomorphy of the iterates
* `stepW:w1:quartic` [PROPOSED] — Quartic form
* `stepW:w1:ratio` [PROPOSED] — Ratio
* `stepW:w1:realflow` [PROPOSED] — Real flow
* `stepW:w1:recanalytic` [PROPOSED] — Analyticity
* `stepW:w1:recder` [PROPOSED] — Derivatives
* `stepW:w1:restr` [PROPOSED] — Restriction
* `stepW:w1:rot` [PROPOSED] — Unboundedness and rotations
* `stepW:w1:rows` [PROPOSED] — Row and column sums
* `stepW:w1:rules` [PROPOSED] — Algebraic rules
* `stepW:w1:schurtest` [PROPOSED] — Schur test
* `stepW:w1:schurweights` [PROPOSED] — Weights
* `stepW:w1:sel1` [PROPOSED] — One-sided selection
* `stepW:w1:sel2` [PROPOSED] — Two-sided selection
* `stepW:w1:sep` [PROPOSED] — Separability
* `stepW:w1:shift` [PROPOSED] — Shifted coefficients
* `stepW:w1:sinereal` [PROPOSED] — Real restriction
* `stepW:w1:smooth1` [PROPOSED] — One-sided smoothing
* `stepW:w1:smooth2` [PROPOSED] — Two-sided smoothing
* `stepW:w1:tricont` [PROPOSED] — Continuity
* `stepW:w1:tricoord` [PROPOSED] — Coordinates
* `stepW:w1:tricoord#via-cubic-bound` [PROPOSED] — Coordinates of the trilinear map via Theorem bpW:w0n:cubic-bound
* `stepW:w1:tricoord#via-selection` [PROPOSED] — Coordinates of the trilinear map via Lemma bpW:w1:selection(a)
* `stepW:w1:trifrozen` [PROPOSED] — Frozen identification
* `stepW:w1:trireal` [PROPOSED] — Real structure and compatibility
* `stepW:w1:ulcauchy` [PROPOSED] — Cauchy in derivatives
* `stepW:w1:ullimit` [PROPOSED] — Limit
* `stepW:w1:youngsum` [PROPOSED] — Summation
* `stepW:w2:bdry` [PROPOSED] — Boundary values
* `stepW:w2:bound` [PROPOSED] — Bound
* `stepW:w2:ccoord` [PROPOSED] — Coordinates
* `stepW:w2:cdiff` [PROPOSED] — Differentiability
* `stepW:w2:fcub` [PROPOSED] — Cubic part
* `stepW:w2:features` [PROPOSED] — Choice of the features
* `stepW:w2:flin` [PROPOSED] — Linear part
* `stepW:w2:frozen` [PROPOSED] — The frozen definition
* `stepW:w2:fsum` [PROPOSED] — Summability
* `stepW:w2:joint` [PROPOSED] — Joint analyticity
* `stepW:w2:mconc` [PROPOSED] — Conclusions
* `stepW:w2:mred` [PROPOSED] — Reduction to a curve
* `stepW:w2:norms` [PROPOSED] — Norms
* `stepW:w2:oan` [PROPOSED] — Analyticity
* `stepW:w2:oshift` [PROPOSED] — Shift
* `stepW:w2:pairing` [PROPOSED] — Pairings
* `stepW:w2:t1` [PROPOSED] — First time derivative
* `stepW:w2:t2` [PROPOSED] — Second time derivative
* `stepW:w2:x` [PROPOSED] — Space derivatives
* `stepW:w2:xder` [PROPOSED] — $x$-derivatives
* `stepW:w3:Fconcl` [PROPOSED] — Conclusions
* `stepW:w3:Gnor` [PROPOSED] — Normal part
* `stepW:w3:Greal` [PROPOSED] — Reality
* `stepW:w3:Gz` [PROPOSED] — The quartic
* `stepW:w3:K1` [PROPOSED] — The bound for $K_1$
* `stepW:w3:K2` [PROPOSED] — The bound for $K_2$
* `stepW:w3:Kanalytic` [PROPOSED] — Analyticity and reality
* `stepW:w3:Phireal` [PROPOSED] — Reality
* `stepW:w3:XG` [PROPOSED] — The field
* `stepW:w3:XK1` [PROPOSED] — The field of $K_1$
* `stepW:w3:XK2` [PROPOSED] — The field of $K_2$
* `stepW:w3:XKconcl` [PROPOSED] — Conclusion of (ii)
* `stepW:w3:Xfcoord` [PROPOSED] — Field coordinates
* `stepW:w3:conj` [PROPOSED] — Conjugacy
* `stepW:w3:constform` [PROPOSED] — Constant form
* `stepW:w3:conv` [PROPOSED] — Convergence and analyticity
* `stepW:w3:count` [PROPOSED] — Count the paired terms
* `stepW:w3:divconcl` [PROPOSED] — Conclusion
* `stepW:w3:divide` [PROPOSED] — Divide
* `stepW:w3:est` [PROPOSED] — Estimates
* `stepW:w3:euler` [PROPOSED] — Euler identity
* `stepW:w3:fcoef` [PROPOSED] — Coefficients
* `stepW:w3:floweq` [PROPOSED] — Flow equation
* `stepW:w3:gradbound` [PROPOSED] — Bound the gradient
* `stepW:w3:gradtrans` [PROPOSED] — Gradient transport
* `stepW:w3:identify` [PROPOSED] — Identify
* `stepW:w3:iii` [PROPOSED] — (iii)
* `stepW:w3:inv` [PROPOSED] — Inverse
* `stepW:w3:leib` [PROPOSED] — Leibniz rule
* `stepW:w3:leibid` [PROPOSED] — The identity
* `stepW:w3:maj` [PROPOSED] — Majorize
* `stepW:w3:majA` [PROPOSED] — The derivative
* `stepW:w3:majN` [PROPOSED] — The inverse
* `stepW:w3:majX` [PROPOSED] — The cubic field along the flow
* `stepW:w3:majY` [PROPOSED] — The integrand
* `stepW:w3:majcalc` [PROPOSED] — Majorant calculus
* `stepW:w3:majflow` [PROPOSED] — The flow
* `stepW:w3:majint` [PROPOSED] — Integrate in $t$
* `stepW:w3:majps` [PROPOSED] — Power series
* `stepW:w3:majreal` [PROPOSED] — Reality
* `stepW:w3:norms` [PROPOSED] — Norms
* `stepW:w3:rec` [PROPOSED] — Recursion
* `stepW:w3:res` [PROPOSED] — Resonance
* `stepW:w3:s0` [PROPOSED] — No minus sign
* `stepW:w3:s1` [PROPOSED] — One minus sign
* `stepW:w3:s1inner` [PROPOSED] — Two minus signs, inner pair
* `stepW:w3:s23` [PROPOSED] — Two minus signs, outer pairs
* `stepW:w3:sel` [PROPOSED] — Selection rule
* `stepW:w3:signs` [PROPOSED] — Signs
* `stepW:w3:skew` [PROPOSED] — Skewness of $DX_F$
* `stepW:w3:transport` [PROPOSED] — Transport equation
* `stepW:w3:var` [PROPOSED] — Variational equation

### Explicit source gaps

* _(none)_
<!-- END PROOF DEPGRAPH GENERATED -->
