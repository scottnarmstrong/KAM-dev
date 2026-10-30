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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
DEPS: bpW:w0:mass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:mass | blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L40-L40 | lambda_j = sqrt(j^2+m) > 0 uses the fixed m > 0
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
DEPS: bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L53-L53 | the norm of l^{a,p} is weighted by j^p e^{aj}, at a = p = 1 the weight of the weighted coordinates
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
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
DEPS: bpW:w0:basis#lam, bpW:w0:reconstruction#reconU, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:H@L89-L89 | Lambda is weighted by lambda_j
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-conventions.tex#bpW:w0:H@L90-L90 | G integrates U_m(q)^4
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w0-conventions.tex#bpW:w0:H@L88-L88 | H is defined on E_{1,1}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
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
DEPS: bpW:w0:reconstruction#reconU, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L98-L98 | the integrand U_m(q)^3
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L98-L98 | the factor 1/sqrt(lambda_l)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L98-L98 | the test mode phi_l
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
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
DEPS: bpW:w0:H, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:H | blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L104-L104 | the equations are Hamilton's equations of H
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L107-L107 | the linear part lambda_j
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L107-L107 | the nonlinear part G_q(q)_j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
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
DEPS: bpW:w0:H, bpW:w0:eqmotion
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:H | blueprint-W/parts/w0-conventions.tex#bpW:w0:z@L121-L121 | Lambda = sum lambda_j ¦z_j¦^2 rewrites the quadratic part of H
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w0-conventions.tex#bpW:w0:z@L122-L122 | the linear flow dq_j = lambda_j p_j, dp_j = -lambda_j q_j and the form sum dq ^ dp
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
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
DEPS: bpW:w0:z, bpW:w0:eqmotion
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:z | blueprint-W/parts/w0-conventions.tex#bpW:w0:actions@L128-L128 | I_j = ¦z_j¦^2 and z_j = sqrt(I_j) e^{-i phi_j}
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w0-conventions.tex#bpW:w0:actions@L132-L132 | the linear flow in action-angle form
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
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
DEPS: bpW:w0:actions, bpW:w0:ellap#WaveSpace, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:actions | blueprint-W/parts/w0-conventions.tex#bpW:w0:periodone@L141-L141 | the formula is the action-angle map with phi_j = 2 pi theta_j
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w0-conventions.tex#bpW:w0:periodone@L141-L141 | K^0_I takes values in E (frozen: WaveSpace, weighted coordinates)
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w0-conventions.tex#bpW:w0:periodone@L141-L141 | frozen weighted coordinates ellWeight 1 1 j * Q^0_j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose (L45-L47) stating facts that later proofs consume (SPEC section-data rule); justification is elementary and inline.
