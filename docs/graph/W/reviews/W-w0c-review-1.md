# W-w0c review 1

Reviewer: sol-review-W-w0c. Verdict: **FAIL**. Source topology only; no proof-status inference.

Re-read all 180 lines of w0-conventions.tex, SPEC, both rendered packets, the permitted frozen definitions and nlw2 statement. All ten anchors in this slice match manifest path, export, ID, contract ID/version and ABI; docstring mappings agree. No cross-part dependency is retained in this slice. Forward pointers at L84–85, L99–100 and L111 correctly create no edges.

| Node | Verdict | Source spans re-read / reason |
|---|---|---|
| bpW:w0:mass | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:mass@L24-L27 |
| bpW:w0:nlw#IsClassicalSolution | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:nlw@L29-L35 |
| bpW:w0:basis#lam | FAIL | Eigenfunction identity in the retained conclusion directly uses sineMode (L41), but has no edge. |
| bpW:w0:basis#sineMode | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L39-L42 |
| bpW:w0:ellap#ellWeight | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L51-L57 |
| bpW:w0:ellap#WaveSpace | FAIL | General spaces at L52–56 are missing; the interpretation explicitly uses coeff without its required anchor edge. |
| bpW:w0:ellap#coeff | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L51-L57 |
| bpW:w0:twosided | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:twosided@L66-L71 |
| bpW:w0:reconstruction#reconU | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L75-L81 |
| bpW:w0:reconstruction#reconV | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L75-L81 |
| bpW:w0:H | FAIL | The retained finiteness claim on general E_{a,p} needs the missing general-space definition. |
| bpW:w0:Gq#cubicGrad | FAIL | Its source fields explicitly identify q with frozen coeff y, but omit that anchor dependency. |
| bpW:w0:eqmotion | FAIL | Missing direct use of m in sqrt(1+m), of E_{1,1}, and of general weighted spaces (L109–110). |
| bpW:w0:z | FAIL | Direct occurrences of lambda in the energy and linear flow (L121–122) lack the mandated lam edge. |
| bpW:w0:actions | FAIL | Direct lambda in Lambda and the angular velocity (L131–132) lacks the mandated lam edge. |
| bpW:w0:periodone#linearTorus | FAIL | The retained invariance frequency (lambda_1,lambda_2)/(2 pi) at L143 lacks the mandated lam edge. |
| bpW:w0:basis#lambda-facts | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L45-L47 |
| bpW:w0:ellap#spaces | FAIL | NEW: the general real/complex sequence spaces and E_{a,p} at L52–56 are not the frozen specialized WaveSpace. |
| bpW:w0:reconstruction#rescaling | FAIL | NEW: L78–80 inverse dictionary and symplectic carrier change are absent from both reconstruction records. |

## Coverage

| Item | Verdict | Reason |
|---|---|---|
| bpW:w0:ellap#WaveSpace | FAIL | L51–57 inventory omits the general real/complex spaces and general product norm. |
| bpW:w0:reconstruction#reconU | FAIL | L75–81 inventory omits the inverse dictionary and symplectic rescaling at L78–80. |
| bpW:w0:eq | FAIL | Missing equation-label inventory required by SPEC. |
| bpW:w0:coeffsys | FAIL | Missing equation-label inventory required by SPEC. |

all other coverage items PASS.

## Replacement fragments

Complete blocks below preserve the original anchor identities. New records are proposals; no packet changes were made.

```text
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
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
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
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
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
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
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
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The \ref{bpW:w0n:gradient} and \ref{bpW:w0n:cubic-bound} of L99-L100 are forward pointers (they would close the cycle cubicGrad -> gradient -> cubicGrad); not edges.
```

```text
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
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The \ref{bpW:w0n:cubic-bound} of L111 (smoothing of order one) is a forward pointer, not an edge.
```

```text
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
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
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
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
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
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
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
EXTRACTOR: sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
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
EXTRACTOR: sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
ITEM: bpW:w0:ellap#WaveSpace
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L51-L57
DISPOSITION: NODE bpW:w0:ellap#WaveSpace, bpW:w0:ellap#spaces
REASON: includes the general spaces and product norm, as well as the frozen specialization
COVERAGE_STATUS: PROPOSED
EXTRACTOR: sol-review-W-w0c
REVIEWER: -
```

```text
ITEM: bpW:w0:reconstruction#reconU
KIND: definition
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L75-L81
DISPOSITION: NODE bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#rescaling
REASON: reconstruction formula plus the inverse coefficient dictionary and symplectic rescaling
COVERAGE_STATUS: PROPOSED
EXTRACTOR: sol-review-W-w0c
REVIEWER: -
```

```text
ITEM: bpW:w0:eq
KIND: equation
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:eq@L32-L34
DISPOSITION: NODE bpW:w0:nlw#IsClassicalSolution
REASON: equation label maps to its enclosing definition, per SPEC
COVERAGE_STATUS: PROPOSED
EXTRACTOR: sol-review-W-w0c
REVIEWER: -
```

```text
ITEM: bpW:w0:coeffsys
KIND: equation
SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:coeffsys@L106-L108
DISPOSITION: NODE bpW:w0:eqmotion
REASON: equation label maps to its enclosing definition, per SPEC
COVERAGE_STATUS: PROPOSED
EXTRACTOR: sol-review-W-w0c
REVIEWER: -
```

## Suspected blueprint defects and specification discrepancy

- w0-conventions.tex L67–70: “For $a\ge0$, $s\in\R$” and “The convolution is $(c*d)_l=\sum_{i\in\Z}c_id_{l-i}$.” This does not guarantee a convergent convolution for every pair in the stated space: at a = 0, s = -1, the constant sequence c_i = d_i = 1 has finite weighted square norm, whereas every convolution coordinate diverges. The node faithfully records the literal formula; convergence at later restricted exponents requires its own result. No extra global convolution theorem is certified here.
- SPEC slice table says W-w0c has “11 of the 13 anchors”. Its own mapping and manifest identify ten here; W-wh contains embedding, IsDiophantine and nlw2 (three). Mapping identities themselves agree.

## Checks

- Allowed slice checker: `W-w0c: 17 nodes, 28 edges, 39 coverage items, 0 problems`. This checks structure, not the missing uses above.
- Read-only Python comparison: all ten anchor identity tuples and contract ID/version match the manifest.
- No git, Lean, lake, build or lint was run. Only this report was written.
