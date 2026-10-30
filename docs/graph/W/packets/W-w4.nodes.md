NODE: bpW:w4:ext-roots
KIND: external
TITLE: Roots of unity
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ext-roots@L43-L44
PROOF_SOURCE: -
CONTRACT_ID: bpW:w4:ext-roots
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: for m in Z, sum_{u=0}^3 i^{um} = 4 if 4 ¦ m and 0 otherwise (finite geometric sum)
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

NODE: bpW:w4:ext-parallelogram
KIND: external
TITLE: Parallelogram law
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ext-parallelogram@L45-L46
PROOF_SOURCE: -
CONTRACT_ID: bpW:w4:ext-parallelogram
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: parallelogram law ¦¦x+y¦¦^2 + ¦¦x-y¦¦^2 = 2¦¦x¦¦^2 + 2¦¦y¦¦^2 in a complex inner product space
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

NODE: bpW:w4:ext-exp
KIND: external
TITLE: Exponential inequalities
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ext-exp@L47-L49
PROOF_SOURCE: -
CONTRACT_ID: bpW:w4:ext-exp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: e^t >= 1 + t for real t; hence e^{t-1} >= t and x^q e^{-x} <= (q/e)^q for q > 0, x >= 0; sum_{N>=1} e^{-xN} = 1/(e^x - 1) for x > 0
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

NODE: bpW:w4:ext-intparts
KIND: external
TITLE: Periodic integration by parts
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ext-intparts@L50-L52
PROOF_SOURCE: -
CONTRACT_ID: bpW:w4:ext-intparts
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: if g : R -> E (Banach) is C^1 and 1-periodic then int_0^1 g' = 0; continuous linear maps commute with Bochner integrals
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

NODE: bpW:w4:index
KIND: definition
TITLE: Normal modes, reindexing, coordinates
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:index@L59-L103
PROOF_SOURCE: -
CONTRACT_ID: bpW:w4:index
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: a >= 0, p >= 0
SOURCE_QUANTIFIERS: a, p
SOURCE_CONCLUSION: convention: bar p = p+1; tangential modes 1,2, normal modes J = j+2 indexed by the P96-K index j >= 1; the space l^N_{a,q} of (z_j)_{j>=1} with ¦¦z¦¦_{a,q}^2 = sum omega_{a,q}(j+2)^2 ¦z_j¦^2 (wave weights; realized in lp with the entries J = 1,2 zero); max norm on C^2, ¦k¦_1 on Z^2; the unweighted pairing <x,x'>_0 with (bpW:w4:pairing) ¦<x,x'>_0¦ <= ¦¦x¦¦_{a,q} ¦¦x'¦¦_{a,q'} for q + q' >= 0; z = (u+iv)/sqrt2, zbar = (u-iv)/sqrt2 with (bpW:w4:zu); period-one angle theta (x = 2 pi theta), strip T_s, domain D(s,r); symplectic form 2 pi sum dtheta ^ dy + sum du ^ dv and Hamilton's equations (bpW:w4:hameq); angular frequencies omega, nu = omega/(2 pi)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, bpW:w1:tails, bpW:w0:z, bpW:w1:kam-space
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L69-L69 | weighted coordinates at weight (a,q)
EDGE: bpW:w1:tails | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L70-L70 | the convention for normal-mode sequences (entries J = 1,2 zero)
EDGE: bpW:w0:z | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L86-L86 | the W0 convention z = (q + ip)/sqrt2
EDGE: bpW:w1:kam-space | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L93-L93 | the domain D(s,r) of Definition bpW:w1:kam-space
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The pointer to Lemma bpW:w4:lie(iv) (guard (G)) at L61-L62 and to Remark bpW:w4:weights are forward pointers; not edges.

NODE: bpW:w4:ops
KIND: definition
TITLE: Normal operators and their norms
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ops@L117-L128
PROOF_SOURCE: -
CONTRACT_ID: bpW:w4:ops
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2))
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines L (bounded linear maps l^N_{a,p} -> l^N_{a,bar p}, operator norm), matrices M_ij = <M e_j, e_i>_0, transpose and symmetry; the bilinear norm and the space B of bounded bilinear forms; Lambda : L -> B, Lambda M(z,z') = <Mz,z'>_0 with ¦¦Lambda M¦¦_bil <= ¦¦M¦¦; the dual norm ¦¦c¦¦_* and the space l^N_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:ops@L118-L118 | the spaces l^N_{a,q}, the pairing and (bpW:w4:pairing)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:taylor
KIND: definition
TITLE: Taylor Hamiltonians
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L132-L151
PROOF_SOURCE: -
CONTRACT_ID: bpW:w4:taylor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); s > 0; r > 0 for the field norm
SOURCE_QUANTIFIERS: s, r
SOURCE_CONCLUSION: defines the class T_s of R = a + <b,y> + <c^+,z>_0 + <c^-,zbar>_0 + <Pz,z>_0 + <Qz,zbar>_0 + <P'zbar,zbar>_0 (bpW:w4:R) with components a, b, c^+-, P, P', Q, Q^T complex differentiable, 1-periodic and bounded on T_s, P, P' symmetric; the derivatives R_y, R_theta, R_z, R_zbar, R_u, R_v; the field X_R = (R_y/(2pi), -R_theta/(2pi), R_v, -R_u) and ¦X_R¦_r; reality; the mean [g] = hat g_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index, bpW:w4:ops
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L139-L139 | the spaces and the coordinates z, zbar, u, v
EDGE: bpW:w4:ops | blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L138-L138 | the operator space L
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:melnikov
KIND: definition
TITLE: Frequencies, divisors, Melnikov conditions
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:melnikov@L157-L178
PROOF_SOURCE: -
CONTRACT_ID: bpW:w4:melnikov
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); Pi subset R^2; frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega); tau >= 0; alpha > 0
SOURCE_QUANTIFIERS: Pi, omega, Omega, tau, alpha
SOURCE_CONCLUSION: defines (bpW:w4:freq) (Omega_j = j + 2 + tilde Omega_j, sup j¦tilde Omega_j¦ <= M_0, Lipschitz bounds M_omega, M_Omega), M = M_omega + M_Omega, A_0 = 1, A_k = 1 + ¦k¦_1^tau, ¦l¦, <l> = max(1,¦sum j l_j¦), the set Z, the Melnikov conditions (H_alpha) ¦<k,omega(xi)> + <l,Omega(xi)>¦ >= alpha <l>/A_k for (k,l) in Z, the divisors delta^0, delta^+-, delta^P, delta^{P'}, delta^Q and their weights
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:melnikov@L158-L158 | the P96-K normal index j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:wave
KIND: lemma
TITLE: The wave frequencies
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L184-L198
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L200-L214
CONTRACT_ID: bpW:w4:wave
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: lambda_J = sqrt(J^2+m); b = (1/lambda_1, 1/lambda_2); omega(xi) = (lambda_1,lambda_2) + A xi, Omega_j(xi) = lambda_{j+2} + (3/(2 pi lambda_{j+2}))<b,xi> (j >= 1), A of Theorem bpW:w0n:AB
SOURCE_QUANTIFIERS: for every Pi subset R^2
SOURCE_CONCLUSION: (i) (bpW:w4:freq) holds with M_omega = 9/(8 pi lambda_1^2) + 3/(2 pi lambda_1 lambda_2), M_Omega = (3/(2pi))(1/lambda_1 + 1/lambda_2), M_0 = m/2 + (3/(2pi)) sup_Pi ¦<b,xi>¦; P96-K Assumption B holds with d = 1, delta = -1, bar Omega_j = j + 2; (ii) <l> <= <l>^w <= 3<l> for 1 <= ¦l¦ <= 2 unless sum l_j = 0 (then equal), so (H_alpha) with <l>^w implies (H_alpha), and (H_alpha) implies the <l>^w-conditions with alpha/3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w4:melnikov, stepW:w4:waveLip, stepW:w4:waveTail, stepW:w4:waveIdx, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L187-L187 | the matrix A
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L189-L189 | (bpW:w4:freq) and (H_alpha)
EDGE: stepW:w4:waveLip | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L201-L201 | proof step
EDGE: stepW:w4:waveTail | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L206-L206 | proof step
EDGE: stepW:w4:waveIdx | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L210-L210 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L185-L185 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:waveLip
KIND: step
TITLE: Lipschitz constants
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L201-L205
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L201-L205
CONTRACT_ID: stepW:w4:waveLip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:wave: lambda_J = sqrt(J^2+m); b = (1/lambda_1, 1/lambda_2); omega(xi) = (lambda_1,lambda_2) + A xi, Omega_j(xi) = lambda_{j+2} + (3/(2 pi lambda_{j+2}))<b,xi> (j >= 1), A of Theorem bpW:w0n:AB
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:wave (for every Pi subset R^2); within the step: xi, zeta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦A(xi - zeta)¦ <= max row sum ¦xi - zeta¦ (the first row); j¦Omega_j(xi) - Omega_j(zeta)¦ <= (3/(2pi)) ¦b¦_1 ¦xi - zeta¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L203-L203 | A_ii' > 0 and lambda_1 < lambda_2
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L205-L205 | lambda_{j+2} > j; lambda increasing
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L203-L203 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:waveTail
KIND: step
TITLE: Tails
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L206-L209
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L206-L209
CONTRACT_ID: stepW:w4:waveTail
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:wave: lambda_J = sqrt(J^2+m); b = (1/lambda_1, 1/lambda_2); omega(xi) = (lambda_1,lambda_2) + A xi, Omega_j(xi) = lambda_{j+2} + (3/(2 pi lambda_{j+2}))<b,xi> (j >= 1), A of Theorem bpW:w0n:AB
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:wave (for every Pi subset R^2); within the step: xi; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: j¦tilde Omega_j¦ <= m/2 + (3/(2pi))¦<b,xi>¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w1:tails, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L208-L208 | 0 < lambda_J - J = m/(lambda_J + J) <= m/(2J)
EDGE: bpW:w1:tails | blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L209-L209 | the same bound in the wave index
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L207-L207 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:waveIdx
KIND: step
TITLE: Index comparison
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveIdx@L210-L213
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveIdx@L210-L213
CONTRACT_ID: stepW:w4:waveIdx
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:wave: lambda_J = sqrt(J^2+m); b = (1/lambda_1, 1/lambda_2); omega(xi) = (lambda_1,lambda_2) + A xi, Omega_j(xi) = lambda_{j+2} + (3/(2 pi lambda_{j+2}))<b,xi> (j >= 1), A of Theorem bpW:w0n:AB
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:wave (for every Pi subset R^2); within the step: l; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum (j+2) l_j = sum j l_j + 2 sum l_j; the ratio lies in [1,3]
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

NODE: bpW:w4:k0
KIND: lemma
TITLE: The conditions with $k=0$ for the wave frequencies
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:k0@L219-L224
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:k0@L226-L236
CONTRACT_ID: bpW:w4:k0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Lemma bpW:w4:wave; alpha_0(m) = 2/sqrt(9+m); xi in R^2 with ¦<b,xi>¦ <= 2 pi; 0 < alpha <= alpha_0(m)
SOURCE_QUANTIFIERS: for all such xi, alpha; every l with 1 <= ¦l¦ <= 2
SOURCE_CONCLUSION: ¦<l,Omega(xi)>¦ >= alpha <l>; i.e. (H_alpha) with k = 0 holds on Pi subset {¦<b,xi>¦ <= 2 pi}
CONSTANT_SCOPE: alpha_0 depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:wave, bpW:w4:melnikov, stepW:w4:k0one, stepW:w4:k0diff, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:wave | blueprint-W/parts/w4-homological.tex#bpW:w4:k0@L220-L220 | the wave frequencies
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:k0@L222-L222 | (H_alpha) and <l>
EDGE: stepW:w4:k0one | blueprint-W/parts/w4-homological.tex#bpW:w4:k0@L228-L228 | proof step
EDGE: stepW:w4:k0diff | blueprint-W/parts/w4-homological.tex#bpW:w4:k0@L231-L231 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w4-homological.tex#bpW:w4:k0@L229-L229 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:k0one
KIND: step
TITLE: One mode
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:k0one@L228-L230
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:k0one@L228-L230
CONTRACT_ID: stepW:w4:k0one
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:k0: the setting of Lemma bpW:w4:wave; alpha_0(m) = 2/sqrt(9+m); xi in R^2 with ¦<b,xi>¦ <= 2 pi; 0 < alpha <= alpha_0(m); local data: beta = (3/(2pi))<b,xi>, ¦beta¦ <= 3; J = j + 2 >= 3
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:k0 (for all such xi, alpha; every l with 1 <= ¦l¦ <= 2); within the step: j, i; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Omega_j >= J - 1 = j + 1 > alpha<e_j>; Omega_i + Omega_j >= i + j + 2 > alpha<e_i + e_j>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w4-homological.tex#stepW:w4:k0one@L229-L229 | lambda_J > J >= 3
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w4-homological.tex#stepW:w4:k0one@L229-L229 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:k0diff
KIND: step
TITLE: Differences
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:k0diff@L231-L235
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:k0diff@L231-L235
CONTRACT_ID: stepW:w4:k0diff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:k0: the setting of Lemma bpW:w4:wave; alpha_0(m) = 2/sqrt(9+m); xi in R^2 with ¦<b,xi>¦ <= 2 pi; 0 < alpha <= alpha_0(m); local data: beta as above; I = i + 2, J = j + 2
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:k0 (for all such xi, alpha; every l with 1 <= ¦l¦ <= 2); within the step: i > j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Omega_i - Omega_j >= (2/3)(lambda_I - lambda_J) >= alpha_0(m)(i - j) = alpha_0(m)<e_i - e_j>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w4-homological.tex#stepW:w4:k0diff@L234-L234 | lambda_K <= K sqrt(1 + m/9) for K >= 3; lambda_I lambda_J > 9
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w4-homological.tex#stepW:w4:k0diff@L232-L232 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:w1-requests
KIND: claim
TITLE: What W4 uses from W1
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:w1-requests@L275-L293
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:w1-requests@L275-L293
CONTRACT_ID: bpW:w4:w1-requests
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E complex Banach, s > 0, f : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m on T_s; hat f_k
SOURCE_QUANTIFIERS: f, k, c_k, s' < s
SOURCE_CONCLUSION: (F1) ¦¦hat f_k¦¦ <= m e^{-2 pi ¦k¦_1 s}; (F2) for c_k with sum ¦¦c_k¦¦ e^{2 pi ¦k¦_1 s'} < infinity, g = sum c_k e^{2 pi i <k,theta>} converges absolutely and uniformly on T_{s'}, is complex differentiable and 1-periodic, hat g_k = c_k, ¦¦g¦¦ <= sum ¦¦c_k¦¦ e^{2 pi ¦k¦_1 s'}; (F3) (scalar) hat f_k = 0 for all k implies f = 0 on T_s; (F1) is Lemma bpW:w1:fourier-banach(i), (F2) its (iii), (F3) Lemma bpW:w1:fourier-l2(iii) with H = C
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:fourier-banach, bpW:w1:fourier-l2
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:fourier-banach | blueprint-W/parts/w4-homological.tex#bpW:w4:w1-requests@L288-L288 | (F1) is (i), (F2) is (iii)
EDGE: bpW:w1:fourier-l2 | blueprint-W/parts/w4-homological.tex#bpW:w4:w1-requests@L289-L289 | (F3) is (iii) with H = C
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Remark kept as a node: its items (F1)-(F3) are cited by label (\ref{bpW:w4:F1}..F3) in the proofs of W4.

NODE: bpW:w4:fourier-ops
KIND: lemma
TITLE: Coefficients of linear images and derivatives
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L295-L304
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L306-L317
CONTRACT_ID: bpW:w4:fourier-ops
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: f : T_s -> E as in Remark bpW:w4:w1-requests; (iii) f depending on xi in Pi with ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦
SOURCE_QUANTIFIERS: for all such f; Lambda; i in {1,2}; xi, zeta
SOURCE_CONCLUSION: (i) (Lambda f)^_k = Lambda hat f_k for continuous linear Lambda; (ii) d_{theta_i} f is complex differentiable, 1-periodic and (d_{theta_i} f)^_k = 2 pi i k_i hat f_k; (iii) ¦¦hat f_k(xi) - hat f_k(zeta)¦¦ <= m^L ¦xi - zeta¦ e^{-2 pi ¦k¦_1 s}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:w1-requests, stepW:w4:linimg, stepW:w4:deriv, stepW:w4:fpar
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L296-L296 | the setting of f
EDGE: stepW:w4:linimg | blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L307-L307 | proof step
EDGE: stepW:w4:deriv | blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L309-L309 | proof step
EDGE: stepW:w4:fpar | blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L315-L315 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:linimg
KIND: step
TITLE: Linear images
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:linimg@L307-L308
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:linimg@L307-L308
CONTRACT_ID: stepW:w4:linimg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:fourier-ops: f : T_s -> E as in Remark bpW:w4:w1-requests; (iii) f depending on xi in Pi with ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:fourier-ops (for all such f; Lambda; i in {1,2}; xi, zeta); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i): Lambda commutes with the integral defining hat f_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:ext-intparts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:ext-intparts | blueprint-W/parts/w4-homological.tex#stepW:w4:linimg@L308-L308 | continuous linear maps commute with Bochner integrals
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:deriv
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L309-L314
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L309-L314
CONTRACT_ID: stepW:w4:deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:fourier-ops: f : T_s -> E as in Remark bpW:w4:w1-requests; (iii) f depending on xi in Pi with ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:fourier-ops (for all such f; Lambda; i in {1,2}; xi, zeta); within the step: i, k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii): d_{theta_i} f complex differentiable and periodic; (d_{theta_i} f)^_k = 2 pi i k_i hat f_k by periodic integration by parts and Fubini
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-onevar, bpW:w4:ext-intparts, bpW:w1:ext-rect
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L310-L310 | derivatives of holomorphic maps (in theta_i)
EDGE: bpW:w4:ext-intparts | blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L313-L313 | periodic integration by parts
EDGE: bpW:w1:ext-rect | blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L314-L314 | Fubini for continuous functions on [0,1]^2
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:fpar
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:fpar@L315-L316
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:fpar@L315-L316
CONTRACT_ID: stepW:w4:fpar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:fourier-ops: f : T_s -> E as in Remark bpW:w4:w1-requests; (iii) f depending on xi in Pi with ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:fourier-ops (for all such f; Lambda; i in {1,2}; xi, zeta); within the step: xi, zeta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii): (F1) applied to f(.,xi) - f(.,zeta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:w1-requests
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#stepW:w4:fpar@L316-L316 | (F1)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:lattice
KIND: lemma
TITLE: Lattice sums in $\Z^2$
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L320-L335
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L337-L355
CONTRACT_ID: bpW:w4:lattice
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: sigma > 0; S_q(sigma) = sum_{k in Z^2} ¦k¦_1^q e^{-2 pi ¦k¦_1 sigma} (q >= 0, 0^0 = 1); (iv) tau >= 0, A_k as in Definition bpW:w4:melnikov, B^W_sigma = sum (1 + ¦k¦_1) A_k^2 e^{-2 pi ¦k¦_1 sigma}
SOURCE_QUANTIFIERS: for all sigma > 0, q, tau
SOURCE_CONCLUSION: (i) #{k : ¦k¦_1 = N} = 4N; (ii) S_0 = coth(pi sigma)^2 <= (1 + 1/(pi sigma))^2; (iii) S_q <= (4/(pi sigma)) ((q+1)/(e pi sigma))^{q+1} for q > 0; (iv) sum A_k e^{-2 pi¦k¦_1 sigma} <= B^W_sigma and for 0 < sigma <= 1, B^W_sigma <= b_W(tau)/sigma^{2tau+3}, b_W(tau) = 2(C_0 + C_1 + C_{2tau} + C_{2tau+1})
CONSTANT_SCOPE: b_W depends only on tau
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:melnikov, stepW:w4:count, stepW:w4:coth, stepW:w4:wsum, stepW:w4:bw
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L326-L326 | A_k
EDGE: stepW:w4:count | blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L338-L338 | proof step
EDGE: stepW:w4:coth | blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L341-L341 | proof step
EDGE: stepW:w4:wsum | blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L344-L344 | proof step
EDGE: stepW:w4:bw | blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L347-L347 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:count
KIND: step
TITLE: Counting
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:count@L338-L340
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:count@L338-L340
CONTRACT_ID: stepW:w4:count
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lattice: sigma > 0; S_q(sigma) = sum_{k in Z^2} ¦k¦_1^q e^{-2 pi ¦k¦_1 sigma} (q >= 0, 0^0 = 1); (iv) tau >= 0, A_k as in Definition bpW:w4:melnikov, B^W_sigma = sum (1 + ¦k¦_1) A_k^2 e^{-2 pi ¦k¦_1 sigma}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lattice (for all sigma > 0, q, tau); within the step: N >= 1; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i) #{¦k¦_1 = N} = 4N
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

NODE: stepW:w4:coth
KIND: step
TITLE: Product
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:coth@L341-L343
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:coth@L341-L343
CONTRACT_ID: stepW:w4:coth
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lattice: sigma > 0; S_q(sigma) = sum_{k in Z^2} ¦k¦_1^q e^{-2 pi ¦k¦_1 sigma} (q >= 0, 0^0 = 1); (iv) tau >= 0, A_k as in Definition bpW:w4:melnikov, B^W_sigma = sum (1 + ¦k¦_1) A_k^2 e^{-2 pi ¦k¦_1 sigma}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lattice (for all sigma > 0, q, tau); within the step: sigma; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii): the sum factorizes and sum_m e^{-x¦m¦} = coth(x/2); coth t <= 1 + 1/t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:ext-exp
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:ext-exp | blueprint-W/parts/w4-homological.tex#stepW:w4:coth@L343-L343 | geometric sum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:wsum
KIND: step
TITLE: Weighted sums
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:wsum@L344-L346
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:wsum@L344-L346
CONTRACT_ID: stepW:w4:wsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lattice: sigma > 0; S_q(sigma) = sum_{k in Z^2} ¦k¦_1^q e^{-2 pi ¦k¦_1 sigma} (q >= 0, 0^0 = 1); (iv) tau >= 0, A_k as in Definition bpW:w4:melnikov, B^W_sigma = sum (1 + ¦k¦_1) A_k^2 e^{-2 pi ¦k¦_1 sigma}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lattice (for all sigma > 0, q, tau); within the step: q > 0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii): S_q = 4 sum N^{q+1} e^{-xN} with the stated bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:count, bpW:w4:ext-exp
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:count | blueprint-W/parts/w4-homological.tex#stepW:w4:wsum@L345-L345 | (i)
EDGE: bpW:w4:ext-exp | blueprint-W/parts/w4-homological.tex#stepW:w4:wsum@L346-L346 | x^q e^{-x} <= (q/e)^q and the geometric sum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:bw
KIND: step
TITLE: The constant
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:bw@L347-L354
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:bw@L347-L354
CONTRACT_ID: stepW:w4:bw
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lattice: sigma > 0; S_q(sigma) = sum_{k in Z^2} ¦k¦_1^q e^{-2 pi ¦k¦_1 sigma} (q >= 0, 0^0 = 1); (iv) tau >= 0, A_k as in Definition bpW:w4:melnikov, B^W_sigma = sum (1 + ¦k¦_1) A_k^2 e^{-2 pi ¦k¦_1 sigma}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lattice (for all sigma > 0, q, tau); within the step: tau, sigma <= 1; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): the bound on B^W_sigma via S_0, S_1, S_{2tau}, S_{2tau+1}
CONSTANT_SCOPE: b_W depends only on tau
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:coth, stepW:w4:wsum
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:coth | blueprint-W/parts/w4-homological.tex#stepW:w4:bw@L352-L352 | (ii)
EDGE: stepW:w4:wsum | blueprint-W/parts/w4-homological.tex#stepW:w4:bw@L352-L352 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:divisors
KIND: lemma
TITLE: Divisor bounds
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L361-L367
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L369-L380
CONTRACT_ID: bpW:w4:divisors
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega); (H_alpha)
SOURCE_QUANTIFIERS: for every divisor delta with weight w; all xi, zeta in Pi; k in Z^2
SOURCE_CONCLUSION: ¦delta(xi)¦ >= alpha w/A_k and ¦1/delta(xi) - 1/delta(zeta)¦ <= 2(1 + ¦k¦_1) A_k^2 M ¦xi - zeta¦/(alpha^2 w); w^Q_ij >= ¦i-j¦, w^P_ij >= ¦i-j¦ for i != j, all weights >= 1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:melnikov, stepW:w4:member, stepW:w4:divlip
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L362-L362 | (bpW:w4:freq), (H_alpha), divisors and weights
EDGE: stepW:w4:member | blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L370-L370 | proof step
EDGE: stepW:w4:divlip | blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L375-L375 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:member
KIND: step
TITLE: Membership
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:member@L370-L374
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:member@L370-L374
CONTRACT_ID: stepW:w4:member
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:divisors: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega); (H_alpha)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:divisors (for every divisor delta with weight w; all xi, zeta in Pi; k in Z^2); within the step: divisors; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: each divisor is <k,omega> + <l,Omega> with (k,l) in Z and <l> = w; (H_alpha) gives the lower bound
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

NODE: stepW:w4:divlip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L375-L379
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L375-L379
CONTRACT_ID: stepW:w4:divlip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:divisors: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega); (H_alpha)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:divisors (for every divisor delta with weight w; all xi, zeta in Pi; k in Z^2); within the step: xi, zeta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦delta(xi) - delta(zeta)¦ <= (¦k¦_1 + 2) M ¦xi - zeta¦; dividing by ¦delta(xi) delta(zeta)¦ gives the Lipschitz bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:member
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:member | blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L378-L378 | the lower bound alpha w/A_k
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:schur
KIND: lemma
TITLE: Hadamard division of operators
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L387-L402
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L404-L416
CONTRACT_ID: bpW:w4:schur
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); K_S = 1 + pi/sqrt3; d_ij with ¦d_ij¦ <= c/¦i-j¦ (i != j), ¦d_ii¦ <= c; positive mu, nu; A with weighted matrix (mu_i A_ij nu_j) bounded on l^2 with norm N_A
SOURCE_QUANTIFIERS: for all such d, c, mu, nu, A
SOURCE_CONCLUSION: (mu_i d_ij A_ij nu_j) is bounded with norm <= c K_S N_A; (i) H_d : M -> (d_ij M_ij) is bounded L -> L with norm <= c K_S and H_d(M)^T = H_{d^T}(M^T); (ii) the same on bilinear forms B -> B, Lambda o H_d = H_d o Lambda; (iii) for diagonal d the bound is c, in particular (i+2)¦M_ii¦ <= ¦¦M¦¦ for M in L
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:ops, stepW:w4:schurtr, stepW:w4:schurrep, stepW:w4:schurdiag
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:ops | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L394-L394 | L, B, Lambda
EDGE: stepW:w4:schurtr | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L405-L405 | proof step
EDGE: stepW:w4:schurrep | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L408-L408 | proof step
EDGE: stepW:w4:schurdiag | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L414-L414 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:schurtr
KIND: step
TITLE: Transport
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurtr@L405-L407
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurtr@L405-L407
CONTRACT_ID: stepW:w4:schurtr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:schur: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); K_S = 1 + pi/sqrt3; d_ij with ¦d_ij¦ <= c/¦i-j¦ (i != j), ¦d_ii¦ <= c; positive mu, nu; A with weighted matrix (mu_i A_ij nu_j) bounded on l^2 with norm N_A
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:schur (for all such d, c, mu, nu, A); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the weighted matrices satisfy the hypotheses of Lemma bpW:w1:schur(iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:schur
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:schurtr@L406-L406 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:schurrep
KIND: step
TITLE: Representatives
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L408-L413
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L408-L413
CONTRACT_ID: stepW:w4:schurrep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:schur: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); K_S = 1 + pi/sqrt3; d_ij with ¦d_ij¦ <= c/¦i-j¦ (i != j), ¦d_ii¦ <= c; positive mu, nu; A with weighted matrix (mu_i A_ij nu_j) bounded on l^2 with norm N_A
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:schur (for all such d, c, mu, nu, A); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the weighted matrix of M in L is that of its representative; bounded weighted matrices are exactly elements of L; the bilinear case via Riesz on l^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L410-L410 | the representative tau o M o kappa
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:schurdiag
KIND: step
TITLE: Diagonal
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurdiag@L414-L415
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurdiag@L414-L415
CONTRACT_ID: stepW:w4:schurdiag
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:schur: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); K_S = 1 + pi/sqrt3; d_ij with ¦d_ij¦ <= c/¦i-j¦ (i != j), ¦d_ii¦ <= c; positive mu, nu; A with weighted matrix (mu_i A_ij nu_j) bounded on l^2 with norm N_A
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:schur (for all such d, c, mu, nu, A); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii): diagonal multipliers; mu_i nu_i = i + 2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:schur, bpW:w1:multiplier
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:schurdiag@L415-L415 | (ii)
EDGE: bpW:w1:multiplier | blueprint-W/parts/w4-homological.tex#stepW:w4:schurdiag@L415-L415 | diagonal multipliers
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:solve
KIND: lemma
TITLE: Multiplier solve
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L421-L439
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L441-L461
CONTRACT_ID: bpW:w4:solve
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: (i) the series converges absolutely and uniformly on T_{s-sigma}; S f is complex differentiable, 1-periodic, with coefficients T_k hat f_k and ¦¦S f¦¦ <= kappa B^W_sigma m/alpha; (ii) ¦¦S f(xi) - S f(zeta)¦¦ <= (kappa B^W_sigma/alpha)(m^L + 2Mm/alpha)¦xi - zeta¦; (iii) if d_{theta_i} f is bounded then d_{theta_i} S f = S(d_{theta_i} f); (iv) S commutes with continuous linear images (Lambda S f, Lambda_1 S f = S'(Lambda_0 f))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:lattice, stepW:w4:solvecoef, stepW:w4:solvediff, stepW:w4:solvecomm, stepW:w4:solvelin
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L431-L431 | B^W_sigma
EDGE: stepW:w4:solvecoef | blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L442-L442 | proof step
EDGE: stepW:w4:solvediff | blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L446-L446 | proof step
EDGE: stepW:w4:solvecomm | blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L452-L452 | proof step
EDGE: stepW:w4:solvelin | blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L458-L458 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:solvecoef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L442-L445
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L442-L445
CONTRACT_ID: stepW:w4:solvecoef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:solve: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:solve (for all such data); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i): sum ¦¦T_k hat f_k¦¦ e^{2 pi ¦k¦_1 (s-sigma)} <= kappa m B^W_sigma/alpha and (F2) with s' = s - sigma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:w1-requests, bpW:w4:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L443-L443 | (F1), (F2)
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L445-L445 | (iv)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:solvediff
KIND: step
TITLE: Differences
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L446-L451
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L446-L451
CONTRACT_ID: stepW:w4:solvediff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:solve: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:solve (for all such data); within the step: xi, zeta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii): the coefficient differences are bounded and summed
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:fourier-ops, bpW:w4:w1-requests, bpW:w4:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L448-L448 | (iii)
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L448-L448 | (F1), (F2)
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L450-L450 | B^W_sigma
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:solvecomm
KIND: step
TITLE: Commutation
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L452-L457
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L452-L457
CONTRACT_ID: stepW:w4:solvecomm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:solve: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:solve (for all such data); within the step: i; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii): termwise differentiation gives d_{theta_i} S f = S(d_{theta_i} f)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:fourier-ops, stepW:w4:solvecoef, bpW:w1:ext-unifderiv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L453-L453 | (ii)
EDGE: stepW:w4:solvecoef | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L454-L454 | summability
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L456-L456 | termwise differentiation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:solvelin
KIND: step
TITLE: Linear images
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L458-L460
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L458-L460
CONTRACT_ID: stepW:w4:solvelin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:solve: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:solve (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): Lambda commutes with absolutely convergent sums
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:fourier-ops
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L460-L460 | (i)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:lie
KIND: lemma
TITLE: Lie derivative and weak bracket
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L480-L508
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L510-L537
CONTRACT_ID: bpW:w4:lie
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega); F in T_{s'} with components a_F, b_F, c^+-_F, P_F, Q_F, P'_F; L_N F and the weak bracket <<N,F>> as displayed; (iv) the guard (G)
SOURCE_QUANTIFIERS: for (theta,y,z,zbar) in T_{s'} x C^2 x (l^N_{a,p})^2
SOURCE_CONCLUSION: (i) Omega z in l^N_{a,p-1} with ¦¦Omega z¦¦_{a,p-1} <= (1+M_0)¦¦z¦¦; L_N F and <<N,F>> are continuous in (z,zbar) and polynomials of degree <= 2; (ii) <<N,F>> = -L_N F; (iii) on finitely supported z, zbar, L_N F replaces the k-th coefficient of each component by i delta times it (delta = <k,omega>, delta^+-, delta^P, delta^Q with delta^Q_{0,jj} = 0, delta^{P'}); (iv) under (G), N_Omega is a continuous bilinear form with ¦N_Omega¦ <= (1+M_0) gamma_{a,p} ¦¦z¦¦ ¦¦zbar¦¦, N is a continuous polynomial, Frechet differentiable, and DN(w) . X_F(w) = <<N,F>>(w) = -L_N F(w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:taylor, bpW:w4:lie-sec#guard, bpW:w4:melnikov, stepW:w4:liebd, stepW:w4:liebr, stepW:w4:liecoef, stepW:w4:lieder
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L481-L481 | the class T_{s'}, components and gradients
EDGE: bpW:w4:lie-sec#guard | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L500-L500 | the guard (G) and N
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L481-L481 | (bpW:w4:freq) and the divisors
EDGE: stepW:w4:liebd | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L511-L511 | proof step
EDGE: stepW:w4:liebr | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L516-L516 | proof step
EDGE: stepW:w4:liecoef | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L520-L520 | proof step
EDGE: stepW:w4:lieder | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L528-L528 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:liebd
KIND: step
TITLE: Bounds
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liebd@L511-L515
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liebd@L511-L515
CONTRACT_ID: stepW:w4:liebd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lie: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega); F in T_{s'} with components a_F, b_F, c^+-_F, P_F, Q_F, P'_F; L_N F and the weak bracket <<N,F>> as displayed; (iv) the guard (G)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lie (for (theta,y,z,zbar) in T_{s'} x C^2 x (l^N_{a,p})^2); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦Omega_j¦ <= (1+M_0)(j+2); the pairings are bounded by (bpW:w4:pairing) with q = p-1, q' = p+1; continuity in (z,zbar)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#stepW:w4:liebd@L513-L513 | (bpW:w4:pairing)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:liebr
KIND: step
TITLE: Weak bracket
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liebr@L516-L519
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liebr@L516-L519
CONTRACT_ID: stepW:w4:liebr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lie: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega); F in T_{s'} with components a_F, b_F, c^+-_F, P_F, Q_F, P'_F; L_N F and the weak bracket <<N,F>> as displayed; (iv) the guard (G)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lie (for (theta,y,z,zbar) in T_{s'} x C^2 x (l^N_{a,p})^2); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii): substitution gives <<N,F>> = -L_N F, an identity of expressions
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

NODE: stepW:w4:liecoef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liecoef@L520-L527
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liecoef@L520-L527
CONTRACT_ID: stepW:w4:liecoef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lie: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega); F in T_{s'} with components a_F, b_F, c^+-_F, P_F, Q_F, P'_F; L_N F and the weak bracket <<N,F>> as displayed; (iv) the guard (G)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lie (for (theta,y,z,zbar) in T_{s'} x C^2 x (l^N_{a,p})^2); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii): coefficient collection; the k-th coefficient of (1/(2pi))<omega, d_theta g> is i<k,omega> hat g_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:taylor, bpW:w4:fourier-ops
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#stepW:w4:liecoef@L522-L522 | F_z, F_zbar
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w4-homological.tex#stepW:w4:liecoef@L526-L526 | (i), (ii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:lieder
KIND: step
TITLE: The guarded derivative
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L528-L536
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L528-L536
CONTRACT_ID: stepW:w4:lieder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lie: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega); F in T_{s'} with components a_F, b_F, c^+-_F, P_F, Q_F, P'_F; L_N F and the weak bracket <<N,F>> as displayed; (iv) the guard (G)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lie (for (theta,y,z,zbar) in T_{s'} x C^2 x (l^N_{a,p})^2); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): under (G) N_Omega is bounded bilinear, N a continuous polynomial with the displayed derivative; DN . X_F = <<N,F>>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:lie-sec#guard, bpW:w1:embed, bpW:w4:index, stepW:w4:liebr
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lie-sec#guard | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L529-L529 | (G)
EDGE: bpW:w1:embed | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L533-L533 | l^N_{a,bar p} subset l^N_{a,p}
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L532-L532 | (bpW:w4:hameq): the components of X_F
EDGE: stepW:w4:liebr | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L536-L536 | (ii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:extract
KIND: lemma
TITLE: Coefficient extraction
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:extract@L547-L551
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:extract@L553-L559
CONTRACT_ID: bpW:w4:extract
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: E complex Banach, rho_1, rho_2 > 0, g(zeta,eta) = sum_{p+q<=2} g_pq zeta^p eta^q with g_pq in E, ¦¦g¦¦ <= K on ¦zeta¦ < rho_1, ¦eta¦ < rho_2
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: ¦¦g_pq¦¦ <= K rho_1^{-p} rho_2^{-q} for p + q <= 2; likewise in one variable
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:ext-roots
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:ext-roots | blueprint-W/parts/w4-homological.tex#bpW:w4:extract@L557-L557 | averages over fourth roots of unity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:components
KIND: lemma
TITLE: Component bounds
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:components@L563-L573
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:components@L575-L601
CONTRACT_ID: bpW:w4:components
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); s, r > 0; R in T_s with ¦X_R(theta,y,z,zbar)¦_r <= eps on D(s,r)
SOURCE_QUANTIFIERS: for all theta in T_s, i in {1,2}
SOURCE_CONCLUSION: (i) ¦b¦ <= 2 pi eps, ¦¦c^+-¦¦_{bar p} <= r eps/sqrt2, ¦¦2P¦¦, ¦¦Q¦¦, ¦¦Q^T¦¦, ¦¦2P'¦¦ <= eps; (ii) ¦d_{theta_i} a¦ <= 2 pi r^2 eps, ¦d_{theta_i} b¦_1 <= 2 pi eps, ¦¦d_{theta_i} c^+-¦¦_* <= 2 sqrt2 pi r eps, ¦¦Lambda d_{theta_i} P¦¦_bil, ¦¦Lambda d_{theta_i} P'¦¦_bil <= 4 pi eps, ¦¦Lambda d_{theta_i} Q¦¦_bil <= 16 pi eps
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:taylor, bpW:w4:ops, stepW:w4:testpts, stepW:w4:first, stepW:w4:angle, stepW:w4:polar
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L564-L564 | T_s and ¦X_R¦_r
EDGE: bpW:w4:ops | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L568-L568 | norms on L, B, l^N_*
EDGE: stepW:w4:testpts | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L576-L576 | proof step
EDGE: stepW:w4:first | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L582-L582 | proof step
EDGE: stepW:w4:angle | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L587-L587 | proof step
EDGE: stepW:w4:polar | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L596-L596 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:testpts
KIND: step
TITLE: Test points
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:testpts@L576-L581
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:testpts@L576-L581
CONTRACT_ID: stepW:w4:testpts
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:components: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); s, r > 0; R in T_s with ¦X_R(theta,y,z,zbar)¦_r <= eps on D(s,r)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:components (for all theta in T_s, i in {1,2}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the test points lie in D(s,r); there ¦R_y¦ <= 2 pi eps, ¦R_theta¦ <= 2 pi r^2 eps, ¦¦R_z¦¦, ¦¦R_zbar¦¦ <= r eps/sqrt2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#stepW:w4:testpts@L577-L577 | (bpW:w4:zu)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:first
KIND: step
TITLE: Zeroth and first order
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:first@L582-L586
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:first@L582-L586
CONTRACT_ID: stepW:w4:first
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:components: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); s, r > 0; R in T_s with ¦X_R(theta,y,z,zbar)¦_r <= eps on D(s,r)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:components (for all theta in T_s, i in {1,2}); within the step: theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i) via the polynomial structure and coefficient extraction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:testpts, bpW:w4:extract
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:testpts | blueprint-W/parts/w4-homological.tex#stepW:w4:first@L584-L584 | bounds at the test points
EDGE: bpW:w4:extract | blueprint-W/parts/w4-homological.tex#stepW:w4:first@L585-L585 | coefficient extraction
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:angle
KIND: step
TITLE: Angle derivatives
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:angle@L587-L595
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:angle@L587-L595
CONTRACT_ID: stepW:w4:angle
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:components: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); s, r > 0; R in T_s with ¦X_R(theta,y,z,zbar)¦_r <= eps on D(s,r)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:components (for all theta in T_s, i in {1,2}); within the step: theta, i; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) for a, b, c^+-, P, Q, P' by coefficient extraction in zeta, eta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:testpts, bpW:w4:extract
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:testpts | blueprint-W/parts/w4-homological.tex#stepW:w4:angle@L589-L589 | bounds at the test points
EDGE: bpW:w4:extract | blueprint-W/parts/w4-homological.tex#stepW:w4:angle@L589-L589 | coefficient extraction
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:polar
KIND: step
TITLE: Polarization
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:polar@L596-L600
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:polar@L596-L600
CONTRACT_ID: stepW:w4:polar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:components: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); s, r > 0; R in T_s with ¦X_R(theta,y,z,zbar)¦_r <= eps on D(s,r)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:components (for all theta in T_s, i in {1,2}); within the step: unit z, z'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: polarization: ¦beta(z,z')¦ <= 4 pi eps for symmetric beta = Lambda d_{theta_i} P
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:angle, bpW:w4:ext-parallelogram
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:angle | blueprint-W/parts/w4-homological.tex#stepW:w4:polar@L599-L599 | the diagonal bound
EDGE: bpW:w4:ext-parallelogram | blueprint-W/parts/w4-homological.tex#stepW:w4:polar@L600-L600 | parallelogram law
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:lemma1
KIND: theorem
TITLE: P96-K Lemma~1 for the wave setting
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L608-L633
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L635-L708
CONTRACT_ID: bpW:w4:lemma1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega) on Pi subset R^2; tau >= 0; (H_alpha) for some alpha > 0; 0 < sigma < s, r > 0, eps, eps^L >= 0; for each xi in Pi, R(.,xi) in T_s with ¦X_{R(xi)}¦_r <= eps and ¦X_{R(xi)} - X_{R(zeta)}¦_r <= eps^L ¦xi - zeta¦ on D(s,r); F defined componentwise by division by i delta; hat N = <hat omega,y> + sum hat Omega_j z_j zbar_j, hat omega = [b], hat Omega_j = ([Q])_jj; C_1 = 7 + 10 K_S, B = B^W_sigma
SOURCE_QUANTIFIERS: for every xi in Pi
SOURCE_CONCLUSION: (i) F in T_{s-sigma} with hat a_{F,0} = 0, hat b_{F,0} = 0, (hat Q_{F,0})_jj = 0; real if R is real (hat omega in R^2, hat Omega_j in R); (ii) L_N F + hat N = R - hat a_0, equivalently R + <<N,F>> = hat N + hat a_0, and under (G) (in particular a = p = 1) R + DN . X_F = hat N + hat a_0; (iii) ¦X_F¦_r <= C_1 B eps/alpha and ¦X_{F(xi)} - X_{F(zeta)}¦_r <= (C_1 B/alpha)(eps^L + 2M eps/alpha)¦xi - zeta¦ on D(s-sigma,r); (iv) ¦hat omega¦ <= 2 pi eps, sup (j+2)¦hat Omega_j¦ <= eps (likewise for differences), ¦X_{hat N}¦_r <= 2 eps and the Lipschitz analogue on D(s,r)
CONSTANT_SCOPE: C_1 = 7 + 10 K_S < 36 absolute; B = B^W_sigma depends on tau, sigma
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:taylor, bpW:w4:melnikov, bpW:w4:lie, bpW:w4:lie-sec#guard, bpW:w4:lattice, bpW:w4:schur, stepW:w4:divops, stepW:w4:class, stepW:w4:equation, stepW:w4:Fcomp, stepW:w4:assembly, stepW:w4:lip, stepW:w4:Nhat, stepW:w4:real
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L611-L611 | the class T_s
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L614-L614 | divisors and (H_alpha)
EDGE: bpW:w4:lie | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L624-L624 | L_N and the weak bracket
EDGE: bpW:w4:lie-sec#guard | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L626-L626 | the guard (G)
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L620-L620 | B^W_sigma
EDGE: bpW:w4:schur | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L620-L620 | K_S
EDGE: stepW:w4:divops | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L636-L636 | proof step
EDGE: stepW:w4:class | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L645-L645 | proof step
EDGE: stepW:w4:equation | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L650-L650 | proof step
EDGE: stepW:w4:Fcomp | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L660-L660 | proof step
EDGE: stepW:w4:assembly | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L674-L674 | proof step
EDGE: stepW:w4:lip | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L687-L687 | proof step
EDGE: stepW:w4:Nhat | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L693-L693 | proof step
EDGE: stepW:w4:real | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L700-L700 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:divops
KIND: step
TITLE: Division operators
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L636-L644
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L636-L644
CONTRACT_ID: stepW:w4:divops
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lemma1: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega) on Pi subset R^2; tau >= 0; (H_alpha) for some alpha > 0; 0 < sigma < s, r > 0, eps, eps^L >= 0; for each xi in Pi, R(.,xi) in T_s with ¦X_{R(xi)}¦_r <= eps and ¦X_{R(xi)} - X_{R(zeta)}¦_r <= eps^L ¦xi - zeta¦ on D(s,r); F defined componentwise by division by i delta; hat N = <hat omega,y> + sum hat Omega_j z_j zbar_j, hat omega = [b], hat Omega_j = ([Q])_jj; C_1 = 7 + 10 K_S, B = B^W_sigma
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lemma1 (for every xi in Pi); within the step: k, xi; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the division operators T_k satisfy the hypotheses of Lemma bpW:w4:solve with kappa = 1 (a, b, c^+-) and kappa = K_S (P, Q, Q^T, P')
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:divisors, bpW:w4:schur, bpW:w1:multiplier, bpW:w4:solve
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:divisors | blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L640-L640 | divisor bounds
EDGE: bpW:w4:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L642-L642 | Hadamard maps
EDGE: bpW:w1:multiplier | blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L643-L643 | diagonal multipliers
EDGE: bpW:w4:solve | blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L643-L643 | its hypotheses
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:class
KIND: step
TITLE: The solution is in the class
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:class@L645-L649
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:class@L645-L649
CONTRACT_ID: stepW:w4:class
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lemma1: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega) on Pi subset R^2; tau >= 0; (H_alpha) for some alpha > 0; 0 < sigma < s, r > 0, eps, eps^L >= 0; for each xi in Pi, R(.,xi) in T_s with ¦X_{R(xi)}¦_r <= eps and ¦X_{R(xi)} - X_{R(zeta)}¦_r <= eps^L ¦xi - zeta¦ on D(s,r); F defined componentwise by division by i delta; hat N = <hat omega,y> + sum hat Omega_j z_j zbar_j, hat omega = [b], hat Omega_j = ([Q])_jj; C_1 = 7 + 10 K_S, B = B^W_sigma
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lemma1 (for every xi in Pi); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: each component of F is S g (in T_{s-sigma}); Q_F^T via H_d(M)^T = H_{d^T}(M^T); P_F, P'_F symmetric; vanishing coefficients
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:solve, bpW:w4:schur, stepW:w4:divops
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:solve | blueprint-W/parts/w4-homological.tex#stepW:w4:class@L646-L646 | (i)
EDGE: bpW:w4:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:class@L647-L647 | (i) transpose identity
EDGE: stepW:w4:divops | blueprint-W/parts/w4-homological.tex#stepW:w4:class@L646-L646 | the division operators
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:equation
KIND: step
TITLE: The equation
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L650-L659
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L650-L659
CONTRACT_ID: stepW:w4:equation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lemma1: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega) on Pi subset R^2; tau >= 0; (H_alpha) for some alpha > 0; 0 < sigma < s, r > 0, eps, eps^L >= 0; for each xi in Pi, R(.,xi) in T_s with ¦X_{R(xi)}¦_r <= eps and ¦X_{R(xi)} - X_{R(zeta)}¦_r <= eps^L ¦xi - zeta¦ on D(s,r); F defined componentwise by division by i delta; hat N = <hat omega,y> + sum hat Omega_j z_j zbar_j, hat omega = [b], hat Omega_j = ([Q])_jj; C_1 = 7 + 10 K_S, B = B^W_sigma
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lemma1 (for every xi in Pi); within the step: y, finitely supported z, zbar; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii): the coefficients of L_N F + hat N - R + hat a_0 vanish, so it vanishes; extended by continuity and density; second and third forms
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:solve, bpW:w4:components, bpW:w4:lie, bpW:w4:w1-requests, bpW:w1:space, stepW:w4:class, stepW:w4:Nhat
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:solve | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L653-L653 | (iii)
EDGE: bpW:w4:components | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L653-L653 | (ii)
EDGE: bpW:w4:lie | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L653-L653 | (i)-(iv)
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L656-L656 | (F3)
EDGE: bpW:w1:space | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L658-L658 | (iii) density of finitely supported sequences
EDGE: stepW:w4:class | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L654-L654 | the components of F
EDGE: stepW:w4:Nhat | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L657-L657 | hat N continuous
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:Fcomp
KIND: step
TITLE: Component bounds of $F$
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L660-L673
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L660-L673
CONTRACT_ID: stepW:w4:Fcomp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lemma1: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega) on Pi subset R^2; tau >= 0; (H_alpha) for some alpha > 0; 0 < sigma < s, r > 0, eps, eps^L >= 0; for each xi in Pi, R(.,xi) in T_s with ¦X_{R(xi)}¦_r <= eps and ¦X_{R(xi)} - X_{R(zeta)}¦_r <= eps^L ¦xi - zeta¦ on D(s,r); F defined componentwise by division by i delta; hat N = <hat omega,y> + sum hat Omega_j z_j zbar_j, hat omega = [b], hat Omega_j = ([Q])_jj; C_1 = 7 + 10 K_S, B = B^W_sigma
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lemma1 (for every xi in Pi); within the step: theta in T_{s-sigma}; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the component bounds of F (values and theta-derivatives)
CONSTANT_SCOPE: C_1 absolute
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:components, stepW:w4:divops, bpW:w4:solve, bpW:w4:schur, bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:components | blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L661-L661 | the component bounds of R
EDGE: stepW:w4:divops | blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L661-L661 | kappa
EDGE: bpW:w4:solve | blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L661-L661 | (i), (iii), (iv)
EDGE: bpW:w4:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L669-L669 | (ii) Hadamard maps on B
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L672-L672 | (bpW:w4:pairing): ¦¦c¦¦_* <= ¦¦c¦¦_{bar p}
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:assembly
KIND: step
TITLE: Assembly
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:assembly@L674-L686
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:assembly@L674-L686
CONTRACT_ID: stepW:w4:assembly
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lemma1: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega) on Pi subset R^2; tau >= 0; (H_alpha) for some alpha > 0; 0 < sigma < s, r > 0, eps, eps^L >= 0; for each xi in Pi, R(.,xi) in T_s with ¦X_{R(xi)}¦_r <= eps and ¦X_{R(xi)} - X_{R(zeta)}¦_r <= eps^L ¦xi - zeta¦ on D(s,r); F defined componentwise by division by i delta; hat N = <hat omega,y> + sum hat Omega_j z_j zbar_j, hat omega = [b], hat Omega_j = ([Q])_jj; C_1 = 7 + 10 K_S, B = B^W_sigma
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lemma1 (for every xi in Pi); within the step: (theta,y,z,zbar) in D(s-sigma,r); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦X_F¦_r <= C_1 B eps/alpha
CONSTANT_SCOPE: C_1 absolute
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index, stepW:w4:Fcomp
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#stepW:w4:assembly@L675-L675 | (bpW:w4:zu)
EDGE: stepW:w4:Fcomp | blueprint-W/parts/w4-homological.tex#stepW:w4:assembly@L676-L676 | the component bounds
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:lip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L687-L692
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L687-L692
CONTRACT_ID: stepW:w4:lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lemma1: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega) on Pi subset R^2; tau >= 0; (H_alpha) for some alpha > 0; 0 < sigma < s, r > 0, eps, eps^L >= 0; for each xi in Pi, R(.,xi) in T_s with ¦X_{R(xi)}¦_r <= eps and ¦X_{R(xi)} - X_{R(zeta)}¦_r <= eps^L ¦xi - zeta¦ on D(s,r); F defined componentwise by division by i delta; hat N = <hat omega,y> + sum hat Omega_j z_j zbar_j, hat omega = [b], hat Omega_j = ([Q])_jj; C_1 = 7 + 10 K_S, B = B^W_sigma
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lemma1 (for every xi in Pi); within the step: xi, zeta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) Lipschitz part via R(xi) - R(zeta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:components, bpW:w4:solve, stepW:w4:assembly, stepW:w4:Fcomp
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:components | blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L689-L689 | applied to R(xi) - R(zeta)
EDGE: bpW:w4:solve | blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L690-L690 | (ii)
EDGE: stepW:w4:assembly | blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L691-L691 | linear assembly
EDGE: stepW:w4:Fcomp | blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L689-L689 | the inputs
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:Nhat
KIND: step
TITLE: The normal form correction
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:Nhat@L693-L699
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:Nhat@L693-L699
CONTRACT_ID: stepW:w4:Nhat
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lemma1: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega) on Pi subset R^2; tau >= 0; (H_alpha) for some alpha > 0; 0 < sigma < s, r > 0, eps, eps^L >= 0; for each xi in Pi, R(.,xi) in T_s with ¦X_{R(xi)}¦_r <= eps and ¦X_{R(xi)} - X_{R(zeta)}¦_r <= eps^L ¦xi - zeta¦ on D(s,r); F defined componentwise by division by i delta; hat N = <hat omega,y> + sum hat Omega_j z_j zbar_j, hat omega = [b], hat Omega_j = ([Q])_jj; C_1 = 7 + 10 K_S, B = B^W_sigma
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lemma1 (for every xi in Pi); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): bounds on hat omega, hat Omega and X_{hat N}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:components, bpW:w4:schur
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:components | blueprint-W/parts/w4-homological.tex#stepW:w4:Nhat@L694-L694 | ¦b¦ <= 2 pi eps, ¦¦Q¦¦ <= eps
EDGE: bpW:w4:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:Nhat@L695-L695 | (iii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w4:real
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:real@L700-L707
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:real@L700-L707
CONTRACT_ID: stepW:w4:real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:lemma1: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega) on Pi subset R^2; tau >= 0; (H_alpha) for some alpha > 0; 0 < sigma < s, r > 0, eps, eps^L >= 0; for each xi in Pi, R(.,xi) in T_s with ¦X_{R(xi)}¦_r <= eps and ¦X_{R(xi)} - X_{R(zeta)}¦_r <= eps^L ¦xi - zeta¦ on D(s,r); F defined componentwise by division by i delta; hat N = <hat omega,y> + sum hat Omega_j z_j zbar_j, hat omega = [b], hat Omega_j = ([Q])_jj; C_1 = 7 + 10 K_S, B = B^W_sigma
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:lemma1 (for every xi in Pi); within the step: real xi; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the reality relations pass to F and hat N
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:taylor, stepW:w4:class
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#stepW:w4:real@L701-L701 | reality of R
EDGE: stepW:w4:class | blueprint-W/parts/w4-homological.tex#stepW:w4:real@L705-L705 | the coefficients of F
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:lemma2
KIND: corollary
TITLE: P96-K Lemma~2
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lemma2@L721-L729
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lemma2@L731-L735
CONTRACT_ID: bpW:w4:lemma2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Theorem bpW:w4:lemma1 with M > 0; 0 <= lambda <= alpha/M; ¦X¦^lambda = eps_X + lambda eps_X^L
SOURCE_QUANTIFIERS: for all such lambda
SOURCE_CONCLUSION: ¦X_{hat N}¦^lambda_{r,D(s,r)} <= 2 ¦X_R¦^lambda_{r,D(s,r)}, ¦X_F¦^lambda_{r,D(s-sigma,r)} <= (3 C_1 B^W_sigma/alpha) ¦X_R¦^lambda_{r,D(s,r)}, and for 0 < sigma <= 1, B^W_sigma <= b_W(tau) sigma^{-(2tau+3)} (P96-K (4), b = b_W(tau)); 3 C_1 < 108 replaces P96-K's absolute a
CONSTANT_SCOPE: 3 C_1 absolute; b_W depends only on tau
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:lemma1, bpW:w4:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma2@L733-L733 | (iii), (iv)
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma2@L734-L734 | (iv)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: lambda here is the P96-K weighting parameter, not the frequency lambda_j (no lam edge).

NODE: bpW:w4:from-w3
KIND: claim
TITLE: From W3
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L774-L793
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L774-L793
CONTRACT_ID: bpW:w4:from-w3
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the Birkhoff coordinates of Theorem bpW:w3:main; Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2))
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: z_j = w_{j+2}, zbar_j = w_{-(j+2)}, on real points u_j = q_{j+2}, v_j = p_{j+2}; ¦¦hat w¦¦^2 = ¦¦z¦¦^2 + ¦¦zbar¦¦^2 = ¦¦u¦¦^2 + ¦¦v¦¦^2 with the wave weights; (b) ¦¦hat w¦¦ <= ¦¦u¦¦ + ¦¦v¦¦ <= sqrt2 ¦¦hat w¦¦; (c) the smoothing class of W3 gives normal gradients in l^N_{a,bar p}; (d) Omega restricted to the normal part is sum du ^ dv and dz = -i H_zbar agrees with X_P(w)_l = -i sgn(l) DP(w) e_{-l}; ownership ruling: W5 owns the action-angle substitution, the domain check and the norm comparisons
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w3:space, bpW:w3:coords, bpW:w4:index, bpW:w3:omega, bpW:w3:hamfield-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L775-L775 | the Birkhoff map
EDGE: bpW:w3:space | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L776-L776 | the coordinates w_l
EDGE: bpW:w3:coords | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L777-L777 | u_j = q_{j+2}, v_j = p_{j+2}
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L779-L779 | the wave weights
EDGE: bpW:w3:omega | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L782-L782 | the symplectic form
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L783-L783 | X_P
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Remark kept as a node: its identifications are consumed by W5 (action-angle substitution); the ownership ruling and the pointer to Remark bpW:w3:interface are administrative.

NODE: bpW:w4:lie-sec#guard
KIND: definition
TITLE: The guard (G) and the weak-bracket setting
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L469-L478
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L469-L478
CONTRACT_ID: bpW:w4:lie-sec#guard
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega)
SOURCE_QUANTIFIERS: a, p
SOURCE_CONCLUSION: defines the formal normal form N = <omega(xi),y> + sum Omega_j z_j zbar_j and the guard (G) gamma_{a,p} = sup_j (j+2)/omega_{a,p}(j+2)^2 < infinity (bpW:w4:guard); records that the series of N need not converge for a = p = 0, that (G) holds iff a > 0 or p >= 1/2, and gamma_{1,1} = e^{-6}/3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:index, bpW:w4:melnikov
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L474-L474 | the wave weights omega_{a,p}(j+2)
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L469-L469 | omega, Omega
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L469-L478 with the display label bpW:w4:guard (SPEC section-data rule); consumed by Lemma bpW:w4:lie(iv) and Theorem bpW:w4:lemma1(ii).
