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
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
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
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
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
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
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
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w4:index
KIND: definition
TITLE: Normal modes, reindexing, coordinates
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:index@L69-L113
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
DEPS: bpW:w1:transport, bpW:w1:tails, bpW:w0:z, bpW:w1:kam-space, bpW:w0:ellap#ellWeight, bpW:w1:kam-conventions
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L79-L79 | weighted coordinates at weight (a,q)
EDGE: bpW:w1:tails | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L80-L80 | the convention for normal-mode sequences (entries J = 1,2 zero)
EDGE: bpW:w0:z | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L96-L96 | the W0 convention z = (q + ip)/sqrt2
EDGE: bpW:w1:kam-space | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L103-L103 | the domain D(s,r) of Definition bpW:w1:kam-space
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L77-L77 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
EDGE: bpW:w1:kam-conventions | blueprint-W/parts/w4-homological.tex#bpW:w4:index@L97-L97 | the W0/P96-K conjugate-coordinate exchange cited inside the convention
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4+sol-delta5-W-w1b
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homWt, KAM.Wave.HomNormal, KAM.Wave.homNormLp, KAM.Wave.homNorm, KAM.Wave.homPair_le, KAM.Wave.norm_homPair_le, KAM.Wave.homNormal_mul, KAM.Wave.HomL2, KAM.Wave.homNorm_le_uv, KAM.Wave.HomDomain (KAM/Wave/Homological/Index.lean, KAM/Wave/Homological/Schur.lean, KAM/Wave/Homological/Taylor.lean)
LEAN_NOTE: definition formalized by W4-HOMOLOGICAL in the representative model (z in l^N_{a,q} as hat z_j = omega_{a,q}(j+2) z_j in HomL2); W4-HOMOLOGICAL audit 1 PASS (index, pairing), unchanged in audit 2; the symplectic form and Hamilton's equations enter through the field X_R of the Taylor class (homXnorm)
NOTE: The pointer to Lemma bpW:w4:lie(iv) (guard (G)) at L71-L72 and to Remark bpW:w4:weights are forward pointers; not edges.

NODE: bpW:w4:ops
KIND: definition
TITLE: Normal operators and their norms
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ops@L127-L138
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
DEPS: bpW:w4:index, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:ops@L128-L128 | the spaces l^N_{a,q}, the pairing and (bpW:w4:pairing)
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#bpW:w4:ops@L135-L135 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.HomOp, KAM.Wave.homNormalEntry, KAM.Wave.homLamCLM, KAM.Wave.norm_homLamCLM_apply_le, KAM.Wave.homDualNorm, KAM.Wave.norm_le_of_pairing_le (KAM/Wave/Homological/Schur.lean, KAM/Wave/Homological/PPlusOne.lean, KAM/Wave/Homological/NormalOps.lean)
LEAN_NOTE: definition formalized by W4-HOMOLOGICAL in the weighted-matrix model (L = HomOp on representatives, Lambda M = D hat M, ||Lambda M||_bil = ||Lambda M||, dual norm ||D hat c||); W4-HOMOLOGICAL audit 1 PASS WITH NOTES (schur (ii), ops); no public isometric equivalence with an abstract space of bounded bilinear forms (audit 1 model limit)
NOTE: -

NODE: bpW:w4:taylor
KIND: definition
TITLE: Taylor Hamiltonians
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L142-L161
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
DEPS: bpW:w4:index, bpW:w4:ops, bpW:w1:kam-space
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L149-L149 | the spaces and the coordinates z, zbar, u, v
EDGE: bpW:w4:ops | blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L148-L148 | the operator space L
EDGE: bpW:w1:kam-space | blueprint-W/parts/w4-homological.tex#bpW:w4:taylor@L156-L156 | the field norm is identified with this domain/norm definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.HomTaylor, KAM.Wave.HomTaylor_gen, KAM.Wave.homRval, KAM.Wave.homRy, KAM.Wave.homRz, KAM.Wave.homRzb, KAM.Wave.homRu, KAM.Wave.homRv, KAM.Wave.homRtheta, KAM.Wave.homXnorm, KAM.Wave.HomFieldBound, KAM.Wave.HomTaylor.isRealTaylor, KAM.Wave.homCoeff (KAM/Wave/Homological/PPlusOne.lean, KAM/Wave/Homological/Taylor.lean, KAM/Wave/Homological/Solve.lean)
LEAN_NOTE: definition formalized by W4-HOMOLOGICAL; W4-HOMOLOGICAL audit 1 PASS ON SOURCE DOMAIN (eight components, P, P' symmetric and Q^T the entrywise transpose on T_s, independent z and zbar); reality is HomTaylor.isRealTaylor
NOTE: -

NODE: bpW:w4:melnikov
KIND: definition
TITLE: Frequencies, divisors, Melnikov conditions
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:melnikov@L167-L188
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
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:melnikov@L168-L168 | the P96-K normal index j
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.HomFreqHyp1, KAM.Wave.HomFreqHyp, KAM.Wave.HomFreqHyp1.toHyp, KAM.Wave.HomMelnikov, KAM.Wave.homJap, KAM.Wave.waveA, KAM.Wave.homDelta0, KAM.Wave.homDeltaPlus, KAM.Wave.homDeltaMinus, KAM.Wave.homDeltaP, KAM.Wave.homDeltaP', KAM.Wave.homDeltaQ, KAM.Wave.homWeightQ (KAM/Wave/Homological/Melnikov.lean, KAM/Wave/Homological/LatticeBW.lean)
LEAN_NOTE: definition formalized by W4-HOMOLOGICAL; W4-HOMOLOGICAL audit 1 PASS (exclusions correct, repeated indices in P retained, Q weight is the max form); the W4 frequency hypothesis is HomFreqHyp1 (tail weight j), HomFreqHyp is the weak j^{1/2} form of bpW:w5:freq
NOTE: -

NODE: bpW:w4:wave
KIND: lemma
TITLE: The wave frequencies
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L194-L208
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L210-L224
CONTRACT_ID: bpW:w4:wave
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: lambda_J = sqrt(J^2+m); b = (1/lambda_1, 1/lambda_2); omega(xi) = (lambda_1,lambda_2) + A xi, Omega_j(xi) = lambda_{j+2} + (3/(2 pi lambda_{j+2}))<b,xi> (j >= 1), A of Theorem bpW:w0n:AB
SOURCE_QUANTIFIERS: for every Pi subset R^2
SOURCE_CONCLUSION: (i) (bpW:w4:freq) holds with M_omega = 9/(8 pi lambda_1^2) + 3/(2 pi lambda_1 lambda_2), M_Omega = (3/(2pi))(1/lambda_1 + 1/lambda_2), M_0 = m/2 + (3/(2pi)) sup_Pi ¦<b,xi>¦ when that supremum is finite; P96-K Assumption B holds with d = 1, delta = -1, bar Omega_j = j + 2; (ii) <l> <= <l>^w <= 3<l> for 1 <= ¦l¦ <= 2 unless sum l_j = 0 (then equal), so (H_alpha) with <l>^w implies (H_alpha), and (H_alpha) implies the <l>^w-conditions with alpha/3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w4:melnikov, stepW:w4:waveLip, stepW:w4:waveTail, stepW:w4:waveIdx, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L197-L197 | the matrix A
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L199-L199 | (bpW:w4:freq) and (H_alpha)
EDGE: stepW:w4:waveLip | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L211-L211 | proof step
EDGE: stepW:w4:waveTail | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L216-L216 | proof step
EDGE: stepW:w4:waveIdx | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L220-L220 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w4-homological.tex#bpW:w4:wave@L195-L195 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.waveFreqTan, KAM.Wave.waveFreqNor, KAM.Wave.waveMomega, KAM.Wave.waveMOmega, KAM.Wave.homFreqHyp1_wave, KAM.Wave.homFreqHyp_wave, KAM.Wave.homJapW_reindex, KAM.Wave.homJap_le_japW_le, KAM.Wave.homMelnikov_of_melnikovW, KAM.Wave.homMelnikovW_of_melnikov (KAM/Wave/Homological/Wave.lean, KAM/Wave/Homological/WaveReindex.lean)
LEAN_NOTE: W4-HOMOLOGICAL audit 1 PASS ((i), (ii)); M_0 stated with an arbitrary valid upper bound for sup |<b,xi>|
NOTE: -

NODE: stepW:w4:waveLip
KIND: step
TITLE: Lipschitz constants
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L211-L215
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L211-L215
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
EDGE: bpW:w0n:AB | blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L213-L213 | A_ii' > 0 and lambda_1 < lambda_2
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L215-L215 | lambda_{j+2} > j; lambda increasing
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w4-homological.tex#stepW:w4:waveLip@L213-L213 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homFreqHyp1_wave, KAM.Wave.waveMomega, KAM.Wave.waveMOmega (KAM/Wave/Homological/Wave.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:wave; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: stepW:w4:waveTail
KIND: step
TITLE: Tails
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L216-L219
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L216-L219
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
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L218-L218 | 0 < lambda_J - J = m/(lambda_J + J) <= m/(2J)
EDGE: bpW:w1:tails | blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L219-L219 | the same bound in the wave index
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w4-homological.tex#stepW:w4:waveTail@L217-L217 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homFreqHyp1_wave (KAM/Wave/Homological/Wave.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:wave; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: stepW:w4:waveIdx
KIND: step
TITLE: Index comparison
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveIdx@L220-L223
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:waveIdx@L220-L223
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
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homJapW_reindex, KAM.Wave.homJap_le_japW_le (KAM/Wave/Homological/WaveReindex.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:wave; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: bpW:w4:w1-requests
KIND: claim
TITLE: What W4 uses from W1
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:w1-requests@L286-L304
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:w1-requests@L286-L304
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
EDGE: bpW:w1:fourier-banach | blueprint-W/parts/w4-homological.tex#bpW:w4:w1-requests@L299-L299 | (F1) is (i), (F2) is (iii)
EDGE: bpW:w1:fourier-l2 | blueprint-W/parts/w4-homological.tex#bpW:w4:w1-requests@L300-L300 | (F3) is (iii) with H = C
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.kamFourierBanach_coeff_le, KAM.Wave.kamFourierBanach_summation, KAM.Wave.kamFourierL2_eq_fourierSum (KAM/Wave/KamSupport/FourierBanach.lean, KAM/Wave/KamSupport/FourierL2.lean)
LEAN_NOTE: pointer remark; (F1)-(F3) are the W1 lemmas bpW:w1:fourier-banach (i), (iii) and bpW:w1:fourier-l2 (iii), PROVED by W1-KAMSUP (audit 2 PASS WITH NOTES) and used by W4-HOMOLOGICAL; (F3) follows from the representation theorem with all coefficients zero, not stated separately
NOTE: Remark kept as a node: its items (F1)-(F3) are cited by label (\ref{bpW:w4:F1}..F3) in the proofs of W4.

NODE: bpW:w4:fourier-ops
KIND: lemma
TITLE: Coefficients of linear images and derivatives
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L306-L315
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L317-L328
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
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L307-L307 | the setting of f
EDGE: stepW:w4:linimg | blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L318-L318 | proof step
EDGE: stepW:w4:deriv | blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L320-L320 | proof step
EDGE: stepW:w4:fpar | blueprint-W/parts/w4-homological.tex#bpW:w4:fourier-ops@L326-L326 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homCoeff_clm, KAM.Wave.homPartial_differentiableOn, KAM.Wave.homCoeff_partial, KAM.Wave.differentiableOn_fderiv_of_isOpen_pi_banach, KAM.Wave.homCoeff_sub_banach (KAM/Wave/Homological/SolveLinear.lean, KAM/Wave/Homological/SolveDeriv.lean, KAM/Wave/Homological/HolomorphicBanach.lean, KAM/Wave/Homological/Lemma1.lean)
LEAN_NOTE: W4-HOMOLOGICAL audit 1 PASS ((ii); derivative holomorphy also for nonseparable Banach targets), PASS WITH NOTES ((i), (iii): summability is an explicit premise of low-level linear-image helpers, supplied by homSolve_spec)
NOTE: -

NODE: stepW:w4:linimg
KIND: step
TITLE: Linear images
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:linimg@L318-L319
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:linimg@L318-L319
CONTRACT_ID: stepW:w4:linimg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:fourier-ops: f : T_s -> E as in Remark bpW:w4:w1-requests; (iii) f depending on xi in Pi with ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:fourier-ops (for all such f; Lambda; i in {1,2}; xi, zeta)
SOURCE_CONCLUSION: (i): Lambda commutes with the integral defining hat f_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:ext-intparts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:ext-intparts | blueprint-W/parts/w4-homological.tex#stepW:w4:linimg@L319-L319 | continuous linear maps commute with Bochner integrals
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homCoeff_clm (KAM/Wave/Homological/SolveLinear.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:fourier-ops; W4-HOMOLOGICAL audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w4:deriv
KIND: step
TITLE: Derivatives
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L320-L325
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L320-L325
CONTRACT_ID: stepW:w4:deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:fourier-ops: f : T_s -> E as in Remark bpW:w4:w1-requests; (iii) f depending on xi in Pi with ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:fourier-ops (for all such f; Lambda; i in {1,2}; xi, zeta); within the step: i, k
SOURCE_CONCLUSION: (ii): d_{theta_i} f complex differentiable and periodic; (d_{theta_i} f)^_k = 2 pi i k_i hat f_k by periodic integration by parts and Fubini
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-onevar, bpW:w4:ext-intparts, bpW:w1:ext-rect
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L321-L321 | derivatives of holomorphic maps (in theta_i)
EDGE: bpW:w4:ext-intparts | blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L324-L324 | periodic integration by parts
EDGE: bpW:w1:ext-rect | blueprint-W/parts/w4-homological.tex#stepW:w4:deriv@L325-L325 | Fubini for continuous functions on [0,1]^2
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homPartial_differentiableOn, KAM.Wave.homCoeff_partial, KAM.Wave.differentiableOn_fderiv_of_isOpen_pi_banach (KAM/Wave/Homological/SolveDeriv.lean, KAM/Wave/Homological/HolomorphicBanach.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:fourier-ops; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: stepW:w4:fpar
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:fpar@L326-L327
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:fpar@L326-L327
CONTRACT_ID: stepW:w4:fpar
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:fourier-ops: f : T_s -> E as in Remark bpW:w4:w1-requests; (iii) f depending on xi in Pi with ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:fourier-ops (for all such f; Lambda; i in {1,2}; xi, zeta); within the step: xi, zeta
SOURCE_CONCLUSION: (iii): (F1) applied to f(.,xi) - f(.,zeta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:w1-requests
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#stepW:w4:fpar@L327-L327 | (F1)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homCoeff_sub_banach (KAM/Wave/Homological/Lemma1.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:fourier-ops; W4-HOMOLOGICAL audit 1 PASS WITH NOTES
NOTE: -

NODE: bpW:w4:lattice
KIND: lemma
TITLE: Lattice sums in $\Z^2$
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L331-L346
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L348-L366
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
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L337-L337 | A_k
EDGE: stepW:w4:count | blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L349-L349 | proof step
EDGE: stepW:w4:coth | blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L352-L352 | proof step
EDGE: stepW:w4:wsum | blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L355-L355 | proof step
EDGE: stepW:w4:bw | blueprint-W/parts/w4-homological.tex#bpW:w4:lattice@L358-L358 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.waveSphere_card, KAM.Wave.waveS_zero_value, KAM.Wave.waveS_zero_le, KAM.Wave.waveS_le, KAM.Wave.waveS_summable, KAM.Wave.waveA, KAM.Wave.waveBW, KAM.Wave.waveC, KAM.Wave.waveBWconst, KAM.Wave.waveSum_A_le_waveBW, KAM.Wave.waveBW_le (KAM/Wave/Homological/LatticeCount.lean, KAM/Wave/Homological/Lattice.lean, KAM/Wave/Homological/LatticeBW.lean)
LEAN_NOTE: W4-HOMOLOGICAL audit 1 PASS ((i)-(iii)), PASS ON SOURCE DOMAIN ((iv): A_0 = 1 also at tau = 0, exponent 2tau+3; raw sums are totalized off the source domain)
NOTE: -

NODE: stepW:w4:count
KIND: step
TITLE: Counting
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:count@L349-L351
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:count@L349-L351
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
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.waveSphere_card (KAM/Wave/Homological/LatticeCount.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:lattice; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: stepW:w4:coth
KIND: step
TITLE: Product
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:coth@L352-L354
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:coth@L352-L354
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
EDGE: bpW:w4:ext-exp | blueprint-W/parts/w4-homological.tex#stepW:w4:coth@L354-L354 | geometric sum
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.waveS_zero_value, KAM.Wave.waveS_zero_le (KAM/Wave/Homological/Lattice.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:lattice; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: stepW:w4:wsum
KIND: step
TITLE: Weighted sums
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:wsum@L355-L357
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:wsum@L355-L357
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
EDGE: stepW:w4:count | blueprint-W/parts/w4-homological.tex#stepW:w4:wsum@L356-L356 | (i)
EDGE: bpW:w4:ext-exp | blueprint-W/parts/w4-homological.tex#stepW:w4:wsum@L357-L357 | x^q e^{-x} <= (q/e)^q and the geometric sum
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.waveS_le, KAM.Wave.waveS_summable (KAM/Wave/Homological/Lattice.lean, KAM/Wave/Homological/LatticeBW.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:lattice; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: stepW:w4:bw
KIND: step
TITLE: The constant
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:bw@L358-L365
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:bw@L358-L365
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
EDGE: stepW:w4:coth | blueprint-W/parts/w4-homological.tex#stepW:w4:bw@L363-L363 | (ii)
EDGE: stepW:w4:wsum | blueprint-W/parts/w4-homological.tex#stepW:w4:bw@L363-L363 | (iii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.waveSum_A_le_waveBW, KAM.Wave.waveBW_le, KAM.Wave.waveBWconst (KAM/Wave/Homological/LatticeBW.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:lattice; W4-HOMOLOGICAL audit 1 PASS ON SOURCE DOMAIN
NOTE: -

NODE: bpW:w4:divisors
KIND: lemma
TITLE: Divisor bounds
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L372-L378
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L380-L391
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
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L373-L373 | (bpW:w4:freq), (H_alpha), divisors and weights
EDGE: stepW:w4:member | blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L381-L381 | proof step
EDGE: stepW:w4:divlip | blueprint-W/parts/w4-homological.tex#bpW:w4:divisors@L386-L386 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homDivGen_bounds, KAM.Wave.homDelta0_bound, KAM.Wave.homDeltaPlus_bound, KAM.Wave.homDeltaMinus_bound, KAM.Wave.homDeltaP_bound, KAM.Wave.homDeltaP'_bound, KAM.Wave.homDeltaQ_bound, KAM.Wave.homWeightQ (KAM/Wave/Homological/Divisors.lean, KAM/Wave/Homological/DivisorsConcrete.lean, KAM/Wave/Homological/Melnikov.lean)
LEAN_NOTE: W4-HOMOLOGICAL audit 1 PASS (weak tail suffices for the same difference estimate)
NOTE: -

NODE: stepW:w4:member
KIND: step
TITLE: Membership
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:member@L381-L385
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:member@L381-L385
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
DEPS: bpW:w4:melnikov
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#stepW:w4:member@L383-L383 | the exclusions defining the divisors and Z are used to prove membership
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homDivGen_bounds (KAM/Wave/Homological/Divisors.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:divisors; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: stepW:w4:divlip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L386-L390
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L386-L390
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
DEPS: stepW:w4:member, bpW:w4:melnikov
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:member | blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L389-L389 | the lower bound alpha w/A_k
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#stepW:w4:divlip@L388-L388 | direct use of the frequency Lipschitz hypothesis (freq)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homDivGen_bounds (KAM/Wave/Homological/Divisors.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:divisors; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: bpW:w4:schur
KIND: lemma
TITLE: Hadamard division of operators
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L398-L413
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L415-L438
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
DEPS: bpW:w4:ops, stepW:w4:schurtr, stepW:w4:schurrep, stepW:w4:schurdiag, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:ops | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L405-L405 | L, B, Lambda
EDGE: stepW:w4:schurtr | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L416-L416 | proof step
EDGE: stepW:w4:schurrep | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L419-L419 | proof step
EDGE: stepW:w4:schurdiag | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L436-L436 | proof step
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#bpW:w4:schur@L404-L404 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homKS, KAM.Wave.homHadamardOp, KAM.Wave.homHadamardCLM, KAM.Wave.norm_homHadamardCLM_le, KAM.Wave.homNormalEntry_hadamard_gen, KAM.Wave.homHadamard_transpose_entry, KAM.Wave.homSolve_entry_symm_gen, KAM.Wave.homHadamardOp_lam, KAM.Wave.norm_homLam_hadamard_le, KAM.Wave.norm_homHadamardOp_diag_le, KAM.Wave.homDiagonal_bound (KAM/Wave/Homological/Schur.lean, KAM/Wave/Homological/LemmaOneF.lean, KAM/Wave/Homological/PPlusOne.lean)
LEAN_NOTE: W4-HOMOLOGICAL audit 1 PASS ((i), (iii)), PASS WITH NOTES (transpose: the source transpose is through homNormalEntry, not the raw representative transpose; (ii) in the weighted-matrix model, where Hadamard division on HomOp commutes with Lambda and no Riesz transfer is needed)
NOTE: -

NODE: stepW:w4:schurtr
KIND: step
TITLE: Transport
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurtr@L416-L418
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurtr@L416-L418
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
EDGE: bpW:w1:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:schurtr@L417-L417 | (iii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homHadamardCLM, KAM.Wave.norm_homHadamardCLM_le (KAM/Wave/Homological/Schur.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:schur; W4-HOMOLOGICAL audit 1 PASS (W1 Schur test applied to the weighted matrices)
NOTE: -

NODE: stepW:w4:schurrep
KIND: step
TITLE: Representatives
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L419-L435
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L419-L435
CONTRACT_ID: stepW:w4:schurrep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:schur: Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2)); K_S = 1 + pi/sqrt3; d_ij with ¦d_ij¦ <= c/¦i-j¦ (i != j), ¦d_ii¦ <= c; positive mu, nu; A with weighted matrix (mu_i A_ij nu_j) bounded on l^2 with norm N_A
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:schur (for all such d, c, mu, nu, A); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the weighted matrix of M in L is that of its representative tau o M o kappa, so bounded weighted matrices are exactly elements of L with the same norm (transpose entrywise); in the bilinear case, hat beta(x,y) = beta(kappa x, kappa y) has the same norm, T = C o B^sharp o C (C coordinatewise conjugation, B(v,w) = hat beta(Cv,w)) is a bounded operator on l^2_C with <Tx,y>_0 = hat beta(x,y), ¦¦T¦¦ = ¦¦beta¦¦_bil and matrix mu_j mu_i beta(e_j,e_i); conversely every bounded T gives a bounded form of norm <= ¦¦T¦¦; so Lemma bpW:w1:schur(iii) transfers
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:transport, bpW:w0:ellap#ellWeight, bpW:w4:ops, bpW:w4:ext-riesz, bpW:w1:ext-lp, bpW:w1:schur, bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:transport | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L421-L421 | the representative tau o M o kappa
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L421-L421 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
EDGE: bpW:w4:ops | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L420-L435 | the spaces L and B, their matrix entries and Lambda are the objects being represented
EDGE: bpW:w4:ext-riesz | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L428-L430 | B^sharp and the norm formula
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L427-L427 | l^2_C, <Cu,w> = <u,w>_0
EDGE: bpW:w1:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L435-L435 | (iii) transfers
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L434-L434 | (bpW:w4:pairing)-type Cauchy-Schwarz
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta6-W-W-w4+claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homNormalEntry, KAM.Wave.homLamCLM, KAM.Wave.norm_le_of_pairing_le (KAM/Wave/Homological/PPlusOne.lean, KAM/Wave/Homological/NormalOps.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:schur; W4-HOMOLOGICAL audit 1 PASS WITH NOTES; not separately formalized; Lean route differs: the representative model works with operators throughout and the Riesz construction T = C o B^sharp o C is not formalized (audit 1: sound for the actual consumers)
NOTE: -

NODE: stepW:w4:schurdiag
KIND: step
TITLE: Diagonal
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurdiag@L436-L437
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:schurdiag@L436-L437
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
EDGE: bpW:w1:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:schurdiag@L437-L437 | (ii)
EDGE: bpW:w1:multiplier | blueprint-W/parts/w4-homological.tex#stepW:w4:schurdiag@L437-L437 | diagonal multipliers
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.norm_homHadamardOp_diag_le, KAM.Wave.homDiagonal_bound (KAM/Wave/Homological/Schur.lean, KAM/Wave/Homological/PPlusOne.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:schur; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: bpW:w4:solve
KIND: lemma
TITLE: Multiplier solve
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L443-L461
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L463-L483
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
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L453-L453 | B^W_sigma
EDGE: stepW:w4:solvecoef | blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L464-L464 | proof step
EDGE: stepW:w4:solvediff | blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L468-L468 | proof step
EDGE: stepW:w4:solvecomm | blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L474-L474 | proof step
EDGE: stepW:w4:solvelin | blueprint-W/parts/w4-homological.tex#bpW:w4:solve@L480-L480 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homSolve_spec, KAM.Wave.isHomComp_solve, KAM.Wave.homSolve_sub_le, KAM.Wave.homSolve_partial, KAM.Wave.homSolve_intertwine, KAM.Wave.homSolve_clm (KAM/Wave/Homological/Solve.lean, KAM/Wave/Homological/LemmaOneF.lean, KAM/Wave/Homological/SolveDeriv.lean, KAM/Wave/Homological/SolveLinear.lean)
LEAN_NOTE: W4-HOMOLOGICAL audit 1 PASS ON SOURCE DOMAIN ((i)), PASS ((ii)), PASS WITH NOTES ((iii), (iv): low-level commutation helpers take the produced summability evidence)
NOTE: -

NODE: stepW:w4:solvecoef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L464-L467
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L464-L467
CONTRACT_ID: stepW:w4:solvecoef
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:solve: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:solve (for all such data); within the step: k
SOURCE_CONCLUSION: (i): sum ¦¦T_k hat f_k¦¦ e^{2 pi ¦k¦_1 (s-sigma)} <= kappa m B^W_sigma/alpha and (F2) with s' = s - sigma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:w1-requests, bpW:w4:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L465-L465 | (F1), (F2)
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecoef@L467-L467 | (iv)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homSolve_spec (KAM/Wave/Homological/Solve.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:solve; W4-HOMOLOGICAL audit 1 PASS ON SOURCE DOMAIN
NOTE: -

NODE: stepW:w4:solvediff
KIND: step
TITLE: Differences
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L468-L473
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L468-L473
CONTRACT_ID: stepW:w4:solvediff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:solve: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:solve (for all such data); within the step: xi, zeta
SOURCE_CONCLUSION: (ii): the coefficient differences are bounded and summed
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:fourier-ops, bpW:w4:w1-requests, bpW:w4:lattice
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L470-L470 | (iii)
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L470-L470 | (F1), (F2)
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#stepW:w4:solvediff@L472-L472 | B^W_sigma
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homSolve_sub_le (KAM/Wave/Homological/Solve.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:solve; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: stepW:w4:solvecomm
KIND: step
TITLE: Commutation
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L474-L479
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L474-L479
CONTRACT_ID: stepW:w4:solvecomm
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:solve: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}; for part (iii), partial_{theta_i} f is bounded on T_s (L455)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:solve (for all such data); within the step: i
SOURCE_CONCLUSION: (iii): termwise differentiation gives d_{theta_i} S f = S(d_{theta_i} f)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:fourier-ops, stepW:w4:solvecoef, bpW:w1:ext-unifderiv
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L475-L475 | (ii)
EDGE: stepW:w4:solvecoef | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L476-L476 | summability
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w4-homological.tex#stepW:w4:solvecomm@L478-L478 | termwise differentiation
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homSolve_partial (KAM/Wave/Homological/SolveDeriv.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:solve; W4-HOMOLOGICAL audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w4:solvelin
KIND: step
TITLE: Linear images
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L480-L482
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L480-L482
CONTRACT_ID: stepW:w4:solvelin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w4:solve: E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ¦¦T_k(xi)¦¦ <= kappa A_k/alpha and ¦¦T_k(xi) - T_k(zeta)¦¦ <= 2 kappa (1+¦k¦_1) A_k^2 M ¦xi - zeta¦/alpha^2; f(.,xi) : T_s -> E complex differentiable, 1-periodic, ¦¦f¦¦ <= m, ¦¦f(theta,xi) - f(theta,zeta)¦¦ <= m^L ¦xi - zeta¦; S f = sum T_k hat f_k e^{2 pi i <k,theta>}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w4:solve (for all such data)
SOURCE_CONCLUSION: (iv): Lambda commutes with absolutely convergent sums
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:fourier-ops, bpW:w3:ext-tsum
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L482-L482 | (i)
EDGE: bpW:w3:ext-tsum | blueprint-W/parts/w4-homological.tex#stepW:w4:solvelin@L481-L481 | continuous linear maps commute with norm-absolutely convergent sums
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homSolve_intertwine, KAM.Wave.homSolve_clm (KAM/Wave/Homological/SolveLinear.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:solve; W4-HOMOLOGICAL audit 1 PASS WITH NOTES
NOTE: -

NODE: bpW:w4:lie
KIND: lemma
TITLE: Lie derivative and weak bracket
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L502-L530
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L532-L559
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
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L503-L503 | the class T_{s'}, components and gradients
EDGE: bpW:w4:lie-sec#guard | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L522-L522 | the guard (G) and N
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L503-L503 | (bpW:w4:freq) and the divisors
EDGE: stepW:w4:liebd | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L533-L533 | proof step
EDGE: stepW:w4:liebr | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L538-L538 | proof step
EDGE: stepW:w4:liecoef | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L542-L542 | proof step
EDGE: stepW:w4:lieder | blueprint-W/parts/w4-homological.tex#bpW:w4:lie@L550-L550 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.homOmega_le, KAM.Wave.homLie_Omega_mem, KAM.Wave.homLie_pairing_summable, KAM.Wave.homPair0, KAM.Wave.homPair0_hasSum, KAM.Wave.homLieSeq, KAM.Wave.homWeakBracket, KAM.Wave.homWeakBracket_eq_neg_lieN, KAM.Wave.HomOmegaCarrier, KAM.Wave.homLieN_gen, KAM.Wave.homLieN_gen_eq, KAM.Wave.homOmegaCarrier_of_guard, KAM.Wave.HomGuard, KAM.Wave.homNOmegaCLM, KAM.Wave.homNOmega_le_gen, KAM.Wave.homNfun, KAM.Wave.homDN, KAM.Wave.homNfun_hasFDerivAt, KAM.Wave.homLemma_lie_iv_gen, KAM.Wave.homLemma_lie_iv, KAM.Wave.homEq_a, KAM.Wave.homEq_b, KAM.Wave.homEq_Q (KAM/Wave/Homological/Lie.lean, KAM/Wave/Homological/PPlusOne.lean, KAM/Wave/Homological/LemmaOneFin.lean, KAM/Wave/Homological/LemmaOneEquation.lean, KAM/Wave/Homological/LieDeriv.lean, KAM/Wave/Homological/LemmaOneEqFam.lean)
LEAN_NOTE: W4-HOMOLOGICAL audit 1 FAIL (F1: unrestricted pairing carriers), audit 2 PASS WITH NOTES (F1 closed: evidence-bearing homPair0, homLieSeq, homWeakBracket, homLieN_gen); (i), (ii), (iv) proved; missing: (iii) the coefficient rule for general F is not exported, only for the solved F on finitely supported vectors (homEq_a ... homEq_Q, gate-taking HomMultBounds, internal raw L_N; audit 2: conditional); continuity of L_N F in (z, zbar) only inside homLemma1_equation_all; homLemma_lie_iv (p_+ = p+1) displays the raw L_N formula
NOTE: -

NODE: stepW:w4:liebd
KIND: step
TITLE: Bounds
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liebd@L533-L537
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liebd@L533-L537
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
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#stepW:w4:liebd@L535-L535 | (bpW:w4:pairing)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homOmega_le, KAM.Wave.homLie_Omega_mem, KAM.Wave.homLie_pairing_summable (KAM/Wave/Homological/Lie.lean, KAM/Wave/Homological/PPlusOne.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w4:lie; W4-HOMOLOGICAL audit 1 PASS ON SOURCE DOMAIN; continuity in (z, zbar) through the continuous_homPairRep_*_gen helpers (LemmaOneAll)
NOTE: -

NODE: stepW:w4:liebr
KIND: step
TITLE: Weak bracket
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liebr@L538-L541
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liebr@L538-L541
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
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homWeakBracket, KAM.Wave.homLieSeq, KAM.Wave.homWeakBracket_eq_neg_lieN (KAM/Wave/Homological/Lie.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w4:lie; W4-HOMOLOGICAL audit 2 PASS (F1 closed, exact summability hypotheses)
NOTE: -

NODE: stepW:w4:liecoef
KIND: step
TITLE: Coefficients
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liecoef@L542-L549
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:liecoef@L542-L549
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
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#stepW:w4:liecoef@L544-L544 | F_z, F_zbar
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w4-homological.tex#stepW:w4:liecoef@L548-L548 | (i), (ii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.homEq_a, KAM.Wave.homEq_b, KAM.Wave.homEq_cp_gen, KAM.Wave.homEq_cm_gen, KAM.Wave.homEq_P_gen, KAM.Wave.homEq_P'_gen, KAM.Wave.homEq_Q_gen, KAM.Wave.homCohEq_scalar (KAM/Wave/Homological/LemmaOneEqFam.lean, KAM/Wave/Homological/CohEq.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w4:lie; W4-HOMOLOGICAL audit 1 CONDITIONAL (F2), audit 2: gate-taking internal steps remain conditional; the coefficient identities are proved only for the solved F = S(R) under HomMultBounds on finitely supported vectors, not as the general coefficient collection
NOTE: -

NODE: stepW:w4:lieder
KIND: step
TITLE: The guarded derivative
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L550-L558
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L550-L558
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
DEPS: bpW:w4:lie-sec#guard, bpW:w1:embed, bpW:w4:index, stepW:w4:liebr, bpW:w3:ext-multilinear, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lie-sec#guard | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L551-L551 | (G)
EDGE: bpW:w1:embed | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L555-L555 | l^N_{a,bar p} subset l^N_{a,p}
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L554-L554 | (bpW:w4:hameq): the components of X_F
EDGE: stepW:w4:liebr | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L558-L558 | (ii)
EDGE: bpW:w3:ext-multilinear | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L553-L553 | differentiate the bounded bilinear polynomial and its linear part
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#stepW:w4:lieder@L551-L551 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homNOmegaCLM, KAM.Wave.homNOmega_le_gen, KAM.Wave.homNfun, KAM.Wave.homDN, KAM.Wave.homNfun_hasFDerivAt, KAM.Wave.homOmegaCarrier_of_guard, KAM.Wave.homLemma_lie_iv_gen (KAM/Wave/Homological/LieDeriv.lean, KAM/Wave/Homological/Lie.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w4:lie; W4-HOMOLOGICAL audit 1 PASS WITH NOTES, audit 2 PASS WITH NOTE (homLemma_lie_iv_gen stated with the evidence-bearing homLieN_gen)
NOTE: -

NODE: bpW:w4:extract
KIND: lemma
TITLE: Coefficient extraction
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:extract@L569-L573
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:extract@L575-L581
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
EDGE: bpW:w4:ext-roots | blueprint-W/parts/w4-homological.tex#bpW:w4:extract@L579-L579 | averages over fourth roots of unity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.polyEval2, KAM.Wave.polyExtract, KAM.Wave.polyExtract_one (KAM/Wave/Homological/Extract.lean)
LEAN_NOTE: W4-HOMOLOGICAL audit 1 PASS (roots-of-unity extraction, including the mixed coefficient)
NOTE: -

NODE: bpW:w4:components
KIND: lemma
TITLE: Component bounds
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:components@L585-L595
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:components@L597-L623
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
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L586-L586 | T_s and ¦X_R¦_r
EDGE: bpW:w4:ops | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L590-L590 | norms on L, B, l^N_*
EDGE: stepW:w4:testpts | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L598-L598 | proof step
EDGE: stepW:w4:first | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L604-L604 | proof step
EDGE: stepW:w4:angle | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L609-L609 | proof step
EDGE: stepW:w4:polar | blueprint-W/parts/w4-homological.tex#bpW:w4:components@L618-L618 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homComp_first, KAM.Wave.homComp_angle, KAM.Wave.homComp_first_gen, KAM.Wave.homComp_angle_gen, KAM.Wave.homPairL2, KAM.Wave.norm_le_of_quadratic (KAM/Wave/Homological/PPlusOne.lean, KAM/Wave/Homological/ComponentsFirst.lean, KAM/Wave/Homological/ComponentsAngleQ.lean, KAM/Wave/Homological/NormalPol.lean)
LEAN_NOTE: W4-HOMOLOGICAL audit 1 PASS (angle derivatives controlled in dual and bilinear norms through Lambda, not the operator norm of d_theta P)
NOTE: -

NODE: stepW:w4:testpts
KIND: step
TITLE: Test points
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:testpts@L598-L603
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:testpts@L598-L603
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
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#stepW:w4:testpts@L599-L599 | (bpW:w4:zu)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homNorm_le_uv, KAM.Wave.homComp_first (KAM/Wave/Homological/Taylor.lean, KAM/Wave/Homological/PPlusOne.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:components; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: stepW:w4:first
KIND: step
TITLE: Zeroth and first order
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:first@L604-L608
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:first@L604-L608
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
EDGE: stepW:w4:testpts | blueprint-W/parts/w4-homological.tex#stepW:w4:first@L606-L606 | bounds at the test points
EDGE: bpW:w4:extract | blueprint-W/parts/w4-homological.tex#stepW:w4:first@L607-L607 | coefficient extraction
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homComp_first, KAM.Wave.polyExtract (KAM/Wave/Homological/PPlusOne.lean, KAM/Wave/Homological/Extract.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:components; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: stepW:w4:angle
KIND: step
TITLE: Angle derivatives
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:angle@L609-L617
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:angle@L609-L617
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
EDGE: stepW:w4:testpts | blueprint-W/parts/w4-homological.tex#stepW:w4:angle@L611-L611 | bounds at the test points
EDGE: bpW:w4:extract | blueprint-W/parts/w4-homological.tex#stepW:w4:angle@L611-L611 | coefficient extraction
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homComp_angle, KAM.Wave.polyExtract (KAM/Wave/Homological/PPlusOne.lean, KAM/Wave/Homological/Extract.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:components; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: stepW:w4:polar
KIND: step
TITLE: Polarization
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:polar@L618-L622
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:polar@L618-L622
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
EDGE: stepW:w4:angle | blueprint-W/parts/w4-homological.tex#stepW:w4:polar@L621-L621 | the diagonal bound
EDGE: bpW:w4:ext-parallelogram | blueprint-W/parts/w4-homological.tex#stepW:w4:polar@L622-L622 | parallelogram law
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homPairL2, KAM.Wave.norm_le_of_quadratic (KAM/Wave/Homological/NormalPol.lean)
LEAN_NOTE: step of PROVED parent bpW:w4:components; W4-HOMOLOGICAL audit 1 PASS
NOTE: -

NODE: bpW:w4:lemma1
KIND: theorem
TITLE: P96-K Lemma~1 for the wave setting
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L630-L655
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L657-L730
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
DEPS: bpW:w4:taylor, bpW:w4:melnikov, bpW:w4:lie, bpW:w4:lie-sec#guard, bpW:w4:lattice, bpW:w4:schur, stepW:w4:divops, stepW:w4:class, stepW:w4:equation, stepW:w4:Fcomp, stepW:w4:assembly, stepW:w4:lip, stepW:w4:Nhat, stepW:w4:real, bpW:w4:index
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L633-L633 | the class T_s
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L636-L636 | divisors and (H_alpha)
EDGE: bpW:w4:lie | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L646-L646 | L_N and the weak bracket
EDGE: bpW:w4:lie-sec#guard | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L648-L648 | the guard (G)
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L642-L642 | B^W_sigma
EDGE: bpW:w4:schur | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L642-L642 | K_S
EDGE: stepW:w4:divops | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L658-L658 | proof step
EDGE: stepW:w4:class | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L667-L667 | proof step
EDGE: stepW:w4:equation | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L672-L672 | proof step
EDGE: stepW:w4:Fcomp | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L682-L682 | proof step
EDGE: stepW:w4:assembly | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L696-L696 | proof step
EDGE: stepW:w4:lip | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L709-L709 | proof step
EDGE: stepW:w4:Nhat | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L715-L715 | proof step
EDGE: stepW:w4:real | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L722-L722 | proof step
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma1@L631-L631 | the theorem explicitly assumes this convention
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.homMultBounds_of, KAM.Wave.homSolveTaylor, KAM.Wave.homLemma1_zero_modes, KAM.Wave.homSolveTaylor_isReal, KAM.Wave.homNhatTaylor_isReal, KAM.Wave.homLemma1_equation_all, KAM.Wave.homLemma1_fieldBound, KAM.Wave.homLemma1_lipschitz, KAM.Wave.homNhat, KAM.Wave.homNhatTaylor, KAM.Wave.homNhatTaylor_val, KAM.Wave.homNhat_coeff_bounds, KAM.Wave.homNhat_fieldBound, KAM.Wave.homNhat_lipschitz (KAM/Wave/Homological/LemmaOneF.lean, KAM/Wave/Homological/PPlusOne.lean)
LEAN_NOTE: W4-HOMOLOGICAL audit 1 FAIL (F2: headline exports took intermediate gates), audit 2 PASS WITH NOTES (F2 closed for homLemma1_fieldBound, homLemma1_lipschitz, homLemma1_equation_all and their _gen forms, now from the source premises HomFreqHyp, HomMelnikov); proved from source premises: (ii) first form for all (y, z, zbar), (iii), (iv); missing: (i) zero modes and reality of F exported only as gate-taking helpers (homLemma1_zero_modes, homSolveTaylor_isReal take HomMultBounds; the supplier homMultBounds_of is not composed into an export); (ii) the bracket form R + <<N,F>> = hat N + hat a_0 and the guarded form R + DN.X_F = hat N + hat a_0 are not exported (they follow by composing with homWeakBracket_eq_neg_lieN and homLemma_lie_iv)
NOTE: -

NODE: stepW:w4:divops
KIND: step
TITLE: Division operators
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L658-L666
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L658-L666
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
DEPS: bpW:w4:divisors, bpW:w4:schur, bpW:w1:multiplier
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:divisors | blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L662-L662 | divisor bounds
EDGE: bpW:w4:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L664-L664 | Hadamard maps
EDGE: bpW:w1:multiplier | blueprint-W/parts/w4-homological.tex#stepW:w4:divops@L665-L665 | diagonal multipliers
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.HomMultBounds, KAM.Wave.homMultBounds_of, KAM.Wave.HomMultLip, KAM.Wave.homMultLip_of (KAM/Wave/Homological/LemmaOneF.lean, KAM/Wave/Homological/LemmaOneLip.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w4:lemma1; W4-HOMOLOGICAL audit 1 (F2 section: checked gate suppliers), audit 2 PASS WITH NOTES (gates discharged from source premises)
NOTE: -

NODE: stepW:w4:class
KIND: step
TITLE: The solution is in the class
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:class@L667-L671
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:class@L667-L671
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
EDGE: bpW:w4:solve | blueprint-W/parts/w4-homological.tex#stepW:w4:class@L668-L668 | (i)
EDGE: bpW:w4:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:class@L669-L669 | (i) transpose identity
EDGE: stepW:w4:divops | blueprint-W/parts/w4-homological.tex#stepW:w4:class@L668-L668 | the division operators
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.homSolveTaylor, KAM.Wave.isHomComp_solve, KAM.Wave.homSolve_entry_symm_gen, KAM.Wave.homLemma1_zero_modes (KAM/Wave/Homological/PPlusOne.lean, KAM/Wave/Homological/LemmaOneF.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w4:lemma1; W4-HOMOLOGICAL audit 1 CONDITIONAL / BRIDGED; F in T_{s-sigma} is the type of homSolveTaylor (gate HomMultBounds an argument); the vanishing coefficients are exported only gate-taking
NOTE: -

NODE: stepW:w4:equation
KIND: step
TITLE: The equation
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L672-L681
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L672-L681
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
EDGE: bpW:w4:solve | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L675-L675 | (iii)
EDGE: bpW:w4:components | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L675-L675 | (ii)
EDGE: bpW:w4:lie | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L675-L675 | (i)-(iv)
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L678-L678 | (F3)
EDGE: bpW:w1:space | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L680-L680 | (iii) density of finitely supported sequences
EDGE: stepW:w4:class | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L676-L676 | the components of F
EDGE: stepW:w4:Nhat | blueprint-W/parts/w4-homological.tex#stepW:w4:equation@L679-L679 | hat N continuous
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.homLemma1_equation, KAM.Wave.homLemma1_equation_all (KAM/Wave/Homological/PPlusOne.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w4:lemma1; first form for all vectors from source premises (audit 2 PASS; finitely supported case and extension by continuity and truncation); second and third forms not exported
NOTE: -

NODE: stepW:w4:Fcomp
KIND: step
TITLE: Component bounds of $F$
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L682-L695
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L682-L695
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
EDGE: bpW:w4:components | blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L683-L683 | the component bounds of R
EDGE: stepW:w4:divops | blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L683-L683 | kappa
EDGE: bpW:w4:solve | blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L683-L683 | (i), (iii), (iv)
EDGE: bpW:w4:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L691-L691 | (ii) Hadamard maps on B
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#stepW:w4:Fcomp@L694-L694 | (bpW:w4:pairing): ¦¦c¦¦_* <= ¦¦c¦¦_{bar p}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homF_compBounds, KAM.Wave.homMultBounds_of, KAM.Wave.homLemma1_fieldBound (KAM/Wave/Homological/PPlusOne.lean, KAM/Wave/Homological/LemmaOneF.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w4:lemma1; gate-taking helper homF_compBounds, gate discharged by homMultBounds_of inside the source-premise export homLemma1_fieldBound (audit 2 PASS)
NOTE: -

NODE: stepW:w4:assembly
KIND: step
TITLE: Assembly
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:assembly@L696-L708
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:assembly@L696-L708
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
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#stepW:w4:assembly@L697-L697 | (bpW:w4:zu)
EDGE: stepW:w4:Fcomp | blueprint-W/parts/w4-homological.tex#stepW:w4:assembly@L698-L698 | the component bounds
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homXnorm_le_of_components, KAM.Wave.homKS_lt_29, KAM.Wave.homLemma1_fieldBound (KAM/Wave/Homological/PPlusOne.lean, KAM/Wave/Homological/Lemma1.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w4:lemma1; audit 2 PASS (homLemma1_fieldBound); C_1 = 7 + 10 K_S
NOTE: -

NODE: stepW:w4:lip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L709-L714
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L709-L714
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
EDGE: bpW:w4:components | blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L711-L711 | applied to R(xi) - R(zeta)
EDGE: bpW:w4:solve | blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L712-L712 | (ii)
EDGE: stepW:w4:assembly | blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L713-L713 | linear assembly
EDGE: stepW:w4:Fcomp | blueprint-W/parts/w4-homological.tex#stepW:w4:lip@L711-L711 | the inputs
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homF_sub_compBounds, KAM.Wave.homMultLip_of, KAM.Wave.homLemma1_lipschitz (KAM/Wave/Homological/PPlusOne.lean, KAM/Wave/Homological/LemmaOneLip.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w4:lemma1; audit 2 PASS (homLemma1_lipschitz, difference Taylor Hamiltonian)
NOTE: -

NODE: stepW:w4:Nhat
KIND: step
TITLE: The normal form correction
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:Nhat@L715-L721
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:Nhat@L715-L721
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
EDGE: bpW:w4:components | blueprint-W/parts/w4-homological.tex#stepW:w4:Nhat@L716-L716 | ¦b¦ <= 2 pi eps, ¦¦Q¦¦ <= eps
EDGE: bpW:w4:schur | blueprint-W/parts/w4-homological.tex#stepW:w4:Nhat@L717-L717 | (iii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.homNhatTaylor_val, KAM.Wave.homNhat_coeff_bounds, KAM.Wave.homNhat_fieldBound, KAM.Wave.homNhat_lipschitz (KAM/Wave/Homological/PPlusOne.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w4:lemma1; W4-HOMOLOGICAL audit 1 PASS ON SOURCE DOMAIN (no gate)
NOTE: -

NODE: stepW:w4:real
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:real@L722-L729
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#stepW:w4:real@L722-L729
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
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#stepW:w4:real@L723-L723 | reality of R
EDGE: stepW:w4:class | blueprint-W/parts/w4-homological.tex#stepW:w4:real@L727-L727 | the coefficients of F
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.homSolveTaylor_isReal, KAM.Wave.homNhatTaylor_isReal (KAM/Wave/Homological/PPlusOne.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w4:lemma1; reality of hat N unconditional; reality of F only gate-taking (HomMultBounds), W4-HOMOLOGICAL audit 1 CONDITIONAL / BRIDGED
NOTE: -

NODE: bpW:w4:lemma2
KIND: corollary
TITLE: P96-K Lemma~2
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lemma2@L743-L751
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lemma2@L753-L757
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
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma2@L755-L755 | (iii), (iv)
EDGE: bpW:w4:lattice | blueprint-W/parts/w4-homological.tex#bpW:w4:lemma2@L756-L756 | (iv)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w4
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.homLamNorm, KAM.Wave.homLemma2, KAM.Wave.homKS_lt_29, KAM.Wave.waveBW_le (KAM/Wave/Homological/Lemma1.lean, KAM/Wave/Homological/LatticeBW.lean)
LEAN_NOTE: W4-HOMOLOGICAL audit 1 PASS WITH NOTES (arithmetic assembly of explicit bounds, not a theorem supplying the field estimates); proved: the inequalities between the explicit bounds (homLamNorm lam eps epsL = eps + lam epsL), 3 C_1 < 108 and (4) B^W_sigma <= b_W(tau) sigma^{-(2tau+3)}; missing: the lambda-weighted field norms |X|^lambda_{r,D} have no Lean definition, so the inequalities for X_hat N and X_F are not exported (they follow by combining with homNhat_fieldBound, homNhat_lipschitz, homLemma1_fieldBound, homLemma1_lipschitz)
NOTE: lambda here is the P96-K weighting parameter, not the frequency lambda_j (no lam edge).

NODE: bpW:w4:from-w3
KIND: claim
TITLE: From W3
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L796-L815
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L796-L815
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
DEPS: bpW:w3:main, bpW:w3:space, bpW:w3:coords, bpW:w4:index, bpW:w3:omega, bpW:w3:hamfield-def, bpW:w4:taylor, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L797-L797 | the Birkhoff map
EDGE: bpW:w3:space | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L798-L798 | the coordinates w_l
EDGE: bpW:w3:coords | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L799-L799 | u_j = q_{j+2}, v_j = p_{j+2}
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L801-L801 | the wave weights
EDGE: bpW:w3:omega | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L804-L804 | the symplectic form
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L805-L805 | X_P
EDGE: bpW:w4:taylor | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L804-L804 | the smoothing gradients required by the Taylor class
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L800-L801 | the frozen wave weights occur directly in the asserted equality of normal norms
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta6-W-W-w4
REVIEWER: sol-delta7-W-w4
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Remark kept as a node: its identifications are consumed by W5 (action-angle substitution); the ownership ruling and the pointer to Remark bpW:w3:interface are administrative.

NODE: bpW:w4:lie-sec#guard
KIND: definition
TITLE: The guard (G) and the weak-bracket setting
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L491-L500
PROOF_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L491-L500
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
DEPS: bpW:w4:index, bpW:w4:melnikov, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:index | blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L496-L496 | the wave weights omega_{a,p}(j+2)
EDGE: bpW:w4:melnikov | blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L491-L491 | omega, Omega
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w4-homological.tex#bpW:w4:lie-sec@L497-L497 | the wave weight omega_{a,q}(J) is the frozen ellWeight at these parameters
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w4
REVIEWER: sol-delta6-W-W-w4
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.HomGuard, KAM.Wave.homGuard_of_cond, KAM.Wave.not_homGuard_of_lt, KAM.Wave.homGuard_one_one, KAM.Wave.homNfun (KAM/Wave/Homological/Lie.lean, KAM/Wave/Homological/LieDeriv.lean)
LEAN_NOTE: definition formalized by W4-HOMOLOGICAL; W4-HOMOLOGICAL audit 1 PASS WITH NOTES (lie (iv), guard); (G) iff a > 0 or p >= 1/2 (a, p >= 0) by homGuard_of_cond and not_homGuard_of_lt, gamma_{1,1} = e^{-6}/3 by homGuard_one_one; the remark that the series of N need not converge for a = p = 0 is not formalized
NOTE: Unlabelled prose L491-L500 with the display label bpW:w4:guard (SPEC section-data rule); consumed by Lemma bpW:w4:lie(iv) and Theorem bpW:w4:lemma1(ii).

NODE: bpW:w4:ext-riesz
KIND: external
TITLE: Riesz representation of bounded sesquilinear forms
STATEMENT_SOURCE: blueprint-W/parts/w4-homological.tex#bpW:w4:ext-riesz@L53-L62
PROOF_SOURCE: -
CONTRACT_ID: bpW:w4:ext-riesz
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: for a complex Hilbert space E and a bounded form B : E -> E -> C, conjugate-linear in the first and linear in the second argument, B^sharp = InnerProductSpace.continuousLinearMapOfBilin B is a continuous linear map with <B^sharp v, w> = B(v,w); and ¦¦u¦¦ = sup_{¦¦w¦¦ <= 1} ¦<u,w>¦ (toDual is a conjugate-linear isometry)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w4
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
