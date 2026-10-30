NODE: bpW:wh:embedding#IsAnalyticTorusEmbedding
KIND: definition
TITLE: Analytic torus embedding: KAM.Wave.IsAnalyticTorusEmbedding
STATEMENT_SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:embedding@L28-L33
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
STATEMENT_SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:dioph@L39-L43
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
STATEMENT_SOURCE: blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L47-L71
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L552-L599
CONTRACT_ID: wave.nlw2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0 (frozen hm : 0 < m); the data fixed at L19-L22: weights a = p = 1, E = E_{1,1} with the max norm, U_m, V_m, G_q, P = (0,infinity)^2, r(I) = sqrt(I_1+I_2), B_h = {I : max_i ¦I_i¦ < h}
SOURCE_QUANTIFIERS: for every m > 0, there exist r_0 > 0, C > 0, tau > 1, eta : (0,r_0) -> [0,infinity) with eta(r) -> 0 as r -> 0+, a Borel set Gamma subset {I in P : r(I) < r_0}, a continuous nu : Gamma -> R^2 and maps K_I = (Q_I,P_I) : R^2 -> E (I in Gamma) with (I,theta) -> K_I(theta) continuous on Gamma x R^2; then (1)-(6) hold with inner quantifiers: (2) for every I in Gamma there is gamma_I > 0; (3)-(5) for every I in Gamma, theta (resp. theta_0, t, x) and j >= 1; (6) for all I, I' in Gamma and theta, theta'
SOURCE_CONCLUSION: (1) Leb_2(Gamma cap B_h)/Leb_2(P cap B_h) -> 1 as h -> 0+; (2) nu(I) is (gamma_I,tau)-Diophantine and nu(I) -> (lambda_1,lambda_2)/(2 pi) as I -> 0 in Gamma; (3) each K_I is an analytic torus embedding, sup_theta ¦¦K_I(theta) - K^0_I(theta)¦¦_E <= eta(r(I)) r(I) and sup_theta ¦¦K_I(theta)¦¦_E <= C r(I); (4) D_{nu(I)} Q_{I,j} = lambda_j P_{I,j} and D_{nu(I)} P_{I,j} = -lambda_j Q_{I,j} - G_q(Q_I)_j for all theta, j >= 1 (frozen: HasDerivAt of t -> coeff (K I (theta + t nu I)).i j at t = 0); (5) for every theta_0, u(t,x) = U_m(Q_I(theta_0 + t nu(I)))(x) is real analytic near every point of R x [0,pi], is a classical solution of u_tt = u_xx - m u - u^3 on R, u_t(t,.) = V_m(P_I(theta_0 + t nu(I))), and sup_{t, x in [0,pi]} (¦u¦ + ¦u_x¦ + ¦u_t¦) <= C r(I) (frozen: u_x as derivWithin on [0,pi]); (6) K_I(theta) = K_I'(theta') implies I = I' and theta - theta' in Z^2
CONSTANT_SCOPE: r_0, C, tau, eta, Gamma, nu, K are chosen after m and before I, theta, theta_0; they may depend on m; gamma_I is chosen per I (it may degenerate as I -> 0); C is common to (3) and (5); no uniformity in m
FROZEN_FILE: KAM/Frozen/Wave/Theorems/Nlw2.lean
FROZEN_DECL: KAM.Wave.nlw2
FROZEN_ANCHOR_ID: wave.nlw2.v1
FROZEN_ABI_SHA256: eca3aee797e9040ce3fde0e946ce30e10fe8550faa413b6a83fc9abda495ddb7
DEPS: bpW:w0:mass, bpW:w0:ellap#WaveSpace, bpW:wh:dioph#IsDiophantine, bpW:w0:basis#lam, bpW:wh:embedding#IsAnalyticTorusEmbedding, bpW:w0:periodone#linearTorus, bpW:w0:ellap#coeff, bpW:w0:Gq#cubicGrad, bpW:w0:reconstruction#reconU, bpW:w0:nlw#IsClassicalSolution, bpW:w0:reconstruction#reconV, bpW:w8:nlw2-proof
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:mass | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L48-L48 | for every m > 0 (hm)
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L50-L50 | K_I : R^2 -> E, E = E_{1,1} (frozen WaveSpace)
EDGE: bpW:wh:dioph#IsDiophantine | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L56-L56 | (2) nu(I) is (gamma_I,tau)-Diophantine
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L56-L56 | (2) limit (lambda_1,lambda_2)/(2 pi); (4) lambda_j
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L57-L57 | (3) each K_I is an analytic torus embedding
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L58-L58 | (3) closeness to K^0_I
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L60-L60 | (4) the coefficients Q_{I,j}, P_{I,j} (frozen coeff)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L61-L61 | (4) the cubic gradient G_q(Q_I(theta))_j
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L63-L63 | (5) u = U_m(Q_I(theta_0 + t nu(I)))
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L64-L64 | (5) classical solution of (bpW:w0:eq) on R
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w-headline.tex#bpW:wh:nlw2@L65-L65 | (5) u_t = V_m(P_I(theta_0 + t nu(I)))
EDGE: bpW:w8:nlw2-proof | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L548-L550 | Theorem bpW:w8:nlw2-proof states that Theorem bpW:wh:nlw2 holds exactly as frozen; its proof (L552-L599) is the proof of the root
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+claude-suborch-W-w2
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Root of track W. PROOF_SOURCE is the proof environment of Theorem bpW:w8:nlw2-proof (W8 assembly, wave 2), which proves the frozen statement conjunct by conjunct; the root depends on it through one edge, and on the statement-level definitions through the symbol edges. W2 (bpW:w2:clause5) enters through Step stepW:w8:p-pde. D_nu (bpW:wh:Dnu) is inlined in the frozen statement.
