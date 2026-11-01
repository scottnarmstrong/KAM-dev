NODE: bpW:w8:ext-inner
KIND: external
TITLE: Inner products along curves
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-inner@L59-L64
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:ext-inner
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: if c_1, c_2 : R -> l^2_R are differentiable at t then s -> <c_1(s),c_2(s)> has derivative <c_1'(t),c_2(t)> + <c_1(t),c_2'(t)>; <f,g> = sum f_j g_j with absolutely summable terms; termwise sums and differences of summable series; Cauchy-Schwarz
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
REVIEWER: sol-review-W-w8a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:ext-mono
KIND: external
TITLE: Sign of the derivative
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-mono@L65-L68
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:ext-mono
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: a real function differentiable on an interval with nonpositive (nonnegative) derivative is antitone (monotone) there; derivatives of products and of t -> e^{ct}
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
REVIEWER: sol-review-W-w8a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:ext-compact
KIND: external
TITLE: Compactness
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-compact@L69-L71
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:ext-compact
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: a continuous map on [-T,T] is bounded; analytic maps are continuous
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
REVIEWER: sol-review-W-w8a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:ext-exp
KIND: external
TITLE: Complex exponential and integers
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-exp@L72-L76
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:ext-exp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: e^z = 1 iff z in 2 pi i Z; ¦e^{ix}¦ = 1 and ¦e^{ix} - 1¦ <= ¦x¦ for real x; a continuous integer-valued function on a connected space (R or R^2) is constant; if t -> tc is bounded on R then c = 0
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
REVIEWER: sol-review-W-w8a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:ext-sqrt
KIND: external
TITLE: Square roots
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-sqrt@L77-L78
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:ext-sqrt
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: for a > 0 and a + b >= 0: ¦sqrt(a+b) - sqrt(a)¦ <= ¦b¦/sqrt(a)
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
REVIEWER: sol-review-W-w8a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:ext-dist
KIND: external
TITLE: Distance to a set
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-dist@L79-L81
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:ext-dist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: x -> dist(x,S) is 1-Lipschitz, so {dist(x,S) > a} is open; it is 0 on S and <= ¦x - y¦ for y in S
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
REVIEWER: sol-review-W-w8a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:ext-rpow
KIND: external
TITLE: Real powers
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-rpow@L82-L86
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:ext-rpow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: for x > 0: x^a x^b = x^{a+b}; x -> x^a monotone on [0,infinity) for a >= 0; x^a <= x^b for 0 < x <= 1, a >= b; x^a >= 0 for x >= 0; x -> x^a continuous at 0 with value 0 for a > 0, hence tends to 0 along nhdsWithin 0 (Ioi 0)
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
REVIEWER: sol-review-W-w8a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:ext-local
KIND: external
TITLE: Local definitions
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:ext-local@L87-L92
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:ext-local
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: local continuity gives continuity on S; continuity transfers to maps agreeing on S; continuous linear maps preserve AnalyticOnNhd and compose with fderiv by the chain rule; inequalities pass to limits
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
REVIEWER: sol-review-W-w8a
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w8:const
KIND: definition
TITLE: W8 constants
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:const@L100-L113
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:const
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W8 standing data (bpW:w8#data, L36-L53): m > 0, a = p = 1, max norms, Leb = volume, the constants of W2-W7, tau_E, r(I)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines E_1 = 1 + 2C_* + 6(2c_A)^{5/2} C'_K, E_3 = (1 + 8/M)E_1, E_4 = c^natural_F gamma sigma_P^{-52} + 5 c_F gamma_1 sigma_0^{-51}, E_5 = E_3 E_4/gamma, E_6 = 6 sqrt2 C_F (2c_A)^{3/2}, E_7 = 162 E_5 + E_6, t_0 = min{4^{-64}, alpha_0^{64/95}, rho_1^2/(8c_A), (gamma/E_3)^64, (7/(256 E_5))^64}, and the headline data tau = 24, r_0 = sqrt(2t_0), C_3 = 4 sqrt(c_A), C = max(1,M_m) C_3, eta(r) = 2^{33/64} E_7 r^{1/32}; all fixed after m and depending on m only
CONSTANT_SCOPE: all depend on m only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#bpW:w8:const@L101-L101 | the constants of the standing data
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W8UpstreamConsts, KAM.Wave.w8Upstream, KAM.Wave.w8cA, KAM.Wave.w8CStar, KAM.Wave.w8CF, KAM.Wave.w8Rho1, KAM.Wave.w8CKp, KAM.Wave.w8M, KAM.Wave.w8SigmaP, KAM.Wave.w8Sigma0, KAM.Wave.w8E1, KAM.Wave.w8E3, KAM.Wave.w8E4, KAM.Wave.w8E5, KAM.Wave.w8E6, KAM.Wave.w8E7, KAM.Wave.w8T0, KAM.Wave.w8T0W, KAM.Wave.w8Tau, KAM.Wave.w8R0, KAM.Wave.w8C3, KAM.Wave.w8C, KAM.Wave.w8Eta, KAM.Wave.w8SigmaP_eq_w6, KAM.Wave.w8Sigma0_eq_w6, KAM.Wave.w8M_eq_w6 (KAM/Wave/Assembly/Consts.lean, KAM/Wave/Assembly/UpstreamW6.lean, KAM/Wave/Assembly/ShellInit.lean)
LEAN_NOTE: definition formalized by W8-PREP/W8-FINAL; W8 audit 2 PASS WITH NOTES (literal constants at the actual upstream instance w8Upstream; the W5/W6 constants enter through the record W8UpstreamConsts, deviation D1 of W8-PREP; stale comments in Consts.lean noted)
NOTE: -

NODE: bpW:w8:shells
KIND: definition
TITLE: Shells
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shells@L117-L128
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:shells
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W8 standing data (bpW:w8#data, L36-L53): m > 0, a = p = 1, max norms, Leb = volume, the constants of W2-W7, tau_E, r(I); the constants of Definition bpW:w8:const
SOURCE_QUANTIFIERS: n >= 0
SOURCE_CONCLUSION: defines q = 1/2, t_n = 2^{-n} t_0, R_n (W7's shells with q = 1/2), alpha_n = t_n^{95/64}, r_n = t_n^{3/4}, rho_{xi,n} = alpha_n/2, rho_n = (c_A(t_n + r_n^2))^{1/2}, eps^sharp_n = E_3 t_n^{3/2}, kappa_n = (E_3/gamma) t_n^{1/64}, eps_{0,n} = kappa_n^{4/3} gamma_1 check alpha_n (check alpha_n = alpha_n^{48/47}), hat alpha_n = alpha_n^{44/47}, and the trimmed shell Pi_n = U_{-alpha_n} R_n
CONSTANT_SCOPE: depend on m and n
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:const, bpW:w7:shells, bpW:w8#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#bpW:w8:shells@L118-L118 | t_0, E_3
EDGE: bpW:w7:shells | blueprint-W/parts/w8-assembly.tex#bpW:w8:shells@L119-L119 | W7's shells
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#bpW:w8:shells@L117-L128 | the consumer explicitly inherits the standing section data recorded in SOURCE_HYPOTHESES
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-global-W
REVIEWER: sol-delta9-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8tn, KAM.Wave.w8Rn, KAM.Wave.w8alpha, KAM.Wave.w8rn, KAM.Wave.w8rhoXi, KAM.Wave.w8rho, KAM.Wave.w8epsSharp, KAM.Wave.w8kappa, KAM.Wave.w8eps0, KAM.Wave.w8alphaHat, KAM.Wave.w8Pi, KAM.Wave.w8kappa_eq (KAM/Wave/Assembly/Consts.lean)
LEAN_NOTE: definition formalized by W8-PREP; W8 audit 2 PASS (dyadic ratio, exponents, strict infDist margin agreeing with W7 shellInner)
NOTE: -

NODE: bpW:w8:shell-data
KIND: lemma
TITLE: Shell data are admissible
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-data@L132-L148
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-data@L149-L172
CONTRACT_ID: bpW:w8:shell-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definitions bpW:w8:const and bpW:w8:shells
SOURCE_QUANTIFIERS: for every n >= 0
SOURCE_CONCLUSION: (i) 0 < t_n <= t_0 <= 4^{-64}; alpha_n <= min(alpha_0, t_n); r_n <= 1; r_n^2 <= alpha_n/4; kappa_n <= 1 so eps^sharp_n <= gamma alpha_n; rho_n^2 <= 2 c_A t_n < rho_1^2/2 = r_1^2; (ii) Pi_n open, Pi_n subset R_n subset (0,t_n)^2 subset {¦xi¦ <= 1/2}, alpha_n < xi_i < t_n - alpha_n, and ¦xi - xi'¦ > alpha_n for xi' not in R_n; (iii) the hypotheses of Proposition bpW:w5:initial hold (s = 1/8, r = r_n, t = t_n, rho_xi = rho_{xi,n}, Pi = Pi_n) with eps_in(1 + 8/M) <= eps^sharp_n, so ¦X_P¦^lambda <= eps^sharp_n for lambda = alpha_n/M; (iv) the hypotheses of Lemma bpW:w6:prep-step hold (alpha = alpha_n, r = r_n, eps = eps^sharp_n) and those of Remark bpW:w6:to-w8
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shells, stepW:w8:sd-size, stepW:w8:sd-trim, stepW:w8:sd-init, stepW:w8:sd-prep
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shells | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-data@L133-L133 | the shell data
EDGE: stepW:w8:sd-size | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-data@L150-L150 | proof step
EDGE: stepW:w8:sd-trim | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-data@L154-L154 | proof step
EDGE: stepW:w8:sd-init | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-data@L160-L160 | proof step
EDGE: stepW:w8:sd-prep | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-data@L168-L168 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellData_sizes, KAM.Wave.w8Pi_isOpen, KAM.Wave.w8Pi_subset_Rn, KAM.Wave.w8Rn_subset_box, KAM.Wave.boxIoo_subset_closedBall_half, KAM.Wave.w8Pi_coord, KAM.Wave.w8Pi_sep, KAM.Wave.w8_shellData_init, KAM.Wave.w8_shellData_prep, KAM.Wave.w8HW, KAM.Wave.w8EpsIn_shell_sharp (KAM/Wave/Assembly/ShellData.lean, KAM/Wave/Assembly/ShellGeom.lean, KAM/Wave/Assembly/ShellInit.lean, KAM/Wave/Assembly/ShellTorus.lean)
LEAN_NOTE: W8 audit 1 FAIL (F1 w6-general constants/tori conjunct, F2 Kshell totalization, N1 partial labels), W8 audit 2 PASS WITH NOTES (F1, F2, N1 closed); W8 audit 2 PASS (all numerical premises and the actual initial perturbation supplied: w8HW builds the prep-step hypotheses from W5 initial via w6PrepHyp_initial)
NOTE: -

NODE: stepW:w8:sd-size
KIND: step
TITLE: Sizes
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-size@L150-L153
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-size@L150-L153
CONTRACT_ID: stepW:w8:sd-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-data: Definitions bpW:w8:const and bpW:w8:shells
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-data (for every n >= 0); within the step: n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-rpow, bpW:w8:const
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-rpow | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-size@L151-L151 | real powers
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-size@L152-L152 | the entries of t_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellData_sizes, KAM.Wave.w8tn_facts, KAM.Wave.w8alpha_le, KAM.Wave.w8rn_le, KAM.Wave.w8kappa_le, KAM.Wave.w8rho_sq_le (KAM/Wave/Assembly/ShellData.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-data; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:sd-trim
KIND: step
TITLE: Trimmed shell
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-trim@L154-L159
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-trim@L154-L159
CONTRACT_ID: stepW:w8:sd-trim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-data: Definitions bpW:w8:const and bpW:w8:shells
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-data (for every n >= 0); within the step: xi; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:ext-dist, bpW:w7:shell-geom
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:ext-dist | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-trim@L154-L154 | distance to a set
EDGE: bpW:w7:shell-geom | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-trim@L159-L159 | (i) disjoint shells
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8Pi_isOpen, KAM.Wave.w8Pi_subset_Rn, KAM.Wave.w8Rn_subset_box, KAM.Wave.w8Pi_coord, KAM.Wave.w8Pi_sep (KAM/Wave/Assembly/ShellGeom.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-data; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:sd-init
KIND: step
TITLE: Proposition~\ref{bpW:w5:initial}
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-init@L160-L167
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-init@L160-L167
CONTRACT_ID: stepW:w8:sd-init
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-data: Definitions bpW:w8:const and bpW:w8:shells
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-data (for every n >= 0); within the step: xi, zeta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) eps_in <= E_1 t_n^{3/2} and ¦X_P¦^lambda <= eps^sharp_n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:initial, stepW:w8:sd-trim, stepW:w8:sd-size
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:initial | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-init@L160-L160 | its hypotheses and bound
EDGE: stepW:w8:sd-trim | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-init@L162-L162 | (ii)
EDGE: stepW:w8:sd-size | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-init@L162-L162 | (i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellData_init, KAM.Wave.w8EpsIn_shell_le, KAM.Wave.w8EpsIn_shell_sharp (KAM/Wave/Assembly/ShellInit.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-data; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:sd-prep
KIND: step
TITLE: Lemma~\ref{bpW:w6:prep-step}
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L171
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L171
CONTRACT_ID: stepW:w8:sd-prep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-data: Definitions bpW:w8:const and bpW:w8:shells
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-data (for every n >= 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:prep-step, bpW:w5:initial, stepW:w8:sd-init, bpW:w6:to-w8, stepW:w8:sd-size, stepW:w8:sd-trim
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:prep-step | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L168 | its hypotheses
EDGE: bpW:w5:initial | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L170-L170 | P real periodic in S_{p+1}
EDGE: stepW:w8:sd-init | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L171-L171 | (iii)
EDGE: bpW:w6:to-w8 | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L171 | the checks conclude clause (iv), including the conditions of the W6 interface remark
EDGE: stepW:w8:sd-size | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L171-L171 | (i) supplies eps^sharp_n <= gamma alpha_n
EDGE: stepW:w8:sd-trim | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L168 | the trimmed shell is Borel and lies in the required half-unit box
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta6-W-W-w8a
REVIEWER: sol-delta7-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellData_prep, KAM.Wave.w8HW (KAM/Wave/Assembly/ShellInit.lean, KAM/Wave/Assembly/ShellTorus.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-data; W8 audit 2 PASS (prep-step hypotheses proved at the source instance)
NOTE: -

NODE: bpW:w8:sharp-prep
KIND: lemma
TITLE: Sharp size after the preparatory step
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:sharp-prep@L178-L185
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:sharp-prep@L186-L194
CONTRACT_ID: bpW:w8:sharp-prep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n fixed; Lemma bpW:w6:prep-step run with the data of Lemma bpW:w8:shell-data(iv), eps = eps^sharp_n
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: eta_P = (eps^sharp_n/(hat alpha_n sigma_P^{53}))^{1/3} and ¦X_{P_0}¦^{lambda_0}_{r_0,D_0} <= eps^flat_{0,n} := 2 C^natural_2 (eps^sharp_n)^{4/3}(hat alpha_n sigma_P^{53})^{-1/3} <= eps_{0,n} <= gamma_1 check alpha_n with lambda_0 = check alpha_n/(2M); eps^flat_{0,n} > 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-data, bpW:w6:prep-step, stepW:w8:sp-step, stepW:w8:sp-cmp
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#bpW:w8:sharp-prep@L179-L179 | (iv)
EDGE: bpW:w6:prep-step | blueprint-W/parts/w8-assembly.tex#bpW:w8:sharp-prep@L179-L179 | the preparatory step
EDGE: stepW:w8:sp-step | blueprint-W/parts/w8-assembly.tex#bpW:w8:sharp-prep@L187-L187 | proof step
EDGE: stepW:w8:sp-cmp | blueprint-W/parts/w8-assembly.tex#bpW:w8:sharp-prep@L189-L189 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_epsFlat_shell, KAM.Wave.w8_sharpPrep (KAM/Wave/Assembly/ShellIter.lean)
LEAN_NOTE: W8 audit 2 PASS (sharp positive size and admissible starting interval at H = w8HW)
NOTE: -

NODE: stepW:w8:sp-step
KIND: step
TITLE: The sharp bound
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-step@L187-L188
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-step@L187-L188
CONTRACT_ID: stepW:w8:sp-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:sharp-prep: n fixed; Lemma bpW:w6:prep-step run with the data of Lemma bpW:w8:shell-data(iv), eps = eps^sharp_n
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:sharp-prep (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the sharp bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:prep-step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:prep-step | blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-step@L187-L187 | (v)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_sharpPrep (KAM/Wave/Assembly/ShellIter.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:sharp-prep; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:sp-cmp
KIND: step
TITLE: Comparison
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-cmp@L189-L193
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-cmp@L189-L193
CONTRACT_ID: stepW:w8:sp-cmp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:sharp-prep: n fixed; Lemma bpW:w6:prep-step run with the data of Lemma bpW:w8:shell-data(iv), eps = eps^sharp_n
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:sharp-prep (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: eps^flat_{0,n} <= eps_{0,n} <= gamma_1 check alpha_n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:constants, bpW:w8:shell-data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:constants | blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-cmp@L192-L192 | gamma
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:sp-cmp@L193-L193 | (i) kappa_n <= 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_epsFlat_shell (KAM/Wave/Assembly/ShellIter.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:sharp-prep; W8 audit 2 PASS
NOTE: -

NODE: bpW:w8:shell-iter
KIND: definition
TITLE: The shell iteration
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-iter@L198-L209
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:shell-iter
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 0; the shell data
SOURCE_QUANTIFIERS: n
SOURCE_CONCLUSION: defines the shell iteration: Definition bpW:w6:wave-iteration with the data of Lemma bpW:w8:shell-data(iv) and eps_0 = eps_{0,n} (in [eps^flat_{0,n}, gamma_1 check alpha_n]); its outputs Pi^(n)_*, omega^(n)_*, nu^(n)_*, Phi^(n)_*, Phi^(n)_P, tilde Psi^(n)_xi, the admissible family and E^(n), e^(n)_tor, eps^(n)_omega; Gamma_n = Pi^(n)_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:wave-iteration, bpW:w8:shell-data, bpW:w8:sharp-prep, bpW:w6:tori, bpW:w7:family
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-iter@L199-L199 | W6's wave iteration
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-iter@L200-L200 | (iv)
EDGE: bpW:w8:sharp-prep | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-iter@L201-L201 | the starting size is admissible
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-iter@L203-L203 | tilde Psi
EDGE: bpW:w7:family | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-iter@L204-L204 | admissible family and excluded set
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8Eps0W, KAM.Wave.w8MeasSetup, KAM.Wave.w8ShellSeqData, KAM.Wave.w8ShellStart, KAM.Wave.w8ShellGamma, KAM.Wave.w8ShellOmega, KAM.Wave.w8ShellNu, KAM.Wave.w8ShellFamily, KAM.Wave.w8ShellExcl, KAM.Wave.w8ShellEtor, KAM.Wave.w8ShellEpsOm, KAM.Wave.w8ShellTorusKam, KAM.Wave.w8TK, KAM.Wave.w8Psi, KAM.Wave.w8Phase, KAM.Wave.w8Yact, KAM.Wave.w8Xang, KAM.Wave.w8XC (KAM/Wave/Assembly/ShellIter.lean, KAM/Wave/Assembly/ShellTorus.lean)
LEAN_NOTE: definition formalized by W8-ASM/W8-FINAL; W8 audit 2 PASS (actual W6 iteration with shell-dependent starting size; action-angle map composed in w8Psi)
NOTE: -

NODE: bpW:w8:w6-general
KIND: lemma
TITLE: W6 with the sharp starting size
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:w6-general@L212-L217
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:w6-general@L218-L227
CONTRACT_ID: bpW:w8:w6-general
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the shell iteration (Definition bpW:w8:shell-iter)
SOURCE_QUANTIFIERS: for every n
SOURCE_CONCLUSION: the conclusions of Lemmas bpW:w6:applicable, bpW:w6:freq-lip (eps_omega = eps^(n)_omega, eps_1 = 3 gamma alpha_n, eps_2 = 4 eps_{0,n}, theta = 425(1+M) max(gamma,gamma_1) <= theta_0), bpW:w6:exclusion, bpW:w6:final-freq and Theorem bpW:w6:tori hold for the shell iteration, with e_tor = e^(n)_tor
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-iter, stepW:w8:g-app, stepW:w8:g-freq, stepW:w8:g-excl, stepW:w8:g-tori
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#bpW:w8:w6-general@L213-L213 | the shell iteration
EDGE: stepW:w8:g-app | blueprint-W/parts/w8-assembly.tex#bpW:w8:w6-general@L219-L219 | proof step
EDGE: stepW:w8:g-freq | blueprint-W/parts/w8-assembly.tex#bpW:w8:w6-general@L222-L222 | proof step
EDGE: stepW:w8:g-excl | blueprint-W/parts/w8-assembly.tex#bpW:w8:w6-general@L224-L224 | proof step
EDGE: stepW:w8:g-tori | blueprint-W/parts/w8-assembly.tex#bpW:w8:w6-general@L225-L225 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_w6General, KAM.Wave.w8ShellToriKam, KAM.Wave.w8_toriData, KAM.Wave.W6PrepHyp.w6Tori, KAM.Wave.w6WaveFamilyJ, KAM.Wave.w6ExclusionJ (KAM/Wave/Assembly/ShellIter.lean, KAM/Wave/Assembly/ShellTorus.lean, KAM/Wave/Iteration/Tori.lean, KAM/Wave/Iteration/FreqLipJ.lean)
LEAN_NOTE: W8 audit 1 FAIL (F1 w6-general constants/tori conjunct, F2 Kshell totalization, N1 partial labels), W8 audit 2 PASS WITH NOTES (F1, F2, N1 closed); W8 audit 2 PASS WITH NOTES (exact frequency constants eps_1 = 3 gamma alpha_n, eps_2 = 4 eps_(0,n); the tori conclusion is the separate unconditional w8ShellToriKam plus W6PrepHyp.w6Tori fed by w8_toriData, not a conjunct of w8_w6General)
NOTE: -

NODE: stepW:w8:g-app
KIND: step
TITLE: Applicability
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L219-L221
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L219-L221
CONTRACT_ID: stepW:w8:g-app
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:w6-general: the shell iteration (Definition bpW:w8:shell-iter)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:w6-general (for every n); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Lemma bpW:w6:applicable for the value eps_{0,n}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:applicable, bpW:w8:sharp-prep, bpW:w6:wave-iteration
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:applicable | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L219-L219 | applicability
EDGE: bpW:w8:sharp-prep | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L221-L221 | eps_{0,n} admissible
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L220-L220 | the allowed parameter interval for eps_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_w6General, KAM.Wave.w8_epsFlat_shell (KAM/Wave/Assembly/ShellIter.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:w6-general; W8 audit 2 PASS WITH NOTES
NOTE: -

NODE: stepW:w8:g-freq
KIND: step
TITLE: Frequencies
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-freq@L222-L223
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-freq@L222-L223
CONTRACT_ID: stepW:w8:g-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:w6-general: the shell iteration (Definition bpW:w8:shell-iter)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:w6-general (for every n); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Lemma bpW:w6:freq-lip for this value
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:freq-lip
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-freq@L222-L222 | Lipschitz frequencies
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_w6General, KAM.Wave.w6WaveFamilyJ (KAM/Wave/Assembly/ShellIter.lean, KAM/Wave/Iteration/FreqLipJ.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:w6-general; W8 audit 2 PASS WITH NOTES (blueprint constants)
NOTE: -

NODE: stepW:w8:g-excl
KIND: step
TITLE: Exclusion and final frequencies
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-excl@L224-L224
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-excl@L224-L224
CONTRACT_ID: stepW:w8:g-excl
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:w6-general: the shell iteration (Definition bpW:w8:shell-iter)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:w6-general (for every n); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Lemmas bpW:w6:exclusion and bpW:w6:final-freq for this value
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:exclusion, bpW:w6:final-freq
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:exclusion | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-excl@L224-L224 | exclusion
EDGE: bpW:w6:final-freq | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-excl@L224-L224 | final frequencies
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_w6General, KAM.Wave.w6ExclusionJ (KAM/Wave/Assembly/ShellIter.lean, KAM/Wave/Iteration/FreqLipJ.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:w6-general; W8 audit 2 PASS WITH NOTES
NOTE: -

NODE: stepW:w8:g-tori
KIND: step
TITLE: Tori
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-tori@L225-L226
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:g-tori@L225-L226
CONTRACT_ID: stepW:w8:g-tori
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:w6-general: the shell iteration (Definition bpW:w8:shell-iter)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:w6-general (for every n); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Theorem bpW:w6:tori with e_tor = e^(n)_tor
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-tori@L225-L225 | the tori
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8ShellToriKam, KAM.Wave.w8_toriData, KAM.Wave.W6PrepHyp.w6Tori (KAM/Wave/Assembly/ShellIter.lean, KAM/Wave/Assembly/ShellTorus.lean, KAM/Wave/Iteration/Tori.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:w6-general; W8 audit 2 PASS WITH NOTES (separate tori export)
NOTE: -

NODE: bpW:w8:etor
KIND: lemma
TITLE: Shell errors tend to zero
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:etor@L231-L234
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:etor@L235-L244
CONTRACT_ID: bpW:w8:etor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the shell iteration
SOURCE_QUANTIFIERS: for every n
SOURCE_CONCLUSION: e^(n)_tor <= E_4 kappa_n = E_5 t_n^{1/64} <= 7/256, and eps^(n)_omega <= alpha_n/(70 L_A) <= alpha_n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-iter, stepW:w8:e-tor, stepW:w8:e-om, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#bpW:w8:etor@L232-L232 | e^(n)_tor, eps^(n)_omega
EDGE: stepW:w8:e-tor | blueprint-W/parts/w8-assembly.tex#bpW:w8:etor@L236-L236 | proof step
EDGE: stepW:w8:e-om | blueprint-W/parts/w8-assembly.tex#bpW:w8:etor@L240-L240 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#bpW:w8:etor@L243-L243 | lambda occurs directly here (frozen lam)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_etor, KAM.Wave.w8ShellEtor_eq (KAM/Wave/Assembly/Etor.lean, KAM/Wave/Assembly/ShellIter.lean)
LEAN_NOTE: W8 audit 2 PASS (E_4 kappa = E_5 t^(1/64) <= 7/256; frequency error <= alpha/(70 L_A) <= alpha)
NOTE: -

NODE: stepW:w8:e-tor
KIND: step
TITLE: $e_{\rm tor}$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L236-L239
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L236-L239
CONTRACT_ID: stepW:w8:e-tor
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:etor: the shell iteration
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:etor (for every n); within the step: n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: e^(n)_tor <= E_5 t_n^{1/64} <= 7/256
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:const, bpW:w8:shell-iter, bpW:w8:shell-data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L238-L238 | E_4, E_5, t_0
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L236-L238 | the formula for e_tor and eps_{0,n}
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L238-L238 | alpha_n and kappa_n <= 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_etor, KAM.Wave.w8_rpow_one_sub_exp (KAM/Wave/Assembly/Etor.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:etor; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:e-om
KIND: step
TITLE: $\varepsilon_\omega$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L240-L243
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L240-L243
CONTRACT_ID: stepW:w8:e-om
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:etor: the shell iteration
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:etor (for every n); within the step: n; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: eps^(n)_omega <= alpha_n/(70 L_A) <= alpha_n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:constants, bpW:w7:constdef, bpW:w7:freqcoords, bpW:w0:basis#lam, bpW:w8:sharp-prep, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:constants | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L242-L242 | gamma, gamma_1
EDGE: bpW:w7:constdef | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L242-L242 | (C4) theta_0
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L243-L243 | (ii) L_A
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L243-L243 | lambda occurs directly here (frozen lam)
EDGE: bpW:w8:sharp-prep | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L240-L240 | the upper bound on eps_{0,n}
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L243-L243 | lambda_1 > 1 and lambda_2 > 2 yield L_A > 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_etor (KAM/Wave/Assembly/Etor.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:etor; W8 audit 2 PASS
NOTE: -

NODE: bpW:w8:freq-shell
KIND: lemma
TITLE: Frequencies on one shell
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:freq-shell@L248-L257
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:freq-shell@L258-L269
CONTRACT_ID: bpW:w8:freq-shell
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the shell iteration
SOURCE_QUANTIFIERS: for every n and xi, xi' in Gamma_n
SOURCE_CONCLUSION: (i) ¦(omega^(n)_* - omega^0)(xi) - (omega^(n)_* - omega^0)(xi')¦ <= theta_0 ¦xi - xi'¦; (ii) ¦omega^(n)_*(xi) - omega^(n)_*(xi')¦ >= (7/(8 L_A))¦xi - xi'¦; (iii) ¦omega^(n)_*(xi) - omega^0(xi)¦ <= eps^(n)_omega <= alpha_n/(70 L_A) and ¦<k,omega^(n)_*(xi)>¦ >= check alpha_n/(2 A_k) for k != 0; (iv) nu^(n)_* is Lipschitz on Gamma_n and Gamma_n is Borel
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-iter, stepW:w8:fs-lim, stepW:w8:fs-low, stepW:w8:fs-size, stepW:w8:fs-reg
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#bpW:w8:freq-shell@L249-L249 | Gamma_n, omega^(n)_*
EDGE: stepW:w8:fs-lim | blueprint-W/parts/w8-assembly.tex#bpW:w8:freq-shell@L259-L259 | proof step
EDGE: stepW:w8:fs-low | blueprint-W/parts/w8-assembly.tex#bpW:w8:freq-shell@L262-L262 | proof step
EDGE: stepW:w8:fs-size | blueprint-W/parts/w8-assembly.tex#bpW:w8:freq-shell@L264-L264 | proof step
EDGE: stepW:w8:fs-reg | blueprint-W/parts/w8-assembly.tex#bpW:w8:freq-shell@L266-L266 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_freqShell, KAM.Wave.w8ShellGamma_subset_D, KAM.Wave.w8ShellOmega_tendsto, KAM.Wave.w8ShellGamma_measurableSet (KAM/Wave/Assembly/FreqShell.lean)
LEAN_NOTE: W8 audit 2 PASS ((H1) limit, 7/(8 L_A) co-Lipschitz bound, divisors, Lipschitz nu and Borel Gamma_n)
NOTE: -

NODE: stepW:w8:fs-lim
KIND: step
TITLE: Limit of (H1)
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-lim@L259-L261
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-lim@L259-L261
CONTRACT_ID: stepW:w8:fs-lim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:freq-shell: the shell iteration
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:freq-shell (for every n and xi, xi' in Gamma_n); within the step: xi, xi'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i) by passing (H1) to the limit
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:w6-general, bpW:w6:convergence, bpW:w8:ext-local
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:w6-general | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-lim@L260-L260 | (H1)
EDGE: bpW:w6:convergence | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-lim@L261-L261 | (ii)
EDGE: bpW:w8:ext-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-lim@L261-L261 | limits
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_freqShell, KAM.Wave.w8ShellOmega_tendsto (KAM/Wave/Assembly/FreqShell.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:freq-shell; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:fs-low
KIND: step
TITLE: Lower bound
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-low@L262-L263
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-low@L262-L263
CONTRACT_ID: stepW:w8:fs-low
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:freq-shell: the shell iteration
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:freq-shell (for every n and xi, xi' in Gamma_n); within the step: xi, xi'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:freqcoords, bpW:w0n:nondeg, stepW:w8:fs-lim, bpW:w7:constdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-low@L262-L262 | (iv)
EDGE: bpW:w0n:nondeg | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-low@L263-L263 | (i) det A != 0
EDGE: stepW:w8:fs-lim | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-low@L263-L263 | (i)
EDGE: bpW:w7:constdef | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-low@L263-L263 | theta_0 <= 1/(8 L_A)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_freqShell, KAM.Wave.measTheta0_le_inv_eight_LA (KAM/Wave/Assembly/FreqShell.lean, KAM/Wave/Assembly/Etor.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:freq-shell; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:fs-size
KIND: step
TITLE: Size and divisors
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-size@L264-L265
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-size@L264-L265
CONTRACT_ID: stepW:w8:fs-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:freq-shell: the shell iteration
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:freq-shell (for every n and xi, xi' in Gamma_n); within the step: xi; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:final-freq, bpW:w8:w6-general, bpW:w8:etor
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:final-freq | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-size@L264-L264 | via Lemma bpW:w8:w6-general
EDGE: bpW:w8:w6-general | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-size@L264-L264 | transfer
EDGE: bpW:w8:etor | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-size@L265-L265 | eps_omega bound
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_freqShell, KAM.Wave.w8ShellGamma_subset_D (KAM/Wave/Assembly/FreqShell.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:freq-shell; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:fs-reg
KIND: step
TITLE: Regularity
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-reg@L266-L268
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-reg@L266-L268
CONTRACT_ID: stepW:w8:fs-reg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:freq-shell: the shell iteration
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:freq-shell (for every n and xi, xi' in Gamma_n); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w8:w6-general, bpW:w6:convergence, bpW:w8:shell-data, bpW:w7:measurable, stepW:w6:fl-borel
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-reg@L266-L266 | (ii)
EDGE: bpW:w8:w6-general | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-reg@L266-L266 | transfer
EDGE: bpW:w6:convergence | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-reg@L267-L267 | (i)
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-reg@L267-L267 | (ii)
EDGE: bpW:w7:measurable | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-reg@L267-L267 | Borel
EDGE: stepW:w6:fl-borel | blueprint-W/parts/w8-assembly.tex#stepW:w8:fs-reg@L268-L268 | continuity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_freqShell, KAM.Wave.w8ShellGamma_measurableSet (KAM/Wave/Assembly/FreqShell.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:freq-shell; W8 audit 2 PASS
NOTE: -

NODE: bpW:w8:torus-shape
KIND: lemma
TITLE: Shape of a shell torus
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L275-L289
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L290-L310
CONTRACT_ID: bpW:w8:torus-shape
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 0, xi in Gamma_n, Psi = tilde Psi^(n)_xi, Phi^(n)_P Phi^(n)_*(theta) = (theta + X(theta), y(theta), u(theta), v(theta)) on T_{s_0/2}, e = e^(n)_tor
SOURCE_QUANTIFIERS: theta (complex or real as stated)
SOURCE_CONCLUSION: (i) X, y holomorphic with ¦X¦ <= e, ¦y¦ <= r_n^2 e and ¦¦hat Psi¦¦ <= r_n e; (ii) for real theta, X, y real, xi_i + y_i >= (3/4) alpha_n > 0 and Psi_{+-i} = sqrt(xi_i + y_i) e^{-+2 pi i(theta_i + X_i)}; (iii) X(theta + k) = X(theta); (iv) ¦¦DX(theta)¦¦ <= 128e/7 <= 1/2 and X is 1/2-Lipschitz on R^2; (v) ¦¦Psi(theta)¦¦ < rho_n <= r_1 and x(theta) = Z^{-1} Psi(theta) in B^E_{r_1} is real
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-iter, bpW:w6:tori, stepW:w8:ts-bd, stepW:w8:ts-real, stepW:w8:ts-per, stepW:w8:ts-cauchy, stepW:w8:ts-ball
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L276-L276 | tilde Psi, Phi_P, Phi_*
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L277-L277 | (iv)
EDGE: stepW:w8:ts-bd | blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L291-L291 | proof step
EDGE: stepW:w8:ts-real | blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L294-L294 | proof step
EDGE: stepW:w8:ts-per | blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L300-L300 | proof step
EDGE: stepW:w8:ts-cauchy | blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L303-L303 | proof step
EDGE: stepW:w8:ts-ball | blueprint-W/parts/w8-assembly.tex#bpW:w8:torus-shape@L307-L307 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8TK_differentiableOn, KAM.Wave.w8TK_close, KAM.Wave.w8_torusShape_bounds, KAM.Wave.w8_torusShape_real, KAM.Wave.w8_torusShape_coord, KAM.Wave.w8TK_real, KAM.Wave.w8XC_real, KAM.Wave.w8_coord_true, KAM.Wave.w8XC_periodic, KAM.Wave.w8Xang_periodic, KAM.Wave.w8Psi_periodic, KAM.Wave.w8_torusShape_deriv, KAM.Wave.w8Xang_lipschitz, KAM.Wave.w8Psi_ball (KAM/Wave/Assembly/ShellTorus.lean, KAM/Wave/Assembly/ShellEmbed.lean)
LEAN_NOTE: W8 audit 2 PASS (one theorem per clause; deviation D4 of W8-FINAL: reality and periodicity of X, y read from W6 tori in KAM coordinates instead of the phase argument; (iv) for the complex derivative at real theta plus the real 1/2-Lipschitz bound)
NOTE: -

NODE: stepW:w8:ts-bd
KIND: step
TITLE: Bounds
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-bd@L291-L293
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-bd@L291-L293
CONTRACT_ID: stepW:w8:ts-bd
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:torus-shape: n >= 0, xi in Gamma_n, Psi = tilde Psi^(n)_xi, Phi^(n)_P Phi^(n)_*(theta) = (theta + X(theta), y(theta), u(theta), v(theta)) on T_{s_0/2}, e = e^(n)_tor
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:torus-shape (theta (complex or real as stated)); within the step: theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w8:w6-general, bpW:w5:action-angle
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-bd@L291-L291 | (iv)
EDGE: bpW:w8:w6-general | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-bd@L291-L291 | transfer
EDGE: bpW:w5:action-angle | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-bd@L293-L293 | (vi)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_torusShape_bounds, KAM.Wave.w8TK_close (KAM/Wave/Assembly/ShellTorus.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:torus-shape; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:ts-real
KIND: step
TITLE: Reality
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L294-L299
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L294-L299
CONTRACT_ID: stepW:w8:ts-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:torus-shape: n >= 0, xi in Gamma_n, Psi = tilde Psi^(n)_xi, Phi^(n)_P Phi^(n)_*(theta) = (theta + X(theta), y(theta), u(theta), v(theta)) on T_{s_0/2}, e = e^(n)_tor
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:torus-shape (theta (complex or real as stated)); within the step: real theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w3:coords, bpW:w8:shell-data, bpW:w8:ext-exp, stepW:w8:ts-bd, bpW:w8:etor
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L294-L294 | (i), (iv)
EDGE: bpW:w3:coords | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L295-L295 | rho
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L297-L297 | (i), (ii)
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L299-L299 | complex exponential
EDGE: stepW:w8:ts-bd | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L297-L297 | (i)
EDGE: bpW:w8:etor | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L297-L297 | e <= 7/256 <= 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_torusShape_real, KAM.Wave.w8_torusShape_coord, KAM.Wave.w8TK_real, KAM.Wave.w8XC_real (KAM/Wave/Assembly/ShellTorus.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:torus-shape; W8 audit 2 PASS; Lean route differs (D4)
NOTE: -

NODE: stepW:w8:ts-per
KIND: step
TITLE: Periodicity
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L300-L302
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L300-L302
CONTRACT_ID: stepW:w8:ts-per
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:torus-shape: n >= 0, xi in Gamma_n, Psi = tilde Psi^(n)_xi, Phi^(n)_P Phi^(n)_*(theta) = (theta + X(theta), y(theta), u(theta), v(theta)) on T_{s_0/2}, e = e^(n)_tor
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:torus-shape (theta (complex or real as stated)); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w8:ext-exp, stepW:w8:ts-real, bpW:w8:etor
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L300-L300 | (i) periodicity
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L301-L301 | integer-valued continuous functions
EDGE: stepW:w8:ts-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L300-L300 | (ii)
EDGE: bpW:w8:etor | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L302-L302 | 2e <= 14/256 < 1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8Xang_periodic, KAM.Wave.w8XC_periodic, KAM.Wave.w8Psi_periodic (KAM/Wave/Assembly/ShellTorus.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:torus-shape; W8 audit 2 PASS; Lean route differs (D4)
NOTE: -

NODE: stepW:w8:ts-cauchy
KIND: step
TITLE: Cauchy
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-cauchy@L303-L306
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-cauchy@L303-L306
CONTRACT_ID: stepW:w8:ts-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:torus-shape: n >= 0, xi in Gamma_n, Psi = tilde Psi^(n)_xi, Phi^(n)_P Phi^(n)_*(theta) = (theta + X(theta), y(theta), u(theta), v(theta)) on T_{s_0/2}, e = e^(n)_tor
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:torus-shape (theta (complex or real as stated)); within the step: real theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:cauchy, bpW:w8:etor, stepW:w8:ts-bd
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:cauchy | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-cauchy@L304-L304 | Cauchy estimate
EDGE: bpW:w8:etor | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-cauchy@L304-L304 | e <= 7/256
EDGE: stepW:w8:ts-bd | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-cauchy@L304-L304 | ¦X¦ <= e
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_torusShape_deriv, KAM.Wave.w8Xang_lipschitz (KAM/Wave/Assembly/ShellTorus.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:torus-shape; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:ts-ball
KIND: step
TITLE: Ball
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-ball@L307-L309
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-ball@L307-L309
CONTRACT_ID: stepW:w8:ts-ball
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:torus-shape: n >= 0, xi in Gamma_n, Psi = tilde Psi^(n)_xi, Phi^(n)_P Phi^(n)_*(theta) = (theta + X(theta), y(theta), u(theta), v(theta)) on T_{s_0/2}, e = e^(n)_tor
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:torus-shape (theta (complex or real as stated)); within the step: real theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (v)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:action-angle, bpW:w8:shell-data, bpW:w3:coords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:action-angle | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-ball@L308-L308 | (ii)
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-ball@L308-L308 | (i)
EDGE: bpW:w3:coords | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-ball@L309-L309 | Z^{-1}
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8Psi_ball (KAM/Wave/Assembly/ShellTorus.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:torus-shape; W8 audit 2 PASS
NOTE: -

NODE: bpW:w8:Kshell
KIND: definition
TITLE: Shell embeddings
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:Kshell@L314-L319
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8:Kshell
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 0, xi in Gamma_n, theta in R^2
SOURCE_QUANTIFIERS: n, xi, theta
SOURCE_CONCLUSION: defines K^(n)_xi(theta) = tau_E(Gamma^R(Z^{-1} tilde Psi^(n)_xi(theta))) = tau_E(Z^{-1} Gamma(tilde Psi^(n)_xi(theta))) in WaveSpace
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8#data, bpW:w8:torus-shape, bpW:w3:gamma-real, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#bpW:w8:Kshell@L316-L316 | tau_E, Gamma, Gamma^R, Z
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#bpW:w8:Kshell@L318-L318 | (v) well defined
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#bpW:w8:Kshell@L318-L318 | Gamma^R
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w8-assembly.tex#bpW:w8:Kshell@L317-L317 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8AA, KAM.Wave.w8Kshell, KAM.Wave.w8KOfBirk, KAM.Wave.w8Kshell_eq, KAM.Wave.w8KOfBirk_of_mem, KAM.Wave.w8KOfBirk_eq_gamma, KAM.Wave.w8Psi_ball (KAM/Wave/Assembly/ShellEmbed.lean, KAM/Wave/Assembly/PatchInst.lean, KAM/Wave/Assembly/ShellInv.lean, KAM/Wave/Assembly/ShellTorus.lean)
LEAN_NOTE: definition formalized by W8-FINAL; W8 audit 1 FAIL (F1 w6-general constants/tori conjunct, F2 Kshell totalization, N1 partial labels), W8 audit 2 PASS WITH NOTES (F1, F2, N1 closed); W8 audit 2 PASS WITH NOTES: exact source map w8Kshell w8AA (w8HW hm n) on Gamma_n x R^2 (both source formulas, ball membership by w8Psi_ball, tau_E = id); the unrestricted wrappers w8KOfBirk and w8Kshell A H are generic and not certified as the source definition off that carrier
NOTE: -

NODE: bpW:w8:shell-embedding
KIND: lemma
TITLE: Each shell torus is an analytic torus embedding
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-embedding@L323-L325
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-embedding@L326-L350
CONTRACT_ID: bpW:w8:shell-embedding
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 0, xi in Gamma_n
SOURCE_QUANTIFIERS: for every n, xi
SOURCE_CONCLUSION: IsAnalyticTorusEmbedding K^(n)_xi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:Kshell, stepW:w8:se-per, stepW:w8:se-an, stepW:w8:se-inj, stepW:w8:se-der, bpW:wh:embedding#IsAnalyticTorusEmbedding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:Kshell | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-embedding@L324-L324 | K^(n)_xi
EDGE: stepW:w8:se-per | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-embedding@L328-L328 | proof step
EDGE: stepW:w8:se-an | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-embedding@L329-L329 | proof step
EDGE: stepW:w8:se-inj | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-embedding@L331-L331 | proof step
EDGE: stepW:w8:se-der | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-embedding@L338-L338 | proof step
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-embedding@L324-L324 | the frozen IsAnalyticTorusEmbedding occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellEmbedding, KAM.Wave.w8Kshell_analytic, KAM.Wave.w8Kshell_injMod, KAM.Wave.w8Kshell_fderiv_injective (KAM/Wave/Assembly/ShellEmbed.lean)
LEAN_NOTE: W8 audit 2 PASS (every frozen embedding conjunct)
NOTE: -

NODE: stepW:w8:se-per
KIND: step
TITLE: Periodicity
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-per@L328-L328
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-per@L328-L328
CONTRACT_ID: stepW:w8:se-per
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-embedding: n >= 0, xi in Gamma_n
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-embedding (for every n, xi); within the step: k; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: K(theta + k) = K(theta)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-per@L328-L328 | (i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellEmbedding, KAM.Wave.w8KOfBirk_periodic, KAM.Wave.w8Psi_periodic (KAM/Wave/Assembly/ShellEmbed.lean, KAM/Wave/Assembly/PatchInst.lean, KAM/Wave/Assembly/ShellTorus.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-embedding; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:se-an
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L329-L330
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L329-L330
CONTRACT_ID: stepW:w8:se-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-embedding: n >= 0, xi in Gamma_n
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-embedding (for every n, xi); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: AnalyticOnNhd R K univ
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w8:ext-local, bpW:w8#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L329-L329 | (v)
EDGE: bpW:w8:ext-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L330-L330 | continuous linear maps preserve AnalyticOnNhd
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L330-L330 | tau_E is a continuous linear isometric bijection
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8Kshell_analytic (KAM/Wave/Assembly/ShellEmbed.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-embedding; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:se-inj
KIND: step
TITLE: Injectivity modulo $\Z^2$
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L331-L337
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L331-L337
CONTRACT_ID: stepW:w8:se-inj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-embedding: n >= 0, xi in Gamma_n; local implication premise K(theta) = K(theta'); local definitions Psi = tilde Psi^(n)_xi, x = Z^{-1} Psi, K = K^(n)_xi
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-embedding (for every n, xi); within the step: theta, theta'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: injectivity modulo Z^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:gamma-real, bpW:w8:torus-shape, bpW:w8:ext-exp, bpW:w8#data, bpW:w3:coords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L332-L332 | (iii) injectivity
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L333-L333 | (ii)-(v)
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L335-L335 | e^z = 1
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L332-L332 | tau_E is injective
EDGE: bpW:w3:coords | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L333-L333 | Z is bijective
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8Kshell_injMod, KAM.Wave.w8_injMod_of_phase, KAM.Wave.w8_phase_int_of_eq (KAM/Wave/Assembly/ShellEmbed.lean, KAM/Wave/Assembly/InjAssembly.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-embedding; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:se-der
KIND: step
TITLE: Derivative
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L338-L349
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L338-L349
CONTRACT_ID: stepW:w8:se-der
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-embedding: n >= 0, xi in Gamma_n; local kernel premise fderiv R K theta h = 0; Psi = tilde Psi^(n)_xi, x = Z^{-1} Psi, K = K^(n)_xi
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-embedding (for every n, xi); within the step: theta, h; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: fderiv R K theta is injective
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:torus-analytic, stepW:w6:t-an, bpW:w8:ext-local, bpW:w3:flow, bpW:w8:torus-shape, bpW:w8#data, bpW:w3:coords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:torus-analytic | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L339-L339 | fderiv via the complex derivative
EDGE: stepW:w6:t-an | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L339-L339 | holomorphy
EDGE: bpW:w8:ext-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L340-L340 | chain rule
EDGE: bpW:w3:flow | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L342-L342 | (iii) invertible, (iv) real
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L345-L345 | (ii), (iv)
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L340-L340 | the inverse transport tau_E^{-1} and its linearity
EDGE: bpW:w3:coords | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L341-L344 | Z^{-1} identifies fixed real points and is injective
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8Kshell_fderiv_injective, KAM.Wave.w8Kshell_leftInv, KAM.Wave.w8Kshell_leftInv_hasFDerivAt, KAM.Wave.w8_eq_zero_of_add_clm (KAM/Wave/Assembly/ShellEmbed.lean, KAM/Wave/Assembly/InjAssembly.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-embedding; W8 audit 2 PASS; Lean route differs (D1 of W8-FINAL: differentiable left inverse from birkGammaR_inv instead of invertibility of DGamma)
NOTE: -

NODE: bpW:w8:shell-close
KIND: lemma
TITLE: Closeness and size on one shell
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L355-L358
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L359-L378
CONTRACT_ID: bpW:w8:shell-close
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 0, xi in Gamma_n, theta in R^2; K^0_xi the linear torus
SOURCE_QUANTIFIERS: for all such n, xi, theta
SOURCE_CONCLUSION: ¦¦K^(n)_xi(theta) - tau_E K^0_xi(theta)¦¦ <= E_7 t_n^{33/64} and ¦¦K^(n)_xi(theta)¦¦ <= 2 rho_n
CONSTANT_SCOPE: E_7 depends on m only
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:Kshell, bpW:w8:const, stepW:w8:sc-tan, stepW:w8:sc-dist, stepW:w8:sc-gamma, stepW:w8:sc-close, stepW:w8:sc-size, bpW:w0:periodone#linearTorus
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:Kshell | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L357-L357 | K^(n)_xi
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L357-L357 | E_7
EDGE: stepW:w8:sc-tan | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L362-L362 | proof step
EDGE: stepW:w8:sc-dist | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L366-L366 | proof step
EDGE: stepW:w8:sc-gamma | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L370-L370 | proof step
EDGE: stepW:w8:sc-close | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L373-L373 | proof step
EDGE: stepW:w8:sc-size | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L376-L376 | proof step
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-close@L356-L356 | the linear torus K^0_I occurs directly here (frozen linearTorus)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellClose, KAM.Wave.w8_shellDist, KAM.Wave.w8_gammaR_bounds, KAM.Wave.w8_gamma_arith, KAM.Wave.w8_tan_arith (KAM/Wave/Assembly/ShellClose.lean)
LEAN_NOTE: W8 audit 2 PASS (same E_7 and 2 rho_n bounds; deviations D2, D3 of W8-FINAL: constant 1/4 + 2pi in sc-tan, extra sqrt2 in sc-gamma absorbed by the t exponent)
NOTE: -

NODE: stepW:w8:sc-tan
KIND: step
TITLE: Tangential modes
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-tan@L362-L365
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-tan@L362-L365
CONTRACT_ID: stepW:w8:sc-tan
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-close: n >= 0, xi in Gamma_n, theta in R^2; K^0_xi the linear torus
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-close (for all such n, xi, theta); within the step: i; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦w_{+-i} - w^0_{+-i}¦ <= (1 + 2pi) sqrt(t_n) e
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:torus-shape, bpW:w8:ext-sqrt, bpW:w8:ext-exp, bpW:w8:shell-data, bpW:w5:action-angle
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-tan@L362-L362 | (ii)
EDGE: bpW:w8:ext-sqrt | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-tan@L365-L365 | square roots
EDGE: bpW:w8:ext-exp | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-tan@L365-L365 | ¦e^{ix}-1¦ <= ¦x¦
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-tan@L365-L365 | (ii)
EDGE: bpW:w5:action-angle | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-tan@L361-L361 | (i) the linear torus
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellDist, KAM.Wave.w8_tanDiff_hasSum, KAM.Wave.w8_tanDiff_norm_le, KAM.Wave.w8_tan_weights (KAM/Wave/Assembly/ShellClose.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-close; W8 audit 2 PASS; constant (1/4 + 2pi) instead of (1 + 2pi) (D2)
NOTE: -

NODE: stepW:w8:sc-dist
KIND: step
TITLE: Phase-space distance
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-dist@L366-L369
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-dist@L366-L369
CONTRACT_ID: stepW:w8:sc-dist
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-close: n >= 0, xi in Gamma_n, theta in R^2; K^0_xi the linear torus
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-close (for all such n, xi, theta); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦x - x^0¦¦_E <= 162 sqrt(t_n) e
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:sc-tan, bpW:w8:torus-shape, bpW:w3:coords
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:sc-tan | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-dist@L367-L367 | tangential modes
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-dist@L368-L368 | (i)
EDGE: bpW:w3:coords | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-dist@L369-L369 | Z
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellDist, KAM.Wave.w8_coord_diff_le (KAM/Wave/Assembly/ShellClose.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-close; W8 audit 2 PASS (162 retained)
NOTE: -

NODE: stepW:w8:sc-gamma
KIND: step
TITLE: Birkhoff map
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L370-L372
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L370-L372
CONTRACT_ID: stepW:w8:sc-gamma
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-close: n >= 0, xi in Gamma_n, theta in R^2; K^0_xi the linear torus
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-close (for all such n, xi, theta); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦Gamma^R(x) - x¦¦_E <= E_6 t_n^{3/2}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:gamma-real, bpW:w1:embed, bpW:w8:torus-shape, bpW:w8:shell-data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L370-L370 | (ii)
EDGE: bpW:w1:embed | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L370-L370 | norm comparison
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L372-L372 | (v)
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L372-L372 | rho_n^2 <= 2 c_A t_n
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_gammaR_bounds, KAM.Wave.w8_gamma_arith (KAM/Wave/Assembly/ShellClose.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-close; W8 audit 2 PASS; Lean route differs (D3, through ||Z psi|| <= sqrt2 ||psi||)
NOTE: -

NODE: stepW:w8:sc-close
KIND: step
TITLE: Closeness
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L373-L375
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L373-L375
CONTRACT_ID: stepW:w8:sc-close
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-close: n >= 0, xi in Gamma_n, theta in R^2; K^0_xi the linear torus
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-close (for all such n, xi, theta); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the closeness bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w8:sc-dist, stepW:w8:sc-gamma, bpW:w8:etor, bpW:w0:periodone#linearTorus, bpW:w8#data, bpW:w8:const
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w8:sc-dist | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L374-L374 | distance
EDGE: stepW:w8:sc-gamma | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L374-L374 | Birkhoff map
EDGE: bpW:w8:etor | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L375-L375 | e
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L374-L374 | the linear torus K^0_I occurs directly here (frozen linearTorus)
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L373-L374 | tau_E is isometric
EDGE: bpW:w8:const | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L374-L375 | E_7 = 162 E_5 + E_6
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellClose, KAM.Wave.w8_birkPi_linearTorus (KAM/Wave/Assembly/ShellClose.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-close; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:sc-size
KIND: step
TITLE: Size
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L377
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L377
CONTRACT_ID: stepW:w8:sc-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-close: n >= 0, xi in Gamma_n, theta in R^2; K^0_xi the linear torus
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-close (for all such n, xi, theta); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦K^(n)_xi(theta)¦¦ < 2 rho_n
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:gamma-real, stepW:w8:sc-gamma, bpW:w8:torus-shape, bpW:w8#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L376 | rho_1^2 = 1/(160 C_F)
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L376 | (ii)
EDGE: stepW:w8:sc-gamma | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L377 | the cubic bound on Gamma^R(x)-x
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L377 | ¦¦x¦¦ < rho_n <= r_1 = rho_1/sqrt2
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L377-L377 | tau_E preserves the norm
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellClose, KAM.Wave.w8_tan_arith (KAM/Wave/Assembly/ShellClose.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-close; W8 audit 2 PASS
NOTE: -

NODE: bpW:w8:shell-inv
KIND: lemma
TITLE: Invariance and continuity on one shell
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L383-L392
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L393-L407
CONTRACT_ID: bpW:w8:shell-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: n >= 0
SOURCE_QUANTIFIERS: (i) for xi in Gamma_n, theta in R^2, j in N_+
SOURCE_CONCLUSION: (i) with K = K^(n)_xi, nu = nu^(n)_*(xi): t -> coeff (K(theta + t nu)).1 j has derivative lambda_j coeff (K theta).2 j at 0 and t -> coeff (K(theta + t nu)).2 j has derivative -lambda_j coeff (K theta).1 j - cubicGrad m hm (K theta).1 j at 0 (clause (4)); (ii) (xi,theta) -> K^(n)_xi(theta) is continuous on Gamma_n x R^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:Kshell, bpW:w8:shell-iter, stepW:w8:si-weak, stepW:w8:si-tr, stepW:w8:si-frozen, stepW:w8:si-cont, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:Kshell | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L386-L386 | K^(n)_xi
EDGE: bpW:w8:shell-iter | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L386-L386 | nu^(n)_*
EDGE: stepW:w8:si-weak | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L394-L394 | proof step
EDGE: stepW:w8:si-tr | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L398-L398 | proof step
EDGE: stepW:w8:si-frozen | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L400-L400 | proof step
EDGE: stepW:w8:si-cont | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L404-L404 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L388-L388 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L389-L389 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w8-assembly.tex#bpW:w8:shell-inv@L387-L387 | the frozen coeff occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellInv, KAM.Wave.w8_shellInvCont, KAM.Wave.w8ShellNu_eq, KAM.Wave.w8_birkEmbed_comp, KAM.Wave.w8_shellInv_of_birk, KAM.Wave.w8_shellInvCont_of_birk (KAM/Wave/Assembly/ShellFamily.lean, KAM/Wave/Assembly/ShellInv.lean)
LEAN_NOTE: W8 audit 1 FAIL (F1 w6-general constants/tori conjunct, F2 Kshell totalization, N1 partial labels), W8 audit 2 PASS WITH NOTES (F1, F2, N1 closed); W8 audit 2 PASS (full coefficient derivatives and joint continuity; the conditional reductions _of_birk are discharged by w8Psi_ball, W6 tori (ii)/(iii) and w8_birkEmbed_comp)
NOTE: -

NODE: stepW:w8:si-weak
KIND: step
TITLE: Weak invariance
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-weak@L394-L397
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-weak@L394-L397
CONTRACT_ID: stepW:w8:si-weak
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-inv: n >= 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-inv ((i) for xi in Gamma_n, theta in R^2, j in N_+); within the step: real theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Psi maps into B_{rho_1}, is differentiable into W, real, and D Psi nu = X_{H'}(Psi) in W_{a,p-1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w8:w6-general, bpW:w3:main
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-weak@L394-L394 | (i), (iii)
EDGE: bpW:w8:w6-general | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-weak@L394-L394 | transfer
EDGE: bpW:w3:main | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-weak@L397-L397 | H'
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6PrepHyp.w6Tori, KAM.Wave.w8Psi_ball, KAM.Wave.w8_birkEmbed_comp (KAM/Wave/Iteration/Tori.lean, KAM/Wave/Assembly/ShellTorus.lean, KAM/Wave/Assembly/ShellFamily.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-inv; W8 audit 2 PASS (W6 tori (iii))
NOTE: -

NODE: stepW:w8:si-tr
KIND: step
TITLE: Transport
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-tr@L398-L399
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-tr@L398-L399
CONTRACT_ID: stepW:w8:si-tr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-inv: n >= 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-inv ((i) for xi in Gamma_n, theta in R^2, j in N_+); within the step: theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the coefficient system along nu for (Q,P) = Z^{-1} Gamma o Psi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:transport-tori-weak, bpW:w0:eqmotion, stepW:w8:si-weak, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:transport-tori-weak | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-tr@L398-L398 | weak invariance is transported
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-tr@L398-L398 | (bpW:w0:coeffsys)
EDGE: stepW:w8:si-weak | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-tr@L398-L398 | its hypothesis
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-tr@L399-L399 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-tr@L399-L399 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellInv_of_birk, KAM.Wave.birk_transport_tori_weak_frozen_coord (KAM/Wave/Assembly/ShellInv.lean, KAM/Wave/Birkhoff/MainBallReal.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-inv; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:si-frozen
KIND: step
TITLE: Frozen form
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L403
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L403
CONTRACT_ID: stepW:w8:si-frozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-inv: n >= 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-inv ((i) for xi in Gamma_n, theta in R^2, j in N_+); within the step: theta, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i) in the frozen form
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:coordinatewise, bpW:w1:cubic-analytic, stepW:w8:si-tr, bpW:w8#data, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:coordinatewise | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L402-L402 | coordinates of the derivative
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L402-L402 | (iv)
EDGE: stepW:w8:si-tr | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L400 | the coefficient system
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L400 | tau_E and coeff
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L403-L403 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L402-L402 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L402 | kappa_{1,1} of each component of K is its frozen coeff
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellInv, KAM.Wave.w8KOfBirk_eq_gamma (KAM/Wave/Assembly/ShellFamily.lean, KAM/Wave/Assembly/ShellInv.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-inv; W8 audit 2 PASS
NOTE: -

NODE: stepW:w8:si-cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L404-L406
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L404-L406
CONTRACT_ID: stepW:w8:si-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-inv: n >= 0
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-inv ((i) for xi in Gamma_n, theta in R^2, j in N_+); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) continuity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w8:w6-general, bpW:w8:torus-shape, bpW:w3:gamma-real, bpW:w8#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L404-L404 | (ii)
EDGE: bpW:w8:w6-general | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L404-L404 | transfer
EDGE: bpW:w8:torus-shape | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L405-L405 | (v)
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L406-L406 | (i) Gamma^R analytic
EDGE: bpW:w8#data | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L405-L406 | Z^{-1} and tau_E are continuous linear
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w8_shellInvCont (KAM/Wave/Assembly/ShellFamily.lean)
LEAN_NOTE: step of PROVED parent bpW:w8:shell-inv; W8 audit 2 PASS
NOTE: -

NODE: bpW:w8#data
KIND: definition
TITLE: W8 standing data and notation
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#bpW:w8@L36-L53
PROOF_SOURCE: -
CONTRACT_ID: bpW:w8#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: m > 0 and the W0 conventions, a = p = 1; max norms on R^2, C^2; Leb = volume on Fin 2 -> R; Fin 2 index i is mode i+1; shells indexed by n, W6's iteration index mu; the exponent 52 of W5-W6; W3's rho_1, C_*, C'_K, C_F, Z, Gamma, Gamma^R, r_1 = rho_1/sqrt2; W5's c_A and A_xi; W6's s, sigma_P, s_0, sigma_0, M, gamma_0, gamma_1, gamma, c_F, c^natural_F, C^natural_2, t^natural = 53; W7's tau = 24, theta_0, alpha_0, C_7, L_A, N_A, omega^0, Omega^0; W2's M_m; the transport tau_E = tau_{1,1} x tau_{1,1} : E_{1,1} -> WaveSpace, a linear isometric bijection with inverse coeff in each factor; r(I) = sqrt(I_1 + I_2); linearTorus I hI = tau_E o K^0_I (independent of hI)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:mass, bpW:w3:main, bpW:w3:gamma-real, bpW:w3:coords, bpW:w5:action-angle, bpW:w6:constants, bpW:w7:constdef, bpW:w7:omega0, bpW:w7:freqcoords, bpW:w2:curve, bpW:w1:space, bpW:w0:ellap#coeff, bpW:w0:ellap#WaveSpace, bpW:w0:periodone#linearTorus, bpW:w3:majorant, bpW:w3:F, bpW:w5:data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:mass | blueprint-W/parts/w8-assembly.tex#bpW:w8@L36-L36 | m > 0
EDGE: bpW:w3:main | blueprint-W/parts/w8-assembly.tex#bpW:w8@L42-L42 | Gamma
EDGE: bpW:w3:gamma-real | blueprint-W/parts/w8-assembly.tex#bpW:w8@L42-L42 | Gamma^R
EDGE: bpW:w3:coords | blueprint-W/parts/w8-assembly.tex#bpW:w8@L41-L41 | Z
EDGE: bpW:w5:action-angle | blueprint-W/parts/w8-assembly.tex#bpW:w8@L43-L43 | c_A, A_xi
EDGE: bpW:w6:constants | blueprint-W/parts/w8-assembly.tex#bpW:w8@L45-L45 | W6's constants
EDGE: bpW:w7:constdef | blueprint-W/parts/w8-assembly.tex#bpW:w8@L47-L47 | W7's constants
EDGE: bpW:w7:omega0 | blueprint-W/parts/w8-assembly.tex#bpW:w8@L47-L47 | omega^0, Omega^0
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w8-assembly.tex#bpW:w8@L48-L48 | L_A, N_A
EDGE: bpW:w2:curve | blueprint-W/parts/w8-assembly.tex#bpW:w8@L48-L48 | M_m
EDGE: bpW:w1:space | blueprint-W/parts/w8-assembly.tex#bpW:w8@L50-L50 | (iv) tau_E isometric with inverse coeff
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w8-assembly.tex#bpW:w8@L50-L50 | coeff
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w8-assembly.tex#bpW:w8@L49-L49 | WaveSpace
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w8-assembly.tex#bpW:w8@L52-L52 | linearTorus = tau_E o K^0_I
EDGE: bpW:w3:majorant | blueprint-W/parts/w8-assembly.tex#bpW:w8@L40-L40 | C_*
EDGE: bpW:w3:F | blueprint-W/parts/w8-assembly.tex#bpW:w8@L40-L40 | C_F
EDGE: bpW:w5:data | blueprint-W/parts/w8-assembly.tex#bpW:w8@L45-L46 | the ordinary and preparatory step constants, summarized in the W5 ledger
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a
REVIEWER: sol-delta6-W-W-w8a
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled 'Standing data and notation' paragraph (SPEC hypothesis packages).
