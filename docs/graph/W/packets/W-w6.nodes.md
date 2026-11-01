NODE: bpW:w6:sequences
KIND: definition
TITLE: Iteration sequences
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:sequences@L31-L41
PROOF_SOURCE: -
CONTRACT_ID: bpW:w6:sequences
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; 0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0
SOURCE_QUANTIFIERS: s_0, r_0, alpha_0, M_0, eps_0
SOURCE_CONCLUSION: defines sigma_0 = s_0/40 and sigma_nu, s_nu, alpha_nu, M_nu, lambda_nu, eta_nu, r_nu, eps_nu, D_nu, gamma_0 = (2^{t+4} C_2 + c_0)^{-3}, K_0 = (96 pi gamma_0 sigma_0^t)^{-1/(tau+1)}, K_nu = K_0 2^nu, K_{-1} = 0; records s_nu decreasing to (3/4) s_0, sigma_nu <= min(1/4, s_nu/6), lambda_nu >= lambda_0/4, K_0 >= 1, K_nu >= 2^nu
CONSTANT_SCOPE: gamma_0, K_0 depend only on tau and W5's constants (and sigma_0)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6#data | blueprint-W/parts/w6-iteration.tex#bpW:w6:sequences@L36-L36 | C_2, c_0, t, tau
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6SeqData, KAM.Wave.W6SeqData.SeqValid, KAM.Wave.W6SeqData.sigma, KAM.Wave.W6SeqData.s, KAM.Wave.W6SeqData.alpha, KAM.Wave.W6SeqData.Mnu, KAM.Wave.W6SeqData.lam, KAM.Wave.W6SeqData.etaOf, KAM.Wave.W6SeqData.eps, KAM.Wave.W6SeqData.etaNu, KAM.Wave.W6SeqData.rNu, KAM.Wave.W6SeqData.qNu, KAM.Wave.W6SeqData.domNu, KAM.Wave.W6SeqData.K0, KAM.Wave.W6SeqData.K, KAM.Wave.W6SeqData.KprevNu, KAM.Wave.W6SeqData.sInfty, KAM.Wave.w6Gamma0, KAM.Wave.W6SeqData.s_antitone, KAM.Wave.W6SeqData.s_tendsto, KAM.Wave.W6SeqData.sInf_le_s, KAM.Wave.W6SeqData.sigma_le_min, KAM.Wave.W6SeqData.lam_ge, KAM.Wave.W6SeqData.one_le_K0, KAM.Wave.W6SeqData.two_pow_le_K (KAM/Wave/Iteration/Sequences.lean)
LEAN_NOTE: definition formalized by W6-PREP; W6 audit 1 (git show inp-w6aud:docs/tracks/W/audits/W6-audit-1.md) PASS (recurrences, tau = 24, t = 52, radii, cutoffs and limits), unchanged in W6 audit 2; 2^(-nu) written 1/2^nu, sigma^t as Real.rpow (deviation E3)
NOTE: -

NODE: bpW:w6:iter-lemma
KIND: lemma
TITLE: Iterative lemma
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L47-L67
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L68-L84
CONTRACT_ID: bpW:w6:iter-lemma
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; at stage nu: Pi_nu subset R^2; (omega_nu,Omega_nu) satisfying (bpW:w5:freq) with M_omega + M_Omega <= M_nu; (bpW:w6:melnikov) on Pi_nu for (k,l) in Z; a real periodic family P_nu in S_{p_+}(D_nu) with ¦X_{P_nu}¦^{lambda_nu}_{r_nu,D_nu} <= eps_nu; q_nu = eps_nu/(alpha_nu sigma_nu^t)
SOURCE_QUANTIFIERS: for every stage nu >= 0
SOURCE_CONCLUSION: q_nu <= gamma_0 2^{-nu}, q_{nu+1} <= q_nu/4; W5's step (unmodified) applies and yields Phi_{nu+1} : D_{nu+1} -> D_nu, N_{nu+1}, P_{nu+1} such that with Pi_{nu+1} = Pi_nu minus the zones R^{nu+1}_{kl} (¦k¦ > K_nu) all hypotheses hold at stage nu+1, provided (bpW:w6:melnikov) for k = 0 holds at nu+1; the transformation, derivative and frequency increment bounds (with M_{F,nu} = c_F q_nu sigma_nu)
CONSTANT_SCOPE: as in Definition bpW:w6:sequences
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:sequences, bpW:w5:w4-general, bpW:w7:indexdef, bpW:w5:class, bpW:w5:step, stepW:w6:il-small, stepW:w6:il-err, stepW:w6:il-lip, stepW:w6:il-div, stepW:w6:il-tr
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:sequences | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L48-L48 | the sequences
EDGE: bpW:w5:w4-general | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L50-L50 | (bpW:w5:freq)
EDGE: bpW:w7:indexdef | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L50-L50 | W7's index set Z and <l>
EDGE: bpW:w5:class | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L54-L54 | S_{p_+} and the lambda-norm
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L56-L56 | W5's step
EDGE: stepW:w6:il-small | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L69-L69 | proof step
EDGE: stepW:w6:il-err | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L72-L72 | proof step
EDGE: stepW:w6:il-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L76-L76 | proof step
EDGE: stepW:w6:il-div | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L79-L79 | proof step
EDGE: stepW:w6:il-tr | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L83-L83 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6Mel, KAM.Wave.w6_homMelnikov_of_mel, KAM.Wave.W6Stage, KAM.Wave.W6Stage.stageStepHyp, KAM.Wave.W6Stage.PhiN, KAM.Wave.W6Stage.PsiN, KAM.Wave.W6Stage.phiN_mapsTo, KAM.Wave.W6Stage.phiN_bounds, KAM.Wave.W6Stage.next_stage, KAM.Wave.W6Stage.omN_inc, KAM.Wave.W6Stage.OmN_inc, KAM.Wave.w6StepReal_holds, KAM.Wave.w6_mel_perturb, KAM.Wave.W6SeqData.w6Iter_q_bounds, KAM.Wave.W6Stage.w6IterLemma (KAM/Wave/Iteration/Bridge.lean, KAM/Wave/Iteration/Stage.lean, KAM/Wave/Iteration/IterLemma.lean, KAM/Wave/Iteration/IterArith.lean)
LEAN_NOTE: W6 audit 1 PASS for the arithmetic, step applicability, next stage and frequency increments, FAIL on the transformation clause (F1: ambient norms only); W6 audit 2 PASS (F1 closed: Phi_(nu+1) = id + iota Psi_(nu+1) with p_+ = 3/2 bounds 2 M_F,nu and 16 M_F,nu/sigma_nu including the lambda-Lipschitz parts, from W5's smooth_clause_v); reality discharged by w6StepReal_holds; low-mode Dirichlet divisors re-proved directly (w6_mel_perturb), see the audit note on step il-div
NOTE: -

NODE: stepW:w6:il-small
KIND: step
TITLE: Smallness
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-small@L69-L71
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-small@L69-L71
CONTRACT_ID: stepW:w6:il-small
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:iter-lemma: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; at stage nu: Pi_nu subset R^2; (omega_nu,Omega_nu) satisfying (bpW:w5:freq) with M_omega + M_Omega <= M_nu; (bpW:w6:melnikov) on Pi_nu for (k,l) in Z; a real periodic family P_nu in S_{p_+}(D_nu) with ¦X_{P_nu}¦^{lambda_nu}_{r_nu,D_nu} <= eps_nu; q_nu = eps_nu/(alpha_nu sigma_nu^t)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:iter-lemma (for every stage nu >= 0); within the step: nu; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: q_nu <= gamma_0 2^{-nu}; (bpW:w5:small) holds; Theorem bpW:w5:step applies
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:data, bpW:w4:wave
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:data | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-small@L70-L70 | (bpW:w5:small)
EDGE: bpW:w4:wave | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-small@L71-L71 | Dirichlet Melnikov conditions imply P96-K indexed conditions by wave(ii), as fixed at L26-L27
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: sol-delta6-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6SeqData.w6Iter_q_bounds, KAM.Wave.W6SeqData.eps_le_small, KAM.Wave.W6Stage.stageStepHyp (KAM/Wave/Iteration/IterArith.lean, KAM/Wave/Iteration/Stage.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:iter-lemma; W6 audit 1 PASS
NOTE: -

NODE: stepW:w6:il-err
KIND: step
TITLE: New error
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-err@L72-L75
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-err@L72-L75
CONTRACT_ID: stepW:w6:il-err
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:iter-lemma: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; at stage nu: Pi_nu subset R^2; (omega_nu,Omega_nu) satisfying (bpW:w5:freq) with M_omega + M_Omega <= M_nu; (bpW:w6:melnikov) on Pi_nu for (k,l) in Z; a real periodic family P_nu in S_{p_+}(D_nu) with ¦X_{P_nu}¦^{lambda_nu}_{r_nu,D_nu} <= eps_nu; q_nu = eps_nu/(alpha_nu sigma_nu^t)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:iter-lemma (for every stage nu >= 0); within the step: nu; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦X_{P_{nu+1}}¦ <= eps_{nu+1} and q_{nu+1} <= q_nu/4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step, stepW:w6:il-small
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-err@L72-L72 | (ii) (bpW:w5:newerror)
EDGE: stepW:w6:il-small | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-err@L74-L74 | q_nu <= gamma_0
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6SeqData.eps_succ_le, KAM.Wave.W6SeqData.lam_succ_le, KAM.Wave.W6Stage.w6_newerror_eq, KAM.Wave.W6Stage.w6IterLemma (KAM/Wave/Iteration/IterArith.lean, KAM/Wave/Iteration/IterLemma.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:iter-lemma; W6 audit 1 PASS
NOTE: -

NODE: stepW:w6:il-lip
KIND: step
TITLE: Lipschitz constants
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-lip@L76-L78
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-lip@L76-L78
CONTRACT_ID: stepW:w6:il-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:iter-lemma: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; at stage nu: Pi_nu subset R^2; (omega_nu,Omega_nu) satisfying (bpW:w5:freq) with M_omega + M_Omega <= M_nu; (bpW:w6:melnikov) on Pi_nu for (k,l) in Z; a real periodic family P_nu in S_{p_+}(D_nu) with ¦X_{P_nu}¦^{lambda_nu}_{r_nu,D_nu} <= eps_nu; q_nu = eps_nu/(alpha_nu sigma_nu^t)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:iter-lemma (for every stage nu >= 0); within the step: nu; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the Lipschitz constants stay <= M_{nu+1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-lip@L76-L76 | (iii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6SeqData.lip_growth_le, KAM.Wave.W6SeqData.M_growth_le, KAM.Wave.W6Stage.w6IterLemma (KAM/Wave/Iteration/IterArith.lean, KAM/Wave/Iteration/IterLemma.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:iter-lemma; W6 audit 1 PASS
NOTE: -

NODE: stepW:w6:il-div
KIND: step
TITLE: Divisors
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-div@L79-L82
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-div@L79-L82
CONTRACT_ID: stepW:w6:il-div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:iter-lemma: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; at stage nu: Pi_nu subset R^2; (omega_nu,Omega_nu) satisfying (bpW:w5:freq) with M_omega + M_Omega <= M_nu; (bpW:w6:melnikov) on Pi_nu for (k,l) in Z; a real periodic family P_nu in S_{p_+}(D_nu) with ¦X_{P_nu}¦^{lambda_nu}_{r_nu,D_nu} <= eps_nu; q_nu = eps_nu/(alpha_nu sigma_nu^t)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:iter-lemma (for every stage nu >= 0); within the step: nu; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (bpW:w6:melnikov) at nu+1 on Pi_nu for 0 < ¦k¦ <= K_nu, and on Pi_{nu+1} for ¦k¦ > K_nu by construction
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-div@L81-L81 | (iv) divisors
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6SeqData.div_arith, KAM.Wave.w6_mel_perturb, KAM.Wave.W6Stage.next_stage (KAM/Wave/Iteration/IterArith.lean, KAM/Wave/Iteration/IterLemma.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:iter-lemma; W6 audit 1 PASS; Lean route differs: the stage nu+1 Dirichlet-weight divisor bound is re-proved by a direct perturbation argument (w6_mel_perturb) instead of being taken from W5's weaker bracket (audit note on the blueprint attribution)
NOTE: -

NODE: stepW:w6:il-tr
KIND: step
TITLE: Transformations
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-tr@L83-L83
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:il-tr@L83-L83
CONTRACT_ID: stepW:w6:il-tr
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:iter-lemma: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; at stage nu: Pi_nu subset R^2; (omega_nu,Omega_nu) satisfying (bpW:w5:freq) with M_omega + M_Omega <= M_nu; (bpW:w6:melnikov) on Pi_nu for (k,l) in Z; a real periodic family P_nu in S_{p_+}(D_nu) with ¦X_{P_nu}¦^{lambda_nu}_{r_nu,D_nu} <= eps_nu; q_nu = eps_nu/(alpha_nu sigma_nu^t)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:iter-lemma (for every stage nu >= 0); within the step: nu; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the transformation bounds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-tr@L83-L83 | (v)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6Stage.PsiN, KAM.Wave.W6Stage.phiN_bounds, KAM.Wave.W6SeqData.transf_arith (KAM/Wave/Iteration/IterLemma.lean, KAM/Wave/Iteration/IterArith.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:iter-lemma; W6 audit 1 FAIL (F1), W6 audit 2 PASS (p_+ bounds)
NOTE: -

NODE: bpW:w6:k0
KIND: lemma
TITLE: The conditions with $k=0$
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:k0@L89-L93
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:k0@L94-L98
CONTRACT_ID: bpW:w6:k0
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Lemma bpW:w6:iter-lemma; ¦<l,Omega_0>¦ >= 2 beta_0 <l> for l in Lambda on Pi_0, beta_0 >= alpha_0, 8 eps_0 <= beta_0
SOURCE_QUANTIFIERS: for every nu
SOURCE_CONCLUSION: (bpW:w6:melnikov) with k = 0 holds on Pi_nu, and sup_j (j+2)^{1/2}¦Omega_{nu,j} - Omega_{0,j}¦ <= sum_{mu<nu} 3 eps_mu <= 4 eps_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:iter-lemma, bpW:w7:indexdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:iter-lemma | blueprint-W/parts/w6-iteration.tex#bpW:w6:k0@L90-L90 | the setting and the increments
EDGE: bpW:w7:indexdef | blueprint-W/parts/w6-iteration.tex#bpW:w6:k0@L90-L90 | Lambda and <l>
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6SeqData.w6K0_of_increments, KAM.Wave.w6Seq_k0 (KAM/Wave/Iteration/K0.lean, KAM/Wave/Iteration/Sequence.lean)
LEAN_NOTE: W6 audit 1 (git show inp-w6aud:docs/tracks/W/audits/W6-audit-1.md) PASS; stated in the inductive form at stage nu with the increment bounds of the earlier stages as hypotheses (deviation E1: what the iterative lemma supplies; no current-stage bound assumed), and along the actual iteration in w6Seq_k0
NOTE: Inline proof (L94-L98).

NODE: bpW:w6:convergence
KIND: proposition
TITLE: Iteration and convergence; P96-K Theorem~A, proof
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L103-L133
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L134-L161
CONTRACT_ID: bpW:w6:convergence
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; Pi_{-1} subset R^2; (omega_0,Omega_0) on Pi_{-1} with (bpW:w5:freq), M_omega + M_Omega <= M_0; the k = 0 bound of Lemma bpW:w6:k0 on Pi_{-1}; a real periodic family P_0 in S_{p_+}(D_0) with ¦X_{P_0}¦^{lambda_0} <= eps_0; Pi_0, Pi_nu, Pi_* = cap Pi_nu, Phi^nu = Phi_1 o ... o Phi_nu
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: (i) Pi_{-1} minus Pi_* is the union of the zones R^nu_{kl} (¦k¦ > K_{nu-1}); Borel if Pi_{-1} is Borel and the frequencies continuous; (ii) omega_nu -> omega_*, Omega_nu -> Omega_* uniformly on Pi_* with ¦omega_* - omega_0¦ <= 8 pi eps_0, Lipschitz <= 64 pi eps_0/lambda_0, sup (j+2)^{1/2}¦Omega_* - Omega_0¦ <= 4 eps_0 (Lipschitz <= 16 eps_0/lambda_0), and ¦<k,omega_*> + <l,Omega_*>¦ >= (alpha_0/2)<l>/A_k on Pi_*; (iii) theta -> Phi^nu(iota theta) converge uniformly on T_{s_infty} x Pi_* to Phi_*, holomorphic, periodic, real, jointly continuous, with values in closure D(s_0-4sigma_0,2 eta_0 r_0) and ¦Phi_* - iota¦_{p_+,r_0} <= e_Phi = 5 c_F eps_0/(alpha_0 sigma_0^{t-1}); derivatives converge on T_{s_0/2}; (iv) ¦D Phi^nu(w) W¦_{q,r_0} <= 2¦W¦_{q,r_nu}, D Phi^nu symplectic and onto P^{p_+}
CONSTANT_SCOPE: e_Phi explicit
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:sequences, bpW:w6:k0, bpW:w6:iter-lemma, stepW:w6:c-ind, stepW:w6:c-par, stepW:w6:c-freq, stepW:w6:c-dom, stepW:w6:c-op, stepW:w6:c-cauchy, stepW:w6:c-lim, stepW:w6:c-cont
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:sequences | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L104-L104 | the sequences
EDGE: bpW:w6:k0 | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L106-L106 | the k = 0 bound
EDGE: bpW:w6:iter-lemma | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L109-L109 | Pi_nu
EDGE: stepW:w6:c-ind | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L135-L135 | proof step
EDGE: stepW:w6:c-par | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L137-L137 | proof step
EDGE: stepW:w6:c-freq | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L139-L139 | proof step
EDGE: stepW:w6:c-dom | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L143-L143 | proof step
EDGE: stepW:w6:c-op | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L147-L147 | proof step
EDGE: stepW:w6:c-cauchy | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L151-L151 | proof step
EDGE: stepW:w6:c-lim | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L155-L155 | proof step
EDGE: stepW:w6:c-cont | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L158-L158 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6ConvHyp, KAM.Wave.w6Seq, KAM.Wave.w6Seq_stage, KAM.Wave.w6Seq_Pi_eq, KAM.Wave.w6PiStarIt, KAM.Wave.w6PiStarIt_eq, KAM.Wave.w6ConvParams, KAM.Wave.w6ConvBorel, KAM.Wave.w6OmStar, KAM.Wave.w6OmStar7, KAM.Wave.w6ConvFreq, KAM.Wave.w6_divisor_limit, KAM.Wave.W6SeqData.ePhi, KAM.Wave.w6PsiStar, KAM.Wave.w6PhiStar, KAM.Wave.W6ConvTorusClause, KAM.Wave.w6ConvTorus, KAM.Wave.w6ConvOpsSrc, KAM.Wave.w6StepSmooth_holds (KAM/Wave/Iteration/Sequence.lean, KAM/Wave/Iteration/ConvSource.lean, KAM/Wave/Iteration/ConvFreq.lean, KAM/Wave/Iteration/Limits.lean, KAM/Wave/Iteration/ConvArith.lean, KAM/Wave/Iteration/ConvCauchy.lean, KAM/Wave/Iteration/ConvMaps.lean, KAM/Wave/Iteration/SmoothSrc.lean, KAM/Wave/Iteration/StepSmoothW5.lean)
LEAN_NOTE: W6 audit 1 PASS ((i)), PASS WITH NOTES ((ii): coordinatewise uniform normal-frequency convergence plus uniform weighted drift bounds; (iii), (iv) conditional on W6StepSmooth); W6 audit 2 PASS (W6StepSmooth discharged by w6StepSmooth_holds; unconditional w6ConvTorus, w6ConvOpsSrc); (i) for arbitrary frequency sequences (deviation E2), instantiated on the iteration by w6ConvParams; Lipschitz bound 32 pi eps_0/lambda_0 proved, stronger than the stated 64
NOTE: -

NODE: stepW:w6:c-ind
KIND: step
TITLE: Induction
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-ind@L135-L136
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-ind@L135-L136
CONTRACT_ID: stepW:w6:c-ind
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:convergence: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; Pi_{-1} subset R^2; (omega_0,Omega_0) on Pi_{-1} with (bpW:w5:freq), M_omega + M_Omega <= M_0; the k = 0 bound of Lemma bpW:w6:k0 on Pi_{-1}; a real periodic family P_0 in S_{p_+}(D_0) with ¦X_{P_0}¦^{lambda_0} <= eps_0; Pi_0, Pi_nu, Pi_* = cap Pi_nu, Phi^nu = Phi_1 o ... o Phi_nu
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:convergence (for all such data); within the step: nu; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: all stages exist; eps_nu <= 4^{-nu} eps_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:k0, bpW:w6:iter-lemma
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:k0 | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-ind@L136-L136 | k = 0
EDGE: bpW:w6:iter-lemma | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-ind@L136-L136 | induction
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6Seq_stage, KAM.Wave.w6Seq_k0, KAM.Wave.W6SeqData.eps_le_four_pow (KAM/Wave/Iteration/Sequence.lean, KAM/Wave/Iteration/IterArith.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:convergence; W6 audit 1 PASS
NOTE: -

NODE: stepW:w6:c-par
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-par@L137-L138
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-par@L137-L138
CONTRACT_ID: stepW:w6:c-par
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:convergence: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; Pi_{-1} subset R^2; (omega_0,Omega_0) on Pi_{-1} with (bpW:w5:freq), M_omega + M_Omega <= M_0; the k = 0 bound of Lemma bpW:w6:k0 on Pi_{-1}; a real periodic family P_0 in S_{p_+}(D_0) with ¦X_{P_0}¦^{lambda_0} <= eps_0; Pi_0, Pi_nu, Pi_* = cap Pi_nu, Phi^nu = Phi_1 o ... o Phi_nu
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:convergence (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i) and Borel measurability
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:ext-borel
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:ext-borel | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-par@L138-L138 | relatively open zones in a Borel set
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6ConvParams, KAM.Wave.w6ConvBorel, KAM.Wave.w6PiSeq_measurableSet (KAM/Wave/Iteration/ConvSource.lean, KAM/Wave/Iteration/Params.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:convergence; W6 audit 1 PASS
NOTE: -

NODE: stepW:w6:c-freq
KIND: step
TITLE: Frequencies
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-freq@L139-L142
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-freq@L139-L142
CONTRACT_ID: stepW:w6:c-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:convergence: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; Pi_{-1} subset R^2; (omega_0,Omega_0) on Pi_{-1} with (bpW:w5:freq), M_omega + M_Omega <= M_0; the k = 0 bound of Lemma bpW:w6:k0 on Pi_{-1}; a real periodic family P_0 in S_{p_+}(D_0) with ¦X_{P_0}¦^{lambda_0} <= eps_0; Pi_0, Pi_nu, Pi_* = cap Pi_nu, Phi^nu = Phi_1 o ... o Phi_nu
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:convergence (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) by summing the increments; the divisor bound in the limit
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:iter-lemma
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:iter-lemma | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-freq@L139-L139 | the increments
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6ConvFreq, KAM.Wave.W6SeqData.freq_sum_le, KAM.Wave.W6SeqData.freq_lip_sum_le, KAM.Wave.w6_divisor_limit (KAM/Wave/Iteration/ConvSource.lean, KAM/Wave/Iteration/ConvArith.lean, KAM/Wave/Iteration/Limits.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:convergence; W6 audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w6:c-dom
KIND: step
TITLE: Domains
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-dom@L143-L146
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-dom@L143-L146
CONTRACT_ID: stepW:w6:c-dom
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:convergence: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; Pi_{-1} subset R^2; (omega_0,Omega_0) on Pi_{-1} with (bpW:w5:freq), M_omega + M_Omega <= M_0; the k = 0 bound of Lemma bpW:w6:k0 on Pi_{-1}; a real periodic family P_0 in S_{p_+}(D_0) with ¦X_{P_0}¦^{lambda_0} <= eps_0; Pi_0, Pi_nu, Pi_* = cap Pi_nu, Phi^nu = Phi_1 o ... o Phi_nu
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:convergence (for all such data); within the step: nu; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Phi^nu is defined, holomorphic, real and equivariant on D_nu
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-dom@L143-L143 | (i), the image domain
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6Compose_main, KAM.Wave.w6Compose_real_periodic, KAM.Wave.w6IterHyp_src (KAM/Wave/Iteration/ComposeMaps.lean, KAM/Wave/Iteration/SmoothSrc.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:convergence; W6 audit 1 PASS WITH NOTES (conditional), W6 audit 2 PASS (w6IterHyp_src unconditional)
NOTE: -

NODE: stepW:w6:c-op
KIND: step
TITLE: Operator bounds
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L147-L150
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L147-L150
CONTRACT_ID: stepW:w6:c-op
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:convergence: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; Pi_{-1} subset R^2; (omega_0,Omega_0) on Pi_{-1} with (bpW:w5:freq), M_omega + M_Omega <= M_0; the k = 0 bound of Lemma bpW:w6:k0 on Pi_{-1}; a real periodic family P_0 in S_{p_+}(D_0) with ¦X_{P_0}¦^{lambda_0} <= eps_0; Pi_0, Pi_nu, Pi_* = cap Pi_nu, Phi^nu = Phi_1 o ... o Phi_nu
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:convergence (for all such data); within the step: W; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) operator bounds, symplecticity, surjectivity on P^{p_+}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:iter-lemma, bpW:w5:omega, bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:iter-lemma | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L148-L148 | derivative bounds
EDGE: bpW:w5:omega | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L148-L148 | norm comparison
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L150-L150 | (i)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6ConvOpsSrc, KAM.Wave.w6Compose_ops, KAM.Wave.w6prod_le_two (KAM/Wave/Iteration/SmoothSrc.lean, KAM/Wave/Iteration/ComposeMaps.lean, KAM/Wave/Iteration/ConvArith.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:convergence; W6 audit 2 PASS (unconditional w6ConvOpsSrc)
NOTE: -

NODE: stepW:w6:c-cauchy
KIND: step
TITLE: Cauchy sequence
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cauchy@L151-L153
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cauchy@L151-L153
CONTRACT_ID: stepW:w6:c-cauchy
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:convergence: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; Pi_{-1} subset R^2; (omega_0,Omega_0) on Pi_{-1} with (bpW:w5:freq), M_omega + M_Omega <= M_0; the k = 0 bound of Lemma bpW:w6:k0 on Pi_{-1}; a real periodic family P_0 in S_{p_+}(D_0) with ¦X_{P_0}¦^{lambda_0} <= eps_0; Pi_0, Pi_nu, Pi_* = cap Pi_nu, Phi^nu = Phi_1 o ... o Phi_nu
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:convergence (for all such data); within the step: theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦Phi^{nu+1}(iota theta) - Phi^nu(iota theta)¦_{p_+,r_0} <= 4 c_F q_nu sigma_nu, summing to e_Phi
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w6:c-op, bpW:w6:iter-lemma, bpW:w3:ext-integral, stepW:w6:il-err
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w6:c-op | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cauchy@L152-L152 | (iv)
EDGE: bpW:w6:iter-lemma | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cauchy@L152-L152 | transformation bounds
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cauchy@L151-L151 | the fundamental theorem along the segment w_tau
EDGE: stepW:w6:il-err | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cauchy@L153-L153 | q_nu <= 4^{-nu} q_0 gives the 8^{-nu} summation with sigma_nu
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: sol-delta6-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6PsiC_cauchy, KAM.Wave.W6SeqData.cauchy_sum_le, KAM.Wave.W6SeqData.cauchy_tail_le (KAM/Wave/Iteration/ConvCauchy.lean, KAM/Wave/Iteration/ConvArith.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:convergence; W6 audit 1 PASS WITH NOTES, W6 audit 2 PASS (smoothing discharged)
NOTE: -

NODE: stepW:w6:c-lim
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-lim@L154-L157
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-lim@L154-L157
CONTRACT_ID: stepW:w6:c-lim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:convergence: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; Pi_{-1} subset R^2; (omega_0,Omega_0) on Pi_{-1} with (bpW:w5:freq), M_omega + M_Omega <= M_0; the k = 0 bound of Lemma bpW:w6:k0 on Pi_{-1}; a real periodic family P_0 in S_{p_+}(D_0) with ¦X_{P_0}¦^{lambda_0} <= eps_0; Pi_0, Pi_nu, Pi_* = cap Pi_nu, Phi^nu = Phi_1 o ... o Phi_nu
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:convergence (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the limit Phi_* is holomorphic, periodic, real; derivatives converge; image bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:uniform-limit, stepW:w6:c-cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:uniform-limit | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-lim@L155-L155 | holomorphy of the uniform limit
EDGE: stepW:w6:c-cauchy | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-lim@L154-L154 | Cauchy sequence
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6PsiStar, KAM.Wave.w6PhiStar, KAM.Wave.w6ConvTorus (KAM/Wave/Iteration/ConvCauchy.lean, KAM/Wave/Iteration/SmoothSrc.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:convergence; W6 audit 2 PASS (unconditional w6ConvTorus)
NOTE: -

NODE: stepW:w6:c-cont
KIND: step
TITLE: Continuity in $\xi$
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cont@L158-L160
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cont@L158-L160
CONTRACT_ID: stepW:w6:c-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:convergence: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2; Pi_{-1} subset R^2; (omega_0,Omega_0) on Pi_{-1} with (bpW:w5:freq), M_omega + M_Omega <= M_0; the k = 0 bound of Lemma bpW:w6:k0 on Pi_{-1}; a real periodic family P_0 in S_{p_+}(D_0) with ¦X_{P_0}¦^{lambda_0} <= eps_0; Pi_0, Pi_nu, Pi_* = cap Pi_nu, Phi^nu = Phi_1 o ... o Phi_nu
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:convergence (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: joint continuity in (theta,xi)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow, stepW:w6:c-cauchy
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cont@L158-L158 | (i) Lipschitz in xi
EDGE: stepW:w6:c-cauchy | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cont@L159-L159 | the uniform convergence used to pass joint continuity to the limit
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: sol-delta6-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6ConvTorus, KAM.Wave.W6ConvTorusClause (KAM/Wave/Iteration/SmoothSrc.lean, KAM/Wave/Iteration/ConvMaps.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:convergence; joint continuity is a clause of W6ConvTorusClause; W6 audit 2 PASS
NOTE: -

NODE: bpW:w6:strong
KIND: lemma
TITLE: Strong conjugacy at regular points
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:strong@L170-L175
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:strong@L176-L179
CONTRACT_ID: bpW:w6:strong
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; Phi : O -> P C^1 on open O with D Phi(w) symplectic and onto P^{p_+} from P^{p_+}; H, H_+ with fields X_H : Phi(O) -> P^{p-1}, X_{H_+} : O -> P^{p-1} and varpi(X_H(Phi w), D Phi(w) W) = varpi(X_{H_+}(w), W) for W in P^{p_+}; X_{H_+}(w) in P
SOURCE_QUANTIFIERS: for such Phi, H, H_+, w
SOURCE_CONCLUSION: X_H(Phi w) = D Phi(w) X_{H_+}(w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:setting, stepW:w5:omnd
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:setting | blueprint-W/parts/w6-iteration.tex#bpW:w6:strong@L171-L171 | P, varpi
EDGE: stepW:w5:omnd | blueprint-W/parts/w6-iteration.tex#bpW:w6:strong@L178-L178 | test with unit vectors
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6Strong_core, KAM.Wave.w6StrongConj, KAM.Wave.stepTheorem_strong, KAM.Wave.w6StrongConjK (KAM/Wave/Iteration/Strong.lean, KAM/Wave/Iteration/StrongConj.lean, KAM/Wave/Iteration/Invariance.lean)
LEAN_NOTE: W6 audit 1 (git show inp-w6aud:docs/tracks/W/audits/W6-audit-1.md) PASS (pointwise strengthening: symplecticity, onto and weak pairing are the source premises; weight embeddings and nondegeneracy in the right spaces), unchanged in W6 audit 2
NOTE: -

NODE: bpW:w6:invariance
KIND: proposition
TITLE: Invariant tori in KAM coordinates
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L182-L187
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L188-L204
CONTRACT_ID: bpW:w6:invariance
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Proposition bpW:w6:convergence; H_0 = N_0 + P_0; nu_* = omega_*/(2pi); X_{N_0}(w) = (omega_0/(2pi), 0, Omega_0 v, -Omega_0 u)
SOURCE_QUANTIFIERS: for xi in Pi_* and theta in T_{s_0/2}
SOURCE_CONCLUSION: X_{H_0}(Phi_*(theta)) = d_theta Phi_*(theta) nu_* in P^{p-1}, and both sides lie in P
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:convergence, stepW:w6:i-weak, stepW:w6:i-torus, stepW:w6:i-lim
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L183-L183 | Phi_*, omega_*
EDGE: stepW:w6:i-weak | blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L189-L189 | proof step
EDGE: stepW:w6:i-torus | blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L197-L197 | proof step
EDGE: stepW:w6:i-lim | blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L200-L200 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6Invariance, KAM.Wave.w6InvarianceIt, KAM.Wave.w6Compose_weak, KAM.Wave.w6Invariance_step, KAM.Wave.w6NuVec (KAM/Wave/Iteration/SmoothSrc.lean, KAM/Wave/Iteration/Invariance.lean, KAM/Wave/Iteration/ComposeMaps.lean)
LEAN_NOTE: W6 audit 1 PASS WITH NOTES (conditional on W6StepSmooth), W6 audit 2 PASS (unconditional w6Invariance); weak conjugacy in p-1; nu_* = omega_*/(2 pi)
NOTE: -

NODE: stepW:w6:i-weak
KIND: step
TITLE: Weak chain
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L189-L196
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L189-L196
CONTRACT_ID: stepW:w6:i-weak
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:invariance: the setting of Proposition bpW:w6:convergence; H_0 = N_0 + P_0; nu_* = omega_*/(2pi); X_{N_0}(w) = (omega_0/(2pi), 0, Omega_0 v, -Omega_0 u)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:invariance (for xi in Pi_* and theta in T_{s_0/2}); within the step: nu, w, W; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: varpi(X_{H_0}(Phi^nu w), D Phi^nu W) = varpi(X_{H_nu}(w), W)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step, bpW:w6:convergence, stepW:w5:n-conj
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L190-L190 | (i)
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L193-L193 | (iv)
EDGE: stepW:w5:n-conj | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L193-L193 | derivative formulas
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6Compose_weak (KAM/Wave/Iteration/ComposeMaps.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:invariance; W6 audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w6:i-torus
KIND: step
TITLE: Torus points
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-torus@L197-L199
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-torus@L197-L199
CONTRACT_ID: stepW:w6:i-torus
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:invariance: the setting of Proposition bpW:w6:convergence; H_0 = N_0 + P_0; nu_* = omega_*/(2pi); X_{N_0}(w) = (omega_0/(2pi), 0, Omega_0 v, -Omega_0 u)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:invariance (for xi in Pi_* and theta in T_{s_0/2}); within the step: theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: at torus points the strong identity holds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:strong, bpW:w6:convergence, stepW:w6:i-weak
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:strong | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-torus@L198-L198 | strong conjugacy
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-torus@L198-L198 | (iv)
EDGE: stepW:w6:i-weak | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-torus@L198-L198 | weak chain
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6Invariance_step, KAM.Wave.w6StrongConjK, KAM.Wave.w6Field_torus (KAM/Wave/Iteration/Invariance.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:invariance; W6 audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w6:i-lim
KIND: step
TITLE: Limit
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-lim@L200-L203
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:i-lim@L200-L203
CONTRACT_ID: stepW:w6:i-lim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:invariance: the setting of Proposition bpW:w6:convergence; H_0 = N_0 + P_0; nu_* = omega_*/(2pi); X_{N_0}(w) = (omega_0/(2pi), 0, Omega_0 v, -Omega_0 u)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:invariance (for xi in Pi_* and theta in T_{s_0/2}); within the step: theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: passage to the limit in P^{p-1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:lie, bpW:w6:convergence, stepW:w6:i-torus
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lie | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-lim@L202-L202 | (i) X_{N_0} bounded
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-lim@L200-L200 | (ii), (iii)
EDGE: stepW:w6:i-torus | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-lim@L200-L200 | identity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6InvarianceIt, KAM.Wave.w6Invariance (KAM/Wave/Iteration/Invariance.lean, KAM/Wave/Iteration/SmoothSrc.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:invariance; W6 audit 2 PASS
NOTE: -

NODE: bpW:w6:constants
KIND: definition
TITLE: W6 constants
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:constants@L211-L218
PROOF_SOURCE: -
CONTRACT_ID: bpW:w6:constants
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; W7's constants (Definition bpW:w7:constdef) and W5's
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines s = 1/8, sigma_P = s/40, s_0 = (7/8)s, sigma_0 = s_0/40, M = M_omega + M_Omega of Lemma bpW:w4:wave(i), M_0 = 2M, gamma_0, gamma_1 = min{gamma_0 sigma_0^t, theta_0/(425(1+M)), beta_*/8}, gamma = min{1/40, (c^natural_0)^{-3} sigma_P^{t^natural}, theta_0/(425(1+M)), (gamma_1 sigma_P^{t^natural/3}/(2 C^natural_2))^{3/4}}; all depend on m only
CONSTANT_SCOPE: all depend on m only (through M, theta_0, beta_*)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:constdef, bpW:w4:wave, bpW:w6:sequences, bpW:w6#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:constdef | blueprint-W/parts/w6-iteration.tex#bpW:w6:constants@L212-L212 | W7's constants theta_0, beta_*
EDGE: bpW:w4:wave | blueprint-W/parts/w6-iteration.tex#bpW:w6:constants@L213-L213 | (i) M
EDGE: bpW:w6:sequences | blueprint-W/parts/w6-iteration.tex#bpW:w6:constants@L214-L214 | gamma_0
EDGE: bpW:w6#data | blueprint-W/parts/w6-iteration.tex#bpW:w6:constants@L216-L216 | c^natural_0, C^natural_2, t^natural
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6S, KAM.Wave.w6SigmaP, KAM.Wave.w6S0, KAM.Wave.w6Sigma0, KAM.Wave.w6M, KAM.Wave.w6M0, KAM.Wave.w6Gamma0, KAM.Wave.w6Gamma1, KAM.Wave.w6Gamma, KAM.Wave.w6Theta, KAM.Wave.w6Tn, KAM.Wave.w6CFn, KAM.Wave.w6C0n, KAM.Wave.w6C2n, KAM.Wave.w6Gamma_pos, KAM.Wave.w6Gamma1_pos (KAM/Wave/Iteration/Constants.lean, KAM/Wave/Iteration/Sequences.lean)
LEAN_NOTE: definition formalized by W6-PREP; W6 audit 1 (git show inp-w6aud:docs/tracks/W/audits/W6-audit-1.md) PASS (nested minima match, s_0 = 7/64, modified exponent 53); depend on m only
NOTE: -

NODE: bpW:w6:prep-step
KIND: lemma
TITLE: Preparatory step; P96-K \S6
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L220-L245
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L246-L271
CONTRACT_ID: bpW:w6:prep-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; constants of Definition bpW:w6:constants; Pi subset {¦xi¦_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, ¦X_P¦^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: one step of Theorem bpW:w5:step in the modified case (beta = 1/4, p_+ = p + 1/2, level hat alpha) applies on Pi minus Xi and gives Phi_P : D_0 = D(s_0,r_0) -> D(s,r) symplectic, real, holomorphic, with D Phi_P mapping P^{p_+} onto itself, with (N + P) o Phi_P = N_0 + P_0 + const and the weak conjugacy, and (i) for xi in Pi minus Xi and (k,l) in Z, ¦<k,omega^0> + <l,Omega^0>¦ >= hat alpha hat w(l)/A_k by Definition bpW:w7:zones(i), giving the modified bound with beta = 1/4 for difference modes and (H_hat alpha) otherwise via the Dirichlet-to-P96-K weight comparison of bpW:w4:wave(ii); (ii) the frequency shift bounds and (bpW:w5:freq) with M_omega + M_Omega <= 2M; (iii) ¦Phi_P - id¦_{p_+,r,D_0} <= M_{F,P} and Lipschitz in xi; (iv) sup ¦X_{P_0}¦_{p_+,r_0,D_0} <= eps^flat_0 = 2 C^natural_2 eps^{4/3}(hat alpha sigma_P^{t^natural})^{-1/3} <= gamma_1 check alpha; (v) ¦X_{P_0}¦^{lambda_0}_{r_0,D_0} <= eps^flat_0 with lambda_0 = check alpha/M_0
CONSTANT_SCOPE: as in Definition bpW:w6:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:constants, bpW:w7:constdef, bpW:w7:zones, bpW:w7:omega0, bpW:w5:class, bpW:w5:step, bpW:w5:new-ham, stepW:w6:p-data, stepW:w6:p-div, stepW:w6:p-step, stepW:w6:p-lipp, stepW:w6:p-size, stepW:w6:p-gap, bpW:w4:wave
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:constants | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L220-L220 | s, sigma_P, gamma, gamma_1
EDGE: bpW:w7:constdef | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L221-L221 | (C4) alpha_0
EDGE: bpW:w7:zones | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L222-L222 | the preparatory set Xi
EDGE: bpW:w7:omega0 | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L223-L223 | the unperturbed frequencies
EDGE: bpW:w5:class | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L223-L223 | S_{p+1} and the lambda-norm
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L228-L228 | W5's step (modified)
EDGE: bpW:w5:new-ham | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L230-L230 | (iii) weak conjugacy
EDGE: stepW:w6:p-data | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L247-L247 | proof step
EDGE: stepW:w6:p-div | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L250-L252 | proof step
EDGE: stepW:w6:p-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L255-L255 | proof step
EDGE: stepW:w6:p-lipp | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L260-L263 | proof step
EDGE: stepW:w6:p-size | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L264-L264 | proof step
EDGE: stepW:w6:p-gap | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L268-L268 | proof step
EDGE: bpW:w4:wave | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L234-L235 | (ii) the Dirichlet weights dominate the P96-K weights in the stated divisor conclusion
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta7-W-w6
REVIEWER: sol-delta8-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6PrepHyp, KAM.Wave.W6PrepHyp.prepStepHyp, KAM.Wave.W6PrepHyp.PhiP, KAM.Wave.W6PrepHyp.om0, KAM.Wave.W6PrepHyp.Om0, KAM.Wave.W6PrepHyp.w6P0, KAM.Wave.W6PrepHyp.X0, KAM.Wave.w6_prep_divisors, KAM.Wave.w6_homMelnikovMod_of_prep, KAM.Wave.W6PrepHyp.shift_omega, KAM.Wave.W6PrepHyp.shift_Omega_J, KAM.Wave.W6PrepHyp.freq0, KAM.Wave.W6PrepHyp.phiP_sharp, KAM.Wave.W6PrepHyp.prepK_props, KAM.Wave.W6PrepHyp.w6size, KAM.Wave.w6EpsFlat_eq, KAM.Wave.w6EpsFlat_le, KAM.Wave.w6lam0_le_lam, KAM.Wave.w6StepSmoothMod_holds (KAM/Wave/Iteration/PrepStep.lean, KAM/Wave/Iteration/PrepMel.lean, KAM/Wave/Iteration/PrepShiftJ.lean, KAM/Wave/Iteration/SmoothSrc.lean, KAM/Wave/Iteration/WaveData.lean, KAM/Wave/Iteration/StepSmoothW5.lean)
LEAN_NOTE: W6 audit 1 PASS ((i), (iv), (v)), FAIL ((ii) normal shift, F2: J^(1/2) weight), PASS WITH NOTES ((iii) sharp, conditional on W6StepSmoothMod); W6 audit 2 PASS (F2 closed: shift_Omega_J with the J weight on the actual H.Om0; phiP_sharp unconditional, |Phi_P - id|_(p_+,r) <= M_F,P); the step's map properties (symplectic, real, onto P^(p_+), conjugacy) come from W5's modified step through prepStepHyp
NOTE: -

NODE: stepW:w6:p-data
KIND: step
TITLE: Data
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-data@L247-L249
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-data@L247-L249
CONTRACT_ID: stepW:w6:p-data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:prep-step: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; constants of Definition bpW:w6:constants; Pi subset {¦xi¦_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, ¦X_P¦^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:prep-step (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: step data and (bpW:w5:small) hold; frequencies satisfy (bpW:w4:freq)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:data, bpW:w4:wave
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:data | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-data@L248-L248 | (bpW:w5:small)
EDGE: bpW:w4:wave | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-data@L249-L249 | the frequencies
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6PrepHyp.prepStepHyp, KAM.Wave.w6prep_small, KAM.Wave.w6prep_data_arith (KAM/Wave/Iteration/PrepStep.lean, KAM/Wave/Iteration/WaveData.lean, KAM/Wave/Iteration/Constants.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:prep-step; W6 audit 1 PASS (c^natural_0 >= 8 needed for eta_P <= 1/8, proved as w6C0n_ge; blueprint does not state it)
NOTE: -

NODE: stepW:w6:p-div
KIND: step
TITLE: Divisors
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L250-L254
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L250-L254
CONTRACT_ID: stepW:w6:p-div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:prep-step: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; constants of Definition bpW:w6:constants; Pi subset {¦xi¦_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, ¦X_P¦^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:prep-step (for all such data); within the step: (k,l); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i): Xi = union of the S_kl, so for xi in Pi minus Xi the defining inequality of every S_kl fails, which is the divisor bound (unperturbed frequencies, Definition bpW:w7:zones(i), no admissible family); with W7's weights this is (bpW:w5:modified) with beta = 1/4 for l = +-(e_I - e_J) and (H_hat alpha) otherwise
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:indexdef, bpW:w5:w4-modified, bpW:w7:zones
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:indexdef | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L253-L253 | W7's weights hat w
EDGE: bpW:w5:w4-modified | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L253-L253 | (bpW:w5:modified)
EDGE: bpW:w7:zones | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L250-L252 | negating the removed S_kl zone inequalities supplies the divisor premise
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6+claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6_prep_divisors, KAM.Wave.w6_homMelnikovMod_of_prep (KAM/Wave/Iteration/PrepMel.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:prep-step; W6 audit 1 PASS
NOTE: -

NODE: stepW:w6:p-step
KIND: step
TITLE: Step
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L255-L259
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L255-L259
CONTRACT_ID: stepW:w6:p-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:prep-step: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; constants of Definition bpW:w6:constants; Pi subset {¦xi¦_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, ¦X_P¦^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:prep-step (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Theorem bpW:w5:step in the modified case; the frequency shifts
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step, bpW:w5:w4-modified, bpW:w5:taylor, bpW:w4:lemma1
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L255-L255 | modified case
EDGE: bpW:w5:w4-modified | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L256-L256 | both parts
EDGE: bpW:w5:taylor | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L258-L258 | the Taylor polynomial
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L258-L258 | (iv)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6PrepHyp.prepStepHyp, KAM.Wave.W6PrepHyp.shift_omega, KAM.Wave.W6PrepHyp.shift_Omega_J, KAM.Wave.W6PrepHyp.freq0 (KAM/Wave/Iteration/PrepStep.lean, KAM/Wave/Iteration/PrepShiftJ.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:prep-step; W6 audit 2 PASS (J-weighted normal shift)
NOTE: -

NODE: stepW:w6:p-lipp
KIND: step
TITLE: Transformation
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L260-L263
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L260-L263
CONTRACT_ID: stepW:w6:p-lipp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:prep-step: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; constants of Definition bpW:w6:constants; Pi subset {¦xi¦_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, ¦X_P¦^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:prep-step (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii): ¦Phi_P - id¦_{p_+,r,D_0} <= M_F = M_{F,P} by the sharper sup estimate of Step stepW:w5:f-flow (¦phi^1 - id¦_{p_+,r} <= M_F on U containing D_0), and Phi_P is Lipschitz in xi by the Lipschitz part of Theorem bpW:w5:step(v), with ¦.¦_{p,r} <= ¦.¦_{p_+,r}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step, stepW:w5:f-flow, bpW:w5:flow, bpW:w5:data, bpW:w5:omega
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L260-L263 | (v)
EDGE: stepW:w5:f-flow | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L260-L261 | the sharper sup estimate ¦phi^1 - id¦ <= M_F
EDGE: bpW:w5:flow | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L261-L261 | the lemma whose step is used
EDGE: bpW:w5:data | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L262-L262 | M_F = M_{F,P} in the modified case
EDGE: bpW:w5:omega | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L263-L263 | the comparison ¦.¦_{p,r} <= ¦.¦_{p_+,r} transfers the parameter Lipschitz property to the asserted norm
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta7-W-w6
REVIEWER: sol-delta8-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6PrepHyp.phiP_sharp, KAM.Wave.W6PrepHyp.phiP_bounds (KAM/Wave/Iteration/SmoothSrc.lean, KAM/Wave/Iteration/PrepStep.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:prep-step; W6 audit 2 PASS (sharp M_F,P bound unconditional; xi-Lipschitz from W5 (v))
NOTE: -

NODE: stepW:w6:p-size
KIND: step
TITLE: Size
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-size@L264-L267
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-size@L264-L267
CONTRACT_ID: stepW:w6:p-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:prep-step: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; constants of Definition bpW:w6:constants; Pi subset {¦xi¦_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, ¦X_P¦^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:prep-step (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) sup ¦X_{P_0}¦ <= eps^flat_0 <= gamma_1 check alpha
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-size@L264-L264 | (bpW:w5:newerror), modified
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6PrepHyp.w6size, KAM.Wave.w6EpsFlat_eq, KAM.Wave.w6EpsFlat_le, KAM.Wave.w6prep_size_arith (KAM/Wave/Iteration/PrepStep.lean, KAM/Wave/Iteration/WaveData.lean, KAM/Wave/Iteration/Constants.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:prep-step; W6 audit 1 PASS
NOTE: -

NODE: stepW:w6:p-gap
KIND: step
TITLE: Lipschitz part
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L268-L270
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L268-L270
CONTRACT_ID: stepW:w6:p-gap
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:prep-step: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; constants of Definition bpW:w6:constants; Pi subset {¦xi¦_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, ¦X_P¦^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:prep-step (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (v) the lambda-norm bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:w4-modified, stepW:w6:p-size, bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:w4-modified | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L268-L268 | (ii)
EDGE: stepW:w6:p-size | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L269-L269 | the size computation
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L269-L269 | the full lambda-norm newerror estimate in the modified case
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: sol-delta6-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6PrepHyp.w6size, KAM.Wave.w6lam0_le_lam, KAM.Wave.w6prep_lam_le (KAM/Wave/Iteration/PrepStep.lean, KAM/Wave/Iteration/WaveData.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:prep-step; W6 audit 1 PASS
NOTE: -

NODE: bpW:w6:wave-iteration
KIND: definition
TITLE: The wave iteration
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L279-L286
PROOF_SOURCE: -
CONTRACT_ID: bpW:w6:wave-iteration
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Lemma bpW:w6:prep-step with (v)
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: defines the wave iteration: Proposition bpW:w6:convergence with s_0, sigma_0 of Definition bpW:w6:constants, r_0 = eta_P r, alpha_0^it = check alpha, M_0 = 2M, a starting size eps_0 in [eps^flat_0, gamma_1 check alpha] (a parameter, > 0), Pi_{-1} = Pi minus Xi, (omega_0,Omega_0), P_0, beta_0 = beta_*; outputs Pi_*, omega_*, Omega_*, Phi_*, (omega_nu,Omega_nu), R^nu_{kl}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:prep-step, bpW:w6:convergence, bpW:w6:constants, bpW:w7:constdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L280-L280 | the preparatory step
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L280-L280 | the iteration
EDGE: bpW:w6:constants | blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L281-L281 | s_0, sigma_0, gamma_1
EDGE: bpW:w7:constdef | blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L284-L284 | beta_*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6WaveSeq, KAM.Wave.w6WaveSeq_valid, KAM.Wave.W6PrepHyp.waveSeq, KAM.Wave.W6PrepHyp.waveD, KAM.Wave.W6PrepHyp.wavePiStar, KAM.Wave.w6QP, KAM.Wave.w6EtaP, KAM.Wave.w6EpsFlat, KAM.Wave.w6MFP (KAM/Wave/Iteration/WaveData.lean, KAM/Wave/Iteration/FreqInst.lean)
LEAN_NOTE: definition formalized by W6-PREP/W6-ITER; W6 audit 1 (git show inp-w6aud:docs/tracks/W/audits/W6-audit-1.md) PASS (every eps_0 in [eps^flat_0, gamma_1 check alpha])
NOTE: -

NODE: bpW:w6:applicable
KIND: lemma
TITLE: Applicability
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L288-L290
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L291-L297
CONTRACT_ID: bpW:w6:applicable
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition bpW:w6:wave-iteration
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: the hypotheses of Proposition bpW:w6:convergence hold
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:wave-iteration, bpW:w6:prep-step, bpW:w7:unpert-bounds, bpW:w7:constdef, bpW:w6:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L289-L289 | the data
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L292-L292 | (iv)-(v)
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L293-L293 | (ii) k = 0
EDGE: bpW:w7:constdef | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L294-L294 | (C4)
EDGE: bpW:w6:constants | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L296-L296 | gamma_1
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: sol-delta6-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6PrepHyp.w6Applicable, KAM.Wave.w6StepRealMod_holds, KAM.Wave.w6applicable_arith, KAM.Wave.w6WaveSeq_small (KAM/Wave/Iteration/WaveInst.lean, KAM/Wave/Iteration/Constants.lean, KAM/Wave/Iteration/WaveData.lean)
LEAN_NOTE: W6 audit 1 (git show inp-w6aud:docs/tracks/W/audits/W6-audit-1.md) PASS (unconditional after w6StepRealMod_holds; the half-weight shift already suffices for the k = 0 separation), unchanged in W6 audit 2
NOTE: Inline proof (L291-L297).

NODE: bpW:w6:freq-lip
KIND: lemma
TITLE: Lipschitz frequencies; W7's (H1)--(H2)
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L300-L310
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L311-L323
CONTRACT_ID: bpW:w6:freq-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition bpW:w6:wave-iteration; D_nu = Pi_{nu-1}; Omega_{nu,J} at the Dirichlet label J >= 3; K_nu of Definition bpW:w6:sequences
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: (D_nu,omega_nu,Omega_nu,K_nu)_{nu>=0} is admissible for (Pi,alpha) in the sense of Definition bpW:w7:family with eps_omega = 6 pi gamma alpha + 8 pi eps_0, eps_1 = 3 gamma alpha, eps_2 = 4 eps_0 (these three <= alpha) and theta = 425(1+M) max(gamma,gamma_1) <= theta_0; Lipschitz constants for ¦.¦_infty on R^2
CONSTANT_SCOPE: theta depends on m only and is fixed before alpha (Definition bpW:w6:constants)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:wave-iteration, bpW:w7:family, bpW:w6:sequences, stepW:w6:fl-size, stepW:w6:fl-lip, stepW:w6:fl-borel, bpW:w6:constants
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L301-L301 | the data
EDGE: bpW:w7:family | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L304-L304 | admissible families
EDGE: bpW:w6:sequences | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L302-L302 | K_nu
EDGE: stepW:w6:fl-size | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L312-L312 | proof step
EDGE: stepW:w6:fl-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L315-L315 | proof step
EDGE: stepW:w6:fl-borel | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L319-L322 | proof step
EDGE: bpW:w6:constants | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L308-L308 | theta fixed before alpha
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6+claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6PrepHyp.w6wavePairJ, KAM.Wave.W6PrepHyp.w6WaveFamilyJ, KAM.Wave.w6IsFreqPair_of_bounds, KAM.Wave.w6AdmissibleFamilyOfPairs, KAM.Wave.w6freqLip_consts, KAM.Wave.w6Theta_le, KAM.Wave.w6PiMinus_measurableSet (KAM/Wave/Iteration/FreqLipJ.lean, KAM/Wave/Iteration/FreqLip.lean, KAM/Wave/Iteration/Constants.lean, KAM/Wave/Iteration/Params.lean)
LEAN_NOTE: W6 audit 1 FAIL for the literal constants (F3/D4), W6 audit 2 PASS (F3 closed: w6wavePairJ/w6WaveFamilyJ with eps_omega = 6 pi gamma alpha + 8 pi eps_0, eps_1 = 3 gamma alpha, eps_2 = 4 eps_0, theta); the old D4 family w6WaveFamily remains exported but does not certify this node
NOTE: -

NODE: stepW:w6:fl-size
KIND: step
TITLE: Sizes
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L312-L314
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L312-L314
CONTRACT_ID: stepW:w6:fl-size
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:freq-lip: Definition bpW:w6:wave-iteration; D_nu = Pi_{nu-1}; Omega_{nu,J} at the Dirichlet label J >= 3; K_nu of Definition bpW:w6:sequences
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:freq-lip (none); within the step: nu; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the size bounds, all <= alpha
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:prep-step, bpW:w6:convergence
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L312-L312 | (ii)
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L313-L313 | (ii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6PrepHyp.w6wavePairJ, KAM.Wave.w6IsFreqPair_of_bounds, KAM.Wave.w6freqLip_consts (KAM/Wave/Iteration/FreqLipJ.lean, KAM/Wave/Iteration/FreqLip.lean, KAM/Wave/Iteration/Constants.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:freq-lip; W6 audit 2 PASS
NOTE: -

NODE: stepW:w6:fl-lip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L315-L318
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L315-L318
CONTRACT_ID: stepW:w6:fl-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:freq-lip: Definition bpW:w6:wave-iteration; D_nu = Pi_{nu-1}; Omega_{nu,J} at the Dirichlet label J >= 3; K_nu of Definition bpW:w6:sequences
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:freq-lip (none); within the step: nu; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the Lipschitz totals <= 425 max(gamma,gamma_1) M; theta <= theta_0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:constants, bpW:w6:prep-step, bpW:w6:convergence
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:constants | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L318-L318 | gamma, gamma_1
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L315-L315 | (ii)
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L315-L315 | (ii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6_lipcoef_omega, KAM.Wave.w6_lipcoef_Omega, KAM.Wave.w6Theta_le, KAM.Wave.w6freqLip_consts (KAM/Wave/Iteration/FreqLip.lean, KAM/Wave/Iteration/Constants.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:freq-lip; W6 audit 1 PASS (margin 134 pi < 425 tight)
NOTE: -

NODE: stepW:w6:fl-borel
KIND: step
TITLE: Borel
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L319-L322
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L319-L322
CONTRACT_ID: stepW:w6:fl-borel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:freq-lip: Definition bpW:w6:wave-iteration; D_nu = Pi_{nu-1}; Omega_{nu,J} at the Dirichlet label J >= 3; K_nu of Definition bpW:w6:sequences
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:freq-lip (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Pi minus Xi is Borel directly (each S_kl = Pi cap U_kl with U_kl open since phi_kl is affine; Z countable; no admissible family), and Proposition bpW:w6:convergence(i) gives the Borel sets D_nu = Pi_{nu-1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:convergence, bpW:w7:zones, bpW:w7:omega0, bpW:w7:ext-borel, bpW:w7:indexdef
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L319-L322 | (i)
EDGE: bpW:w7:zones | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L319-L319 | S_kl
EDGE: bpW:w7:omega0 | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L320-L320 | phi_kl affine in xi
EDGE: bpW:w7:ext-borel | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L321-L321 | countable unions of Borel sets
EDGE: bpW:w7:indexdef | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L321-L321 | Z countable
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6+claude-suborch-W-gapfix
REVIEWER: sol-delta7-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6PiMinus_measurableSet, KAM.Wave.w6ConvBorel, KAM.Wave.W6PrepHyp.waveD (KAM/Wave/Iteration/Params.lean, KAM/Wave/Iteration/ConvSource.lean, KAM/Wave/Iteration/FreqInst.lean)
LEAN_NOTE: step of PROVED parent bpW:w6:freq-lip; W6 audit 1 PASS
NOTE: -

NODE: bpW:w6:exclusion
KIND: lemma
TITLE: Exclusion
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L327-L330
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L331-L335
CONTRACT_ID: bpW:w6:exclusion
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition bpW:w6:wave-iteration
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: Pi minus Pi_* subset E, W7's excluded set for the admissible family of Lemma bpW:w6:freq-lip; thresholds K_nu >= 2^nu, levels alpha_nu <= check alpha
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:freq-lip, bpW:w7:zones, bpW:w6:convergence, bpW:w7:family
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L328-L328 | the admissible family
EDGE: bpW:w7:zones | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L334-L334 | R_kl(check alpha) is the zone containing each iteration zone
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L332-L332 | (i)
EDGE: bpW:w7:family | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L328-L328 | E is defined in admissible family, not in the zones definition
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: sol-delta6-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6PrepHyp.w6ExclusionJ, KAM.Wave.w6_exclusion, KAM.Wave.w6_exclusion_seq, KAM.Wave.W6SeqData.two_pow_le_K (KAM/Wave/Iteration/FreqLipJ.lean, KAM/Wave/Iteration/Params.lean, KAM/Wave/Iteration/Sequences.lean)
LEAN_NOTE: W6 audit 1 PASS WITH NOTES (for the D4 family only), W6 audit 2 PASS (w6ExclusionJ for the J family of bpW:w6:freq-lip itself); generic w6_exclusion for arbitrary sequences (deviation E2)
NOTE: Inline proof (L332-L334).

NODE: bpW:w6:final-freq
KIND: lemma
TITLE: Final frequencies
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L339-L342
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L343-L346
CONTRACT_ID: bpW:w6:final-freq
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition bpW:w6:wave-iteration
SOURCE_QUANTIFIERS: for xi in Pi_*
SOURCE_CONCLUSION: ¦<k,omega_*(xi)>¦ >= check alpha/(2 A_k) for k != 0, ¦omega_*(xi) - omega^0(xi)¦_infty <= eps_omega; omega_* is Lipschitz on Pi_* with constant <= N_A + theta
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:convergence, bpW:w6:freq-lip, bpW:w7:freqcoords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L344-L344 | (ii)
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L345-L345 | size and Lipschitz bounds
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L345-L345 | (ii) N_A
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.W6PrepHyp.w6FinalFreq, KAM.Wave.w6FinalFreq_of_limits (KAM/Wave/Iteration/ConvSource.lean, KAM/Wave/Iteration/Limits.lean)
LEAN_NOTE: W6 audit 1 (git show inp-w6aud:docs/tracks/W/audits/W6-audit-1.md) PASS (wave result unconditional: |<k,omega_*>| >= check alpha/(2 A_k), |omega_* - omega^0| <= 6 pi gamma alpha + 8 pi eps_0, Lipschitz N_A + theta on Pi_*), unchanged in W6 audit 2
NOTE: Inline proof (L344-L345).

NODE: bpW:w6:tori
KIND: theorem
TITLE: Invariant tori in Birkhoff coordinates
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L351-L370
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L371-L386
CONTRACT_ID: bpW:w6:tori
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition bpW:w6:wave-iteration; H_in = N_xi + P_xi of Lemma bpW:w5:action-angle(iv) on D(s,r) (P supplied by Proposition bpW:w5:initial); tilde Psi_xi(theta) = A_xi(Phi_P(Phi_*(theta))), nu_* = omega_*/(2pi)
SOURCE_QUANTIFIERS: for xi in Pi_*, theta in T_{s_0/2} (resp. R^2)
SOURCE_CONCLUSION: (i) tilde Psi_xi is holomorphic on T_{s_0/2} with values in B_{rho_1} (if c_A(t + r^2) < rho_1^2), 1-periodic, real for real theta, normal part in W^{p+1/2}; (ii) (xi,theta) -> tilde Psi_xi(theta) continuous on Pi_* x R^2, nu_* Lipschitz; (iii) d_theta tilde Psi_xi(theta) nu_* = X_{H'}(tilde Psi_xi(theta)) in W^{p-1}; (iv) closeness with e_tor = M_{F,P} + e_Phi: ¦X¦ <= e_tor, ¦y¦ <= r^2 e_tor, ¦¦u¦¦_{a,p+1/2} + ¦¦v¦¦_{a,p+1/2} <= r e_tor on T_{s_0/2}, hence the displayed form of tilde Psi and ¦¦hat tilde Psi¦¦ <= r e_tor; (v) theta -> Z^{-1} Gamma(tilde Psi_xi(theta)) on R^2 is AnalyticOnNhd R into E_{a,p} (WaveSpace for a = p = 1)
CONSTANT_SCOPE: e_tor explicit
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:action-angle, bpW:w5:initial, bpW:w6:wave-iteration, bpW:w3:main, bpW:w0:ellap#WaveSpace, stepW:w6:t-hol, stepW:w6:t-cont, stepW:w6:t-prep, stepW:w6:t-bk, stepW:w6:t-close, stepW:w6:t-an
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:action-angle | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L352-L352 | A_xi, H_in, (ii), (v)
EDGE: bpW:w5:initial | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L353-L353 | P
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L351-L351 | Phi_P, Phi_*, omega_*
EDGE: bpW:w3:main | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L367-L367 | Gamma
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L368-L368 | the frozen WaveSpace
EDGE: stepW:w6:t-hol | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L372-L372 | proof step
EDGE: stepW:w6:t-cont | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L375-L375 | proof step
EDGE: stepW:w6:t-prep | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L377-L377 | proof step
EDGE: stepW:w6:t-bk | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L380-L380 | proof step
EDGE: stepW:w6:t-close | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L381-L381 | proof step
EDGE: stepW:w6:t-an | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L383-L383 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.W6PrepHyp.w6TorusKam, KAM.Wave.W6PrepHyp.w6ToriKam, KAM.Wave.W6PrepHyp.prepK_props (KAM/Wave/Iteration/ToriPrep.lean, KAM/Wave/Iteration/SmoothSrc.lean)
LEAN_NOTE: KAM-coordinate part only: W6PrepHyp.w6ToriKam (ToriPrep/SmoothSrc; W6 audit 1 PASS WITH NOTES conditional, W6 audit 2 PASS unconditional) for any preparatory Hamiltonian satisfying the source assumptions; the action-angle composition (Tori, ToriBk, ToriBridge, incl. the input H_in = w6InP) is not on main; missing: (i)-(v) in Birkhoff coordinates (holomorphy into B_rho_1 and normal part in W^(p+1/2), continuity and nu_* Lipschitz, invariance for X_H', closeness, real analyticity)
NOTE: -

NODE: stepW:w6:t-hol
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L372-L374
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L372-L374
CONTRACT_ID: stepW:w6:t-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:tori: Definition bpW:w6:wave-iteration; H_in = N_xi + P_xi of Lemma bpW:w5:action-angle(iv) on D(s,r) (P supplied by Proposition bpW:w5:initial); tilde Psi_xi(theta) = A_xi(Phi_P(Phi_*(theta))), nu_* = omega_*/(2pi)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:tori (for xi in Pi_*, theta in T_{s_0/2} (resp. R^2)); within the step: theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i) holomorphy, reality, periodicity; normal part in P^{p_+}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:convergence, bpW:w5:action-angle, bpW:w6:prep-step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L372-L372 | (iii)
EDGE: bpW:w5:action-angle | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L373-L373 | holomorphic A_xi
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L373-L373 | holomorphy and the smoothing increment of Phi_P
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: sol-delta6-W-W-w6
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.W6PrepHyp.w6ToriKam (KAM/Wave/Iteration/SmoothSrc.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w6:tori; KAM-coordinate part only: W6PrepHyp.w6ToriKam (ToriPrep/SmoothSrc; W6 audit 1 PASS WITH NOTES conditional, W6 audit 2 PASS unconditional) for any preparatory Hamiltonian satisfying the source assumptions; the action-angle composition (Tori, ToriBk, ToriBridge, incl. the input H_in = w6InP) is not on main; holomorphy, periodicity, reality and the p_+ normal part are proved for Phi_P o Phi_* only
NOTE: -

NODE: stepW:w6:t-cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L375-L376
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L375-L376
CONTRACT_ID: stepW:w6:t-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:tori: Definition bpW:w6:wave-iteration; H_in = N_xi + P_xi of Lemma bpW:w5:action-angle(iv) on D(s,r) (P supplied by Proposition bpW:w5:initial); tilde Psi_xi(theta) = A_xi(Phi_P(Phi_*(theta))), nu_* = omega_*/(2pi)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:tori (for xi in Pi_*, theta in T_{s_0/2} (resp. R^2)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) continuity; nu_* Lipschitz
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:convergence, bpW:w6:prep-step, bpW:w6:final-freq, bpW:w5:action-angle
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L375-L375 | (iii)
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L375-L375 | (iii)
EDGE: bpW:w6:final-freq | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L376-L376 | Lipschitz
EDGE: bpW:w5:action-angle | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L376-L376 | joint continuity of the action-angle map in (xi,w)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: sol-delta6-W-W-w6
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.W6PrepHyp.w6ToriKam (KAM/Wave/Iteration/SmoothSrc.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w6:tori; KAM-coordinate part only: W6PrepHyp.w6ToriKam (ToriPrep/SmoothSrc; W6 audit 1 PASS WITH NOTES conditional, W6 audit 2 PASS unconditional) for any preparatory Hamiltonian satisfying the source assumptions; the action-angle composition (Tori, ToriBk, ToriBridge, incl. the input H_in = w6InP) is not on main; joint continuity proved for Phi_P o Phi_*; nu_* Lipschitz (from final-freq) not composed into the torus statement
NOTE: -

NODE: stepW:w6:t-prep
KIND: step
TITLE: Invariance, prep step
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L377-L379
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L377-L379
CONTRACT_ID: stepW:w6:t-prep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:tori: Definition bpW:w6:wave-iteration; H_in = N_xi + P_xi of Lemma bpW:w5:action-angle(iv) on D(s,r) (P supplied by Proposition bpW:w5:initial); tilde Psi_xi(theta) = A_xi(Phi_P(Phi_*(theta))), nu_* = omega_*/(2pi)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:tori (for xi in Pi_*, theta in T_{s_0/2} (resp. R^2)); within the step: theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: X_{H_in}(Phi_P Phi_* theta) = d_theta(Phi_P o Phi_*) nu_*
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:invariance, bpW:w5:new-ham, bpW:w6:strong
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:invariance | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L377-L377 | invariance in KAM coordinates
EDGE: bpW:w5:new-ham | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L378-L378 | (iii)
EDGE: bpW:w6:strong | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L378-L378 | strong conjugacy
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.W6PrepHyp.w6ToriKam (KAM/Wave/Iteration/SmoothSrc.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w6:tori; KAM-coordinate part only: W6PrepHyp.w6ToriKam (ToriPrep/SmoothSrc; W6 audit 1 PASS WITH NOTES conditional, W6 audit 2 PASS unconditional) for any preparatory Hamiltonian satisfying the source assumptions; the action-angle composition (Tori, ToriBk, ToriBridge, incl. the input H_in = w6InP) is not on main; invariance X_N + iota X' = d_theta(Phi_P o Phi_*) nu_* proved for a generic preparatory Hamiltonian, not instantiated at H_in
NOTE: -

NODE: stepW:w6:t-bk
KIND: step
TITLE: Invariance, Birkhoff
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L380-L380
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L380-L380
CONTRACT_ID: stepW:w6:t-bk
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:tori: Definition bpW:w6:wave-iteration; H_in = N_xi + P_xi of Lemma bpW:w5:action-angle(iv) on D(s,r) (P supplied by Proposition bpW:w5:initial); tilde Psi_xi(theta) = A_xi(Phi_P(Phi_*(theta))), nu_* = omega_*/(2pi)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:tori (for xi in Pi_*, theta in T_{s_0/2} (resp. R^2)); within the step: theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) in Birkhoff coordinates
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:action-angle, stepW:w6:t-prep
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:action-angle | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L380-L380 | (v)
EDGE: stepW:w6:t-prep | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L380-L380 | the KAM-coordinate identity
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:t-close
KIND: step
TITLE: Closeness
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L381-L382
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L381-L382
CONTRACT_ID: stepW:w6:t-close
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:tori: Definition bpW:w6:wave-iteration; H_in = N_xi + P_xi of Lemma bpW:w5:action-angle(iv) on D(s,r) (P supplied by Proposition bpW:w5:initial); tilde Psi_xi(theta) = A_xi(Phi_P(Phi_*(theta))), nu_* = omega_*/(2pi)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:tori (for xi in Pi_*, theta in T_{s_0/2} (resp. R^2)); within the step: theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) closeness
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:prep-step, bpW:w6:convergence
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L381-L381 | (iii)
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L381-L381 | (iii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.W6PrepHyp.w6ToriKam (KAM/Wave/Iteration/SmoothSrc.lean)
LEAN_NOTE: step of PARTIAL parent bpW:w6:tori; KAM-coordinate part only: W6PrepHyp.w6ToriKam (ToriPrep/SmoothSrc; W6 audit 1 PASS WITH NOTES conditional, W6 audit 2 PASS unconditional) for any preparatory Hamiltonian satisfying the source assumptions; the action-angle composition (Tori, ToriBk, ToriBridge, incl. the input H_in = w6InP) is not on main; |Phi_P Phi_* theta - iota theta|_(p_+,r) <= e_tor = M_F,P + e_Phi in KAM coordinates only
NOTE: -

NODE: stepW:w6:t-an
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L383-L385
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L383-L385
CONTRACT_ID: stepW:w6:t-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:tori: Definition bpW:w6:wave-iteration; H_in = N_xi + P_xi of Lemma bpW:w5:action-angle(iv) on D(s,r) (P supplied by Proposition bpW:w5:initial); tilde Psi_xi(theta) = A_xi(Phi_P(Phi_*(theta))), nu_* = omega_*/(2pi)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:tori (for xi in Pi_*, theta in T_{s_0/2} (resp. R^2)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (v) real analyticity via Corollary bpW:w1:torus-analytic
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:coords, bpW:w1:torus-analytic, bpW:w3:class-remark
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L383-L383 | (i) Gamma analytic, (iv) real
EDGE: bpW:w3:coords | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L384-L384 | Z
EDGE: bpW:w1:torus-analytic | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L385-L385 | real-analytic tori from complex strips
EDGE: bpW:w3:class-remark | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L383-L383 | the regularity claim explicitly cited for Gamma analytic, hence holomorphic
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta5-W-w3
REVIEWER: sol-delta6-W-W-w6
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The cited regularity remark is retained as bpW:w3:class-remark (delta 5). The flow edge remains a direct use for analyticity and reality.

NODE: bpW:w6:to-w8
KIND: claim
TITLE: What W8 consumes from W6
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L392-L422
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L392-L422
CONTRACT_ID: bpW:w6:to-w8
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: for each shell, W8's choices r, t, rho_xi, Pi, alpha subject to Proposition bpW:w5:initial, eps_in(1 + 4 lambda/rho_xi) <= gamma alpha with lambda = alpha/M, c_A(t + r^2) < rho_1^2, Pi subset {¦xi¦_infty <= 1/2} Borel, alpha <= alpha_0
SOURCE_QUANTIFIERS: for every value of the parameter eps_0 in [eps^flat_0, gamma_1 check alpha]
SOURCE_CONCLUSION: (a)-(c) of Theorem bpW:w6:tori and Lemmas bpW:w6:exclusion, bpW:w6:final-freq hold for every eps_0 in [eps^flat_0, gamma_1 check alpha]; with eps_0 = eps^flat_0: eps^flat_0/check alpha = 2 C^natural_2 sigma_P^{-t^natural/3}(eps/alpha)^{4/3}, M_{F,P} = c^natural_F sigma_P^{1-t^natural} alpha^{3/47} eps/alpha and the displayed bound on e_tor; Theorem bpW:w6:tori(i),(iii) on R^2 is the hypothesis of Corollary bpW:w3:transport-tori-weak
CONSTANT_SCOPE: as displayed
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w6:exclusion, bpW:w6:final-freq, bpW:w6:prep-step, bpW:w3:transport-tori-weak, bpW:w0:periodone#linearTorus, bpW:w6:wave-iteration, bpW:w6:freq-lip, bpW:w7:measure, bpW:w7:shell-est, bpW:w7:dioph, bpW:w7:limit, bpW:w1:coordinatewise, bpW:w6:applicable
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L400-L400 | (i)-(v)
EDGE: bpW:w6:exclusion | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L396-L396 | (a)
EDGE: bpW:w6:final-freq | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L399-L399 | (b)
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L407-L407 | (v)
EDGE: bpW:w3:transport-tori-weak | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L414-L414 | the return to Cartesian coordinates
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L402-L402 | the linear torus K^0_I occurs directly here (frozen linearTorus)
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L405-L405 | the starting size epsilon_0 remains a free parameter of the wave iteration
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L397-L397 | the admissible family required for applying W7 measure and shell estimates
EDGE: bpW:w7:measure | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L396-L396 | the measure result applied to the admissible family
EDGE: bpW:w7:shell-est | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L397-L397 | the shell estimate applied to the same admissible family
EDGE: bpW:w7:dioph | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L399-L399 | conversion of the final frequency bound to the stated Diophantine property
EDGE: bpW:w7:limit | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L399-L399 | the limiting-frequency properties cited in the retained interface claim
EDGE: bpW:w1:coordinatewise | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L416-L416 | conversion of the Cartesian coefficient equations to clause (4)
EDGE: bpW:w6:applicable | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L404-L407 | the applicability result is explicitly used for every epsilon_0 in the stated interval
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-delta6-W-W-w6
REVIEWER: sol-delta7-W-w6
LEAN_STATUS: PARTIAL
LEAN_REF: KAM.Wave.w6EpsFlat_div, KAM.Wave.w6MFP_eq, KAM.Wave.w6MFP_le, KAM.Wave.w6WaveSeq_ePhi, KAM.Wave.w6Etor_sharp_le, KAM.Wave.W6PrepHyp.w6ExclusionJ, KAM.Wave.W6PrepHyp.w6FinalFreq, KAM.Wave.W6PrepHyp.w6ToriKam (KAM/Wave/Iteration/WaveData.lean, KAM/Wave/Iteration/FreqLipJ.lean, KAM/Wave/Iteration/ConvSource.lean, KAM/Wave/Iteration/SmoothSrc.lean)
LEAN_NOTE: W6 audit 1 (git show inp-w6aud:docs/tracks/W/audits/W6-audit-1.md) PASS (starting size: eps^flat_0/check alpha, M_F,P and the e_tor bound for eps_0 = eps^flat_0), W6 audit 2 PASS (exclusion, final frequencies for every eps_0 in the interval); missing: (a)-(c) of bpW:w6:tori in Birkhoff coordinates and the link to bpW:w3:transport-tori-weak (modules Tori, ToriBk, ToriBridge not on main); only the KAM-coordinate interface w6ToriKam is landed
NOTE: Remark kept as a node: its starting-size computation (e_tor bound) and the return-trip statement are facts W8 may consume; its 'what W8 must still supply' list is administrative.

NODE: bpW:w6#data
KIND: definition
TITLE: W6 fixed data and notation
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6@L22-L27
PROOF_SOURCE: -
CONTRACT_ID: bpW:w6#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: writes P96-K's kappa = 4/3 as varkappa; fixes m > 0, a = p = 1, tau = 24, t = 2 tau + 4 = 52 and W5's constants c_F, c_0, C_2 (modified step t^natural = 53, c^natural_F, c^natural_0, C^natural_2); Melnikov conditions use W7's Dirichlet weight <l> (by Lemma bpW:w4:wave(ii) they imply W4's)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:data, bpW:w7:indexdef, bpW:w4:wave, bpW:w0:mass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:data | blueprint-W/parts/w6-iteration.tex#bpW:w6@L24-L24 | W5's constants and t
EDGE: bpW:w7:indexdef | blueprint-W/parts/w6-iteration.tex#bpW:w6@L26-L26 | W7's Dirichlet weight <l>
EDGE: bpW:w4:wave | blueprint-W/parts/w6-iteration.tex#bpW:w6@L26-L26 | (ii) reindexing
EDGE: bpW:w0:mass | blueprint-W/parts/w6-iteration.tex#bpW:w6@L23-L23 | the notation paragraph fixes m > 0 itself
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: sol-delta6-W-W-w6
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.w6Tau, KAM.Wave.w6T, KAM.Wave.w6Tau_eq, KAM.Wave.w6T_eq, KAM.Wave.w6CF, KAM.Wave.w6C0, KAM.Wave.w6C2, KAM.Wave.w6CFn, KAM.Wave.w6C0n, KAM.Wave.w6C2n, KAM.Wave.w6Tn, KAM.Wave.W6Mel (KAM/Wave/Iteration/Sequences.lean, KAM/Wave/Iteration/Constants.lean, KAM/Wave/Iteration/Bridge.lean)
LEAN_NOTE: definition formalized by W6-PREP/W6-ITER; W6 audit 1 (git show inp-w6aud:docs/tracks/W/audits/W6-audit-1.md) PASS (sequences, constants rows); Melnikov conditions with W7's Dirichlet weight are W6Mel; (mapping inferred)
NOTE: Unlabelled 'Notation' paragraph (SPEC hypothesis packages); recorded in the SOURCE_HYPOTHESES of W6 results.
