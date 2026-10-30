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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:prep-step
KIND: lemma
TITLE: Preparatory step; P96-K \S6
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L220-L245
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L246-L267
CONTRACT_ID: bpW:w6:prep-step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; constants of Definition bpW:w6:constants; Pi subset {¦xi¦_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, ¦X_P¦^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r
SOURCE_QUANTIFIERS: for all such data
SOURCE_CONCLUSION: one step of Theorem bpW:w5:step in the modified case (beta = 1/4, p_+ = p + 1/2, level hat alpha) applies on Pi minus Xi and gives Phi_P : D_0 = D(s_0,r_0) -> D(s,r) symplectic, real, holomorphic, with (N + P) o Phi_P = N_0 + P_0 + const and the weak conjugacy, and (i) the divisor hypotheses hold (Corollary bpW:w7:melnikov(i)); (ii) the frequency shift bounds and (bpW:w5:freq) with M_omega + M_Omega <= 2M; (iii) ¦Phi_P - id¦_{p_+,r,D_0} <= M_{F,P} and Lipschitz in xi; (iv) sup ¦X_{P_0}¦_{p_+,r_0,D_0} <= eps^flat_0 = 2 C^natural_2 eps^{4/3}(hat alpha sigma_P^{t^natural})^{-1/3} <= gamma_1 check alpha; (v) ¦X_{P_0}¦^{lambda_0}_{r_0,D_0} <= eps^flat_0 with lambda_0 = check alpha/M_0
CONSTANT_SCOPE: as in Definition bpW:w6:constants
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:constants, bpW:w7:constdef, bpW:w7:zones, bpW:w7:omega0, bpW:w5:class, bpW:w5:step, bpW:w5:new-ham, bpW:w7:melnikov, stepW:w6:p-data, stepW:w6:p-div, stepW:w6:p-step, stepW:w6:p-lipp, stepW:w6:p-size, stepW:w6:p-gap
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:constants | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L220-L220 | s, sigma_P, gamma, gamma_1
EDGE: bpW:w7:constdef | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L221-L221 | (C4) alpha_0
EDGE: bpW:w7:zones | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L222-L222 | the preparatory set Xi
EDGE: bpW:w7:omega0 | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L223-L223 | the unperturbed frequencies
EDGE: bpW:w5:class | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L223-L223 | S_{p+1} and the lambda-norm
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L228-L228 | W5's step (modified)
EDGE: bpW:w5:new-ham | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L230-L230 | (iii) weak conjugacy
EDGE: bpW:w7:melnikov | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L233-L233 | (i)
EDGE: stepW:w6:p-data | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L247-L247 | proof step
EDGE: stepW:w6:p-div | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L250-L250 | proof step
EDGE: stepW:w6:p-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L253-L253 | proof step
EDGE: stepW:w6:p-lipp | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L258-L258 | proof step
EDGE: stepW:w6:p-size | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L260-L260 | proof step
EDGE: stepW:w6:p-gap | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L264-L264 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the parenthetical use of W7 melnikov(i) at L233 invokes a corollary stated under the setting of W7 measure, including an admissible family. No such family is supplied at this stage. Step p-div independently argues by negating the preparatory zones; that local argument must not be mistaken for discharge of the additional premise of the cited corollary.

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
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:p-div
KIND: step
TITLE: Divisors
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L250-L252
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L250-L252
CONTRACT_ID: stepW:w6:p-div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:prep-step: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; constants of Definition bpW:w6:constants; Pi subset {¦xi¦_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, ¦X_P¦^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:prep-step (for all such data); within the step: (k,l); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i) the modified divisor hypotheses with beta = 1/4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:indexdef, bpW:w5:w4-modified, bpW:w7:zones
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:indexdef | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L251-L251 | W7's weights hat w
EDGE: bpW:w5:w4-modified | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L251-L251 | (bpW:w5:modified)
EDGE: bpW:w7:zones | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L250-L250 | negating the removed S_kl zone inequalities supplies the divisor premise
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:p-step
KIND: step
TITLE: Step
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L253-L257
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L253-L257
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
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L253-L253 | modified case
EDGE: bpW:w5:w4-modified | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L254-L254 | both parts
EDGE: bpW:w5:taylor | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L256-L256 | the Taylor polynomial
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L256-L256 | (iv)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:p-lipp
KIND: step
TITLE: Transformation
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L258-L259
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L258-L259
CONTRACT_ID: stepW:w6:p-lipp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:prep-step: W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>; constants of Definition bpW:w6:constants; Pi subset {¦xi¦_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, ¦X_P¦^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:prep-step (for all such data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii): |Phi_P-id|_{p_+,r,D_0} <= M_{F,P} = c^natural_F eps/(hat alpha sigma_P^{t^natural-1}); Phi_P is Lipschitz in xi in |.|_{p,r}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:step
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L258-L258 | (v)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L258 cites W5 step(v), whose displayed sup bound is 2 M_F, to assert the sharper M_{F,P} bound in L239. The cited conclusion alone does not pay the factor two. W5 f-flow has a sharper sup estimate, but this proof does not identify or apply it; keep the exact missing bound rather than weakening prep-step(iii).

NODE: stepW:w6:p-size
KIND: step
TITLE: Size
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-size@L260-L263
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-size@L260-L263
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
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-size@L260-L260 | (bpW:w5:newerror), modified
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:p-gap
KIND: step
TITLE: Lipschitz part
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L264-L266
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L264-L266
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
EDGE: bpW:w5:w4-modified | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L264-L264 | (ii)
EDGE: stepW:w6:p-size | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L265-L265 | the size computation
EDGE: bpW:w5:step | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L265-L265 | the full lambda-norm newerror estimate in the modified case
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:wave-iteration
KIND: definition
TITLE: The wave iteration
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L275-L282
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
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L276-L276 | the preparatory step
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L276-L276 | the iteration
EDGE: bpW:w6:constants | blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L277-L277 | s_0, sigma_0, gamma_1
EDGE: bpW:w7:constdef | blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L280-L280 | beta_*
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w6:applicable
KIND: lemma
TITLE: Applicability
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L284-L286
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L287-L293
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
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L285-L285 | the data
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L288-L288 | (iv)-(v)
EDGE: bpW:w7:unpert-bounds | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L289-L289 | (ii) k = 0
EDGE: bpW:w7:constdef | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L290-L290 | (C4)
EDGE: bpW:w6:constants | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L292-L292 | gamma_1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Inline proof (L287-L293).

NODE: bpW:w6:freq-lip
KIND: lemma
TITLE: Lipschitz frequencies; W7's (H1)--(H2)
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L296-L304
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L305-L314
CONTRACT_ID: bpW:w6:freq-lip
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Definition bpW:w6:wave-iteration; D_nu = Pi_{nu-1}; Omega_{nu,J} at the Dirichlet label J >= 3; K_nu of Definition bpW:w6:sequences
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: (D_nu,omega_nu,Omega_nu,K_nu)_{nu>=0} is admissible for (Pi,alpha) in the sense of Definition bpW:w7:family with eps_omega = 6 pi gamma alpha + 8 pi eps_0, eps_1 = 3 gamma alpha, eps_2 = 4 eps_0, theta = 425(1+M) max(gamma,gamma_1) <= theta_0, all <= alpha; Lipschitz constants for ¦.¦_infty
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:wave-iteration, bpW:w7:family, bpW:w6:sequences, stepW:w6:fl-size, stepW:w6:fl-lip, stepW:w6:fl-borel
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L297-L297 | the data
EDGE: bpW:w7:family | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L300-L300 | admissible families
EDGE: bpW:w6:sequences | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L298-L298 | K_nu
EDGE: stepW:w6:fl-size | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L306-L306 | proof step
EDGE: stepW:w6:fl-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L309-L309 | proof step
EDGE: stepW:w6:fl-borel | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L313-L313 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L301-L303 says all <= alpha after also displaying theta. The proof at L306-L312 bounds the three epsilons by alpha and theta by theta_0 only; no theta <= alpha follows as alpha tends to zero. The literal wording is retained pending clarification that all refers only to the epsilons.

NODE: stepW:w6:fl-size
KIND: step
TITLE: Sizes
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L306-L308
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L306-L308
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
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L306-L306 | (ii)
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L307-L307 | (ii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:fl-lip
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L309-L312
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L309-L312
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
EDGE: bpW:w6:constants | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L312-L312 | gamma, gamma_1
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L309-L309 | (ii)
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L309-L309 | (ii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:fl-borel
KIND: step
TITLE: Borel
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L313-L313
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L313-L313
CONTRACT_ID: stepW:w6:fl-borel
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w6:freq-lip: Definition bpW:w6:wave-iteration; D_nu = Pi_{nu-1}; Omega_{nu,J} at the Dirichlet label J >= 3; K_nu of Definition bpW:w6:sequences
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w6:freq-lip (none); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Borel measurability
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:convergence, bpW:w7:measurable
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L313-L313 | (i)
EDGE: bpW:w7:measurable | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L313-L313 | Pi minus Xi Borel
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the citation of W7 measurable for Pi minus Xi uses only the preparatory-set fragment, whereas the W7 lemma is stated in the ambient admissible-family setting. Here admissibility is being established. The independent preparatory measurability reduction to affine frequencies and countable Borel zone unions is not separated by the source; do not assume the desired admissibility to apply the whole lemma.

NODE: bpW:w6:exclusion
KIND: lemma
TITLE: Exclusion
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L318-L321
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L322-L326
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
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L319-L319 | the admissible family
EDGE: bpW:w7:zones | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L325-L325 | R_kl(check alpha) is the zone containing each iteration zone
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L323-L323 | (i)
EDGE: bpW:w7:family | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L319-L319 | E is defined in admissible family, not in the zones definition
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Inline proof (L323-L325).

NODE: bpW:w6:final-freq
KIND: lemma
TITLE: Final frequencies
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L330-L333
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L334-L337
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
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L335-L335 | (ii)
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L336-L336 | size and Lipschitz bounds
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L336-L336 | (ii) N_A
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Inline proof (L335-L336).

NODE: bpW:w6:tori
KIND: theorem
TITLE: Invariant tori in Birkhoff coordinates
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L342-L361
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L362-L377
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
EDGE: bpW:w5:action-angle | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L343-L343 | A_xi, H_in, (ii), (v)
EDGE: bpW:w5:initial | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L344-L344 | P
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L342-L342 | Phi_P, Phi_*, omega_*
EDGE: bpW:w3:main | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L358-L358 | Gamma
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L359-L359 | the frozen WaveSpace
EDGE: stepW:w6:t-hol | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L363-L363 | proof step
EDGE: stepW:w6:t-cont | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L366-L366 | proof step
EDGE: stepW:w6:t-prep | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L368-L368 | proof step
EDGE: stepW:w6:t-bk | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L371-L371 | proof step
EDGE: stepW:w6:t-close | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L372-L372 | proof step
EDGE: stepW:w6:t-an | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L374-L374 | proof step
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:t-hol
KIND: step
TITLE: Holomorphy
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L363-L365
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L363-L365
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
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L363-L363 | (iii)
EDGE: bpW:w5:action-angle | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L364-L364 | holomorphic A_xi
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L364-L364 | holomorphy and the smoothing increment of Phi_P
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:t-cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L366-L367
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L366-L367
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
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L366-L366 | (iii)
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L366-L366 | (iii)
EDGE: bpW:w6:final-freq | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L367-L367 | Lipschitz
EDGE: bpW:w5:action-angle | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L367-L367 | joint continuity of the action-angle map in (xi,w)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:t-prep
KIND: step
TITLE: Invariance, prep step
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L368-L370
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L368-L370
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
EDGE: bpW:w6:invariance | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L368-L368 | invariance in KAM coordinates
EDGE: bpW:w5:new-ham | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L369-L369 | (iii)
EDGE: bpW:w6:strong | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L369-L369 | strong conjugacy
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:t-bk
KIND: step
TITLE: Invariance, Birkhoff
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L371-L371
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L371-L371
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
EDGE: bpW:w5:action-angle | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L371-L371 | (v)
EDGE: stepW:w6:t-prep | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L371-L371 | the KAM-coordinate identity
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
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L372-L373
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L372-L373
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
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L372-L372 | (iii)
EDGE: bpW:w6:convergence | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L372-L372 | (iii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-W-w6
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: stepW:w6:t-an
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L376
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L376
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
EDGE: bpW:w3:flow | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L374 | (i) Gamma analytic, (iv) real
EDGE: bpW:w3:coords | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L375-L375 | Z
EDGE: bpW:w1:torus-analytic | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L376-L376 | real-analytic tori from complex strips
EDGE: bpW:w3:class-remark | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L374 | the regularity claim explicitly cited for Gamma analytic, hence holomorphic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-delta5-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: The cited regularity remark is retained as bpW:w3:class-remark (delta 5). The flow edge remains a direct use for analyticity and reality.

NODE: bpW:w6:to-w8
KIND: claim
TITLE: What W8 consumes from W6
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L383-L413
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L383-L413
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
DEPS: bpW:w6:tori, bpW:w6:exclusion, bpW:w6:final-freq, bpW:w6:prep-step, bpW:w3:transport-tori-weak, bpW:w0:periodone#linearTorus, bpW:w6:wave-iteration, bpW:w6:freq-lip, bpW:w7:measure, bpW:w7:shell-est, bpW:w7:dioph, bpW:w7:limit, bpW:w1:coordinatewise
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L391-L391 | (i)-(v)
EDGE: bpW:w6:exclusion | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L387-L387 | (a)
EDGE: bpW:w6:final-freq | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L390-L390 | (b)
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L398-L398 | (v)
EDGE: bpW:w3:transport-tori-weak | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L405-L405 | the return to Cartesian coordinates
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L393-L393 | the linear torus K^0_I occurs directly here (frozen linearTorus)
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L396-L396 | the starting size epsilon_0 remains a free parameter of the wave iteration
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L388-L388 | the admissible family required for applying W7 measure and shell estimates
EDGE: bpW:w7:measure | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L387-L387 | the measure result applied to the admissible family
EDGE: bpW:w7:shell-est | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L388-L388 | the shell estimate applied to the same admissible family
EDGE: bpW:w7:dioph | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L390-L390 | conversion of the final frequency bound to the stated Diophantine property
EDGE: bpW:w7:limit | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L390-L390 | the limiting-frequency properties cited in the retained interface claim
EDGE: bpW:w1:coordinatewise | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L407-L407 | conversion of the Cartesian coefficient equations to clause (4)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
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
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled 'Notation' paragraph (SPEC hypothesis packages); recorded in the SOURCE_HYPOTHESES of W6 results.
