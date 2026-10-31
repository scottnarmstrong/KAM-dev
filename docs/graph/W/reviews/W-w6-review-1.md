# W-w6: slice review 1
Reviewer: sol-review-W-W-w6
Verdict: FAIL

Source-only refutation review against the eleven files pinned by CORPUS.sha256 (all hashes matched). Read SPEC including wave 2 extraction, REVIEW-BRIEF rules 1-11, AGENTS, PLAN and DECISIONS. No implementation Lean, builds, lake, repository lint or state-changing git was used. The tables cover every packet node; PASS concerns topology and source transcription only.

Bare lambda in W5/W6 is the parameter weight. phi^t in W5 is a flow, not sineMode. Normal indices are j=J-2, and the weights stay at J. Parent proofs are represented by their child steps; a prerequisite used inside a child is not duplicated on the parent solely because its PROOF_SOURCE spans that child.

## Node table

| Node | Verdict | Evidence or reason |
|---|---|---|
| bpW:w6:sequences | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:sequences@L31-L41; proof - |
| bpW:w6:iter-lemma | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L47-L67; proof blueprint-W/parts/w6-iteration.tex#bpW:w6:iter-lemma@L68-L84 |
| stepW:w6:il-small | FAIL | L71 checks applicability of W5 step; this check does not consume its conclusion. The actual invocation remains in iter-lemma and its output steps. Missing direct edge to bpW:w4:wave at L71. |
| stepW:w6:il-err | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-err@L72-L75; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:il-err@L72-L75 |
| stepW:w6:il-lip | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-lip@L76-L78; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:il-lip@L76-L78 |
| stepW:w6:il-div | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-div@L79-L82; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:il-div@L79-L82 |
| stepW:w6:il-tr | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-tr@L83-L83; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:il-tr@L83-L83 |
| bpW:w6:k0 | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:k0@L89-L93; proof blueprint-W/parts/w6-iteration.tex#bpW:w6:k0@L94-L98 |
| bpW:w6:convergence | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L103-L133; proof blueprint-W/parts/w6-iteration.tex#bpW:w6:convergence@L134-L161 |
| stepW:w6:c-ind | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-ind@L135-L136; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:c-ind@L135-L136 |
| stepW:w6:c-par | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-par@L137-L138; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:c-par@L137-L138 |
| stepW:w6:c-freq | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-freq@L139-L142; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:c-freq@L139-L142 |
| stepW:w6:c-dom | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-dom@L143-L146; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:c-dom@L143-L146 |
| stepW:w6:c-op | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L147-L150; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:c-op@L147-L150 |
| stepW:w6:c-cauchy | FAIL | Missing direct edge to bpW:w3:ext-integral at L151. Missing direct edge to stepW:w6:il-err at L153. |
| stepW:w6:c-lim | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-lim@L154-L157; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:c-lim@L154-L157 |
| stepW:w6:c-cont | FAIL | Missing direct edge to stepW:w6:c-cauchy at L159. |
| bpW:w6:strong | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:strong@L170-L175; proof blueprint-W/parts/w6-iteration.tex#bpW:w6:strong@L176-L179 |
| bpW:w6:invariance | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L182-L187; proof blueprint-W/parts/w6-iteration.tex#bpW:w6:invariance@L188-L204 |
| stepW:w6:i-weak | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L189-L196; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:i-weak@L189-L196 |
| stepW:w6:i-torus | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-torus@L197-L199; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:i-torus@L197-L199 |
| stepW:w6:i-lim | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:i-lim@L200-L203; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:i-lim@L200-L203 |
| bpW:w6:constants | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:constants@L211-L218; proof - |
| bpW:w6:prep-step | FAIL | SOURCE_GAP: the parenthetical use of W7 melnikov(i) at L233 invokes a corollary stated under the setting of W7 measure, including an admissible family. No such family is supplied at this stage. Step p-div independently argues by negating the preparatory zones; that local argument must not be mistaken for discharge of the additional premise of the cited corollary. |
| stepW:w6:p-data | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-data@L247-L249; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:p-data@L247-L249 |
| stepW:w6:p-div | FAIL | Missing direct edge to bpW:w7:zones at L250. |
| stepW:w6:p-step | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L253-L257; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:p-step@L253-L257 |
| stepW:w6:p-lipp | FAIL | SOURCE_GAP: L258 cites W5 step(v), whose displayed sup bound is 2 M_F, to assert the sharper M_{F,P} bound in L239. The cited conclusion alone does not pay the factor two. W5 f-flow has a sharper sup estimate, but this proof does not identify or apply it; keep the exact missing bound rather than weakening prep-step(iii). |
| stepW:w6:p-size | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-size@L260-L263; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:p-size@L260-L263 |
| stepW:w6:p-gap | FAIL | Missing direct edge to bpW:w5:step at L265. |
| bpW:w6:wave-iteration | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:wave-iteration@L275-L282; proof - |
| bpW:w6:applicable | FAIL | L285 names the proposition whose hypotheses are being checked, rather than invoking its conclusion. L289-L292 checks the k0 premises; it does not invoke its conclusion. |
| bpW:w6:freq-lip | FAIL | SOURCE_GAP: L301-L303 says all <= alpha after also displaying theta. The proof at L306-L312 bounds the three epsilons by alpha and theta by theta_0 only; no theta <= alpha follows as alpha tends to zero. The literal wording is retained pending clarification that all refers only to the epsilons. |
| stepW:w6:fl-size | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L306-L308; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-size@L306-L308 |
| stepW:w6:fl-lip | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L309-L312; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-lip@L309-L312 |
| stepW:w6:fl-borel | FAIL | SOURCE_GAP: the citation of W7 measurable for Pi minus Xi uses only the preparatory-set fragment, whereas the W7 lemma is stated in the ambient admissible-family setting. Here admissibility is being established. The independent preparatory measurability reduction to affine frequencies and countable Borel zone unions is not separated by the source; do not assume the desired admissibility to apply the whole lemma. |
| bpW:w6:exclusion | FAIL | Missing direct edge to bpW:w7:family at L319. The zones edge must locate the actual R_kl use at L325; E itself belongs to family at L319. |
| bpW:w6:final-freq | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L330-L333; proof blueprint-W/parts/w6-iteration.tex#bpW:w6:final-freq@L334-L337 |
| bpW:w6:tori | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L342-L361; proof blueprint-W/parts/w6-iteration.tex#bpW:w6:tori@L362-L377 |
| stepW:w6:t-hol | FAIL | Missing direct edge to bpW:w6:prep-step at L364. |
| stepW:w6:t-cont | FAIL | Missing direct edge to bpW:w5:action-angle at L367. |
| stepW:w6:t-prep | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L368-L370; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:t-prep@L368-L370 |
| stepW:w6:t-bk | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L371-L371; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:t-bk@L371-L371 |
| stepW:w6:t-close | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L372-L373; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:t-close@L372-L373 |
| stepW:w6:t-an | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L376; proof blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L376 |
| bpW:w6:to-w8 | FAIL | Missing direct edge to bpW:w6:wave-iteration at L396. Missing direct edge to bpW:w6:freq-lip at L388. Missing direct edge to bpW:w7:measure at L387. Missing direct edge to bpW:w7:shell-est at L388. Missing direct edge to bpW:w7:dioph at L390. Missing direct edge to bpW:w7:limit at L390. Missing direct edge to bpW:w1:coordinatewise at L407. |
| bpW:w6#data | FAIL | Missing direct edge to bpW:w0:mass at L23. |

## Coverage

all other coverage items PASS

Every labelled unit and unlabelled prose item was checked against the raw slice. The existing mappings remain valid after the node replacements. SOURCE_GAP findings above are carried in their existing substantive step/claim nodes; their existing inventory items therefore still cover them.

## Complete replacement blocks

```text
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
```

```text
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
```

```text
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
```

```text
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
```

```text
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
```

```text
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
```

```text
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
```

```text
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
```

```text
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
```

```text
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
```

```text
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
```

```text
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
```

```text
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
```

```text
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
```

```text
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
```

## Validation

- `sha256sum -c docs/graph/W/CORPUS.sha256`: all eleven source files OK.
- Permitted `inp_depgraph_slice_check.py docs/graph/W/packets W-w6`: 47 nodes, 154 edges, 70 coverage items, 0 problems (original packets).
- Review-format check: 47 unique packet-node verdicts, 15 complete FAIL replacements; exact required fields; DEPS/EDGE agreement; existing edge targets; source ranges valid; no trailing whitespace.
- Combined read-only packet overlay with all four reports: no dependency cycles. Packets were not modified.

## Suspected blueprint errata and source gaps

1. `w6-iteration.tex:258-259`: "(iii) is Theorem ... step(v) (sup part ...)" cites a 2 M_F bound for the M_{F,P} bound asserted at L239. W5 f-flow L384-L385 contains a sharper estimate, but the present proof does not cite/apply it. The replacement retains the exact factor-two gap.
2. `w6-iteration.tex:233` cites "Corollary ... melnikov(i)" before supplying the admissible-family premise of its stated setting (`w7-measure.tex:566-569,585-586`). The separate zone-negation proof L250-L252 establishes the desired preparatory statement directly; the over-scoped corollary citation should not count as a discharged conditional application.
3. `w6-iteration.tex:313`: "Pi minus Xi is Borel (Lemma ... measurable)" cites a lemma in the admissible-family setting while this proof is still establishing admissibility. The preparatory-set fragment needs to be separated from that setting; no mathematical counterexample to preparatory measurability is claimed.
4. `w6-iteration.tex:301-303`: "theta=425(1+M) max(gamma,gamma_1)<=theta_0, all <=alpha" is ambiguous and, if all includes theta, unsupported: theta is fixed before alpha, and L306-L312 gives only theta<=theta_0. Clarify that the alpha bounds concern the three epsilon size constants.
These are source-scope/justification findings; the review does not replace the stated conclusions or add conclusion-shaped premises.
