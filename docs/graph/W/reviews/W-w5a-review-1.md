# W-w5a: slice review 1
Reviewer: sol-review-W-W-w5a
Verdict: FAIL

Source-only refutation review against the eleven files pinned by CORPUS.sha256 (all hashes matched). Read SPEC including wave 2 extraction, REVIEW-BRIEF rules 1-11, AGENTS, PLAN and DECISIONS. No implementation Lean, builds, lake, repository lint or state-changing git was used. The tables cover every packet node; PASS concerns topology and source transcription only.

Bare lambda in W5/W6 is the parameter weight. phi^t in W5 is a flow, not sineMode. Normal indices are j=J-2, and the weights stay at J. Parent proofs are represented by their child steps; a prerequisite used inside a child is not duplicated on the parent solely because its PROOF_SOURCE spans that child.

## Node table

| Node | Verdict | Evidence or reason |
|---|---|---|
| bpW:w5:ext-taylor | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-taylor@L46-L53; proof - |
| bpW:w5:ext-ftc | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:ext-ftc@L54-L56; proof - |
| bpW:w5:setting | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:setting@L62-L71; proof - |
| bpW:w5:omega | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:omega@L75-L79; proof blueprint-W/parts/w5-kamstep.tex#bpW:w5:omega@L80-L88 |
| stepW:w5:ombd | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:ombd@L81-L82; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:ombd@L81-L82 |
| stepW:w5:omnd | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnd@L83-L85; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnd@L83-L85 |
| stepW:w5:omnorm | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnorm@L86-L87; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnorm@L86-L87 |
| bpW:w5:class | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:class@L91-L105; proof - |
| bpW:w5:lambda-product | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:lambda-product@L109-L114; proof blueprint-W/parts/w5-kamstep.tex#bpW:w5:lambda-product@L109-L114 |
| bpW:w5:w4-general | FAIL | Missing direct edge to bpW:w5#data at L124. |
| stepW:w5:g-pair | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-pair@L136-L138; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-pair@L136-L138 |
| stepW:w5:g-tail | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-tail@L139-L140; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-tail@L139-L140 |
| stepW:w5:g-div | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-div@L141-L143; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-div@L141-L143 |
| stepW:w5:g-diag | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-diag@L144-L146; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-diag@L144-L146 |
| stepW:w5:g-rest | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L147-L150; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L147-L150 |
| bpW:w5:w4-modified | FAIL | Missing direct edge to bpW:w5:w4-general at L157. |
| stepW:w5:m-sup | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-sup@L180-L184; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-sup@L180-L184 |
| stepW:w5:m-other | FAIL | Missing direct edge to bpW:w1:embed at L186. |
| stepW:w5:m-lip | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-lip@L187-L190; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-lip@L187-L190 |
| stepW:w5:m-act | FAIL | Missing direct edge to stepW:w4:assembly at L204. |
| stepW:w5:m-ass | FAIL | Missing direct edge to stepW:w4:lip at L213. |
| stepW:w5:m-const | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-const@L218-L221; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-const@L218-L221 |
| bpW:w5:taylor | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L251-L271; proof blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L272-L306 |
| stepW:w5:t-scale | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-scale@L273-L276; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-scale@L273-L276 |
| stepW:w5:t-disc | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-disc@L277-L279; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-disc@L277-L279 |
| stepW:w5:t-poly | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-poly@L280-L284; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-poly@L280-L284 |
| stepW:w5:t-comp | FAIL | Missing direct edge to bpW:w3:ext-integral at L287. Missing direct edge to bpW:w1:ext-onevar at L286. Missing direct edge to stepW:w5:t-est at L289. SOURCE_GAP: L289-L290 invokes Schwarz symmetry of D^2P without proof or a listed external covering symmetry of the second Frechet derivative. The step retains this unlisted input; it is not an extra hypothesis of the Taylor lemma. |
| stepW:w5:t-field | FAIL | Missing direct edge to bpW:w3:ext-integral at L294. |
| stepW:w5:t-est | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-est@L299-L305; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-est@L299-L305 |
| bpW:w5:data | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:data@L313-L333; proof - |
| bpW:w5:solve | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:solve@L337-L348; proof blueprint-W/parts/w5-kamstep.tex#bpW:w5:solve@L349-L361 |
| stepW:w5:s-in | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-in@L350-L351; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-in@L350-L351 |
| stepW:w5:s-out | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-out@L352-L356; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-out@L352-L356 |
| stepW:w5:s-class | FAIL | Missing direct edge to bpW:w1:ext-analytic at L357. Missing direct edge to bpW:w3:ext-series at L359. |
| bpW:w5:flow | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| stepW:w5:f-margin | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-margin@L381-L383; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-margin@L381-L383 |
| stepW:w5:f-flow | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| stepW:w5:f-par | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| stepW:w5:f-der | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| stepW:w5:f-image | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| stepW:w5:f-real | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| bpW:w5:flow-calc | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| stepW:w5:c-cont | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. Missing direct edge to bpW:w1:ext-onevar at L429. |
| stepW:w5:c-var | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| stepW:w5:c-skew | FAIL | SOURCE_GAP: L435 uses symmetry of the second Frechet derivative D^2F; C^2 regularity alone is not a proof of this symmetry, and no listed external supplies Schwarz symmetry. Do not add the symmetry as a premise of flow-calc. |
| stepW:w5:c-symp | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| stepW:w5:c-inv | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| stepW:w5:c-trans | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. Missing direct edge to bpW:w3:ext-series at L443. Missing direct edge to bpW:w1:ext-onevar at L444. |
| stepW:w5:c-time | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-time@L445-L447; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-time@L445-L447 |
| bpW:w5#data | FAIL | Missing direct edge to bpW:w0:ellap#ellWeight at L37. |

## Coverage

all other coverage items PASS

Every labelled unit and unlabelled prose item was checked against the raw slice. The existing mappings remain valid after the node replacements. SOURCE_GAP findings above are carried in their existing substantive step/claim nodes; their existing inventory items therefore still cover them.

The excluded prep-gap remark is mentioned downstream only in introductory prose or source notes. The exponents are independently fixed by W7 constdef and W6 prep-step. The modified-divisor sourcegap inventory correctly maps to the strengthened conditional lemma and m-lip/m-act.

## Complete replacement blocks

```text
NODE: bpW:w5:w4-general
KIND: lemma
TITLE: W4 with a general smoothing exponent
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L123-L133
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L134-L151
CONTRACT_ID: bpW:w5:w4-general
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W5 standing data (L35-L39): a = p = 1, wave weights omega_{a,q}(j+2) (Convention bpW:w4:index); p_+ in [p+1/2, p+1]; in W4 the exponent bar p = p+1 replaced by p_+ and (bpW:w4:freq) by (bpW:w5:freq)
SOURCE_QUANTIFIERS: for every such p_+
SOURCE_CONCLUSION: Lemma bpW:w4:lie, Theorem bpW:w4:lemma1 and Corollary bpW:w4:lemma2 hold verbatim with the same constants C_1, B^W_sigma, 3C_1, except that Theorem bpW:w4:lemma1(iv) reads sup_j (j+2)^{p_+-p}¦hat Omega_j¦ <= eps (likewise for differences); (bpW:w5:freq): Omega_j = j + 2 + tilde Omega_j, sup j^{1/2}¦tilde Omega_j¦ <= M_0, Lipschitz bounds with sup j^{1/2}
CONSTANT_SCOPE: C_1, B^W_sigma as in W4
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:lie, bpW:w4:lemma1, bpW:w4:lemma2, bpW:w4:ops, bpW:w4:taylor, stepW:w5:g-pair, stepW:w5:g-tail, stepW:w5:g-div, stepW:w5:g-diag, stepW:w5:g-rest, bpW:w5#data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lie | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L130-L130 | restated
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L130-L130 | restated
EDGE: bpW:w4:lemma2 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L130-L130 | restated
EDGE: bpW:w4:ops | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L124-L124 | the exponent bar p replaced
EDGE: bpW:w4:taylor | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L125-L125 | the exponent bar p replaced
EDGE: stepW:w5:g-pair | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L136-L136 | proof step
EDGE: stepW:w5:g-tail | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L139-L139 | proof step
EDGE: stepW:w5:g-div | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L141-L141 | proof step
EDGE: stepW:w5:g-diag | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L144-L144 | proof step
EDGE: stepW:w5:g-rest | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L147-L147 | proof step
EDGE: bpW:w5#data | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L124-L124 | the generalization uses the fixed p = 1 weight regime
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w5:w4-modified
KIND: lemma
TITLE: Modified divisors for the preparatory step
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L156-L177
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L178-L222
CONTRACT_ID: bpW:w5:w4-modified
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W5 standing data (L35-L39): a = p = 1, wave weights omega_{a,q}(j+2) (Convention bpW:w4:index); (bpW:w5:freq) with M = M_omega + M_Omega > 0; hat alpha > 0; beta in (0,1/2]; p_+ in [p+1/2, p+1] with beta <= p+1-p_+; every divisor of Definition bpW:w4:melnikov satisfies the bound of (H_{hat alpha}) except delta^Q_{k,ij}, i != j, for which only (bpW:w5:modified) ¦delta^Q¦ >= (hat alpha/A_k)¦i-j¦/(min(i,j)+2)^beta; R as in Theorem bpW:w4:lemma1 with bar p = p+1; F, hat N by the same formulas
SOURCE_QUANTIFIERS: for all such data; (ii) moreover 2 beta <= p+1-p_+; (iii) 0 < sigma <= 1
SOURCE_CONCLUSION: (i) F(.,xi) in T_{s-sigma} with Q_F, Q_F^T bounded l^N_{a,p} -> l^N_{a,p_+}, all other components as in W4; the equation (ii) and bounds (iv) of Theorem bpW:w4:lemma1 hold and ¦X_F¦_{p_+,r} <= C_1 B^W_sigma eps/hat alpha; (ii) the Lipschitz bound with B^natural_sigma = sum (1+¦k¦_1)^2 A_k^2 e^{-2 pi ¦k¦_1 sigma} >= B^W_sigma, and the lambda-form with 3 C_1 B^natural_sigma/hat alpha for 0 <= lambda <= hat alpha/M; (iii) B^natural_sigma <= b^natural(tau) sigma^{-(2tau+4)}, b^natural(tau) = 4(C_0 + C_2 + C_{2tau} + C_{2tau+2})
CONSTANT_SCOPE: C_1 absolute; b^natural depends only on tau
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:melnikov, bpW:w4:lemma1, stepW:w5:m-sup, stepW:w5:m-other, stepW:w5:m-lip, stepW:w5:m-act, stepW:w5:m-ass, stepW:w5:m-const, bpW:w5:w4-general
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:melnikov | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L158-L158 | divisors and (H_{hat alpha})
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L163-L163 | R, F, hat N
EDGE: stepW:w5:m-sup | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L180-L180 | proof step
EDGE: stepW:w5:m-other | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L185-L185 | proof step
EDGE: stepW:w5:m-lip | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L187-L187 | proof step
EDGE: stepW:w5:m-act | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L191-L191 | proof step
EDGE: stepW:w5:m-ass | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L213-L213 | proof step
EDGE: stepW:w5:m-const | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L218-L218 | proof step
EDGE: bpW:w5:w4-general | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L157-L157 | the modified lemma assumes the new frequency hypothesis (freq) defined here
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:m-other
KIND: step
TITLE: Other components
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-other@L185-L186
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-other@L185-L186
CONTRACT_ID: stepW:w5:m-other
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:w4-modified: W5 standing data (L35-L39): a = p = 1, wave weights omega_{a,q}(j+2) (Convention bpW:w4:index); (bpW:w5:freq) with M = M_omega + M_Omega > 0; hat alpha > 0; beta in (0,1/2]; p_+ in [p+1/2, p+1] with beta <= p+1-p_+; every divisor of Definition bpW:w4:melnikov satisfies the bound of (H_{hat alpha}) except delta^Q_{k,ij}, i != j, for which only (bpW:w5:modified) ¦delta^Q¦ >= (hat alpha/A_k)¦i-j¦/(min(i,j)+2)^beta; R as in Theorem bpW:w4:lemma1 with bar p = p+1; F, hat N by the same formulas
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:w4-modified (for all such data; (ii) moreover 2 beta <= p+1-p_+; (iii) 0 < sigma <= 1); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the other components obey (H_{hat alpha}); W4's bounds hold in l^N_{a,p+1} subset l^N_{a,p_+}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:lemma1, bpW:w1:embed
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-other@L186-L186 | its bounds
EDGE: bpW:w1:embed | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-other@L186-L186 | the inclusion l^{a,p+1} into l^{a,p_+} has norm at most one
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:m-act
KIND: step
TITLE: The action component
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L191-L212
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L191-L212
CONTRACT_ID: stepW:w5:m-act
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:w4-modified: W5 standing data (L35-L39): a = p = 1, wave weights omega_{a,q}(j+2) (Convention bpW:w4:index); (bpW:w5:freq) with M = M_omega + M_Omega > 0; hat alpha > 0; beta in (0,1/2]; p_+ in [p+1/2, p+1] with beta <= p+1-p_+; every divisor of Definition bpW:w4:melnikov satisfies the bound of (H_{hat alpha}) except delta^Q_{k,ij}, i != j, for which only (bpW:w5:modified) ¦delta^Q¦ >= (hat alpha/A_k)¦i-j¦/(min(i,j)+2)^beta; R as in Theorem bpW:w4:lemma1 with bar p = p+1; F, hat N by the same formulas
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:w4-modified (for all such data; (ii) moreover 2 beta <= p+1-p_+; (iii) 0 < sigma <= 1); within the step: i, xi, zeta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: d_{theta_i} Q_F bounded as an operator l^N_{a,p} -> l^N_{a,p_+} by 2 pi K_S B^W_sigma eps/hat alpha; the differences with B^natural_sigma
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w4:components, bpW:w4:w1-requests, stepW:w5:m-sup, bpW:w1:ext-unifderiv, bpW:w4:index, stepW:w5:m-lip, bpW:w4:fourier-ops, stepW:w4:assembly
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w4:components | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L195-L195 | (i): ¦¦Q¦¦ <= eps
EDGE: bpW:w4:w1-requests | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L196-L196 | (F1), (F2)
EDGE: stepW:w5:m-sup | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L197-L197 | the Q-division
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L199-L199 | termwise differentiation
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L202-L202 | (bpW:w4:pairing)
EDGE: stepW:w5:m-lip | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L206-L206 | the divisor differences
EDGE: bpW:w4:fourier-ops | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L209-L209 | (iii)
EDGE: stepW:w4:assembly | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L204-L204 | the revised action-component bound is inserted into W4 assembly
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:m-ass
KIND: step
TITLE: Assembly
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L213-L217
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L213-L217
CONTRACT_ID: stepW:w5:m-ass
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:w4-modified: W5 standing data (L35-L39): a = p = 1, wave weights omega_{a,q}(j+2) (Convention bpW:w4:index); (bpW:w5:freq) with M = M_omega + M_Omega > 0; hat alpha > 0; beta in (0,1/2]; p_+ in [p+1/2, p+1] with beta <= p+1-p_+; every divisor of Definition bpW:w4:melnikov satisfies the bound of (H_{hat alpha}) except delta^Q_{k,ij}, i != j, for which only (bpW:w5:modified) ¦delta^Q¦ >= (hat alpha/A_k)¦i-j¦/(min(i,j)+2)^beta; R as in Theorem bpW:w4:lemma1 with bar p = p+1; F, hat N by the same formulas
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:w4-modified (for all such data; (ii) moreover 2 beta <= p+1-p_+; (iii) 0 < sigma <= 1); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: W4's assembly with the Q_F contribution from Step stepW:w5:m-act; the lambda-form as in Corollary bpW:w4:lemma2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w4:Fcomp, stepW:w4:assembly, stepW:w4:Nhat, stepW:w5:m-act, bpW:w4:lemma2, stepW:w4:lip
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w4:Fcomp | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L213-L213 | W4's component bounds
EDGE: stepW:w4:assembly | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L213-L213 | W4's assembly
EDGE: stepW:w4:Nhat | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L213-L213 | W4's hat N step
EDGE: stepW:w5:m-act | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L214-L214 | the Q_F contribution
EDGE: bpW:w4:lemma2 | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L217-L217 | the lambda-form
EDGE: stepW:w4:lip | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L213-L213 | the explicitly cited Fcomp-through-Nhat range includes the Lipschitz assembly
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:t-comp
KIND: step
TITLE: Components
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L285-L292
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L285-L292
CONTRACT_ID: stepW:w5:t-comp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:taylor: W5 standing data (L35-L39): a = p = 1, wave weights omega_{a,q}(j+2) (Convention bpW:w4:index); s, r > 0; p_+ in [p+1/2, p+1]; P(.,xi) in S_{p_+}(D(s,r)) real, 1-periodic in each theta_i, ¦X_P¦^lambda_{r,D(s,r)} <= eps; S_t, T_t the scalings; a, b, g, H and R as displayed
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:taylor (for all such P; eta in (0,1/8] for (iv)); within the step: theta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: a, b, g holomorphic; H a Cauchy integral, holomorphic, bounded, symmetric; the z-blocks; reality and periodicity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:deriv-continuous, bpW:w1:cauchy, bpW:w4:index, bpW:w3:ext-integral, bpW:w1:ext-onevar, stepW:w5:t-est
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:deriv-continuous | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L287-L287 | the derivative as a Cauchy integral
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L288-L288 | bound
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L291-L291 | substitution u, v in z, zbar
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L287-L287 | differentiate the Cauchy integral with respect to theta
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L286-L286 | Cauchy integral representation of the directional derivative
EDGE: stepW:w5:t-est | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L289-L289 | the proof explicitly invokes t-est for the sharper bound on H
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L289-L290 invokes Schwarz symmetry of D^2P without proof or a listed external covering symmetry of the second Frechet derivative. The step retains this unlisted input; it is not an extra hypothesis of the Taylor lemma.
```

```text
NODE: stepW:w5:t-field
KIND: step
TITLE: Field
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L293-L298
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L293-L298
CONTRACT_ID: stepW:w5:t-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:taylor: W5 standing data (L35-L39): a = p = 1, wave weights omega_{a,q}(j+2) (Convention bpW:w4:index); s, r > 0; p_+ in [p+1/2, p+1]; P(.,xi) in S_{p_+}(D(s,r)) real, 1-periodic in each theta_i, ¦X_P¦^lambda_{r,D(s,r)} <= eps; S_t, T_t the scalings; a, b, g, H and R as displayed
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:taylor (for all such P; eta in (0,1/8] for (iv)); within the step: w, W'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: DR(w)W' = varpi(sum g_k(w), W') so X_R = sum_{k<=2} g_k (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:t-scale, bpW:w5:omega, bpW:w3:ext-integral
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:t-scale | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L295-L295 | X_{P o S_t} = G(t,.)
EDGE: bpW:w5:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L297-L297 | uniqueness
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L294-L294 | differentiate the coefficient integrals in epsilon
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:s-class
KIND: step
TITLE: Class
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L357-L360
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L357-L360
CONTRACT_ID: stepW:w5:s-class
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:solve: step data (Definition bpW:w5:data); R the Taylor polynomial of Lemma bpW:w5:taylor; F, hat N, hat a_0 of Theorem bpW:w4:lemma1 for R (through Lemma bpW:w5:w4-general, or bpW:w5:w4-modified)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:solve (for all step data); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: members of T are C^2 with holomorphic fields into P^{p_+} and DF W = varpi(X_F,W)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:holo-analytic-fd, bpW:w4:taylor, bpW:w1:ext-analytic, bpW:w3:ext-series
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:holo-analytic-fd | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L358-L358 | holomorphic in finitely many variables is analytic
EDGE: bpW:w4:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L360-L360 | the field from the gradients
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L357-L357 | assemble the analytic finite polynomial from its coefficient maps
EDGE: bpW:w3:ext-series | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L359-L359 | derivatives of the analytic coefficient maps are analytic, hence holomorphic
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w5:flow
KIND: lemma
TITLE: The flow with explicit margins; P96-K (9)--(11) and Lemma~A.4
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L364-L379
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L380-L404
CONTRACT_ID: bpW:w5:flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,¦.¦_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = D(s-2sigma,r/2), delta = sigma/4, M = M_F <= sigma/256 < delta, L = M/delta <= 1/64
SOURCE_QUANTIFIERS: for ¦t¦ <= 1, xi, zeta in Pi
SOURCE_CONCLUSION: the hypotheses of Lemma bpW:w1:flow hold, and (i) phi^t exists on U with values in V, phi^t - id is holomorphic U -> P^{p_+}, ¦phi^t - id¦^lambda_{p_+,r,U} <= 2 M_F; (ii) on D(s-3sigma,r/4): ¦D phi^t - I¦_{p->p_+,r} <= 8 M_F/sigma and ¦D phi^t - I¦^lambda <= 16 M_F/sigma <= eta^2; (iii) phi^t(D(s-5sigma,eta r)) subset D(s-4sigma,2 eta r) subset D(s-3sigma,r/4); (iv) phi^t is real on real points and commutes with integer angle translations
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:data, bpW:w1:flow, bpW:w5:solve, stepW:w5:f-margin, stepW:w5:f-flow, stepW:w5:f-par, stepW:w5:f-der, stepW:w5:f-image, stepW:w5:f-real
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:data | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L365-L365 | step data and (bpW:w5:small)
EDGE: bpW:w1:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L365-L365 | W1's holomorphic flow
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L366-L366 | X_F and M_F
EDGE: stepW:w5:f-margin | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L381-L381 | proof step
EDGE: stepW:w5:f-flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L384-L384 | proof step
EDGE: stepW:w5:f-par | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L388-L388 | proof step
EDGE: stepW:w5:f-der | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L394-L394 | proof step
EDGE: stepW:w5:f-image | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L398-L398 | proof step
EDGE: stepW:w5:f-real | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L400-L400 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:f-flow
KIND: step
TITLE: Flow
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L384-L387
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L384-L387
CONTRACT_ID: stepW:w5:f-flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow: step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,¦.¦_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = D(s-2sigma,r/2), delta = sigma/4, M = M_F <= sigma/256 < delta, L = M/delta <= 1/64
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:flow (for ¦t¦ <= 1, xi, zeta in Pi); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i): the flow and phi^t - id holomorphic into P^{p_+} with norm <= ¦t¦ M_F
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:flow, bpW:w1:cauchy, bpW:w3:ext-integral, stepW:w5:f-margin
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L384-L384 | (i)-(iii)
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L387-L387 | uniform derivative bound
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L387-L387 | differentiation under the integral
EDGE: stepW:w5:f-margin | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L384-L384 | hypotheses
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:f-par
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L388-L393
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L388-L393
CONTRACT_ID: stepW:w5:f-par
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow: step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,¦.¦_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = D(s-2sigma,r/2), delta = sigma/4, M = M_F <= sigma/256 < delta, L = M/delta <= 1/64
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:flow (for ¦t¦ <= 1, xi, zeta in Pi); within the step: xi, zeta; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦phi^t - id¦^lambda <= 2 M_F
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:flow, bpW:w1:cauchy, stepW:w5:f-flow
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L389-L389 | (iv)
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L392-L392 | ¦DX_F¦ <= M_F/delta on B(w,delta)
EDGE: stepW:w5:f-flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L390-L390 | the integral identity
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:f-der
KIND: step
TITLE: Derivative
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L394-L397
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L394-L397
CONTRACT_ID: stepW:w5:f-der
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow: step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,¦.¦_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = D(s-2sigma,r/2), delta = sigma/4, M = M_F <= sigma/256 < delta, L = M/delta <= 1/64
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:flow (for ¦t¦ <= 1, xi, zeta in Pi); within the step: w in D(s-3sigma,r/4); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) via Cauchy estimates with margin sigma/8; 16 M_F/sigma <= eta^2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:kam-domain, bpW:w1:cauchy, stepW:w5:f-flow, stepW:w5:f-par, bpW:w5:data
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:kam-domain | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L394-L394 | margins
EDGE: bpW:w1:cauchy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L396-L396 | the Cauchy estimate
EDGE: stepW:w5:f-flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L396-L396 | the bound M_F
EDGE: stepW:w5:f-par | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L397-L397 | the bound 2 N_1
EDGE: bpW:w5:data | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L397-L397 | (bpW:w5:small)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:f-image
KIND: step
TITLE: Image
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-image@L398-L399
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-image@L398-L399
CONTRACT_ID: stepW:w5:f-image
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow: step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,¦.¦_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = D(s-2sigma,r/2), delta = sigma/4, M = M_F <= sigma/256 < delta, L = M/delta <= 1/64
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:flow (for ¦t¦ <= 1, xi, zeta in Pi); within the step: w in D(s-5sigma,eta r); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) the image inclusions
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:f-flow
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:f-flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-image@L398-L398 | the increment bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:f-real
KIND: step
TITLE: Reality and equivariance
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L400-L403
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L400-L403
CONTRACT_ID: stepW:w5:f-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow: step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,¦.¦_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = D(s-2sigma,r/2), delta = sigma/4, M = M_F <= sigma/256 < delta, L = M/delta <= 1/64
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:flow (for ¦t¦ <= 1, xi, zeta in Pi); within the step: k in Z^2; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) reality and equivariance
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:flow, bpW:w4:lemma1, bpW:w4:taylor
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L400-L400 | (i), (iii)
EDGE: bpW:w4:lemma1 | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L401-L401 | (i) X_F real
EDGE: bpW:w4:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L401-L401 | 1-periodic components
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w5:flow-calc
KIND: lemma
TITLE: Flow calculus
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L412-L425
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L426-L448
CONTRACT_ID: bpW:w5:flow-calc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Lemma bpW:w5:flow
SOURCE_QUANTIFIERS: for ¦t¦ <= 1
SOURCE_CONCLUSION: (i) (t,w) -> phi^t(w), D phi^t(w) continuous on [-1,1] x U and D phi^t = I + int_0^t DX_F(phi^tau) D phi^tau dtau; (ii) varpi(D phi^t W, D phi^t W') = varpi(W,W'); (iii) on D(s-3sigma,r/4), D phi^t is invertible on P and maps P^{p_+} onto P^{p_+}; (iv) if G in S_{p_+}(V') and phi^t(O) subset V' then G o phi^t in S_{p_+}(O) with X_{G o phi^t} = (phi^t)^* X_G = D(phi^t)^{-1} X_G o phi^t; (v) d/dt G(phi^t w) = DG(phi^t w) X_F(phi^t w), and d/dt N(phi^t w) = (hat N + hat a_0 - R)(phi^t w)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow, bpW:w5:class, stepW:w5:c-cont, stepW:w5:c-var, stepW:w5:c-skew, stepW:w5:c-symp, stepW:w5:c-inv, stepW:w5:c-trans, stepW:w5:c-time
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L413-L413 | the flow
EDGE: bpW:w5:class | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L419-L419 | S_{p_+}
EDGE: stepW:w5:c-cont | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L427-L427 | proof step
EDGE: stepW:w5:c-var | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L431-L431 | proof step
EDGE: stepW:w5:c-skew | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L434-L434 | proof step
EDGE: stepW:w5:c-symp | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L437-L437 | proof step
EDGE: stepW:w5:c-inv | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L439-L439 | proof step
EDGE: stepW:w5:c-trans | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L441-L441 | proof step
EDGE: stepW:w5:c-time | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L445-L445 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:c-cont
KIND: step
TITLE: Continuity
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-cont@L427-L430
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-cont@L427-L430
CONTRACT_ID: stepW:w5:c-cont
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow-calc: the setting of Lemma bpW:w5:flow
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:flow-calc (for ¦t¦ <= 1); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: continuity of phi^t and D phi^t (Cauchy integral)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:flow, bpW:w1:ext-unifderiv, bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-cont@L428-L428 | (ii)
EDGE: bpW:w1:ext-unifderiv | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-cont@L428-L428 | mean value inequality
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-cont@L429-L429 | Cauchy integral formula for D phi^t
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:c-var
KIND: step
TITLE: Variational equation
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L431-L433
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L431-L433
CONTRACT_ID: stepW:w5:c-var
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow-calc: the setting of Lemma bpW:w5:flow
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:flow-calc (for ¦t¦ <= 1); within the step: t, w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the variational equation
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:ext-integral, stepW:w5:c-cont, bpW:w1:deriv-continuous
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:ext-integral | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L432-L432 | differentiation under the integral
EDGE: stepW:w5:c-cont | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L433-L433 | continuity
EDGE: bpW:w1:deriv-continuous | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L433-L433 | DX_F continuous
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:c-skew
KIND: step
TITLE: Skewness
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-skew@L434-L436
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-skew@L434-L436
CONTRACT_ID: stepW:w5:c-skew
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow-calc: the setting of Lemma bpW:w5:flow
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:flow-calc (for ¦t¦ <= 1); within the step: w, A, B; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: varpi(DX_F A, B) + varpi(A, DX_F B) = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:s-class, bpW:w5:omega
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:s-class | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-skew@L434-L434 | F is C^2
EDGE: bpW:w5:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-skew@L436-L436 | antisymmetry
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L435 uses symmetry of the second Frechet derivative D^2F; C^2 regularity alone is not a proof of this symmetry, and no listed external supplies Schwarz symmetry. Do not add the symmetry as a premise of flow-calc.
```

```text
NODE: stepW:w5:c-symp
KIND: step
TITLE: Symplecticity
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L437-L438
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L437-L438
CONTRACT_ID: stepW:w5:c-symp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow-calc: the setting of Lemma bpW:w5:flow
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:flow-calc (for ¦t¦ <= 1); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (ii) symplecticity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:c-var, stepW:w5:c-skew, bpW:w3:ext-mvt
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:c-var | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L438-L438 | variational equation
EDGE: stepW:w5:c-skew | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L438-L438 | skewness
EDGE: bpW:w3:ext-mvt | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L438-L438 | zero derivative
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:c-inv
KIND: step
TITLE: Inverse
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-inv@L439-L440
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-inv@L439-L440
CONTRACT_ID: stepW:w5:c-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow-calc: the setting of Lemma bpW:w5:flow
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:flow-calc (for ¦t¦ <= 1); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iii) invertibility by Neumann series
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow, bpW:w3:ext-neumann
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-inv@L439-L439 | (ii) ¦D phi^t - I¦ <= 1/8
EDGE: bpW:w3:ext-neumann | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-inv@L440-L440 | Neumann series
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:c-trans
KIND: step
TITLE: Transport
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L441-L444
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L441-L444
CONTRACT_ID: stepW:w5:c-trans
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow-calc: the setting of Lemma bpW:w5:flow
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:flow-calc (for ¦t¦ <= 1); within the step: w, W; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) the transport formula and holomorphy of the field
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:symplectic, stepW:w5:c-symp, stepW:w5:c-inv, bpW:w3:ext-series, bpW:w1:ext-onevar
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:symplectic | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L441-L441 | the same argument
EDGE: stepW:w5:c-symp | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L442-L442 | symplecticity
EDGE: stepW:w5:c-inv | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L442-L442 | invertibility
EDGE: bpW:w3:ext-series | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L443-L443 | holomorphy of inversion on invertible operators, and analytic derivatives
EDGE: bpW:w1:ext-onevar | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L444-L444 | holomorphy of the derivative represented by a Cauchy integral
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w5#data
KIND: definition
TITLE: W5 weights a = p = 1
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5@L35-L39
PROOF_SOURCE: -
CONTRACT_ID: bpW:w5#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: fixes a = p = 1 throughout W5 (Convention bpW:w0:weights); this satisfies the weight guard (G) of W4's bracket identity and p >= 1/2; normal quantities carry the wave weights omega_{a,q}(J), J = j+2
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:ellap#WaveSpace, bpW:w4:lie-sec#guard, bpW:w4:index, bpW:w0:ellap#ellWeight
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w5-kamstep.tex#bpW:w5@L35-L35 | the headline weights a = p = 1 (Convention bpW:w0:weights)
EDGE: bpW:w4:lie-sec#guard | blueprint-W/parts/w5-kamstep.tex#bpW:w5@L36-L36 | the guard (G) holds for a = p = 1
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#bpW:w5@L37-L37 | the wave weights
EDGE: bpW:w0:ellap#ellWeight | blueprint-W/parts/w5-kamstep.tex#bpW:w5@L37-L37 | the fixed shifted wave weights omega_{a,q}(J)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled 'Weights' paragraph (SPEC hypothesis packages); its premise a = p = 1 is recorded in the SOURCE_HYPOTHESES of W5 results that use it (guard (G), pairings).
```

## Validation

- `sha256sum -c docs/graph/W/CORPUS.sha256`: all eleven source files OK.
- Permitted `inp_depgraph_slice_check.py docs/graph/W/packets W-w5a`: 50 nodes, 175 edges, 74 coverage items, 0 problems (original packets).
- Review-format check: 50 unique packet-node verdicts, 22 complete FAIL replacements; exact required fields; DEPS/EDGE agreement; existing edge targets; source ranges valid; no trailing whitespace.
- Combined read-only packet overlay with all four reports: no dependency cycles. Packets were not modified.

## Suspected blueprint errata and source gaps

1. `w5-kamstep.tex:289-290`: "H is symmetric ... because D^2P is symmetric (Schwarz, second_derivative_symmetric)" invokes an unlisted input. `stepW:w5:t-comp` now exposes it as SOURCE_GAP; the same unlisted symmetry is used for F at L435 in `c-skew`.
2. `w5-kamstep.tex:356`: "Lemma ... lie(ii), weight guard" points to the weak-bracket identity; its derivative identification is lie(iv). The accompanying citation of lemma1(ii) contains the guarded derivative identity, so this is a locator/part-number issue rather than evidence that the bracket identity is false.
The P96-K modified-divisor gap at L226-L238 is explicitly repaired here by the stronger condition 2 beta <= loss and B^natural; it is not silently converted into a hypothesis of the unmodified lemma.
