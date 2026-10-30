# W-w5b: slice review 1
Reviewer: sol-review-W-W-w5b
Verdict: FAIL

Source-only refutation review against the eleven files pinned by CORPUS.sha256 (all hashes matched). Read SPEC including wave 2 extraction, REVIEW-BRIEF rules 1-11, AGENTS, PLAN and DECISIONS. No implementation Lean, builds, lake, repository lint or state-changing git was used. The tables cover every packet node; PASS concerns topology and source transcription only.

Bare lambda in W5/W6 is the parameter weight. phi^t in W5 is a flow, not sineMode. Normal indices are j=J-2, and the weights stay at J. Parent proofs are represented by their child steps; a prerequisite used inside a child is not duplicated on the parent solely because its PROOF_SOURCE spans that child.

## Node table

| Node | Verdict | Evidence or reason |
|---|---|---|
| bpW:w5:new-ham | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| stepW:w5:n-exp | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. SOURCE_GAP: L478 exchanges the order of integration on a time triangle without a proof or a permitted external covering this domain; ext-rect gives Fubini for continuous integrands on a box, not this triangular integration statement. |
| stepW:w5:n-br | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-br@L481-L484; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-br@L481-L484 |
| stepW:w5:n-field | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L485-L487; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-field@L485-L487 |
| stepW:w5:n-conj | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L488-L492; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-conj@L488-L492 |
| bpW:w5:pullback | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| stepW:w5:p-inv | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. Missing direct edge to bpW:w3:ext-neumann at L511. SOURCE_GAP: the parameter-difference displays at L512-L513 omit the factor ¦xi-zeta¦ (or the corresponding quotient). The lambda-norm conclusion requires a Lipschitz-quotient estimate, not an unnormalised difference bound independent of the parameter distance; the graph does not silently repair those displays. |
| stepW:w5:p-dy | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L514-L516; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-dy@L514-L516 |
| stepW:w5:p-ass | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. Missing direct edge to stepW:w5:f-par at L520. |
| bpW:w5:commutator | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L526-L529; proof blueprint-W/parts/w5-kamstep.tex#bpW:w5:commutator@L530-L538 |
| stepW:w5:k-cauchy | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L531-L533; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-cauchy@L531-L533 |
| stepW:w5:k-bd | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L534-L537; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:k-bd@L534-L537 |
| bpW:w5:step | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. Part (iv), L561-L562, says whenever the same holds with alpha. That conditional premise cannot be omitted in the modified case. |
| stepW:w5:st-con | FAIL | False symbol edge: phi^t is the Hamiltonian flow, not the frozen sine basis phi_j. |
| stepW:w5:st-1 | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L571-L572; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-1@L571-L572 |
| stepW:w5:st-2 | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L573-L574; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-2@L573-L574 |
| stepW:w5:st-freq | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-freq@L575-L576; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-freq@L575-L576 |
| stepW:w5:st-div | FAIL | The subtraction argument at L579 needs the old unmodified divisor lower bound; modified step data alone does not supply it. |
| bpW:w5:action-angle | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L600-L638; proof blueprint-W/parts/w5-kamstep.tex#bpW:w5:action-angle@L639-L667 |
| stepW:w5:a-hol | FAIL | Missing direct edge to bpW:w0:periodone#linearTorus at L642. Missing direct edge to bpW:w3:coords at L642. SOURCE_GAP: L640 invokes holomorphy of the principal complex square root on Re > 0 without proof or a permitted external stating it. Preserve the principal-branch obligation in this step. |
| stepW:w5:a-dom | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-dom@L644-L646; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-dom@L644-L646 |
| stepW:w5:a-der | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-der@L647-L650; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-der@L647-L650 |
| stepW:w5:a-nf | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L651-L654; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-nf@L651-L654 |
| stepW:w5:a-field | FAIL | Missing direct edge to bpW:w0:basis#lambda-facts at L659. |
| stepW:w5:a-conj | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L661-L666; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-conj@L661-L666 |
| bpW:w5:initial | FAIL | Missing direct edge to bpW:w7:freqcoords at L681. |
| stepW:w5:i-q | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L684-L688; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-q@L684-L688 |
| stepW:w5:i-g | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L689-L691; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-g@L689-L691 |
| stepW:w5:i-k | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L692-L696; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-k@L692-L696 |
| stepW:w5:i-par | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-par@L697-L701; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-par@L697-L701 |
| stepW:w5:i-freq | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L702-L702; proof blueprint-W/parts/w5-kamstep.tex#stepW:w5:i-freq@L702-L702 |
| bpW:w5:newham-sec#bracket | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:newham-sec@L454-L455; proof - |

## Coverage

all other coverage items PASS

Every labelled unit and unlabelled prose item was checked against the raw slice. The existing mappings remain valid after the node replacements. SOURCE_GAP findings above are carried in their existing substantive step/claim nodes; their existing inventory items therefore still cover them.

Prose L594-L598 is correctly mapped to action-angle: its W3 data and branch choice are in that node. The notation-clash remark is only a source-note/ledger citation downstream.

## Complete replacement blocks

```text
NODE: bpW:w5:new-ham
KIND: lemma
TITLE: New Hamiltonian; conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L457-L472
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L473-L493
CONTRACT_ID: bpW:w5:new-ham
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Phi = phi^1, D_+ = D(s-5sigma,eta r), R(t) = (1-t) hat N + t R, H = N + P, N_+ = N + hat N = <omega_+,y> + sum Omega_{+,j} z_j zbar_j, P_+ = (P - R) o Phi + int_0^1 {R(t),F} o phi^t dt
SOURCE_QUANTIFIERS: for w in D_+, W in P^{p_+}
SOURCE_CONCLUSION: (i) H o Phi = N_+ + P_+ + hat a_0 on D_+; (ii) P_+ in S_{p_+}(D_+), real and periodic, X_{P_+} = Phi^*(X_P - X_R) + int_0^1 (phi^t)^* [X_{R(t)},X_F] dt; (iii) varpi(X_H(Phi w), D Phi(w) W) = varpi(X_{N_+}(w) + X_{P_+}(w), W) with X_N : P -> P^{p-1} of Lemma bpW:w4:lie(i) and varpi extended to P^{p-1} x P^{p_+}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow, bpW:w5:newham-sec#bracket, bpW:w5:solve, bpW:w4:lie, bpW:w4:index, bpW:w5:class, stepW:w5:n-exp, stepW:w5:n-br, stepW:w5:n-field, stepW:w5:n-conj
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L458-L458 | the flow and its setting
EDGE: bpW:w5:newham-sec#bracket | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L461-L461 | {R(t),F}
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L459-L459 | hat N, hat omega, hat Omega
EDGE: bpW:w4:lie | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L469-L469 | (i) X_N
EDGE: bpW:w4:index | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L470-L470 | (bpW:w4:pairing)
EDGE: bpW:w5:class | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L464-L464 | S_{p_+}
EDGE: stepW:w5:n-exp | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L474-L474 | proof step
EDGE: stepW:w5:n-br | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L481-L481 | proof step
EDGE: stepW:w5:n-field | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L485-L485 | proof step
EDGE: stepW:w5:n-conj | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L488-L488 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:n-exp
KIND: step
TITLE: Expansion
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L474-L480
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L474-L480
CONTRACT_ID: stepW:w5:n-exp
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:new-ham: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Phi = phi^1, D_+ = D(s-5sigma,eta r), R(t) = (1-t) hat N + t R, H = N + P, N_+ = N + hat N = <omega_+,y> + sum Omega_{+,j} z_j zbar_j, P_+ = (P - R) o Phi + int_0^1 {R(t),F} o phi^t dt
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:new-ham (for w in D_+, W in P^{p_+}); within the step: w in D_+; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: H(Phi w) = N(w) + hat N(w) + hat a_0 + (P - R)(Phi w) + int_0^1 {(1-tau) hat N + tau R, F}(phi^tau w) dtau; this is (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow, bpW:w5:flow-calc, bpW:w5:ext-ftc
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L475-L475 | (iii)
EDGE: bpW:w5:flow-calc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L475-L475 | (v)
EDGE: bpW:w5:ext-ftc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L475-L475 | calculus along curves
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: SOURCE_GAP: L478 exchanges the order of integration on a time triangle without a proof or a permitted external covering this domain; ext-rect gives Fubini for continuous integrands on a box, not this triangular integration statement.
NOTE: SOURCE_GAP: L478 exchanges the order of integration on a time triangle without a proof or a permitted external covering this domain; ext-rect gives Fubini for continuous integrands on a box, not this triangular integration statement.
```

```text
NODE: bpW:w5:pullback
KIND: lemma
TITLE: Pull-back; P96-K (12)
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L502-L506
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L507-L522
CONTRACT_ID: bpW:w5:pullback
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Y(.,xi) holomorphic fields D(s-3sigma,4 eta r) -> P^{p_+}
SOURCE_QUANTIFIERS: for ¦t¦ <= 1
SOURCE_CONCLUSION: ¦(phi^t)^* Y¦^lambda_{eta r,D_+} <= 7 ¦Y¦^lambda_{eta r,D(s-3sigma,4 eta r)} (norm ¦.¦_{p_+,eta r})
CONSTANT_SCOPE: 7 absolute
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:flow, stepW:w5:p-inv, stepW:w5:p-dy, stepW:w5:p-ass
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L503-L503 | the setting
EDGE: stepW:w5:p-inv | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L508-L508 | proof step
EDGE: stepW:w5:p-dy | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L514-L514 | proof step
EDGE: stepW:w5:p-ass | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L517-L517 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:p-inv
KIND: step
TITLE: Inverse in the small scale
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L508-L513
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L508-L513
CONTRACT_ID: stepW:w5:p-inv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:pullback: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Y(.,xi) holomorphic fields D(s-3sigma,4 eta r) -> P^{p_+}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:pullback (for ¦t¦ <= 1); within the step: W; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦D(phi^t)^{-1}¦_{p_+->p_+,eta r} <= 2 and lambda¦Delta(D phi^t)^{-1}¦ <= 4
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:omega, bpW:w5:flow, stepW:w5:f-der, bpW:w3:ext-neumann
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:omega | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L509-L509 | norm comparisons
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L509-L509 | (ii)
EDGE: stepW:w5:f-der | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L512-L512 | the parameter bound
EDGE: bpW:w3:ext-neumann | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L511-L511 | inverse norm bound from the one-half operator perturbation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: the parameter-difference displays at L512-L513 omit the factor |xi-zeta| (or the corresponding quotient). The lambda-norm conclusion requires a Lipschitz-quotient estimate, not an unnormalised difference bound independent of the parameter distance; the graph does not silently repair those displays.
```

```text
NODE: stepW:w5:p-ass
KIND: step
TITLE: Assemble
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L517-L521
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L517-L521
CONTRACT_ID: stepW:w5:p-ass
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:pullback: the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F); Y(.,xi) holomorphic fields D(s-3sigma,4 eta r) -> P^{p_+}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:pullback (for ¦t¦ <= 1); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the total bound 7 ¦Y¦^lambda
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:p-inv, stepW:w5:p-dy, bpW:w5:lambda-product, stepW:w5:f-par
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:p-inv | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L517-L517 | inverse bounds
EDGE: stepW:w5:p-dy | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L519-L519 | derivative of Y
EDGE: bpW:w5:lambda-product | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L518-L518 | lambda-norm of products
EDGE: stepW:w5:f-par | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L520-L520 | the bound on the parameter difference of the flow is used directly
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w5:step
KIND: theorem
TITLE: One KAM step
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L543-L566
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L567-L580
CONTRACT_ID: bpW:w5:step
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step data (Definition bpW:w5:data) and the smallness condition (bpW:w5:small); in the modified case also 2 beta <= p+1-p_+ for the Lipschitz parts; C_2 = 896 + 168 c_F
SOURCE_QUANTIFIERS: there exist a real holomorphic family Phi(.,xi) : D_+ = D(s-5sigma,eta r) -> D(s-4sigma,2 eta r), N_+, P_+; then for all xi in Pi
SOURCE_CONCLUSION: (i) H o Phi = N_+ + P_+ + hat a_0(xi) on D_+ with the weak conjugacy; Phi symplectic, D Phi(w) maps P^{p_+} onto itself, real, Phi(w + tau_k) = Phi(w) + tau_k; (ii) P_+ in S_{p_+}(D_+) real periodic with (bpW:w5:newerror) ¦X_{P_+}¦^lambda_{eta r,D_+} <= C_2(eps^2/(alpha sigma^t eta^2) + eta eps); (iii) ¦omega_+ - omega¦ + lambda¦.¦^L <= 6 pi eps, sup (j+2)^{p_+-p}(¦Omega_{+,j} - Omega_j¦ + lambda¦.¦^L) <= 3 eps, so (omega_+,Omega_+) satisfies (bpW:w5:freq) with M_0 + 3 eps and M_+ <= M + (6pi+3) eps/lambda (lambda > 0); (iv) for K >= 1, 0 < alpha_+ <= alpha with 6 pi (1+K)(1+K^tau) eps <= alpha - alpha_+, the divisor bounds with alpha_+ for ¦k¦_1 <= K, conditional on the same unmodified divisor bounds with alpha for the old frequencies on these modes (also with <l>^w); (v) ¦Phi - id¦^lambda_{p_+,r,D_+} <= 2 M_F and ¦D Phi - I¦^lambda_{p->p_+,r,D_+} <= 16 M_F/sigma
CONSTANT_SCOPE: C_2 = 896 + 168 c_F depends only on tau
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:data, bpW:w5:new-ham, bpW:w5:flow, bpW:w4:wave, bpW:w4:melnikov, stepW:w5:st-con, stepW:w5:st-1, stepW:w5:st-2, stepW:w5:st-freq, stepW:w5:st-div
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:data | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L544-L544 | step data and (bpW:w5:small)
EDGE: bpW:w5:new-ham | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L548-L548 | (iii) weak conjugacy
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L550-L550 | (iv)
EDGE: bpW:w4:wave | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L562-L562 | (ii) <l>^w
EDGE: bpW:w4:melnikov | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L560-L560 | Z, A_k, <l>
EDGE: stepW:w5:st-con | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L568-L568 | proof step
EDGE: stepW:w5:st-1 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L571-L571 | proof step
EDGE: stepW:w5:st-2 | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L573-L573 | proof step
EDGE: stepW:w5:st-freq | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L575-L575 | proof step
EDGE: stepW:w5:st-div | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L577-L577 | proof step
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:st-con
KIND: step
TITLE: Construction
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L570
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L570
CONTRACT_ID: stepW:w5:st-con
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:step: step data (Definition bpW:w5:data) and the smallness condition (bpW:w5:small); in the modified case also 2 beta <= p+1-p_+ for the Lipschitz parts; C_2 = 896 + 168 c_F
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:step (there exist a real holomorphic family Phi(.,xi) : D_+ = D(s-5sigma,eta r) -> D(s-4sigma,2 eta r), N_+, P_+; then for all xi in Pi); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Phi = phi^1, (i), the formula for X_{P_+}, and (v)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w5:taylor, bpW:w5:solve, bpW:w5:flow, bpW:w5:flow-calc, bpW:w5:new-ham
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w5:taylor | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L568 | R
EDGE: bpW:w5:solve | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L568 | F
EDGE: bpW:w5:flow | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L568 | the flow; (i)-(ii)
EDGE: bpW:w5:flow-calc | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L569-L569 | calculus
EDGE: bpW:w5:new-ham | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L569-L569 | the new Hamiltonian
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:st-div
KIND: step
TITLE: Divisors
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L577-L579
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L577-L579
CONTRACT_ID: stepW:w5:st-div
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:step: step data (Definition bpW:w5:data) and the smallness condition (bpW:w5:small); in the modified case also 2 beta <= p+1-p_+ for the Lipschitz parts; C_2 = 896 + 168 c_F; for the modes |k|_1 <= K under consideration, the old frequencies satisfy the same unmodified divisor lower bound with alpha (L561-L562)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:step (there exist a real holomorphic family Phi(.,xi) : D_+ = D(s-5sigma,eta r) -> D(s-4sigma,2 eta r), N_+, P_+; then for all xi in Pi); within the step: ¦k¦_1 <= K; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): the corrections shift the divisors by at most (alpha - alpha_+)<l>/A_k
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w5:st-freq
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w5:st-freq | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L577-L577 | the frequency corrections
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w5:a-hol
KIND: step
TITLE: Holomorphy and reality
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L640-L643
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L640-L643
CONTRACT_ID: stepW:w5:a-hol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:action-angle: W3's normal form H' = Lambda + bar G + G^nor + K on B_{rho_1} (Theorem bpW:w3:main), W = W_{a,p}; a = p = 1; xi in C^2, w = (theta,y,u,v) in P with Re(xi_i + y_i) > 0; A_xi(w) as displayed (principal square root); (ii) 0 < s <= 1/8, r > 0, t > 0, ¦xi¦_infty <= t, Re xi_i >= 2r^2, c_A = 2200
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:action-angle (for all such xi, w; every q in R in (iii)); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (i) holomorphy, reality and the linear torus
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:periodone#linearTorus, bpW:w3:coords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L642-L642 | the displayed recovered q_i,p_i are the frozen linear torus
EDGE: bpW:w3:coords | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L642-L642 | the inverse Z coordinate map is used to recover q_i,p_i
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: SOURCE_GAP: L640 invokes holomorphy of the principal complex square root on Re > 0 without proof or a permitted external stating it. Preserve the principal-branch obligation in this step.
```

```text
NODE: stepW:w5:a-field
KIND: step
TITLE: Fields
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L655-L660
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L655-L660
CONTRACT_ID: stepW:w5:a-field
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:action-angle: W3's normal form H' = Lambda + bar G + G^nor + K on B_{rho_1} (Theorem bpW:w3:main), W = W_{a,p}; a = p = 1; xi in C^2, w = (theta,y,u,v) in P with Re(xi_i + y_i) > 0; A_xi(w) as displayed (principal square root); (ii) 0 < s <= 1/8, r > 0, t > 0, ¦xi¦_infty <= t, Re xi_i >= 2r^2, c_A = 2200
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w5:action-angle (for all such xi, w; every q in R in (iii)); within the step: w; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (v) the field of P_xi lies in P^{p+1}
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, stepW:w5:a-der, bpW:w0:basis#lam, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L655-L655 | (ii)-(iii) fields into W+
EDGE: stepW:w5:a-der | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L656-L656 | (iii)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L658-L658 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L659-L659 | J/lambda_J <= 1 gives the one-weight smoothing multiplier bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w5:initial
KIND: proposition
TITLE: The initial perturbation; KP96 \S7, Step~3
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L673-L682
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L683-L703
CONTRACT_ID: bpW:w5:initial
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0, a = p = 1; rho_1, C_*, C'_K W3's constants; 0 < s <= 1/8, 0 < r <= 1, t > 0, rho_xi > 0, Pi subset R^2 such that every zeta in C^2 with ¦zeta - xi¦_infty < rho_xi for some xi in Pi satisfies Re zeta_i >= 2r^2 and ¦zeta¦_infty <= t, and c_A(t + r^2) < rho_1^2; eps_in as displayed
SOURCE_QUANTIFIERS: for every lambda >= 0
SOURCE_CONCLUSION: P_xi in S_{p+1}(D(s,r)) is a real periodic family on Pi and ¦X_P¦^lambda_{r,D(s,r)} <= eps_in(1 + 4 lambda/rho_xi); omega^0, Omega^0_{j+2} satisfy (bpW:w4:freq) (hence (bpW:w5:freq)) with the constants of Lemma bpW:w4:wave and ¦omega^0(xi) - omega^0(xi')¦ <= N_A ¦xi - xi'¦
CONSTANT_SCOPE: eps_in explicit in r, t, C_*, C'_K, c_A
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:main, bpW:w3:majorant, bpW:w5:action-angle, bpW:w4:wave, stepW:w5:i-q, stepW:w5:i-g, stepW:w5:i-k, stepW:w5:i-par, stepW:w5:i-freq, bpW:w7:freqcoords
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:main | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L674-L674 | rho_1, C'_K
EDGE: bpW:w3:majorant | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L674-L674 | C_*
EDGE: bpW:w5:action-angle | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L678-L678 | P_xi
EDGE: bpW:w4:wave | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L681-L681 | the frequency constants
EDGE: stepW:w5:i-q | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L684-L684 | proof step
EDGE: stepW:w5:i-g | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L689-L689 | proof step
EDGE: stepW:w5:i-k | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L692-L692 | proof step
EDGE: stepW:w5:i-par | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L697-L697 | proof step
EDGE: stepW:w5:i-freq | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L702-L702 | proof step
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L681-L681 | N_A in the stated Lipschitz conclusion is the norm of A defined by freqcoords(ii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Validation

- `sha256sum -c docs/graph/W/CORPUS.sha256`: all eleven source files OK.
- Permitted `inp_depgraph_slice_check.py docs/graph/W/packets W-w5b`: 32 nodes, 120 edges, 48 coverage items, 0 problems (original packets).
- Review-format check: 32 unique packet-node verdicts, 11 complete FAIL replacements; exact required fields; DEPS/EDGE agreement; existing edge targets; source ranges valid; no trailing whitespace.
- Combined read-only packet overlay with all four reports: no dependency cycles. Packets were not modified.

## Suspected blueprint errata and source gaps

1. `w5-kamstep.tex:512-513`: "lambda |Delta D phi^t| ... <=1" and "lambda |Delta(D phi^t)^-1|<=4" omit a parameter-distance factor or division by that distance. L513 itself uses lambda N_1 <= |xi-zeta| M_F. The claimed parameter-independent difference estimates do not follow literally; the lambda norm requires bounds on the quotients. The replacement preserves this issue in `p-inv`.
2. `w5-kamstep.tex:640`: "sqrt is holomorphic on Re>0" has neither a proof in the pinned corpus nor a permitted external covering the principal square root. This unlisted input is retained in `a-hol` as SOURCE_GAP.
3. `w5-kamstep.tex:478`: "exchanging the order of integration" uses a triangular time domain. The listed box-continuity Fubini item does not directly cover it, and this reduction is not given. The existing `n-exp` step retains this source-input gap.

The false sineMode edges are packet defects, not blueprint errata.
