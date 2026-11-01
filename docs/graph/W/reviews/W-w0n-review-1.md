# W-w0n independent review 1

Reviewer: sol-review-W-w0n. Verdict: **FAIL**.

Scope: all 429 lines of w0-normalization.tex; SPEC and REVIEW-BRIEF; governing AGENTS/PLAN/DECISIONS; cross-part definitions in w0-conventions.tex and W1 external, Young and sine-completeness statements/proofs. Reviewed rendered packets, not writer specs. No Lean files, git, lake, builds or lint used. Wave-1 root unreachability is expected and is not a finding.

Structural check: `python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/W/packets W-w0n` exited 0: `W-w0n: 38 nodes, 122 edges, 62 coverage items, 0 problems`. This does not validate source fidelity.

Main findings: derived estimates occur as source hypotheses; several frozen objects and prerequisite estimates lack direct edges. In particular analyticity assumes boundedness without an edge to smoothing; selection asserts absolute convergence without its convolution finiteness dependency; the two-against-two step omits the g != 0 premise and selection-rule supplier. The corrected cubic constant, quartic prefactor, action normalization and clockwise sign agree with the source. Here q,p always denote coefficient sequences; frozen reconstructions use weighted inputs y with q=coeff y, as recorded by W-w0c. No identification of q with y is asserted.

Node table (replacement blocks below are proposals requiring independent delta review):

| Node | Verdict | Source spans re-read or reason |
|---|---|---|
| bpW:w0n:recon-bounded | PASS | blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L18-L27; blueprint-W/parts/w0-normalization.tex#bpW:w0n:recon-bounded@L29-L35 |
| bpW:w0n:quartic-coeff | PASS | blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L40-L51; blueprint-W/parts/w0-normalization.tex#bpW:w0n:quartic-coeff@L53-L69 |
| stepW:w0n:prod | PASS | blueprint-W/parts/w0-normalization.tex#stepW:w0n:prod@L54-L56 |
| stepW:w0n:cos | FAIL | restore source premises; move derived ingredients to DEPS; restore inherited quantifier scope |
| stepW:w0n:signed | FAIL | restore source premises; move derived ingredients to DEPS |
| bpW:w0n:gradient | FAIL | missing direct bpW:w0:basis#lam use at L77; missing direct bpW:w0:basis#sineMode use at L86 |
| bpW:w0n:algebra | PASS | blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L94-L98; blueprint-W/parts/w0-normalization.tex#bpW:w0n:algebra@L100-L113 |
| stepW:w0n:weight | PASS | blueprint-W/parts/w0-normalization.tex#stepW:w0n:weight@L102-L106 |
| stepW:w0n:young | FAIL | restore source premises; move derived ingredients to DEPS; restore inherited quantifier scope |
| bpW:w0n:cubic-bound | FAIL | Missing direct gradient citation at L125 and algebra constant at L124; retain symmetry in SOURCE_CONCLUSION. |
| stepW:w0n:majorant | FAIL | missing direct bpW:w0:basis#lam use at L133; restore source premises; move derived ingredients to DEPS; restore inherited quantifier scope |
| stepW:w0n:selection | FAIL | missing direct bpW:w0n:algebra use at L141; restore source premises; move derived ingredients to DEPS; restore inherited quantifier scope |
| stepW:w0n:smoothing | FAIL | missing direct bpW:w0:basis#lam use at L143; restore source premises; move derived ingredients to DEPS; restore inherited quantifier scope |
| stepW:w0n:analytic | FAIL | missing direct bpW:w0:Gq#cubicGrad use at L154; missing direct stepW:w0n:smoothing use at L151; restore source premises; move derived ingredients to DEPS; restore inherited quantifier scope |
| bpW:w0n:pde-equiv | FAIL | missing direct bpW:w0:basis#lam use at L178; missing direct bpW:w0:Gq#cubicGrad use at L178; missing direct bpW:w0:basis#sineMode use at L178 |
| stepW:w0n:force | FAIL | missing direct bpW:w0:reconstruction#reconU use at L187; missing direct bpW:w0:Gq#cubicGrad use at L187 |
| stepW:w0n:time | FAIL | missing direct bpW:w0:basis#lam use at L194; missing direct bpW:w0:reconstruction#reconU use at L196; missing direct bpW:w0:Gq#cubicGrad use at L196; L195 asserts dot q is C^1, not merely q is C^1 |
| stepW:w0n:ident | FAIL | missing direct bpW:w0:basis#lam use at L200; missing direct bpW:w0:reconstruction#reconU use at L200; missing direct bpW:w0:Gq#cubicGrad use at L200; restore source premises; move derived ingredients to DEPS |
| stepW:w0n:converse | FAIL | missing direct bpW:w0:basis#lam use at L203; missing direct bpW:w0:reconstruction#reconU use at L203; missing direct bpW:w0:reconstruction#reconV use at L203; missing direct bpW:w0:Gq#cubicGrad use at L207 |
| bpW:w0n:nonres | PASS | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L220-L224; blueprint-W/parts/w0-normalization.tex#bpW:w0n:nonres@L226-L247 |
| stepW:w0n:31 | FAIL | missing direct bpW:w0:basis#lam use at L231; missing direct bpW:w0n:quartic-coeff use at L231; restore source premises; move derived ingredients to DEPS; restore inherited quantifier scope |
| stepW:w0n:22 | FAIL | missing direct bpW:w0:basis#lam use at L234; missing direct bpW:w0n:quartic-coeff use at L235; restore source premises; move derived ingredients to DEPS; restore inherited quantifier scope |
| bpW:w0n:Qdef | PASS | blueprint-W/parts/w0-normalization.tex#bpW:w0n:Qdef@L270-L273 |
| bpW:w0n:AB | PASS | blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L275-L286; blueprint-W/parts/w0-normalization.tex#bpW:w0n:AB@L288-L305 |
| stepW:w0n:resavg | FAIL | missing direct bpW:w0n:gradient use at L294 |
| stepW:w0n:moments | PASS | blueprint-W/parts/w0-normalization.tex#stepW:w0n:moments@L295-L298 |
| stepW:w0n:sum | FAIL | missing direct bpW:w0:basis#lam use at L300; restore source premises; move derived ingredients to DEPS; restore inherited quantifier scope |
| bpW:w0n:formal-birkhoff | FAIL | missing direct bpW:w0:basis#lam use at L309 |
| bpW:w0n:nondeg | FAIL | missing direct bpW:w0:basis#lam use at L349 |
| stepW:w0n:det | FAIL | missing direct bpW:w0:basis#lam use at L357; retain the additional general-n determinant identity at L358-L359 |
| stepW:w0n:A2 | FAIL | missing direct bpW:w0:basis#lam use at L361 |
| stepW:w0n:A3red | FAIL | missing direct bpW:w0:basis#lam use at L364 |
| stepW:w0n:l1 | FAIL | missing direct bpW:w0:basis#lam use at L370; missing direct bpW:w0:basis#lambda-facts use at L372; restore source premises; move derived ingredients to DEPS; restore inherited quantifier scope |
| stepW:w0n:l2 | FAIL | missing direct bpW:w0:basis#lam use at L374; restore source premises; move derived ingredients to DEPS; restore inherited quantifier scope |
| bpW:w0n:duffing | FAIL | missing direct bpW:w0:basis#lam use at L394; missing direct bpW:w0:basis#sineMode use at L392; retain asymptotic remainder and leading-order amplitude/action qualification at L395-L410 |
| bpW:w0n:birkhoff#data | PASS | blueprint-W/parts/w0-normalization.tex#bpW:w0n:birkhoff@L258-L268 |
| bpW:w0n:nondeg-sec#data | FAIL | missing direct bpW:w0:basis#lam use at L341 |
| bpW:w0n:ledger#ext-lindstedt | PASS | blueprint-W/parts/w0-normalization.tex#bpW:w0n:ledger@L422-L423 |

Coverage table:

| Item | Verdict | Reason |
|---|---|---|
| w0-normalization:sourcegap-L159 | FAIL | The sourcegap note spans L159-L161; the recorded range stops at its opening line. |

all other coverage items PASS. In particular prose L258-L268 and L341-L344 are represented by data nodes, the ledger maps its unlabelled external, and the N-1 repair maps to majorant. Administrative remarks and forward/provenance pointers are valid exclusions.

Replacement fragments (complete blocks; all unchanged fields retained):

```text
NODE: stepW:w0n:cos
KIND: step
TITLE: Cosine integrals
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:cos@L57-L64
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:cos@L57-L64
CONTRACT_ID: stepW:w0n:cos
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: i,j,k,l >= 1; A,B in Z (auxiliary integration variables)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: int_0^pi cos Ax cos Bx dx = (pi/2)([A=B] + [A=-B]); hence the eight-bracket formula for g_ijkl, which reduces to the stated closed form, with g_iiii = 3/(2pi) and g_iijj = 1/pi (i != j)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:prod
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:prod | blueprint-W/parts/w0-normalization.tex#stepW:w0n:cos@L60-L60 | integrates the product-to-sum expansion termwise
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:signed
KIND: step
TITLE: Signed form
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:signed@L65-L68
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:signed@L65-L68
CONTRACT_ID: stepW:w0n:signed
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: i,j,k,l >= 1
SOURCE_QUANTIFIERS: for all i, j, k, l >= 1
SOURCE_CONCLUSION: the seven bracket relations solved for l give the signed form (bpW:w0n:g-signed) (the eighth pattern l = -i-j-k is impossible for l >= 1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:cos
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:cos | blueprint-W/parts/w0-normalization.tex#stepW:w0n:signed@L66-L66 | rewrites the seven relations of the closed form
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w0n:gradient
KIND: lemma
TITLE: $G$ and its gradient as absolutely convergent sums
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L76-L82
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L84-L92
CONTRACT_ID: bpW:w0n:gradient
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a > 0, p >= 0, q in l^{a,p}; hat q_j = q_j/sqrt(lambda_j)
SOURCE_QUANTIFIERS: for all a > 0, p >= 0, q
SOURCE_CONCLUSION: G(q) = (1/4) sum_{i,j,k,l} g_ijkl hat q_i hat q_j hat q_k hat q_l and G_q(q)_l = (1/sqrt(lambda_l)) sum_{i,j,k} g_ijkl hat q_i hat q_j hat q_k, both absolutely convergent; G is Gateaux differentiable along every coordinate with dG/dq_l = G_q(q)_l; int_0^pi U_m(q)^3 phi_l dx = sqrt(lambda_l) G_q(q)_l
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:recon-bounded, bpW:w0:reconstruction#reconU, bpW:w0:H, bpW:w0n:quartic-coeff, bpW:w1:ext-integral, bpW:w0:Gq#cubicGrad, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L85-L85 | k = 0: sum ¦hat q_j¦ < infinity and U_m(q) = sum hat q_j phi_j uniformly
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L85-L85 | U_m(q) = sum hat q_j phi_j
EDGE: bpW:w0:H | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L88-L88 | G(q) = (1/4) int U_m(q)^4
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L86-L86 | the coefficients g_ijkl of the termwise-integrated quadruple series
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L87-L87 | termwise integration (dominated convergence for series) and differentiation under the integral
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L90-L90 | identifies int U_m(q)^3 phi_l / sqrt(lambda_l) with G_q(q)_l
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L77-L77 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#bpW:w0n:gradient@L86-L86 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:young
KIND: step
TITLE: Young and Cauchy--Schwarz
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L107-L112
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L107-L112
CONTRACT_ID: stepW:w0n:young
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, s >= 1; c,d in l_b^{a,s}; w_l = <l>^s exp(a abs(l)); C_l = w_l abs(c_l), D_l = w_l abs(d_l); C'_l=C_l/<l>^s, D'_l=D_l/<l>^s
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: w_l ¦(c*d)_l¦ <= 2^{s-1}((C*D')_l + (C'*D)_l); with Young ¦¦X*Y¦¦_2 <= ¦¦X¦¦_2 ¦¦Y¦¦_1 and ¦¦D'¦¦_1 <= ¦¦D¦¦_2 (1+2 zeta(2s))^{1/2} this gives the bound with K_s and the absolute convergence
CONSTANT_SCOPE: K_s depends only on s
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:weight, bpW:w1:young
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:weight | blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L108-L108 | inserts the weight inequality
EDGE: bpW:w1:young | blueprint-W/parts/w0-normalization.tex#stepW:w0n:young@L109-L109 | Young's inequality (i) and the l^1 control with 1+2 zeta(2s) (ii)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:majorant
KIND: step
TITLE: Even majorants
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L132-L135
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L132-L135
CONTRACT_ID: stepW:w0n:majorant
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; q,q',q'' in l_C^{a,p}; define x_i=abs(q_abs(i))/sqrt(lambda_abs(i)) for i != 0 and x_0=0, and similarly x',x''
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: x is even and ¦¦x¦¦_{a,p+1/2}^2 = 2 sum_i (i/lambda_i) i^{2p} e^{2ai} ¦q_i¦^2 <= 2 ¦¦q¦¦_{a,p}^2 (the corrected constant sqrt 2, errata N-1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:twosided, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:twosided | blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L135-L135 | the two-sided norm of the majorant
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L134-L134 | lambda_i >= i (i/lambda_i < 1)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:majorant@L133-L133 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:selection
KIND: step
TITLE: Selection rule bound
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L136-L141
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L136-L141
CONTRACT_ID: stepW:w0n:selection
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; q,q',q'' in l_C^{a,p}; l >= 1; hat q and even majorants are the explicit sequences defined at L120-L121 and L133-L134
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: sum_{i,j,k} ¦g_ijkl¦ ¦hat q_i hat q'_j hat q''_k¦ <= (1/(2pi)) (x*x'*x'')_l, so the sum defining T converges absolutely
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, stepW:w0n:majorant, bpW:w0n:algebra
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L137-L137 | the signed form (bpW:w0n:g-signed) and its bound
EDGE: stepW:w0n:majorant | blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L139-L139 | the even majorants x, x', x''
EDGE: bpW:w0n:algebra | blueprint-W/parts/w0-normalization.tex#stepW:w0n:selection@L141-L141 | finiteness of the triple convolution: apply the algebra estimate twice, s=p+1/2 >= 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:smoothing
KIND: step
TITLE: Smoothing
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L142-L148
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L142-L148
CONTRACT_ID: stepW:w0n:smoothing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; q,q',q'' in l_C^{a,p}; s=p+1/2; X=x*x'*x'' with the explicit majorants of L133-L134
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: ¦¦T¦¦_{a,p+1}^2 <= (1/(8 pi^2)) ¦¦X¦¦_{a,p+1/2}^2 and ¦¦X¦¦ <= K_s^2 2^{3/2} prod ¦¦q¦¦, hence ¦¦T¦¦_{a,p+1} <= (K_s^2/pi) prod ¦¦q¦¦
CONSTANT_SCOPE: K_s depends only on s = p + 1/2
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:selection, bpW:w0:basis#lambda-facts, bpW:w0n:algebra, stepW:w0n:majorant, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:selection | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L143-L143 | the pointwise bound by X_l/(2pi)
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L143-L143 | l/lambda_l <= 1
EDGE: bpW:w0n:algebra | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L146-L146 | the algebra bound with s = p + 1/2 >= 1, applied twice
EDGE: stepW:w0n:majorant | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L147-L147 | ¦¦x¦¦ <= sqrt 2 ¦¦q¦¦
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:smoothing@L143-L143 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:analytic
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L149-L154
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L149-L154
CONTRACT_ID: stepW:w0n:analytic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; q in l_C^{a,p}; T is the series formula of L120-L121 (boundedness and symmetry are proved, not assumed)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: T is trilinear and symmetric; q -> T(q,q,q) is a continuous homogeneous cubic polynomial, analytic on the whole space, real on real sequences; for a > 0 it is G_q (Lemma bpW:w0n:gradient)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:quartic-coeff, bpW:w1:ext-analytic, bpW:w0n:gradient, bpW:w0:Gq#cubicGrad, stepW:w0n:smoothing
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L150-L150 | symmetry of g
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L152-L152 | a continuous multilinear map (its diagonal) is analytic
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L154-L154 | identification with G_q for a > 0
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L154-L154 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: stepW:w0n:smoothing | blueprint-W/parts/w0-normalization.tex#stepW:w0n:analytic@L151-L151 | boundedness of the trilinear formula is supplied by the preceding smoothing estimate
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w0n:pde-equiv
KIND: proposition
TITLE: Equivalence, (a)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L165-L183
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L185-L209
CONTRACT_ID: bpW:w0n:pde-equiv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I subset R open interval; q, p : I -> l^{1,1}; (i): q, p continuous into l^{1,1}, continuously differentiable into l^{1,0}, satisfying (bpW:w0:coeffsys) in l^{1,0}; (ii): u(t,x) = U_m(q(t))(x) is a classical solution of (bpW:w0:eq) on I and u_t(t,.) = V_m(p(t)) for every t
SOURCE_QUANTIFIERS: for every open I and q, p as stated; (force identity) for every q in l^{1,1}
SOURCE_CONCLUSION: (i) u = U_m(q(t)) is a classical solution of (bpW:w0:eq) on I with u_t = V_m(p(t)); (ii) every q_j, p_j is C^1 on I and (bpW:w0:coeffsys) holds coordinatewise; and (bpW:w0n:force): U_m(q)^3 = sum_l sqrt(lambda_l) G_q(q)_l phi_l uniformly on [0,pi] and -d_x^2 U_m(q) + m U_m(q) = U_m(lambda^2 q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:eqmotion, bpW:w0:nlw#IsClassicalSolution, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, stepW:w0n:force, stepW:w0n:time, stepW:w0n:ident, stepW:w0n:converse, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L169-L169 | the coefficient system (bpW:w0:coeffsys)
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L170-L170 | classical solution of (bpW:w0:eq)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L170-L170 | u = U_m(q(t))
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L171-L171 | u_t = V_m(p(t))
EDGE: stepW:w0n:force | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L186-L186 | proof step
EDGE: stepW:w0n:time | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L193-L193 | proof step
EDGE: stepW:w0n:ident | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L199-L199 | proof step
EDGE: stepW:w0n:converse | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L202-L202 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L178-L178 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L178-L178 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#bpW:w0n:pde-equiv@L178-L178 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:force
KIND: step
TITLE: Force identity
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L186-L192
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L186-L192
CONTRACT_ID: stepW:w0n:force
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: q in l^{1,1}; f = U_m(q)^3 in C([0,pi])
SOURCE_QUANTIFIERS: for q
SOURCE_CONCLUSION: (bpW:w0n:force): U_m(q)^3 = sum_l sqrt(lambda_l) G_q(q)_l phi_l uniformly on [0,pi], and -d_x^2 U_m(q) + m U_m(q) = U_m(lambda^2 q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient, bpW:w0n:cubic-bound, bpW:w0n:recon-bounded, bpW:w1:sine-completeness, bpW:w0:basis#sineMode, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L187-L187 | int f phi_l = sqrt(lambda_l) G_q(q)_l
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L188-L188 | (sqrt(lambda_l) G_q(q)_l) lies in l^{1,1}
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L188-L188 | uniform convergence of S (k = 0) and termwise differentiation (k = 2)
EDGE: bpW:w1:sine-completeness | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L190-L190 | (phi_l) is a complete orthonormal system of L^2(0,pi)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L192-L192 | -phi_j'' + m phi_j = lambda_j^2 phi_j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L192-L192 | the eigenvalue lambda_j^2 = j^2 + m
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L187-L187 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#stepW:w0n:force@L187-L187 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:time
KIND: step
TITLE: Time regularity
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L193-L198
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L193-L198
CONTRACT_ID: stepW:w0n:time
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the hypotheses of (i)
SOURCE_QUANTIFIERS: t in I
SOURCE_CONCLUSION: dot q is C^1 into l^{1,-1}, hence q is C^2 there, with ddot q = -lambda^2 q - lambda G_q(q); t -> u(t,.) is C^2 into C^2([0,pi]); u,u_t,u_tt,u_x,u_xx exist and are jointly continuous; u_t=U_m(lambda p)=V_m(p), u_tt=U_m(ddot q)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:eqmotion, bpW:w0n:recon-bounded, bpW:w0:reconstruction#reconV, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L194-L194 | dot q = lambda p and dot p = -lambda q - G_q(q)
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L196-L196 | lambda bounded l^{1,0} -> l^{1,-1}; U_m : l^{1,-1} -> C^2([0,pi]) bounded linear
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L198-L198 | U_m(lambda p) = V_m(p)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L194-L194 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L196-L196 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#stepW:w0n:time@L196-L196 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:ident
KIND: step
TITLE: Identification
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L199-L201
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L199-L201
CONTRACT_ID: stepW:w0n:ident
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: I subset R open interval; q,p:I -> l^{1,1}, continuous there and C^1 into l^{1,0}, satisfying the coefficient system in l^{1,0}; u(t,x)=U_m(q(t))(x)
SOURCE_QUANTIFIERS: t in I
SOURCE_CONCLUSION: u_tt = u_xx - m u - u^3 and u(t,0) = u(t,pi) = 0, so u is a classical solution with u_t = V_m(p)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:force, stepW:w0n:time, bpW:w0n:recon-bounded, bpW:w0:nlw#IsClassicalSolution, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:force | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L200-L200 | U_m(lambda^2 q) = -u_xx + m u and U_m(lambda G_q(q)) = u^3
EDGE: stepW:w0n:time | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L200-L200 | u_tt = U_m(ddot q)
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L201-L201 | boundary values vanish
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L201-L201 | the definition of classical solution being verified
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L200-L200 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L200-L200 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#stepW:w0n:ident@L200-L200 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:converse
KIND: step
TITLE: Converse
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L202-L208
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L202-L208
CONTRACT_ID: stepW:w0n:converse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the hypotheses of (ii)
SOURCE_QUANTIFIERS: t in I, l >= 1
SOURCE_CONCLUSION: int u phi_l = q_l/sqrt(lambda_l), int u_t phi_l = sqrt(lambda_l) p_l; dot q_l = lambda_l p_l and sqrt(lambda_l) dot p_l = int u_tt phi_l = -lambda_l^2 q_l/sqrt(lambda_l) - sqrt(lambda_l) G_q(q)_l, i.e. (bpW:w0:coeffsys) coordinatewise with q_l, p_l in C^1
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:nlw#IsClassicalSolution, bpW:w0n:recon-bounded, bpW:w1:ext-integral, bpW:w0:basis#sineMode, bpW:w0n:gradient, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:Gq#cubicGrad
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L204-L204 | u_t, u_tt continuous; the equation and boundary values
EDGE: bpW:w0n:recon-bounded | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L203-L203 | the coefficient formula int (sum c_j phi_j) phi_l = c_l
EDGE: bpW:w1:ext-integral | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L204-L204 | differentiation under the integral sign
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L206-L206 | phi_l(0) = phi_l(pi) = 0 and phi_l'' = -l^2 phi_l (integration by parts)
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L207-L207 | int u^3 phi_l = sqrt(lambda_l) G_q(q)_l
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L203-L203 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L203-L203 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L203-L203 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#stepW:w0n:converse@L207-L207 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:31
KIND: step
TITLE: Four or three equal signs
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L229-L232
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L229-L232
CONTRACT_ID: stepW:w0n:31
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; a,b,c,d >= 1 with g_abcd != 0; sigma in {+1,-1}^4; sum sigma_r lambda_index(r)=0; consider the cases of four or three equal signs
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: all four signs equal is impossible; three equal signs are impossible since lambda_x + lambda_y > lambda_{x+y} and lambda_d <= lambda_{a+b+c} < lambda_a + lambda_b + lambda_c
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:mass, bpW:w0:basis#lam, bpW:w0n:quartic-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L231-L231 | lambda > 0 and j -> lambda_j increasing
EDGE: bpW:w0:mass | blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L232-L232 | squaring: 2 sqrt((x^2+m)(y^2+m)) > 2xy - m uses m > 0
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L231-L231 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:31@L231-L231 | g_abcd != 0 supplies d <= a+b+c via the selection rule at L227-L228
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:22
KIND: step
TITLE: Two against two
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L233-L246
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L233-L246
CONTRACT_ID: stepW:w0n:22
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; a,b,c,d >= 1 with g_abcd != 0; lambda_a+lambda_b=lambda_c+lambda_d; {a,b} != {c,d} as multisets (contradiction case); f(s)=sqrt(s^2+m)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: case (1) a+b = c+d, case (2) a+c = b+d, case (3) a = b+c+d each lead to a contradiction; the cases are exhaustive
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam, bpW:w0n:quartic-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L236-L236 | strict convexity of f, f' > 0 increasing
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L234-L234 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:22@L235-L235 | the signed index relation used in the exhaustive cases comes from L227-L228
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:resavg
KIND: step
TITLE: Resonant equals averaged
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L289-L294
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L289-L294
CONTRACT_ID: stepW:w0n:resavg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the monomials of (bpW:w0n:Gz) with nonzero coefficient
SOURCE_QUANTIFIERS: monomials z^alpha zbar^beta
SOURCE_CONCLUSION: a monomial is resonant iff alpha = beta (it is I_a I_b); the angle average of z^alpha zbar^beta is delta_{alpha beta} I^alpha; hence bar G is the part of <G> (extended from finitely supported q by the absolutely convergent formula) with at least one tangential action
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:nonres, bpW:w0n:birkhoff#data, bpW:w0:actions, bpW:w0n:Qdef, bpW:w0n:gradient
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:nonres | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L290-L290 | resonance with nonzero coefficient forces alpha = beta
EDGE: bpW:w0n:birkhoff#data | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L290-L290 | the monomials of (bpW:w0n:Gz)
EDGE: bpW:w0:actions | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L291-L291 | z_j = sqrt(I_j) e^{-i phi_j}
EDGE: bpW:w0n:Qdef | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L292-L292 | bar G as the resonant tangential monomials
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:resavg@L294-L294 | absolute convergence justifies extension of the finite-support average
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:sum
KIND: step
TITLE: Summation
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L299-L304
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L299-L304
CONTRACT_ID: stepW:w0n:sum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; oscillator actions I_j=abs(z_j)^2; y_j=I_j/lambda_j; first compute on finite support and extend as at L293-L294
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: <G> = (9/(16pi)) sum y_i^2 + (3/(2pi)) sum_{i<j} y_i y_j, which is (bpW:w0n:avgG); matching gives A and B
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient, bpW:w0n:quartic-coeff, stepW:w0n:moments, stepW:w0n:resavg, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L300-L300 | G = (1/4) sum g_ijkl hat q^4 with hat q = q/sqrt(lambda)
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L300-L300 | g_iiii = 3/(2pi), g_iijj = 1/pi
EDGE: stepW:w0n:moments | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L301-L301 | the moments 3/2 I^2, I_i I_j and the multiplicities
EDGE: stepW:w0n:resavg | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L303-L303 | bar G = the part of <G> with a tangential action
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:sum@L300-L300 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w0n:formal-birkhoff
KIND: proposition
TITLE: Formal partial Birkhoff transformation
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L307-L315
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L317-L323
CONTRACT_ID: bpW:w0n:formal-birkhoff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: F the quartic polynomial with coefficient c_ab/(-i<alpha-beta,hat lambda>) on each nonresonant monomial z^alpha zbar^beta of G^tan (coefficient c_ab) and zero otherwise
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: F is real; X_Lambda F = G^tan - bar G (X_Lambda F = dF/dt along the linear flow); formally H o Phi^1_F = Lambda + bar G + G^nor + (terms of degree >= 6); the quartic part of the normal form is independent of the choice of F among solutions of X_Lambda F = G^tan - bar G
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:birkhoff#data, bpW:w0n:Qdef, bpW:w0n:nonres, bpW:w0:z, bpW:w0:H, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:birkhoff#data | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L308-L308 | monomials of G^tan, resonance, divisors <alpha-beta,hat lambda>
EDGE: bpW:w0n:Qdef | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L310-L310 | bar G and the normal form
EDGE: bpW:w0n:nonres | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L318-L318 | the divisors of nonresonant monomials are nonzero
EDGE: bpW:w0:z | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L318-L318 | X_Lambda (z^alpha zbar^beta) = -i<alpha-beta,hat lambda> z^alpha zbar^beta along dz = -i lambda z
EDGE: bpW:w0:H | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L321-L321 | H = Lambda + G in the Lie series
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:formal-birkhoff@L309-L309 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w0n:nondeg
KIND: theorem
TITLE: Nondegeneracy, (e)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L346-L353
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L355-L377
CONTRACT_ID: bpW:w0n:nondeg
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: J = {1,2}; m > 0; A, B of Theorem bpW:w0n:AB; (A1)-(A3) as in bpW:w0n:nondeg-sec#data
SOURCE_QUANTIFIERS: for every m > 0
SOURCE_CONCLUSION: (i) det A = -63/(64 pi^2 lambda_1^2 lambda_2^2) = -63/(64 pi^2 (1+m)(4+m)) != 0; (ii) <l,lambda_N> != 0 for 1 <= ¦l¦ <= 2; (iii) (A3) holds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:nondeg-sec#data, bpW:w0n:AB, stepW:w0n:det, stepW:w0n:A2, stepW:w0n:A3red, stepW:w0n:l1, stepW:w0n:l2, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:nondeg-sec#data | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L351-L351 | the conditions (A2), (A3)
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L349-L349 | the matrix A
EDGE: stepW:w0n:det | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L356-L356 | proof step
EDGE: stepW:w0n:A2 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L360-L360 | proof step
EDGE: stepW:w0n:A3red | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L363-L363 | proof step
EDGE: stepW:w0n:l1 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L369-L369 | proof step
EDGE: stepW:w0n:l2 | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L373-L373 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg@L349-L349 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:det
KIND: step
TITLE: Determinant
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L356-L359
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L356-L359
CONTRACT_ID: stepW:w0n:det
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A of Theorem bpW:w0n:AB
SOURCE_QUANTIFIERS: none
SOURCE_CONCLUSION: det A = (3/(8pi))^2 lambda_1^{-2} lambda_2^{-2} det((3,4),(4,3)) = -63/(64 pi^2) lambda_1^{-2} lambda_2^{-2}; also for general n >= 1, det(4 11^T - Id_n)=(-1)^{n-1}(4n-1)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L357-L357 | A = (3/(8pi)) D(4 11^T - Id) D
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:det@L357-L357 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:A2
KIND: step
TITLE: Pure normal
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L360-L362
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L360-L362
CONTRACT_ID: stepW:w0n:A2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: l in Z^N, 1 <= ¦l¦ <= 2
SOURCE_QUANTIFIERS: l
SOURCE_CONCLUSION: <l,lambda_N> is +-lambda_a, +-2 lambda_a, +-(lambda_a+lambda_b) or +-(lambda_a-lambda_b), a != b in N, all nonzero
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L362-L362 | lambda > 0 strictly increasing
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A2@L361-L361 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:A3red
KIND: step
TITLE: Reduction of (A$_3$)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L363-L368
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L363-L368
CONTRACT_ID: stepW:w0n:A3red
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: b = (1/lambda_1, 1/lambda_2), s = sum_{j>=3} l_j/lambda_j
SOURCE_QUANTIFIERS: (k,l)
SOURCE_CONCLUSION: A = (3/(8pi))(4bb^T - D^2), B^T l = (3/(2pi)) s b; the linear part (3/(8pi))(4(<b,k>+s)b - D^2 k) vanishes iff k_i/lambda_i = c (i = 1,2) with c = 4(<b,k>+s), then <b,k> = 2c, s = -(7/4)c; the constant part is c(lambda_1^2+lambda_2^2) + <l,lambda_N>
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w0n:nondeg-sec#data, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L365-L365 | A and B
EDGE: bpW:w0n:nondeg-sec#data | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L366-L366 | the affine map of (A3)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:A3red@L364-L364 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:l1
KIND: step
TITLE: The case $\abs l=1$
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L369-L372
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L369-L372
CONTRACT_ID: stepW:w0n:l1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; k in Z^2, l in Z^N finitely supported with abs(l)=1; l=sigma e_nu, sigma in {+1,-1}, nu >= 3; consider vanishing of the affine map in (A3)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: the constant part vanishes iff 7 lambda_nu^2 = 4(lambda_1^2+lambda_2^2), and then k_i^2 in (0,4/7) is not the square of an integer; so (A3) holds
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:A3red, bpW:w0:basis#lam, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:A3red | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L370-L370 | the vanishing conditions of the reduction
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L370-L370 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l1@L372-L372 | strict positivity of lambda makes k_i^2 strictly between zero and 4/7
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w0n:l2
KIND: step
TITLE: The case $\abs l=2$
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L373-L376
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L373-L376
CONTRACT_ID: stepW:w0n:l2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; k in Z^2, l in Z^N finitely supported with abs(l)=2; consider vanishing of the linear part of the affine map in (A3)
SOURCE_QUANTIFIERS: for every choice of the source data stated in SOURCE_HYPOTHESES; m > 0 fixed under the standing assumption
SOURCE_CONCLUSION: ¦s¦ <= 2/lambda_3 < 2/3, ¦c¦ < 8/21, k_2 - k_1 = c(lambda_2 - lambda_1) with 0 < lambda_2 - lambda_1 < 1 forces k_1 = k_2, c = 0, s = 0, impossible for ¦l¦ = 2; so the linear part does not vanish
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w0n:A3red, bpW:w0:basis#lambda-facts, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w0n:A3red | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L374-L374 | the vanishing conditions of the reduction
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L375-L375 | lambda_3 > 3, 0 < lambda_2 - lambda_1 < 1, lambda injective
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#stepW:w0n:l2@L374-L374 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w0n:duffing
KIND: proposition
TITLE: One-mode frequency shift, (f)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L391-L400
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L402-L407
CONTRACT_ID: bpW:w0n:duffing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: restriction of (bpW:w0:eq) to u = x(t) phi_j(x), only mode j excited, forcing of other modes dropped
SOURCE_QUANTIFIERS: j >= 1; amplitude a
SOURCE_CONCLUSION: the projected one-mode equation is ddot x+lambda_j^2 x+eps x^3=0, eps=g_jjjj=3/(2pi); its frequency at small amplitude a is lambda_j+3 eps a^2/(8 lambda_j)+O(a^4)=lambda_j+9 a^2/(16pi lambda_j)+O(a^4); setting I_j=lambda_j a^2/2 to leading order gives lambda_j+9 I_j/(8pi lambda_j^2)+O(a^4), agreeing with the normal-form first-order shift A_jj I_j (for the tangential diagonal in AB); the printed coefficient would give a shift 16 times larger
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:nlw#IsClassicalSolution, bpW:w0n:quartic-coeff, bpW:w0n:ledger#ext-lindstedt, bpW:w0:actions, bpW:w0n:AB, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L392-L392 | restriction of the equation (bpW:w0:eq)
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L403-L403 | int (x phi_j)^3 phi_j = x^3 g_jjjj, g_jjjj = 3/(2pi)
EDGE: bpW:w0n:ledger#ext-lindstedt | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L403-L403 | the classical Lindstedt shift 3 eps a^2/(8 omega_0)
EDGE: bpW:w0:actions | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L406-L406 | I_j = (q_j^2+p_j^2)/2 = lambda_j a^2/2 to leading order
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L397-L397 | A_jj = 9/(8 pi lambda_j^2)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L394-L394 | lambda occurs explicitly in the local source statement or calculation
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-normalization.tex#bpW:w0n:duffing@L392-L392 | frozen definition is used by its symbol; coefficients q,p are unweighted, as in the blueprint
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Consistency check (f) of W0; no later proof consumes it so far (decide at W8, SPEC Reachability).
```

```text
NODE: bpW:w0n:nondeg-sec#data
KIND: definition
TITLE: Nondegeneracy conditions (A1)-(A3) of the Cantor Manifold Theorem
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg-sec@L341-L344
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0n:nondeg-sec#data
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: A, B of Theorem bpW:w0n:AB
SOURCE_QUANTIFIERS: (k,l) in Z^2 x Z^N with 1 <= ¦l¦ <= 2
SOURCE_CONCLUSION: defines omega(I) = lambda_J + A I, Omega(I) = lambda_N + B I and the conditions (A1) det A != 0, (A2) <l,lambda_N> != 0, (A3) <k,omega(I)> + <l,Omega(I)> not identically 0 as an affine function of I, for all (k,l) with 1 <= ¦l¦ <= 2 (¦l¦ = sum ¦l_j¦)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:AB, bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:AB | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg-sec@L341-L341 | omega(I) = lambda_J + A I and Omega(I) = lambda_N + B I
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:nondeg-sec@L341-L341 | lambda occurs explicitly in the local source statement or calculation
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Unlabelled prose L341-L344 defining the conditions stated in Theorem bpW:w0n:nondeg (SPEC section-data rule).
```

```text
ITEM: w0-normalization:sourcegap-L159
KIND: proof-region
SOURCE: blueprint-W/parts/w0-normalization.tex#sourcegap@L159-L161
DISPOSITION: NODE stepW:w0n:majorant
REASON: the printed P96-W p. 280 bound (constant 1) is wrong; the blueprint proves the corrected constant sqrt 2 in the majorant step (errata N-1); constants only, no open gap
COVERAGE_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
```

```text
NODE: bpW:w0n:cubic-bound
KIND: theorem
TITLE: Cubic gradient, (b)
STATEMENT_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L118-L129
PROOF_SOURCE: blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L131-L155
CONTRACT_ID: bpW:w0n:cubic-bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a >= 0, p >= 1/2; T(q,q',q'')_l = (1/sqrt(lambda_l)) sum_{i,j,k} g_ijkl hat q_i hat q'_j hat q''_k on (l^{a,p}_C)^3, hat q_j = q_j/sqrt(lambda_j)
SOURCE_QUANTIFIERS: for all a >= 0, p >= 1/2; for all q, q', q''
SOURCE_CONCLUSION: the sums converge absolutely; T is a bounded symmetric trilinear map into l^{a,p+1}_C, real on real arguments, with ¦¦T(q,q',q'')¦¦_{a,p+1} <= C_* ¦¦q¦¦ ¦¦q'¦¦ ¦¦q''¦¦, C_* = K_{p+1/2}^2/pi; for a > 0, G_q(q) = T(q,q,q); for a = p = 1, G_q : l^{1,1} -> l^{1,2} is real analytic (a continuous cubic polynomial) with ¦¦G_q(q)¦¦_{1,2} <= C_m ¦¦q¦¦_{1,1}^3, C_m = 8(1+2 zeta(3))/pi (about 8.67)
CONSTANT_SCOPE: C_* depends only on p; C_m is independent of m > 0 (only lambda_j >= j is used)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0n:gradient, bpW:w0n:algebra, bpW:w0n:quartic-coeff, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, stepW:w0n:majorant, stepW:w0n:selection, stepW:w0n:smoothing, stepW:w0n:analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L120-L120 | the coefficients g_ijkl of T
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L120-L120 | the weights 1/sqrt(lambda)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L125-L125 | the identification G_q(q) = T(q,q,q)
EDGE: stepW:w0n:majorant | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L132-L132 | proof step
EDGE: stepW:w0n:selection | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L136-L136 | proof step
EDGE: stepW:w0n:smoothing | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L142-L142 | proof step
EDGE: stepW:w0n:analytic | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L149-L149 | proof step
EDGE: bpW:w0n:gradient | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L125-L125 | explicit citation identifying G_q with the diagonal T
EDGE: bpW:w0n:algebra | blueprint-W/parts/w0-normalization.tex#bpW:w0n:cubic-bound@L124-L124 | K_{p+1/2} is the algebra constant, with p >= 1/2 ensuring s >= 1
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

Suspected blueprint defects and uncertainties:

- w0-normalization.tex L77-L81, L125: “For a>0, G_q(q)=T(q,q,q)” uses G_q outside the l^{1,1} domain explicitly fixed in w0-conventions.tex L96-L98, including complex inputs. The integral formula supplies a natural extension, but its definition/domain should be stated. The graph must not silently enlarge the frozen cubicGrad domain; general coefficient formulas and the frozen a=p=1 real specialization are distinct. This is a notation/domain defect, not a refutation of the displayed estimate.
- L308 “quartic polynomial” and L313 “time-one map” are formal infinite-mode expressions here; analytic realization is explicitly deferred at L325-L326. Preserve that formal scope.
- L397 “lambda_j+...=lambda_j+A_jj I_j” suppresses O(a^4); L409 explicitly says the action/amplitude identity holds “to leading order only”. The replacement preserves that qualification rather than asserting exact equality of nonlinear frequencies.
- Existing paper defects N-1, N-4, N-5 and E-PDE-W-1/2 are recorded by this blueprint; no independent paper/PDF verification was performed in this source-only review.

Process deviation: an initial raw manifest preview inadvertently displayed state fields; no conclusion uses those fields. Subsequent manifest inspection selected identity fields only. No proof bodies or implementation modules were read. No repository changes other than this review file.
