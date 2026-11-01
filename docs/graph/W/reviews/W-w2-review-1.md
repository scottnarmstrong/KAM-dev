# W-w2 review

Reviewer: sol-review-W-w2

Verdict: FAIL. Raw source w2-reconstruction.tex L1-L403 reread, together with W1 coordinatewise, sine-feature, recon-analytic and trifrozen, W0 force, and the headline embedding record.

| Node | Verdict | Source spans / reason |
|---|---|---|
| bpW:w2:ext-deriv | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-deriv@L40-L48; - |
| bpW:w2:ext-an | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-an@L49-L54; - |
| bpW:w2:ext-sums | FAIL | the external statement drops the arbitrary polynomial degree and the exact geometric sum used in the norms |
| bpW:w2:ext-trig | FAIL | the final identity is for the frozen lambda_j, not an arbitrary scalar |
| bpW:w2:derived | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:derived@L70-L76; - |
| bpW:w2:functionals | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L81-L92; blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L94-L124 |
| stepW:w2:features | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L95-L102; blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L95-L102 |
| stepW:w2:pairing | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L103-L107; blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L103-L107 |
| stepW:w2:norms | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L108-L113; blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L108-L113 |
| stepW:w2:xder | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L114-L119; blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L114-L119 |
| stepW:w2:bdry | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L120-L123; blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L120-L123 |
| bpW:w2:force | FAIL | kappa is the frozen coefficient map by the standing dictionary L28 |
| stepW:w2:fsum | FAIL | kappa is the frozen coefficient map by the standing dictionary L28 |
| stepW:w2:flin | FAIL | kappa is the frozen coefficient map by the standing dictionary L28 |
| stepW:w2:fcub | FAIL | kappa is the frozen coefficient map by the standing dictionary L28 |
| bpW:w2:coeffsol | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L166-L174; - |
| bpW:w2:orbit | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L178-L190; blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L192-L202 |
| stepW:w2:oan | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oan@L193-L195; blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oan@L193-L195 |
| stepW:w2:oshift | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L196-L201; blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L196-L201 |
| bpW:w2:curve-deriv | FAIL | kappa is the frozen coefficient map by the standing dictionary L28 |
| stepW:w2:cdiff | FAIL | analyticity of Y comes from C1 of the analytic coefficient solution package |
| stepW:w2:ccoord | FAIL | the second derivative value is supplied by C2 of the package; kappa is the frozen coefficient map by the standing dictionary L28 |
| bpW:w2:curve | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L233-L249; blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L251-L296 |
| stepW:w2:joint | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L252-L262; blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L252-L262 |
| stepW:w2:t1 | FAIL | kappa is the frozen coefficient map by the standing dictionary L28 |
| stepW:w2:t2 | FAIL | kappa is the frozen coefficient map by the standing dictionary L28 |
| stepW:w2:x | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:x@L279-L280; blueprint-W/parts/w2-reconstruction.tex#stepW:w2:x@L279-L280 |
| stepW:w2:frozen | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L281-L289; blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L281-L289 |
| stepW:w2:bound | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L290-L295; blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L290-L295 |
| bpW:w2:main | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L303-L321; blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L323-L332 |
| stepW:w2:mred | FAIL | the analyticity premise is projected from the frozen embedding predicate; the functions u are identified using their reconU definitions |
| stepW:w2:mconc | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L328-L331; blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L328-L331 |
| bpW:w2:clause5 | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L347-L353; blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L355-L360 |

Coverage table (no failing in-scope items):

| Item | Verdict | Evidence |
|---|---|---|

Coverage: all other coverage items PASS. Every prose disposition was checked. In particular L25-L33 maps the standing dictionary to its consumers rather than creating a new global assumption, and C1/C2, inv and H1-H3 are aliases/premises of their enclosing definitions/results.

The proof applies the conditional reconstruction theorem using analyticity projected from H1 and the coordinate HasDerivAt identities H2; it supplies H3 only for the final norm bound. No root theorem is consumed to prove its own clause (5). The common constant C=max(1,M_m) C_3 is chosen before I and theta_0, with M_m depending only on m. The second time derivative is asserted only for x in [0,pi]; the analytic expression u_tt extends to R x R.

Replacement fragments:

```text
NODE: stepW:w2:cdiff
KIND: step
TITLE: Differentiability
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L213-L215
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L213-L215
CONTRACT_ID: stepW:w2:cdiff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve-deriv: Y an analytic coefficient solution; t in R
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve-deriv (for all Y, t; j in N_+); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Y_i is analytic at t (composite with the continuous linear projection), hence differentiable
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-an, bpW:w2:coeffsol
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L215-L215 | analytic maps are differentiable
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L214-L214 | analyticity of Y comes from C1 of the analytic coefficient solution package
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w2:ccoord
KIND: step
TITLE: Coordinates
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L216-L219
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L216-L219
CONTRACT_ID: stepW:w2:ccoord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve-deriv: Y an analytic coefficient solution; t in R
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve-deriv (for all Y, t; j in N_+); within the step: t, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: s -> kappa(Y_i(s))_j has derivative kappa(Y_i'(t))_j and, by (C2), the derivative stated there; uniqueness gives the identities
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:coordinatewise, stepW:w2:cdiff, bpW:w2:ext-deriv, bpW:w2:coeffsol, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:coordinatewise | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L217-L217 | with (a,p) = (a',p') = (1,1), hat iota = id, v = Y_i'(t)
EDGE: stepW:w2:cdiff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L217-L217 | Y_i differentiable at t
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L219-L219 | uniqueness of derivatives
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L218-L218 | the second derivative value is supplied by C2 of the package
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L218-L218 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w2:mred
KIND: step
TITLE: Reduction to a curve
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L324-L327
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L324-L327
CONTRACT_ID: stepW:w2:mred
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:main: m > 0; M_m as in Theorem bpW:w2:curve; K : (Fin 2 -> R) -> WaveSpace, nu : Fin 2 -> R, B in R with (H1) IsAnalyticTorusEmbedding K, (H2) the invariance (bpW:w2:inv) for every theta and j in N_+, (H3) ¦¦K(theta)¦¦ <= B for every theta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:main (for all m > 0, K, nu, B as stated; for every theta_0; (a) for every z in univ x Icc 0 pi; (c), (d) for all t in R, x in [0,pi]); within the step: theta_0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: from the analyticity conjunct of (H1) and (H2), Y(t) = K(theta_0 + t nu) is an analytic coefficient solution, and the u of the two theorems coincide
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:orbit, bpW:wh:embedding#IsAnalyticTorusEmbedding, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:orbit | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L326-L326 | torus orbits are analytic coefficient solutions
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L325-L325 | the analyticity premise is projected from the frozen embedding predicate
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L327-L327 | the functions u are identified using their reconU definitions
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w2:force
KIND: lemma
TITLE: Force identity in frozen form
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L128-L137
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L139-L160
CONTRACT_ID: bpW:w2:force
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j
SOURCE_QUANTIFIERS: for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))
SOURCE_CONCLUSION: both series converge absolutely; (i) Sigma_lin(x) = -D^2 y(x) + m D^0 y(x) for every x in R; (ii) Sigma_cub(x) = U_m(y)(x)^3 for every x in [0,pi]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:derived, stepW:w2:fsum, stepW:w2:flin, stepW:w2:fcub, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L134-L134 | D^0 y and D^2 y
EDGE: stepW:w2:fsum | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L140-L140 | proof step
EDGE: stepW:w2:flin | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L148-L148 | proof step
EDGE: stepW:w2:fcub | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L154-L154 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L130-L130 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L130-L130 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L134-L134 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L131-L131 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L130-L130 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w2:fsum
KIND: step
TITLE: Summability
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L140-L147
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L140-L147
CONTRACT_ID: stepW:w2:fsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:force: standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:force (for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))); within the step: y, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the summands of Sigma_lin are at most sqrt(2/pi)(1+m)^{3/4} ¦¦y¦¦ j e^{-j}, those of Sigma_cub at most sqrt(2/pi)(1+m)^{1/4} ¦¦G^w(y)¦¦ e^{-j}; both majorants are summable; D^0 y(x), D^2 y(x) converge absolutely
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-lp, bpW:w0:basis#lambda-facts, bpW:w1:cubic-analytic, bpW:w2:ext-sums, bpW:w2:functionals, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L141-L141 | ¦kappa(y)_j¦ <= ¦¦y¦¦/(j e^j)
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L141-L141 | sqrt(lambda_j) lambda_j <= (1+m)^{3/4} j^{3/2}
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L143-L143 | (iv): G(y)_j = G^w(y)_j/omega_{1,2}(j), G^w(y) in l^2_R
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L146-L146 | comparison and summability of the majorants
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L147-L147 | (i): absolute convergence of D^0 y(x), D^2 y(x)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L141-L141 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L142-L142 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L146-L146 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L143-L143 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L141-L141 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w2:flin
KIND: step
TITLE: Linear part
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L148-L153
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L148-L153
CONTRACT_ID: stepW:w2:flin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:force: standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:force (for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))); within the step: y, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: termwise sqrt(lambda_j) lambda_j = (j^2+m)/sqrt(lambda_j), so the j-th summand of Sigma_lin is minus that of D^2 y plus m times that of D^0 y; summing gives (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-trig, bpW:w2:derived, stepW:w2:fsum, bpW:w2:ext-sums, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L149-L149 | lambda/sqrt(lambda) identities and lambda_j^2 = j^2 + m
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L151-L151 | the summands of D^0, D^2
EDGE: stepW:w2:fsum | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L151-L151 | absolute convergence of both series
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L152-L152 | Summable.tsum_add, tsum_mul_left
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L149-L149 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L150-L150 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L151-L151 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L150-L150 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w2:fcub
KIND: step
TITLE: Cubic part
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L154-L159
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L154-L159
CONTRACT_ID: stepW:w2:fcub
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:force: standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:force (for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))); within the step: y, x in [0,pi]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: U_m(y) = U_m(q) and G(y) = G_q(q) for q = kappa(y) in l^{1,1}; the first identity of (bpW:w0n:force) gives U_m(q)^3 = sum_l sqrt(lambda_l) G_q(q)_l phi_l on [0,pi], which is (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:trifrozen, stepW:w0n:force, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:trifrozen | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L155-L155 | the frozen reconU and cubicGrad are U_m and G_q of q = kappa(y)
EDGE: stepW:w0n:force | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L157-L157 | the force identity U_m(q)^3 = sum sqrt(lambda_l) G_q(q)_l phi_l
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L158-L158 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L158-L158 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L155-L155 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L155-L155 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L156-L156 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w2:curve-deriv
KIND: lemma
TITLE: Coefficients of the curve derivative
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L206-L210
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L212-L220
CONTRACT_ID: bpW:w2:curve-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Y an analytic coefficient solution; t in R
SOURCE_QUANTIFIERS: for all Y, t; j in N_+
SOURCE_CONCLUSION: Y_1 = (Y .).1 and Y_2 = (Y .).2 are differentiable at t as maps R -> l^2_R and, with Y_i'(t) their derivatives, kappa(Y_1'(t))_j = lambda_j kappa(Y_2(t))_j and kappa(Y_2'(t))_j = -lambda_j kappa(Y_1(t))_j - G(Y_1(t))_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:coeffsol, stepW:w2:cdiff, stepW:w2:ccoord, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L207-L207 | analytic coefficient solution
EDGE: stepW:w2:cdiff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L213-L213 | proof step
EDGE: stepW:w2:ccoord | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L216-L216 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L209-L209 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L209-L209 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L209-L209 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w2:t1
KIND: step
TITLE: First time derivative
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L263-L270
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L263-L270
CONTRACT_ID: stepW:w2:t1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: t, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: s -> u(s,x) has derivative <Psi^0(x),Y_1'(t)> = U_m(Y_1'(t))(x) = V_m(Y_2(t))(x) = u_t(t,x); this is (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:functionals, bpW:w2:ext-deriv, bpW:w2:curve-deriv, bpW:w2:ext-trig, bpW:w2:ext-sums, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L265-L265 | (i): D^0 y(x) = <Psi^0(x),y> continuous linear in y
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L266-L266 | derivative of a continuous linear image of a curve
EDGE: bpW:w2:curve-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L267-L267 | kappa(Y_1'(t))_j = lambda_j kappa(Y_2(t))_j
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L267-L267 | lambda/sqrt(lambda) = sqrt(lambda)
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L270-L270 | tsum_congr
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L267-L267 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L268-L268 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L264-L264 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L270-L270 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L268-L268 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: stepW:w2:t2
KIND: step
TITLE: Second time derivative
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L271-L278
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L271-L278
CONTRACT_ID: stepW:w2:t2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: t, x in [0,pi]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: s -> u_t(s,x) has derivative V_m(Y_2'(t))(x) = -Sigma_lin(x) - Sigma_cub(x) = u_tt(t,x) for x in [0,pi]; this is (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:functionals, bpW:w2:ext-deriv, bpW:w2:curve-deriv, stepW:w2:fsum, bpW:w2:ext-sums, bpW:w2:force, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconV, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L272-L272 | (i): V_m(y)(x) = <Psi^V(x),y>
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L272-L272 | derivative of a continuous linear image of a curve
EDGE: bpW:w2:curve-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L273-L273 | the coordinates of Y_2'(t)
EDGE: stepW:w2:fsum | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L275-L275 | absolute convergence of Sigma_lin, Sigma_cub with y = Y_1(t)
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L276-L276 | Summable.tsum_sub
EDGE: bpW:w2:force | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L277-L277 | (i), (ii) on [0,pi]
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L274-L274 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L274-L274 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L272-L272 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L274-L274 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L274-L274 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w2:ext-trig
KIND: external
TITLE: Trigonometry
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-trig@L61-L64
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-trig
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: sin 0 = 0, sin(n pi) = 0 for n in N; ¦sin¦, ¦cos¦ <= 1; d/dx sin(jx) = j cos(jx), d/dx cos(jx) = -j sin(jx); sqrt(lambda) sqrt(lambda) = lambda and lambda/sqrt(lambda) = sqrt(lambda) for lambda > 0; lambda_j^2 = j^2 + m
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lam
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-trig@L64-L64 | the final identity is for the frozen lambda_j, not an arbitrary scalar
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W
REVIEWER: -
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

```text
NODE: bpW:w2:ext-sums
KIND: external
TITLE: Series and norms
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-sums@L55-L60
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-sums
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: tsum_congr (termwise equal series have equal tsum, no summability needed); Summable.tsum_sub, Summable.tsum_add, tsum_mul_left for summable series; tsum_zero; comparison; summability of j^k e^{-j} for every k in N, and sum_{j>=1} e^{-2j} = (e^2-1)^{-1} (geometric series); Cauchy-Schwarz ¦<Psi,y>¦ <= ¦¦Psi¦¦ ¦¦y¦¦; on a product norm_fst_le, norm_snd_le
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
```

Suspected defects of the blueprint: no new defect identified. The existing P96-W p.278 sign typo is recorded at L390-L392 (“printed +lambda_j^2 q_j”); the reconstruction uses the negative linear force. No stronger positive-action domain was silently inserted into clause5: its source permits arbitrary Gamma and uses Real.sqrt_nonneg. This report concerns source topology only.

Validation: `python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/W/packets W-w2` returned `W-w2: 33 nodes, 177 edges, 60 coverage items, 0 problems`. Report-only checks verified verdict coverage, complete replacement fields, matching DEPS/EDGE sets, valid locator ranges and whitespace. The checker ran on the unchanged input packet; it does not accept these proposed corrections. No git, Lean, lake or lint commands were run.
