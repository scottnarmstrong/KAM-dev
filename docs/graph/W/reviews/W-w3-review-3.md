# W-w3 delta review

Reviewer: sol-delta3-W-w3 (sol-delta3-W-batch; independent, refute-first).

Verdict: **FAIL**.

Scope: only records still PROPOSED in the current packet, under REVIEW-BRIEF rule 9 and the final SPEC change-log entry (inp merge, corpus re-pin, writer revisions r2). Previously REVIEWED records are context only. All six CORPUS.sha256 entries verified OK. No git, Lean, lake or lint was run.

## Nodes

| id | verdict | spans or reason |
|---|---|---|
| stepW:w3:XG | FAIL | Missing mandatory direct frozen-symbol dependency on bpW:w0:basis#lam at w3-birkhoff.tex L303. The a >= 0 argument itself is complete; no SOURCE_GAP or alternative route is required. |
| stepW:w3:gradtrans | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L598-L602 |
| stepW:w3:majY | FAIL | The SOURCE_HYPOTHESES parenthetical locates the proof preamble at L622, but it is now L632. L622 is the lemma statement. The added majcalc edge and its consumer range are correct. |
| stepW:w3:majps | FAIL | The SOURCE_HYPOTHESES parenthetical locates the proof preamble at L622, but it is now L632. The majint edge correctly identifies the integral represented by the power series. |
| stepW:w3:conj | FAIL | The SOURCE_HYPOTHESES parenthetical locates the proof preamble at L698-L699, but it is now L708-L709. L698-L699 belongs to the theorem statement; the added quartic edge is otherwise correct. |

## Coverage

| id | verdict | spans |
|---|---|---|
| stepW:w3:XG | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L311 |

All other coverage items PASS within this delta scope; already REVIEWED items are not re-adjudicated.

## Findings and source checks

At L298-L311 the a = 0 repair is complete as source mathematics: the nonnegative majorant and weights >= 1 bound the absolute fourfold series for every a >= 0, p >= 1/2; symmetry gives a continuous symmetric four-linear Q; the polynomial expansion gives d_{q_l}G = Q(q,q,q,e_l) = T(q,q,q)_l. The coefficients contain the required lambda_l^{-1/2} through hat e_l. G at a = 0 is the quartic-series definition, not the positive-a integral. The positive-a citations at L310-L311 are consistency remarks. Deleting the two route nodes and the SOURCE_GAP is justified; their pending coverage maps to XG alone.

Gradient transport consumes the Hamiltonian pairing, constant-form identity and invertibility on W and W+. The added edges in majY, majps and conj correctly account respectively for composite-series calculus, identification with the termwise integral, and the quartic derivative pairings. The source/proof and EDGE @L ranges of all five prior-round replacements match the current text. Three embedded proof-preamble references in SOURCE_HYPOTHESES were not remapped; the full replacements below correct them. XG additionally needs its explicit lam-symbol edge.

## Complete replacement: stepW:w3:XG

```text
NODE: stepW:w3:XG
KIND: step
TITLE: The field
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L311
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L311
CONTRACT_ID: stepW:w3:XG
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:quartic-ident: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; real x = (q,p) in E_{a,p}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:quartic-ident (for all real x; for all w in W; for x in T); within the step: real points; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: on real points Z^{-1} X_G = (d_p G, -d_q G) with d_p G = 0; for every a >= 0 (including a = 0), G(Zx) = (1/4) Q(q,q,q,q) with Q(q^1,..,q^4) = sum g_ijkl hat q^1_i hat q^2_j hat q^3_k hat q^4_l absolutely convergent on (l^{a,p})^4 (¦Q¦ <= C_* prod ¦¦q^t¦¦), Q symmetric 4-linear, and d_{q_l} G = Q(q,q,q,e_l) = T(q,q,q)_l; for a > 0 this agrees with the formula of Lemma bpW:w0n:gradient
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lam, bpW:w3:hamfield-def#hamilton, bpW:w0n:cubic-bound, bpW:w3:quartic, stepW:w3:Gz, bpW:w3:majorant, bpW:w0n:quartic-coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:hamfield-def#hamilton | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L299-L299 | on real points Z^{-1} X_P = (d_p P, -d_q P)
EDGE: bpW:w0n:cubic-bound | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L300-L311 | the trilinear T
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L300-L311 | the a=0 Hamiltonian is the two-sided quartic series defined and bounded here
EDGE: stepW:w3:Gz | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L301-L301 | G(Zx) = (1/4) Q(q,q,q,q) from the quartic step
EDGE: bpW:w3:majorant | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L306-L306 | absolute convergence of Q via the majorant M and C_*
EDGE: bpW:w0n:quartic-coeff | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L307-L307 | symmetry of g gives the symmetry of Q
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L303-L303 | hat q_j = q_j/sqrt(lambda_j) uses the frozen lam definition directly
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+claude-suborch-W-r2+sol-delta3-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Writer revision r2 (wave-1 corpus update, inp 99afc128 blueprint cleanup): the step now proves the field formula for every a >= 0 directly; the SOURCE_GAP (a = 0 not covered) is resolved and removed. The citations of bpW:w0n:gradient and bpW:w1:gradient-identity at L310-L311 are consistency remarks for a > 0, not alternative derivations, so the two route nodes are deleted.
```

## Complete replacement: stepW:w3:majY

```text
NODE: stepW:w3:majY
KIND: step
TITLE: The integrand
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L666-L671
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L666-L671
CONTRACT_ID: stepW:w3:majY
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L632)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the composite series cal Y sums to Y(t,w), has shift 3 and mu_Y(1,rho_1) <= 4 C_* rho_1^3; Y_j = cal Y_{j,2j+3}
CONSTANT_SCOPE: C_* depends only on p
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majN, stepW:w3:majX, bpW:w3:main-sec#data, stepW:w3:majcalc
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majN | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L668-L668 | N
EDGE: stepW:w3:majX | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L668-L668 | the cubic field along the flow
EDGE: bpW:w3:main-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L669-L669 | Y(t,w)
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L667-L670 | the bilinear application composite and subtraction use the composite-series identity and product majorant bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-delta-W-w3+sol-delta3-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Complete replacement: stepW:w3:majps

```text
NODE: stepW:w3:majps
KIND: step
TITLE: Power series
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L676-L678
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L676-L678
CONTRACT_ID: stepW:w3:majps
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L632)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:Yseries (there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: sum ¦¦q_n¦¦ rho_1^n < infinity, so the formal power series and analyticity
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w3:majY, bpW:w3:ext-series, stepW:w3:majint
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w3:majY | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L677-L677 | sum ¦¦Y_j¦¦ rho_1^{2j+3}
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L677-L677 | power series give analyticity
EDGE: stepW:w3:majint | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L677-L678 | the preceding termwise integral identity identifies the diagonal series with coefficients q with the integral whose analyticity is asserted
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-delta-W-w3+sol-delta3-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Complete replacement: stepW:w3:conj

```text
NODE: stepW:w3:conj
KIND: step
TITLE: Conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L749-L755
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L749-L755
CONTRACT_ID: stepW:w3:conj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L708-L709)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:main (for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)); within the step: w in B_{rho_1} cap W+; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv): Gamma(w) in W+ and D Gamma(w)[X_Lambda + X_{bar G} + X_{G^nor} + X_K](w) = X_H(Gamma(w))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:Lambda, bpW:w3:symplectic, bpW:w3:omega, stepW:w3:XKconcl, bpW:w3:quartic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L750-L750 | Gamma - id into W+
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L751-L751 | DH(y)u = Omega(X_H(y),u) on W+
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L752-L752 | gradient transport
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L755-L755 | nondegeneracy
EDGE: stepW:w3:XKconcl | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L754-L754 | X_K
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L751-L754 | the quartic Hamiltonian fields supply the G, bar G and G^nor derivative pairings in DH and the transformed Hamiltonian
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-delta-W-w3+sol-delta3-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Suspected blueprint defects

None newly identified in the reviewed delta. Findings above concern graph records; they do not reopen the repaired source gaps or assert Lean proof status.
