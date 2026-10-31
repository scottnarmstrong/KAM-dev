# W-w3 delta review

Reviewer: sol-delta-W-w3 (independent reviewer sol-delta-W-batch2).

Verdict: FAIL.

Scope: rule 9 applied to this slice: only records still PROPOSED on entry. REVIEWED node and coverage records are out of scope; prerequisites and consumers were read only as context. No graph acceptance or proof status is changed by this report.

The new curvature node passes: it separates f prime monotonicity, f second positivity/decrease and beta comparison from the sign cases, with direct mass, lam and lambda-facts edges at L326-L328. The divisor and sign cases consume that node at their own use sites. Both new XG gradient routes pass, and the writer-added target-to-route and route-to-gradient EDGE records are present at L301. ROUTES models alternatives; DEPS does not conjoin the two gradient results. Their SOURCE_GAP notes faithfully retain the a = 0 applicability failure. None of these PASS judgments asserts that this gap is proved.

## Node verdicts

| id | verdict | spans or reason |
| --- | --- | --- |
| bpW:w3:hamfield-def | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L154-L162 |
| stepW:w3:Gz | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L294-L297 |
| stepW:w3:XG | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L301 |
| stepW:w3:Gnor | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L302-L303 |
| bpW:w3:divisor | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L317-L323; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L325-L364 |
| stepW:w3:s0 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L337-L338 |
| stepW:w3:s1 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L339-L343 |
| stepW:w3:s23 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L344-L348 |
| stepW:w3:s1inner | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L349-L359 |
| bpW:w3:lie-coeff | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L451-L456 |
| bpW:w3:flow | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L494-L517; blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L519-L556 |
| stepW:w3:conv | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L520-L527 |
| stepW:w3:floweq | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L528-L531 |
| stepW:w3:transport | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L532-L534 |
| stepW:w3:est | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L535-L541 |
| stepW:w3:Greal | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L542-L543 |
| stepW:w3:var | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L544-L547 |
| stepW:w3:inv | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L548-L555 |
| stepW:w3:constform | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L583-L587 |
| stepW:w3:gradtrans | FAIL | SOURCE_CONCLUSION unconditionally asserts values in W+. The source last claim (L575, L592) is conditional on X_P taking values in W+; the recorded premises only give a W-valued Hamiltonian field. |
| stepW:w3:majcalc | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L623-L634 |
| stepW:w3:majflow | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L635-L637 |
| stepW:w3:majA | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L638-L644 |
| stepW:w3:majN | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L645-L651 |
| stepW:w3:majX | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L652-L655 |
| stepW:w3:majY | FAIL | L657-L660 constructs a new composite series by operator application and bounds its majorant. This directly consumes stepW:w3:majcalc, absent from DEPS and EDGE; the earlier composites majN and majX do not supply this new application. |
| stepW:w3:majint | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L662-L665 |
| stepW:w3:majps | FAIL | The power series is claimed for the integral. The coefficient norm estimate comes from majY, but identification of that integral with the diagonal sum of q uses stepW:w3:majint (L663-L665), missing from DEPS and EDGE. |
| stepW:w3:majreal | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L669-L672 |
| stepW:w3:Kanalytic | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L700-L703 |
| stepW:w3:K1 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L704-L707 |
| stepW:w3:K2 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L708-L713 |
| stepW:w3:XK1 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L714-L721 |
| stepW:w3:XK2 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L722-L731 |
| stepW:w3:XKconcl | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L732-L736 |
| stepW:w3:iii | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L737-L738 |
| stepW:w3:conj | FAIL | L741-L744 consumes the nonlinear Hamiltonian pairings for G, bar G and G^nor. bpW:w3:Lambda supplies only the quadratic pairing, and XKconcl supplies only K. Add the direct bpW:w3:quartic use; it cannot be replaced by a transitive path through XKconcl. |
| stepW:w3:divisor#curvature | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L326-L328 |
| stepW:w3:XG#via-w0-gradient | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L301; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L301-L301 |
| stepW:w3:XG#via-w1-gradient | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L301; blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L301-L301 |

## Coverage verdicts

| id | verdict | spans |
| --- | --- | --- |
| bpW:w3:hamfield-def | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:hamfield-def@L154-L162 |
| stepW:w3:Gz | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gz@L294-L297 |
| stepW:w3:XG | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XG@L298-L301 |
| stepW:w3:Gnor | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Gnor@L302-L303 |
| bpW:w3:divisor | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L317-L323 |
| stepW:w3:s0 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s0@L337-L338 |
| stepW:w3:s1 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1@L339-L343 |
| stepW:w3:s23 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s23@L344-L348 |
| stepW:w3:s1inner | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:s1inner@L349-L359 |
| bpW:w3:lie-coeff | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:lie-coeff@L451-L456 |
| bpW:w3:flow | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:flow@L494-L517 |
| stepW:w3:conv | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conv@L520-L527 |
| stepW:w3:floweq | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:floweq@L528-L531 |
| stepW:w3:transport | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:transport@L532-L534 |
| stepW:w3:est | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:est@L535-L541 |
| stepW:w3:Greal | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Greal@L542-L543 |
| stepW:w3:var | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:var@L544-L547 |
| stepW:w3:inv | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:inv@L548-L555 |
| stepW:w3:constform | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:constform@L583-L587 |
| stepW:w3:gradtrans | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L588-L592 |
| stepW:w3:majcalc | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majcalc@L623-L634 |
| stepW:w3:majflow | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majflow@L635-L637 |
| stepW:w3:majA | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majA@L638-L644 |
| stepW:w3:majN | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majN@L645-L651 |
| stepW:w3:majX | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majX@L652-L655 |
| stepW:w3:majY | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L656-L661 |
| stepW:w3:majint | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majint@L662-L665 |
| stepW:w3:majps | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L666-L668 |
| stepW:w3:majreal | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majreal@L669-L672 |
| stepW:w3:Kanalytic | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:Kanalytic@L700-L703 |
| stepW:w3:K1 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K1@L704-L707 |
| stepW:w3:K2 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:K2@L708-L713 |
| stepW:w3:XK1 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK1@L714-L721 |
| stepW:w3:XK2 | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XK2@L722-L731 |
| stepW:w3:XKconcl | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:XKconcl@L732-L736 |
| stepW:w3:iii | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:iii@L737-L738 |
| stepW:w3:conj | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L739-L745 |
| w3-birkhoff:prose-L326-L328 | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:divisor@L326-L328 |

all other coverage items PASS (within the PROPOSED delta scope only; previously REVIEWED items are not re-reviewed). Each pending disposition maps its source unit to the correct node or nodes, including the route mapping and curvature preamble where applicable. Node contract or edge failures above do not invalidate these coverage mappings.

## Complete replacement blocks

Correction for stepW:w3:gradtrans:

```text
NODE: stepW:w3:gradtrans
KIND: step
TITLE: Gradient transport
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L588-L592
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L588-L592
CONTRACT_ID: stepW:w3:gradtrans
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:symplectic: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; ¦t¦ < 2, w in B_{rho_0}, xi, eta in W; (consequence) P complex differentiable near Gamma_t(B_rho), rho <= rho_0, with Hamiltonian field X_P
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w3:symplectic (for all such t, w, xi, eta; P; w in B_rho); within the step: w, v; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: D(P o Gamma_t)(w)v = Omega(D Gamma_t(w)^{-1} X_P(Gamma_t w), v); thus X_{P o Gamma_t}(w) = D Gamma_t(w)^{-1} X_P(Gamma_t w) takes values in W; if X_P takes values in W+, then so does this transported field, by invertibility of D Gamma_t(w) on W+
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, stepW:w3:constform, bpW:w3:hamfield-def
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L591-L591 | (iii) invertibility on W and W+
EDGE: stepW:w3:constform | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L592-L592 | constant form
EDGE: bpW:w3:hamfield-def | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:gradtrans@L589-L589 | the defining Hamiltonian pairing of P is directly consumed
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-delta-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

Correction for stepW:w3:majY:

```text
NODE: stepW:w3:majY
KIND: step
TITLE: The integrand
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L656-L661
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L656-L661
CONTRACT_ID: stepW:w3:majY
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L622)
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
EDGE: stepW:w3:majN | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L658-L658 | N
EDGE: stepW:w3:majX | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L658-L658 | the cubic field along the flow
EDGE: bpW:w3:main-sec#data | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L659-L659 | Y(t,w)
EDGE: stepW:w3:majcalc | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majY@L657-L660 | the bilinear application composite and subtraction use the composite-series identity and product majorant bound
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-delta-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

Correction for stepW:w3:majps:

```text
NODE: stepW:w3:majps
KIND: step
TITLE: Power series
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L666-L668
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L666-L668
CONTRACT_ID: stepW:w3:majps
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:Yseries: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}; local data: 0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 (proof preamble L622)
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
EDGE: stepW:w3:majY | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L667-L667 | sum ¦¦Y_j¦¦ rho_1^{2j+3}
EDGE: bpW:w3:ext-series | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L667-L667 | power series give analyticity
EDGE: stepW:w3:majint | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:majps@L667-L668 | the preceding termwise integral identity identifies the diagonal series with coefficients q with the integral whose analyticity is asserted
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-delta-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

Correction for stepW:w3:conj:

```text
NODE: stepW:w3:conj
KIND: step
TITLE: Conjugacy
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L739-L745
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L739-L745
CONTRACT_ID: stepW:w3:conj
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w3:main: W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - bar G - G^nor on B_{rho_1}; local data: Z' = bar G - G^tan; K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' (proof preamble L698-L699)
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
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L740-L740 | Gamma - id into W+
EDGE: bpW:w3:Lambda | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L741-L741 | DH(y)u = Omega(X_H(y),u) on W+
EDGE: bpW:w3:symplectic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L742-L742 | gradient transport
EDGE: bpW:w3:omega | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L745-L745 | nondegeneracy
EDGE: stepW:w3:XKconcl | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L744-L744 | X_K
EDGE: bpW:w3:quartic | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:conj@L741-L744 | the quartic Hamiltonian fields supply the G, bar G and G^nor derivative pairings in DH and the transformed Hamiltonian
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w3+sol-delta-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Suspected blueprint defects and deviations

blueprint-W/parts/w3-birkhoff.tex L300-L301: "by the formula of Lemma ... gradient (equivalently Proposition ... gradient-identity)". Both cited results require a > 0 (w0-normalization L77; w1-sequences L510), while quartic-ident and its field step retain a >= 0 (W3 L24, L282-L285). The a = 0 derivative identification is unsupplied by these applications. The parent and both route notes expose it and pass. The unconditional W+ wording flagged in gradtrans is a graph transcription defect: the blueprint itself correctly conditions the last claim at L575.

No mathematical repair is supplied. Validation: all six W corpus hashes and the K import hash match their pin files. Report row counts and complete replacement fields are checked with read-only Python; no git, lake, Lean, or lint was run. Only this batch's seven requested review reports are written.
