# W-w3 delta review 4

Reviewer: sol-delta4-W-w3 (sol-delta4-W-batch; independent).

Verdict: **PASS** for the assigned delta.

Scope: only the four named PROPOSED records, under REVIEW-BRIEF rule 9 and SPEC's delta-review-3 and in-text-remap change-log entry. Previously REVIEWED records were read only as prerequisite context. The current packet, rather than the historical specs or draft packets, was reviewed.

All six entries of `docs/graph/W/CORPUS.sha256` were checked with `sha256sum -c docs/graph/W/CORPUS.sha256`; all returned `OK`.

| id | verdict | spans |
|---|---|---|
| stepW:w3:XG | PASS | blueprint-W/parts/w3-birkhoff.tex L298-L311; standing data L23-L27; enclosing statement L282-L291; prerequisite context L164-L167, L232-L259, L294-L297; blueprint-W/parts/w0-conventions.tex L39-L42; blueprint-W/parts/w0-normalization.tex L40-L51, L119-L131 |
| stepW:w3:majY | PASS | blueprint-W/parts/w3-birkhoff.tex L666-L671; standing data L23-L27; definition L608-L619; enclosing statement L621-L629; proof preamble L632; prerequisite steps L633-L644, L655-L665 |
| stepW:w3:majps | PASS | blueprint-W/parts/w3-birkhoff.tex L676-L678; standing data L23-L27; enclosing statement L621-L629; proof preamble L632; prerequisite context L49-L59, L608-L619, L666-L675 |
| stepW:w3:conj | PASS | blueprint-W/parts/w3-birkhoff.tex L749-L755; standing data L23-L27; enclosing statement L687-L705; proof preamble L708-L709; prerequisite context L139-L145, L200-L206, L248-L259, L504-L527, L579-L586, L742-L746 |

Every source/proof locator, every EDGE locator, and every embedded line reference in these four records was checked against the current numbered source:

- XG: hamfield-def#hamilton at L299; cubic-bound and quartic at L300-L311; Gz at L301; majorant at L306; quartic-coeff at L307; lam at L303. Its SOURCE_HYPOTHESES reference L23-L27 correctly locates standing data, and its NOTE references L310-L311 correctly locate the positive-a consistency citations.
- majY: majN and majX at L668; main-sec#data at L669; majcalc at L667-L670. The embedded standing-data reference L23-L27 and proof-preamble reference L632 are correct.
- majps: majY and ext-series at L677; majint at L677-L678. The embedded standing-data reference L23-L27 and proof-preamble reference L632 are correct.
- conj: flow at L750; Lambda at L751; symplectic at L752; omega at L755; XKconcl at L754; quartic at L751-L754. The embedded standing-data reference L23-L27 and proof-preamble reference L708-L709 are correct.

XG's added lam edge records the explicit hat-q definition at L303. The absolute fourfold-series argument applies for every a >= 0 and p >= 1/2: the majorant estimate and weights >= 1 give the bound on Q; symmetry and the polynomial expansion identify its coordinate derivative with T, including the lambda_l factor from hat e_l. The positive-a citations at L310-L311 are consistency remarks, so neither extra gradient edges nor alternative route nodes are needed. The former a = 0 SOURCE_GAP is no longer present in the source argument.

majY consumes the composite-series calculus directly for bilinear application and subtraction; majN supplies the inverse series, majX the cubic composite, and main-sec#data the definition of Y. The shift, coefficient choice, and bound 4 C_* rho_1^3 match L669-L671. C_* depends only on p. majps uses the summability furnished by majY and the coefficient/integral identification furnished by majint before applying ext-series. Both records preserve the enclosing quantifiers, and the local s, rho, r definitions come from L632 rather than derived proof facts.

For conj, flow supplies Gamma(w) in W+ and invertibility of D Gamma on W and W+. Lambda and quartic supply the derivative pairings of H and the transformed quartic terms; XKconcl supplies the remainder field. The argument uses the symplectic identity and invertibility at w in B_{rho_1} intersect W+, with X_H(Gamma w) defined there. It does not require an everywhere-defined Hamiltonian field X_H on an open subset of W to invoke the conditional transport corollary. Nondegeneracy then yields exactly clause (iv). The source hypotheses, local definitions and quantifiers are faithful, and no missing or unnecessary direct dependency was found.

Coverage: no PROPOSED coverage records are assigned in this delta. Existing mappings of the four labelled steps were checked as context and are consistent. All other coverage items PASS within this delta scope; previously REVIEWED items are not re-adjudicated.

No FAIL rows; no replacement blocks are required.

Suspected blueprint defects: none newly identified in the assigned delta. No deviations introduced. These verdicts concern source topology, not Lean proof status.

Only this report and the companion W-w1b-review-4.md were written. No git, lake, Lean, build, or lint command was run.
