# W-w2 delta review

Reviewer: sol-delta-W-w2 (independent reviewer sol-delta-W-batch2).

Verdict: PASS.

Scope: rule 9 applied to this slice: only records still PROPOSED on entry. REVIEWED node and coverage records are out of scope; prerequisites and consumers were read only as context. No graph acceptance or proof status is changed by this report.

Writer adjudication of bpW:w2:ext-trig: PASS. Externals must be dependency leaves, so DEPS: - and the absence of an EDGE to lam are correct. The positive-lambda square-root identities remain in the external statement. Their concrete uses in flin (L149) and t1 (L267) retain both ext-trig and frozen lam edges. The coefficient-map edges, C1/C2 package dependencies and frozen embedding projection are present. In fcub, a=p=1 supplies the positive-weight and regularity premises of the W0 force identity.

## Node verdicts

| id | verdict | spans or reason |
| --- | --- | --- |
| bpW:w2:ext-sums | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-sums@L55-L60 |
| bpW:w2:ext-trig | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-trig@L61-L64 |
| bpW:w2:force | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L128-L137; blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L139-L160 |
| stepW:w2:fsum | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L140-L147 |
| stepW:w2:flin | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L148-L153 |
| stepW:w2:fcub | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L154-L159 |
| bpW:w2:curve-deriv | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L206-L210; blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L212-L220 |
| stepW:w2:cdiff | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L213-L215 |
| stepW:w2:ccoord | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L216-L219 |
| stepW:w2:t1 | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L263-L270 |
| stepW:w2:t2 | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L271-L278 |
| stepW:w2:mred | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L324-L327 |

## Coverage verdicts

| id | verdict | spans |
| --- | --- | --- |
| bpW:w2:ext-sums | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-sums@L55-L60 |
| bpW:w2:ext-trig | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-trig@L61-L64 |
| bpW:w2:force | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L128-L137 |
| stepW:w2:fsum | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L140-L147 |
| stepW:w2:flin | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L148-L153 |
| stepW:w2:fcub | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L154-L159 |
| bpW:w2:curve-deriv | PASS | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L206-L210 |
| stepW:w2:cdiff | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L213-L215 |
| stepW:w2:ccoord | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L216-L219 |
| stepW:w2:t1 | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L263-L270 |
| stepW:w2:t2 | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L271-L278 |
| stepW:w2:mred | PASS | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L324-L327 |

all other coverage items PASS (within the PROPOSED delta scope only; previously REVIEWED items are not re-reviewed). Each pending disposition maps its source unit to the correct node or nodes, including the route mapping and curvature preamble where applicable. Node contract or edge failures above do not invalidate these coverage mappings.

## Complete replacement blocks

None.
## Suspected blueprint defects and deviations

No additional suspected blueprint defect found in the pending records. The replacements, if any, correct graph records only.

No mathematical repair is supplied. Validation: all six W corpus hashes and the K import hash match their pin files. Report row counts and complete replacement fields are checked with read-only Python; no git, lake, Lean, or lint was run. Only this batch's seven requested review reports are written.
