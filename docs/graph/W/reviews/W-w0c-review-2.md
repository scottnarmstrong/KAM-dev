# W-w0c delta review

Reviewer: sol-delta-W-w0c

Verdict: FAIL. Rule 9 scope: the ten PROPOSED node records and four reviewer-written coverage corrections; prior REVIEWED records are not re-adjudicated.

| Node | Verdict | Evidence / reason |
|---|---|---|
| bpW:w0:basis#lam | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:basis@L39-L42 |
| bpW:w0:ellap#WaveSpace | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L51-L57 |
| bpW:w0:H | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:H@L87-L92 |
| bpW:w0:Gq#cubicGrad | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:Gq@L96-L101 |
| bpW:w0:eqmotion | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:eqmotion@L103-L112 |
| bpW:w0:z | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:z@L118-L123 |
| bpW:w0:actions | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:actions@L127-L134 |
| bpW:w0:periodone#linearTorus | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:periodone@L136-L144 |
| bpW:w0:ellap#spaces | PASS | blueprint-W/parts/w0-conventions.tex#bpW:w0:ellap@L51-L57 |
| bpW:w0:reconstruction#rescaling | FAIL | missing direct sineMode anchor edge at L78 |

Coverage table (no failing in-scope items):

| Item | Verdict | Evidence |
|---|---|---|

Coverage: all other coverage items PASS (all four in-scope corrected items PASS; round-1 REVIEWED items remain outside delta scope).

Replacement fragment:

```text
NODE: bpW:w0:reconstruction#rescaling
KIND: definition
TITLE: Inverse coefficient dictionary and symplectic rescaling
STATEMENT_SOURCE: blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L78-L80
PROOF_SOURCE: -
CONTRACT_ID: bpW:w0:reconstruction#rescaling
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0 through lambda; coefficient data (q,p) in E_{a,p}, a > 0; u = U_m(q), u_t = V_m(p), u = sum x_j phi_j, u_t = sum y_j phi_j
SOURCE_QUANTIFIERS: j >= 1
SOURCE_CONCLUSION: records the equivalent coefficient dictionary q_j = sqrt(lambda_j) x_j, p_j = y_j/sqrt(lambda_j), and the coordinatewise symplectic identity dq_j wedge dp_j = dx_j wedge dy_j; x_j,y_j here are sine coefficients, not the frozen weighted coordinates
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L78-L79 | u = U_m(q) gives the displacement coefficient rescaling
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L78-L79 | u_t = V_m(p) gives the momentum coefficient rescaling
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L79-L80 | reciprocal sqrt(lambda_j) factors give the symplectic rescaling
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w0-conventions.tex#bpW:w0:reconstruction@L78-L78 | the inverse dictionary explicitly expands u and u_t in the frozen sine basis phi_j
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: new+sol-review-W-w0c
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

Suspected defects of the blueprint: none newly identified in this delta. Frozen identities match the manifest identity fields; the weighted carrier, max norm, positive action carrier, mode shift and period-one signs agree with the designated definition files. The rescaling dictionary uses sine coefficients, distinct from weighted coordinates. No Lean proof status is assessed.

Validation: `python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/W/packets W-w0c` returned `W-w0c: 19 nodes, 43 edges, 41 coverage items, 0 problems`. Report-only checks verified verdict coverage, complete replacement fields, matching DEPS/EDGE sets, valid locator ranges and whitespace. The checker ran on the unchanged input packet; it does not accept these proposed corrections. No git, Lean, lake or lint commands were run.
