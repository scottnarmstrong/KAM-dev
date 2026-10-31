# W-w5a: delta 6 independent source review

Reviewer: `sol-delta6-W-W-w5a` (codex-1).
Verdict: **FAIL**.

Scope: 22 PROPOSED nodes and 21 PROPOSED coverage items in this slice. REVIEWED records were read only as dependency context. This report evaluates the current pinned corpus, not concurrent repairs. No packet, corpus, frozen file, manifest, or Lean implementation was edited or interpreted.

The SPEC wave-2 extraction and wave-2 review-1/delta-5 rulings and REVIEW-BRIEF rules 1-11 govern this review. Re-read source statements, proof contexts, consumer use sites and the cross-part prerequisite statements. No gap was made an assumption; ordinary Lean fields remain initialized.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| bpW:w5:w4-general | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L123-L133; blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L134-L151 |
| bpW:w5:w4-modified | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L156-L177; blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L178-L222 |
| stepW:w5:m-other | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-other@L185-L186 |
| stepW:w5:m-act | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L191-L212 |
| stepW:w5:m-ass | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L213-L217 |
| stepW:w5:t-comp | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L285-L292 |
| stepW:w5:t-field | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L293-L298 |
| stepW:w5:s-class | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L357-L360 |
| bpW:w5:flow | FAIL | The M_F <= sigma/256 and L <= 1/64 bounds at L367-L369 are asserted applicability conclusions, not extra source premises. Retain only step data, smallness and the local definitions in SOURCE_HYPOTHESES; the margins/solve dependencies supply the bounds. |
| stepW:w5:f-flow | FAIL | The M_F <= sigma/256 and L <= 1/64 bounds at L367-L369 are asserted applicability conclusions, not extra source premises. Retain only step data, smallness and the local definitions in SOURCE_HYPOTHESES; the margins/solve dependencies supply the bounds. |
| stepW:w5:f-par | FAIL | The M_F <= sigma/256 and L <= 1/64 bounds at L367-L369 are asserted applicability conclusions, not extra source premises. Retain only step data, smallness and the local definitions in SOURCE_HYPOTHESES; the margins/solve dependencies supply the bounds. |
| stepW:w5:f-der | FAIL | The M_F <= sigma/256 and L <= 1/64 bounds at L367-L369 are asserted applicability conclusions, not extra source premises. Retain only step data, smallness and the local definitions in SOURCE_HYPOTHESES; the margins/solve dependencies supply the bounds. |
| stepW:w5:f-image | FAIL | The M_F <= sigma/256 and L <= 1/64 bounds at L367-L369 are asserted applicability conclusions, not extra source premises. Retain only step data, smallness and the local definitions in SOURCE_HYPOTHESES; the margins/solve dependencies supply the bounds. |
| stepW:w5:f-real | FAIL | The M_F <= sigma/256 and L <= 1/64 bounds at L367-L369 are asserted applicability conclusions, not extra source premises. Retain only step data, smallness and the local definitions in SOURCE_HYPOTHESES; the margins/solve dependencies supply the bounds. |
| bpW:w5:flow-calc | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L412-L425; blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L426-L448 |
| stepW:w5:c-cont | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-cont@L427-L430 |
| stepW:w5:c-var | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L431-L433 |
| stepW:w5:c-skew | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-skew@L434-L436 |
| stepW:w5:c-symp | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L437-L438 |
| stepW:w5:c-inv | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-inv@L439-L440 |
| stepW:w5:c-trans | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L441-L444 |
| bpW:w5#data | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5@L35-L39 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w5:w4-general | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-general@L123-L133 |
| bpW:w5:w4-modified | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L156-L177 |
| stepW:w5:m-other | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-other@L185-L186 |
| stepW:w5:m-act | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L191-L212 |
| stepW:w5:m-ass | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L213-L217 |
| stepW:w5:t-comp | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L285-L292 |
| stepW:w5:t-field | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L293-L298 |
| stepW:w5:s-class | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:s-class@L357-L360 |
| bpW:w5:flow | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L364-L379 |
| stepW:w5:f-flow | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L384-L387 |
| stepW:w5:f-par | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L388-L393 |
| stepW:w5:f-der | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L394-L397 |
| stepW:w5:f-image | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-image@L398-L399 |
| stepW:w5:f-real | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L400-L403 |
| bpW:w5:flow-calc | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow-calc@L412-L425 |
| stepW:w5:c-cont | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-cont@L427-L430 |
| stepW:w5:c-var | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-var@L431-L433 |
| stepW:w5:c-skew | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-skew@L434-L436 |
| stepW:w5:c-symp | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-symp@L437-L438 |
| stepW:w5:c-inv | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-inv@L439-L440 |
| stepW:w5:c-trans | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:c-trans@L441-L444 |

All other coverage items PASS within the delta scope; previously REVIEWED items are not re-certified.

## Replacement fragments

### bpW:w5:flow (owner: W-w5a)

The M_F <= sigma/256 and L <= 1/64 bounds at L367-L369 are asserted applicability conclusions, not extra source premises. Retain only step data, smallness and the local definitions in SOURCE_HYPOTHESES; the margins/solve dependencies supply the bounds.

```text
NODE: bpW:w5:flow
KIND: lemma
TITLE: The flow with explicit margins; P96-K (9)--(11) and Lemma~A.4
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L364-L379
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#bpW:w5:flow@L380-L404
CONTRACT_ID: bpW:w5:flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,¦.¦_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = D(s-2sigma,r/2), delta = sigma/4, M = M_F, L = M/delta (local definitions for the application whose hypotheses are to be proved)
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
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a+sol-delta6-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

### stepW:w5:f-flow (owner: W-w5a)

The M_F <= sigma/256 and L <= 1/64 bounds at L367-L369 are asserted applicability conclusions, not extra source premises. Retain only step data, smallness and the local definitions in SOURCE_HYPOTHESES; the margins/solve dependencies supply the bounds.

```text
NODE: stepW:w5:f-flow
KIND: step
TITLE: Flow
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L384-L387
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-flow@L384-L387
CONTRACT_ID: stepW:w5:f-flow
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow: step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,¦.¦_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = D(s-2sigma,r/2), delta = sigma/4, M = M_F, L = M/delta (local definitions for the application whose hypotheses are to be proved)
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
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a+sol-delta6-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

### stepW:w5:f-par (owner: W-w5a)

The M_F <= sigma/256 and L <= 1/64 bounds at L367-L369 are asserted applicability conclusions, not extra source premises. Retain only step data, smallness and the local definitions in SOURCE_HYPOTHESES; the margins/solve dependencies supply the bounds.

```text
NODE: stepW:w5:f-par
KIND: step
TITLE: Parameters
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L388-L393
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-par@L388-L393
CONTRACT_ID: stepW:w5:f-par
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow: step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,¦.¦_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = D(s-2sigma,r/2), delta = sigma/4, M = M_F, L = M/delta (local definitions for the application whose hypotheses are to be proved)
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
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a+sol-delta6-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

### stepW:w5:f-der (owner: W-w5a)

The M_F <= sigma/256 and L <= 1/64 bounds at L367-L369 are asserted applicability conclusions, not extra source premises. Retain only step data, smallness and the local definitions in SOURCE_HYPOTHESES; the margins/solve dependencies supply the bounds.

```text
NODE: stepW:w5:f-der
KIND: step
TITLE: Derivative
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L394-L397
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-der@L394-L397
CONTRACT_ID: stepW:w5:f-der
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow: step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,¦.¦_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = D(s-2sigma,r/2), delta = sigma/4, M = M_F, L = M/delta (local definitions for the application whose hypotheses are to be proved)
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
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a+sol-delta6-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

### stepW:w5:f-image (owner: W-w5a)

The M_F <= sigma/256 and L <= 1/64 bounds at L367-L369 are asserted applicability conclusions, not extra source premises. Retain only step data, smallness and the local definitions in SOURCE_HYPOTHESES; the margins/solve dependencies supply the bounds.

```text
NODE: stepW:w5:f-image
KIND: step
TITLE: Image
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-image@L398-L399
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-image@L398-L399
CONTRACT_ID: stepW:w5:f-image
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow: step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,¦.¦_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = D(s-2sigma,r/2), delta = sigma/4, M = M_F, L = M/delta (local definitions for the application whose hypotheses are to be proved)
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
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a+sol-delta6-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

### stepW:w5:f-real (owner: W-w5a)

The M_F <= sigma/256 and L <= 1/64 bounds at L367-L369 are asserted applicability conclusions, not extra source premises. Retain only step data, smallness and the local definitions in SOURCE_HYPOTHESES; the margins/solve dependencies supply the bounds.

```text
NODE: stepW:w5:f-real
KIND: step
TITLE: Reality and equivariance
STATEMENT_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L400-L403
PROOF_SOURCE: blueprint-W/parts/w5-kamstep.tex#stepW:w5:f-real@L400-L403
CONTRACT_ID: stepW:w5:f-real
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w5:flow: step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,¦.¦_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = D(s-2sigma,r/2), delta = sigma/4, M = M_F, L = M/delta (local definitions for the application whose hypotheses are to be proved)
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
EXTRACTOR: claude-suborch-W+sol-review-W-W-w5a+sol-delta6-W-W-w5a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Source-gap disposition

The following records faithfully expose the pinned source obligations and do not add them to SOURCE_HYPOTHESES: `stepW:w5:t-comp`, `stepW:w5:c-skew`. All retain `LEAN_NOTE: -`. A topology PASS does not certify their mathematics. The schurrep replacement, if present, changes only a defining dependency.

## Suspected blueprint defects

- `blueprint-W/parts/w5-kamstep.tex:289-290`: "because D^2P is symmetric (Schwarz, second_derivative_symmetric)". The named symmetry fact is not one of the permitted externals and is not proved here; t-comp correctly exposes it.
- `blueprint-W/parts/w5-kamstep.tex:434-436`: "which is symmetric". Skewness consumes symmetry of D^2F without a permitted Schwarz input; c-skew correctly exposes the same kind of missing input.

These observations concern the blueprint as pinned here. No claim is made that parallel source repairs have landed.

## Checks

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w5a`: exit 0; `W-w5a: 50 nodes, 178 edges, 74 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This checks the existing graph; the proposed report replacements have not been applied.
- Report validation: all 133 requested node rows and 68 coverage rows occur exactly once across the ten reports; the 15 FAIL rows have 15 complete replacement blocks with all fields, valid locators and matching DEPS/EDGE targets. An in-memory overlay of these replacements is acyclic and retains all 693 packet nodes in the root closure, including alternative routes. Packets were not modified.
- Final corpus recheck: all eleven hashes still OK. Review whitespace check passed.
- No Lean, lake, build, proof-body, axiom, or state-changing git checks: this is the explicitly requested source-only review.

Uncertainty: the named SOURCE_GAP obligations remain unpaid in this corpus; structural validation cannot resolve them. No mathematical repair or source deviation is introduced by this report.

READY sol-delta6-W-W-w5a
