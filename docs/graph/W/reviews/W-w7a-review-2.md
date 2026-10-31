# W-w7a: delta 6 independent source review

Reviewer: `sol-delta6-W-W-w7a` (codex-1).
Verdict: **FAIL**.

Scope: 19 PROPOSED nodes and 1 PROPOSED coverage items in this slice. REVIEWED records were read only as dependency context. This report evaluates the current pinned corpus, not concurrent repairs. No packet, corpus, frozen file, manifest, or Lean implementation was edited or interpreted.

The SPEC wave-2 extraction and wave-2 review-1/delta-5 rulings and REVIEW-BRIEF rules 1-11 govern this review. Re-read source statements, proof contexts, consumer use sites and the cross-part prerequisite statements. No gap was made an assumption; ordinary Lean fields remain initialized.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| stepW:w7:norms | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L158-L162 |
| bpW:w7:unpert-bounds | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L172-L181; blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L182-L204 |
| stepW:w7:ssize | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L183-L185 |
| stepW:w7:plus | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L186-L189 |
| stepW:w7:liplOmega | FAIL | L203 uses 1/lambda_j <= 1/j to bound the affine coefficient by the minus-one index norm; add the direct lambda-facts dependency supplying j < lambda_j. |
| bpW:w7:constdef | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L211-L231 |
| stepW:w7:sep-concl | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L353-L355 |
| stepW:w7:largek-tan | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L365-L367 |
| stepW:w7:largek-cmp | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-cmp@L368-L370 |
| bpW:w7:Xdef | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:Xdef@L398-L401 |
| bpW:w7:dichotomy | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L403-L406; blueprint-W/parts/w7-measure.tex#bpW:w7:dichotomy@L407-L417 |
| stepW:w7:Xfinite | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:Xfinite@L408-L410 |
| stepW:w7:dich-large | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-large@L411-L413 |
| stepW:w7:dich-small | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L414-L416 |
| bpW:w7:Xzones | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L421-L429; blueprint-W/parts/w7-measure.tex#bpW:w7:Xzones@L430-L444 |
| stepW:w7:X-A3 | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L431-L435 |
| stepW:w7:X-const | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L436-L438 |
| stepW:w7:X-slope | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L439-L443 |
| bpW:w7:constdef#base | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L214-L217 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w7:constdef | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L211-L231 |

All other coverage items PASS within the delta scope; previously REVIEWED items are not re-certified.

## Replacement fragments

### stepW:w7:liplOmega (owner: W-w7a)

L203 uses 1/lambda_j <= 1/j to bound the affine coefficient by the minus-one index norm; add the direct lambda-facts dependency supplying j < lambda_j.

```text
NODE: stepW:w7:liplOmega
KIND: step
TITLE: Lipschitz
STATEMENT_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L201-L203
PROOF_SOURCE: blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L201-L203
CONTRACT_ID: stepW:w7:liplOmega
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w7:unpert-bounds: W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, ¦k¦ = ¦k_1¦ + ¦k_2¦; ¦xi¦_infty <= 1/2, zeta = omega^0(xi); beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2 + 1
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w7:unpert-bounds (for such xi; l in Lambda; i > j >= 3); within the step: zeta, zeta'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) the Lipschitz bound
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:basis#lam, bpW:w7:freqcoords, bpW:w0:basis#lambda-facts
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L202-L202 | lambda occurs directly here (frozen lam)
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L202-L203 | the affine Omega^0 formula and s(zeta) from (iii)
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L203-L203 | j < lambda_j gives the reciprocal bound used in the coefficient sum
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w7a+sol-delta6-W-W-w7a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Suspected blueprint defects

No additional suspected blueprint defect found in the reviewed records.

These observations concern the blueprint as pinned here. No claim is made that parallel source repairs have landed.

## Checks

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w7a`: exit 0; `W-w7a: 51 nodes, 153 edges, 79 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This checks the existing graph; the proposed report replacements have not been applied.
- Report validation: all 133 requested node rows and 68 coverage rows occur exactly once across the ten reports; the 15 FAIL rows have 15 complete replacement blocks with all fields, valid locators and matching DEPS/EDGE targets. An in-memory overlay of these replacements is acyclic and retains all 693 packet nodes in the root closure, including alternative routes. Packets were not modified.
- Final corpus recheck: all eleven hashes still OK. Review whitespace check passed.
- No Lean, lake, build, proof-body, axiom, or state-changing git checks: this is the explicitly requested source-only review.

Uncertainty: the named SOURCE_GAP obligations remain unpaid in this corpus; structural validation cannot resolve them. No mathematical repair or source deviation is introduced by this report.

READY sol-delta6-W-W-w7a
