# W-w3: delta 6 independent source review

Reviewer: `sol-delta6-W-W-w3` (codex-1).
Verdict: **FAIL**.

Scope: 2 PROPOSED nodes and 1 PROPOSED coverage items in this slice. REVIEWED records were read only as dependency context. This report evaluates the current pinned corpus, not concurrent repairs. No packet, corpus, frozen file, manifest, or Lean implementation was edited or interpreted.

The SPEC wave-2 extraction and wave-2 review-1/delta-5 rulings and REVIEW-BRIEF rules 1-11 govern this review. Re-read source statements, proof contexts, consumer use sites and the cross-part prerequisite statements. No gap was made an assumption; ordinary Lean fields remain initialized.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| stepW:w3:wk-lin | PASS | blueprint-W/parts/w3-birkhoff.tex#stepW:w3:wk-lin@L845-L849 |
| bpW:w3:class-remark | FAIL | L776 uses analyticity implies complex differentiability; the definition of holomorphic alone does not supply this implication. Add the permitted W1 analytic-map external at the consumer. |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w3:class-remark | PASS | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L771-L778 |

All other coverage items PASS within the delta scope; previously REVIEWED items are not re-certified.

## Replacement fragments

### bpW:w3:class-remark (owner: W-w3)

L776 uses analyticity implies complex differentiability; the definition of holomorphic alone does not supply this implication. Add the permitted W1 analytic-map external at the consumer.

```text
NODE: bpW:w3:class-remark
KIND: claim
TITLE: Regularity class used by the W6 torus proof
STATEMENT_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L771-L778
PROOF_SOURCE: blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L771-L778
CONTRACT_ID: bpW:w3:class-remark
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: W3 standing data: m > 0, a >= 0, p >= 1/2, J = {1,2}; the normal-form objects Gamma,K,X_K
SOURCE_QUANTIFIERS: on the complex ball B_{rho_1}, and on its real form as stated
SOURCE_CONCLUSION: Gamma,K,X_K are complex analytic on B_{rho_1}; Gamma and K arise from compositions of power series, X_{K_1} from composition and operator inversion, X_{K_2} from Yseries; their real restrictions are real analytic; analyticity implies holomorphy in the sense of W1, so W1 Cauchy estimates apply
CONSTANT_SCOPE: rho_1 and the preceding constants retain their W3 dependence on m,a,p; no new constant
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w3:flow, bpW:w3:main, bpW:w3:Yseries, bpW:w3:real-restrict, bpW:w1:holomorphic, bpW:w1:ext-analytic
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w3:flow | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L772-L773 | Gamma has its analytic power series
EDGE: bpW:w3:main | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L772-L774 | K and X_K are analytic
EDGE: bpW:w3:Yseries | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L774-L774 | the explicit series for X_{K_2}
EDGE: bpW:w3:real-restrict | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L774-L774 | real restrictions are analytic
EDGE: bpW:w1:holomorphic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L776-L777 | the definition of holomorphy to which analyticity is applied
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w3-birkhoff.tex#bpW:w3:class-remark@L776-L777 | analytic maps are Frechet differentiable, hence holomorphic in the cited definition
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: new+sol-delta5-W-w3+sol-delta6-W-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Restored because stepW:w6:t-an cites this fact at w6-iteration.tex L374 inside a proof. Source topology only; no Lean proof status inferred.
```

## Suspected blueprint defects

No additional suspected blueprint defect found in the reviewed records.

These observations concern the blueprint as pinned here. No claim is made that parallel source repairs have landed.

## Checks

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w3`: exit 0; `W-w3: 90 nodes, 338 edges, 141 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This checks the existing graph; the proposed report replacements have not been applied.
- Report validation: all 133 requested node rows and 68 coverage rows occur exactly once across the ten reports; the 15 FAIL rows have 15 complete replacement blocks with all fields, valid locators and matching DEPS/EDGE targets. An in-memory overlay of these replacements is acyclic and retains all 693 packet nodes in the root closure, including alternative routes. Packets were not modified.
- Final corpus recheck: all eleven hashes still OK. Review whitespace check passed.
- No Lean, lake, build, proof-body, axiom, or state-changing git checks: this is the explicitly requested source-only review.

Uncertainty: the named SOURCE_GAP obligations remain unpaid in this corpus; structural validation cannot resolve them. No mathematical repair or source deviation is introduced by this report.

READY sol-delta6-W-W-w3
