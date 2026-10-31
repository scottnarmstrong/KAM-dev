# W-w3: independent delta 7 source review

Reviewer: `sol-delta7-W-w3` (codex-1).

Verdict: **FAIL**.

Scope: 1 PROPOSED nodes and 0 PROPOSED coverage items. REVIEWED records were read only as touched dependency context. Governed by SPEC through delta 6 and the accepted W4-W6 gap repair, and REVIEW-BRIEF rules 1-11. The pinned source was checked independently of the earlier gapfix verdict. This is source topology, not Lean theorem closure.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| bpW:w3:class-remark | FAIL | The restored claim and its new analytic-map edge are sound, but NOTE still locates the W6 t-an citation at L374. In the re-pinned corpus it is L383; L374 is in t-hol. Correct this stale in-text locator. |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |

All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

The new edge to `bpW:w1:ext-analytic` is a genuine use at W3 L776: that external states analytic maps are Frechet differentiable (W1 L81-L88), while `holomorphic` supplies the definition. Gamma's power series, K and X_K, Yseries, and real restrictions are supplied by their named W3 dependencies. No assertion that every complex differentiable Banach map is analytic is imported. The single FAIL below is a stale NOTE locator after re-pinning, not a mathematical gap.

## Replacement fragments

### bpW:w3:class-remark (owner: W-w3)

The restored claim and its new analytic-map edge are sound, but NOTE still locates the W6 t-an citation at L374. In the re-pinned corpus it is L383; L374 is in t-hol. Correct this stale in-text locator.

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
EXTRACTOR: new+sol-delta6-W-W-w3+sol-delta7-W-w3
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Restored because stepW:w6:t-an cites this fact at w6-iteration.tex L383 inside a proof. Source topology only; no Lean proof status inferred.
```

## Suspected blueprint errata

No new suspected blueprint defect in the reviewed source delta. The previously reported gap obligations are closed in this pinned corpus. Packet transcription, dependency or stale-locator findings above are graph defects, not blueprint errata. No source deviation is introduced.

## Checks and limits

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK, including the re-pinned W4, W5 and W6.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w3`: exit 0; `W-w3: 90 nodes, 339 edges, 141 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This validates the existing assembled graph; report replacements have not been applied.
- Report validation: nine reports contain exactly the 31 requested node rows and five coverage rows; four FAIL rows have four complete replacement blocks with matching DEPS/EDGE targets and valid source ranges. An in-memory overlay is acyclic and retains all 696 nodes in the root closure (2397 dependency/route edges). Final corpus hashes and protected packet/database/manifest snapshots are unchanged. Review whitespace validation passed.
- No packets, source files, frozen files, manifest or databases were edited. No implementation Lean was read, and no Lean, Lake, build, axiom probe, lint_sources or state-changing git command was run, as required by this source-only brief.
- The report replacements remain PROPOSED with initialized Lean fields; accepting or applying them is the writer's step. Structural checks do not certify analytic correctness or Lean proof completion.

READY sol-delta7-W-w3
