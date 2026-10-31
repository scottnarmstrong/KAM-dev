# W-w8a: independent delta 7 source review

Reviewer: `sol-delta7-W-w8a` (codex-1).

Verdict: **PASS**.

Scope: 1 PROPOSED nodes and 0 PROPOSED coverage items. REVIEWED records were read only as touched dependency context. Governed by SPEC through delta 6 and the accepted W4-W6 gap repair, and REVIEW-BRIEF rules 1-11. The pinned source was checked independently of the earlier gapfix verdict. This is source topology, not Lean theorem closure.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| stepW:w8:sd-prep | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L171 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |

All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

sd-prep directly uses the Borel-domain and box conclusions of sd-trim at L168, the size bound of sd-size and initial perturbation bound of sd-init at L171, and initial for the real periodic smoothing class at L170. The application checks the hypotheses of prep-step, including positivity of epsilon^sharp and alpha, and concludes shell-data(iv), whose second clause is the to-w8 domain condition. Thus the relocated to-w8 use-site edge L168-L171 is genuine and the repaired divisor argument creates no new shell premise.

## Replacement fragments

None.

## Suspected blueprint errata

No new suspected blueprint defect in the reviewed source delta. The previously reported gap obligations are closed in this pinned corpus. Packet transcription, dependency or stale-locator findings above are graph defects, not blueprint errata. No source deviation is introduced.

## Checks and limits

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK, including the re-pinned W4, W5 and W6.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w8a`: exit 0; `W-w8a: 56 nodes, 208 edges, 79 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This validates the existing assembled graph; report replacements have not been applied.
- Report validation: nine reports contain exactly the 31 requested node rows and five coverage rows; four FAIL rows have four complete replacement blocks with matching DEPS/EDGE targets and valid source ranges. An in-memory overlay is acyclic and retains all 696 nodes in the root closure (2397 dependency/route edges). Final corpus hashes and protected packet/database/manifest snapshots are unchanged. Review whitespace validation passed.
- No packets, source files, frozen files, manifest or databases were edited. No implementation Lean was read, and no Lean, Lake, build, axiom probe, lint_sources or state-changing git command was run, as required by this source-only brief.
- The report replacements remain PROPOSED with initialized Lean fields; accepting or applying them is the writer's step. Structural checks do not certify analytic correctness or Lean proof completion.

READY sol-delta7-W-w8a
