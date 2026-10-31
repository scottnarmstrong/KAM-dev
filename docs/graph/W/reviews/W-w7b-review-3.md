# W-w7b: independent delta 7 source review

Reviewer: `sol-delta7-W-w7b` (codex-1).

Verdict: **PASS**.

Scope: 0 PROPOSED nodes and 1 PROPOSED coverage items. REVIEWED records were read only as touched dependency context. Governed by SPEC through delta 6 and the accepted W4-W6 gap repair, and REVIEW-BRIEF rules 1-11. The pinned source was checked independently of the earlier gapfix verdict. This is source topology, not Lean theorem closure.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |

No PROPOSED nodes in this slice.

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w7:melnikov | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:melnikov@L585-L596 |

All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

Searched every W4-W8 source file for `melnikov`, and specifically for `bpW:w7:melnikov`. The only occurrences of that exact label are its own corollary declaration (W7 L585) and references inside the excluded remarks w6-needs (L286-L313, citation L291) and interface (L781-L791, citation L787). There is no remaining citation in a statement or proof step outside that excluded unit. Re-read its own proof L597-L599 as well: it derives (i),(ii) from zones and (iii) from sep; no downstream consumer requires this wrapper. W6 prep-step now uses zones(i) directly (L232-L235, L250-L254). Other occurrences of “melnikov” refer to W4 definitions or W6's own iteration display, not this corollary. The reachability exclusion is therefore valid. The stale corollary mention in the W6 packet conclusion is a graph transcription error, addressed in the W-w6 report; it is not a remaining source use.

## Replacement fragments

None.

## Suspected blueprint errata

No new suspected blueprint defect in the reviewed source delta. The previously reported gap obligations are closed in this pinned corpus. Packet transcription, dependency or stale-locator findings above are graph defects, not blueprint errata. No source deviation is introduced.

## Checks and limits

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK, including the re-pinned W4, W5 and W6.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w7b`: exit 0; `W-w7b: 41 nodes, 122 edges, 63 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This validates the existing assembled graph; report replacements have not been applied.
- Report validation: nine reports contain exactly the 31 requested node rows and five coverage rows; four FAIL rows have four complete replacement blocks with matching DEPS/EDGE targets and valid source ranges. An in-memory overlay is acyclic and retains all 696 nodes in the root closure (2397 dependency/route edges). Final corpus hashes and protected packet/database/manifest snapshots are unchanged. Review whitespace validation passed.
- No packets, source files, frozen files, manifest or databases were edited. No implementation Lean was read, and no Lean, Lake, build, axiom probe, lint_sources or state-changing git command was run, as required by this source-only brief.
- The report replacements remain PROPOSED with initialized Lean fields; accepting or applying them is the writer's step. Structural checks do not certify analytic correctness or Lean proof completion.

READY sol-delta7-W-w7b
