# W-w8b: independent delta 7 source review

Reviewer: `sol-delta7-W-w8b` (codex-1).

Verdict: **PASS**.

Scope: 3 PROPOSED nodes and 0 PROPOSED coverage items. REVIEWED records were read only as touched dependency context. Governed by SPEC through delta 6 and the accepted W4-W6 gap repair, and REVIEW-BRIEF rules 1-11. The pinned source was checked independently of the earlier gapfix verdict. This is source topology, not Lean theorem closure.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| stepW:w8:ni-same | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508 |
| stepW:w8:ni-diff | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L509-L513 |
| stepW:w8:p-lim | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L582 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |

All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

Both injectivity cases consume patch-local at the proof preamble L507 to identify 2 pi nu with shell omega_*. This is a derived fact supplied by an edge, not an added hypothesis. In the same-shell case freq-shell(ii) forces I=I'; in different shells shell-data(ii), freqcoords(iv), and freq-shell(iii) yield the strictly positive difference at L512, contradicting frequency equality.

p-lim uses limit with the patched omega_*=2 pi nu, the direct freq-shell(iii) estimate, the shell sequence alpha_n=(2^(-n)t_0)^(95/64)->0, and the frozen lam at L582. The former etor edge is correctly absent: the direct estimate is already supplied by freq-shell. No extra source premise, changed filter or uniform-in-m limit has been introduced.

## Replacement fragments

None.

## Suspected blueprint errata

No new suspected blueprint defect in the reviewed source delta. The previously reported gap obligations are closed in this pinned corpus. Packet transcription, dependency or stale-locator findings above are graph defects, not blueprint errata. No source deviation is introduced.

## Checks and limits

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK, including the re-pinned W4, W5 and W6.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w8b`: exit 0; `W-w8b: 46 nodes, 200 edges, 61 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This validates the existing assembled graph; report replacements have not been applied.
- Report validation: nine reports contain exactly the 31 requested node rows and five coverage rows; four FAIL rows have four complete replacement blocks with matching DEPS/EDGE targets and valid source ranges. An in-memory overlay is acyclic and retains all 696 nodes in the root closure (2397 dependency/route edges). Final corpus hashes and protected packet/database/manifest snapshots are unchanged. Review whitespace validation passed.
- No packets, source files, frozen files, manifest or databases were edited. No implementation Lean was read, and no Lean, Lake, build, axiom probe, lint_sources or state-changing git command was run, as required by this source-only brief.
- The report replacements remain PROPOSED with initialized Lean fields; accepting or applying them is the writer's step. Structural checks do not certify analytic correctness or Lean proof completion.

READY sol-delta7-W-w8b
