# W-w4: independent delta 7 source review

Reviewer: `sol-delta7-W-w4` (codex-1).

Verdict: **PASS**.

Scope: 3 PROPOSED nodes and 1 PROPOSED coverage items. REVIEWED records were read only as touched dependency context. Governed by SPEC through delta 6 and the accepted W4-W6 gap repair, and REVIEW-BRIEF rules 1-11. The pinned source was checked independently of the earlier gapfix verdict. This is source topology, not Lean theorem closure.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| stepW:w4:schurrep | PASS | blueprint-W/parts/w4-homological.tex#stepW:w4:schurrep@L419-L435 |
| bpW:w4:from-w3 | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:from-w3@L796-L815 |
| bpW:w4:ext-riesz | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:ext-riesz@L53-L62 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w4:ext-riesz | PASS | blueprint-W/parts/w4-homological.tex#bpW:w4:ext-riesz@L53-L62 |

All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

`schurrep`: kappa is an onto isometry. With C coordinate conjugation, B(v,w)=hat beta(Cv,w) is conjugate-linear/linear as ext-riesz requires; T=C B^sharp C is complex linear and its bilinear pairing is hat beta. The dual norm formula gives equality of operator and bilinear norms; testing e_j,e_i gives mu_j mu_i beta(e_j,e_i). The converse is the displayed Cauchy-Schwarz estimate. Thus the previous SOURCE_GAP is closed. ext-riesz, ext-lp, schur(iii), ops, transport, index and ellWeight are direct uses at their consumer locators. The accepted correction that toDual is conjugate-linear is present at W4 L60-L61. The new external is a leaf, with EXTERNAL initial Lean status.

`from-w3`: the frozen ellWeight edge is genuine at L800-L801. The shifted index J=j+2, the sum-norm comparison with sqrt(2), the smoothing gradient and symplectic identifications match W3's space, coords, main, omega and Hamiltonian-field definitions. The ownership ruling is retained as administrative context.

## Replacement fragments

None.

## Suspected blueprint errata

No new suspected blueprint defect in the reviewed source delta. The previously reported gap obligations are closed in this pinned corpus. Packet transcription, dependency or stale-locator findings above are graph defects, not blueprint errata. No source deviation is introduced.

## Checks and limits

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK, including the re-pinned W4, W5 and W6.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w4`: exit 0; `W-w4: 58 nodes, 167 edges, 103 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This validates the existing assembled graph; report replacements have not been applied.
- Report validation: nine reports contain exactly the 31 requested node rows and five coverage rows; four FAIL rows have four complete replacement blocks with matching DEPS/EDGE targets and valid source ranges. An in-memory overlay is acyclic and retains all 696 nodes in the root closure (2397 dependency/route edges). Final corpus hashes and protected packet/database/manifest snapshots are unchanged. Review whitespace validation passed.
- No packets, source files, frozen files, manifest or databases were edited. No implementation Lean was read, and no Lean, Lake, build, axiom probe, lint_sources or state-changing git command was run, as required by this source-only brief.
- The report replacements remain PROPOSED with initialized Lean fields; accepting or applying them is the writer's step. Structural checks do not certify analytic correctness or Lean proof completion.

READY sol-delta7-W-w4
