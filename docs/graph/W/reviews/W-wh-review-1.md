# W-wh independent topology review 1

Reviewer: sol-review-W-wh. Verdict: **PASS** (wave-1 statement topology only).

| Node id | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:wh:embedding#IsAnalyticTorusEmbedding | PASS | blueprint-W/parts/w-headline.tex L13–16, L22–27; frozen IsAnalyticTorusEmbedding definition and docstring |
| bpW:wh:dioph#IsDiophantine | PASS | blueprint-W/parts/w-headline.tex L33–37; frozen KAM.IsDiophantine definition |
| bpW:wh:nlw2 | PASS | blueprint-W/parts/w-headline.tex L13–65, L67–101; frozen Nlw2 statement; w0-conventions.tex L24–35, L39–42, L51–63, L75–81, L96–101, L136–144 |

Coverage: **all other coverage items PASS** (all 14 items; no failing items).

All eleven dependencies are direct statement uses, with consumer locators. Cross-slice targets were checked against W-w0c.nodes.md and their raw definitions. No proof edge to W2, W3 or future W8 is justified yet: SPEC explicitly limits the root to statement definitions. The provisional PROOF_SOURCE is disclosed in NOTE and permitted by that convention. The linear-torus alias and inlined Dnu coverage follow SPEC. The two remarks are administrative; neither introduces a consumed proof premise in this slice. The final source macro is provenance only, not an external input.

The source fields preserve positive mass and actions, the max norm, coefficient versus weighted-coordinate interpretation, positive-mode indexing, period-one frequencies, the common C, per-action gamma, density in sup-norm balls, and all six clauses. Frozen total extensions of eta, nu and K do not alter the restricted source contract. The embedding record explicitly distinguishes the blueprint holomorphic-extension wording from the frozen AnalyticOnNhd wording; D41 authorizes this representation. All six identity fields of each of the three anchors match the manifest (path, export, anchor ID, contract ID/version, ABI hash). Frozen definition docstrings agree with SPEC's anchor mapping.

Checks: `python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_slice_check.py docs/graph/W/packets W-wh` returned exit 0 and `W-wh: 3 nodes, 11 edges, 14 coverage items, 0 problems`. No git, Lean, lake, builds or lint run. Only this report was written. No proof-closure or axiom audit is claimed.

Replacement fragments: none required.

## Suspected blueprint defects

Administrative staleness: w-headline.tex L7 says “nothing here is frozen”; D41 and the frozen declaration docstrings record owner approval and freezing on 2026-10-30. The packet already identifies the frozen anchors and excludes this historical introduction, so this does not invalidate the topology. No mathematical defect found in the reviewed statement; W8 assembly remains pending.

Minor locator precision: coverage item w-headline:source-L102 identifies the opening line of the source macro; its continuation ends at L103. The cited line locates the provenance item unambiguously. Expanding its span to L102–L103 would be clearer, without changing its disposition.

READY sol-review-W-wh
