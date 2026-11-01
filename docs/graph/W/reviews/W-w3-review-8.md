# W-w3: independent delta 8 source review

Reviewer: `sol-delta8-W-W-w3`.

Verdict: **PASS**.

Scope: only the 1 requested PROPOSED delta-7 replacement record(s), under SPEC through “2026-10-31, delta 7” and REVIEW-BRIEF rules 1-11, especially delta rule 9. This is a source-field and dependency review, not proof completion. The reviewer tag is distinct from all earlier review tags.

## Node verdicts

| Node | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w3:class-remark | PASS | blueprint-W/parts/w3-birkhoff.tex L23-L27, L171-L177, L504-L527, L621-L629, L687-L705, L771-L778; blueprint-W/parts/w1-sequences.tex L81-L88, L740-L746; blueprint-W/parts/w6-iteration.tex L383-L385 |

## Coverage verdicts

No coverage item is reopened by this delta. All other coverage items PASS within the requested delta scope; previously REVIEWED coverage is not re-certified.

## Source and dependency findings

The statement/proof locator L771-L778 covers exactly the regularity remark. Its four source fields retain W3's standing scope, the complex ball and real restrictions, the power-series constructions, and the implication from analyticity to W1 holomorphy, without introducing a new premise or constant. The six dependencies are genuine uses at the listed consumer lines: flow supplies Gamma, main supplies K and X_K, Yseries supplies the explicit X_{K_2} series, real-restrict supplies the real restriction, and holomorphic plus ext-analytic supply the final implication. The remark expressly declines to use the converse Banach-space theorem, and no such edge is present.

The corrected NOTE now points to w6-iteration.tex L383, where t-an explicitly cites class-remark inside its proof. Its retention as a claim and the touched t-an edge are justified. There is no stale L374 locator in this record.

## Replacement fragments

None: every in-scope record PASSes.

## Checks

`sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all 11 pinned source files reported `OK`.

```text
python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w3
W-w3: 90 nodes, 339 edges, 141 coverage items, 0 problems
```

Slice checker: exit 0.

```text
python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable
```

Assembled graph checker: exit 0, no output. This checks the existing graph structure; it does not mark these records REVIEWED or certify Lean proofs.

A search of current non-draft `*.nodes.md` packets and `DEPGRAPH.md` found no `bpW:w7:melnikov` references. Its coverage exclusion remains administrative context, outside this delta. None of the four reviewed records has a stale Melnikov dependency, edge, source-field citation or note.

## Suspected blueprint errata

None newly suspected in the reviewed delta. The four delta-7 findings were packet transcription/topology corrections; this review does not reopen previously recorded source errata.

## Handoff

Only the three requested delta-8 review files were written. Packets, graph databases, source files, frozen files and manifest were not edited. No implementation Lean was read. No Lean, Lake, build, axiom probe, source lint or state-changing git command was run. Previously REVIEWED records were read only as dependency/use-site context and are not re-certified.
