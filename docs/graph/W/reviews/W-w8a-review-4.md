# W-w8a: independent delta 9 source review

Reviewer: `sol-delta9-W-W-w8a` (codex-1).

Verdict: **PASS**.

Scope: 1 PROPOSED nodes and 0 PROPOSED coverage items, limited to G1's package edges, the same-rule writer extension, and G3's adaptation/provenance correction as applicable to this slice. Governed by AGENTS.md, PLAN, DECISIONS, SPEC through “2026-10-31, global review 1”, REVIEW-BRIEF rules 1-11 (especially rule 9), and GLOBAL-review findings G1/G3. REVIEWED records were consulted only as touched dependency/consumer context. This is delta acceptance of source topology, not a fresh audit of unchanged fields or Lean proof closure. The reviewer tag is distinct from every earlier tag.

## Node verdicts

| Node | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w8:shells | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:shells@L117-L128 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |


All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

The only reopened record, bpW:w8:shells, explicitly names bpW:w8#data in SOURCE_HYPOTHESES. W8 L36-L53 fixes the weights, norms, constants, indexing and transport notation. In particular the shell formulas L122-L124 directly use c_A, gamma and gamma_1 from this opening, in addition to the separately supplied W8 constants and W7 shells. The new bpW:w8#data DEPS entry and EDGE occur once and cite the consumer definition L117-L128. This repairs the package edge without changing the shell radii, exponents, trimming rule or standing source fields. The REVIEWED package was checked only as the endpoint of this new edge.

Across the rendered, non-draft packets, the explicit package-invocation check found no missing direct dependency: literal package IDs in SOURCE_HYPOTHESES and the W3/W5/W7/W8 standing-data phrases all have their named package in DEPS. All 149 new package edges have the correct target, one DEPS entry, a matching EDGE, valid source ranges and exactly the consumer STATEMENT_SOURCE as locator. Their counts are 81 W3-data, 24 W5-data, 15 W7-data, 28 W7-basic-data and 1 W8-data. All 121 G1 EDGE proposals are retained verbatim in the rendered packets. This limited consistency check does not reopen unrelated REVIEWED records or infer new packages from symbols.

## Replacement fragments

None: every in-scope record PASSes.

## Suspected blueprint errata

None newly suspected in this delta. The W7 owner-slice attribution discrepancy above, where applicable, is in the task description, not the mathematical blueprint. Existing pinned-paper errata/source-gap repairs were not independently re-audited. No source deviation is introduced.

## Checks and limits

`sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK. `sha256sum -c docs/graph/W/IMPORTS.sha256`: exit 0; p1-analysis.tex OK.

```text
python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w8a
W-w8a: 56 nodes, 209 edges, 79 coverage items, 0 problems
```

Slice checker: exit 0.

```text
python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable
```

Assembled graph checker: exit 0, no output. These mechanical results validate structure, not mathematical source fidelity, global acceptance or proof completion. The packets remain PROPOSED pending writer application of the verdicts. G2's separate upstream amendment review is outside this task.

Only the seven requested review reports were written. No packets, databases, blueprint sources, frozen files or manifest were edited. No implementation Lean was read; no Lean, Lake, build, axiom probe, source lint or state-changing git command was run.

Final report validation: the seven reports have exactly the 150 requested PROPOSED node verdicts and one PROPOSED coverage verdict, with no duplicate or out-of-scope verdict row; all PASS. No FAIL replacement blocks are required. Review formatting checks passed. SHA-256 comparison of 234 protected packet/source/database/frozen/manifest files found no changes during report writing.
