# W-w7b: independent delta 9 source review

Reviewer: `sol-delta9-W-W-w7b` (codex-1).

Verdict: **PASS**.

Scope: 15 PROPOSED nodes and 0 PROPOSED coverage items, limited to G1's package edges, the same-rule writer extension, and G3's adaptation/provenance correction as applicable to this slice. Governed by AGENTS.md, PLAN, DECISIONS, SPEC through “2026-10-31, global review 1”, REVIEW-BRIEF rules 1-11 (especially rule 9), and GLOBAL-review findings G1/G3. REVIEWED records were consulted only as touched dependency/consumer context. This is delta acceptance of source topology, not a fresh audit of unchanged fields or Lean proof closure. The reviewer tag is distinct from every earlier tag.

## Node verdicts

| Node | Verdict | Source spans re-read |
| --- | --- | --- |
| stepW:w7:prep-0 | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-0@L467-L468 |
| stepW:w7:prep-plus | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-plus@L469-L473 |
| stepW:w7:prep-minus-group | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L474-L481 |
| stepW:w7:prep-j0 | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-j0@L482-L493 |
| stepW:w7:prep-n | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-n@L494-L496 |
| stepW:w7:prep-X | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-X@L497-L499 |
| stepW:w7:prep-sum | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L500-L503 |
| stepW:w7:it-plus | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-plus@L518-L520 |
| stepW:w7:it-group | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L521-L526 |
| stepW:w7:it-j0 | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L527-L532 |
| stepW:w7:it-n | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-n@L533-L536 |
| stepW:w7:it-sum | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L537-L540 |
| stepW:w7:it-X | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L541-L543 |
| bpW:w7:measurable | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:measurable@L550-L553 |
| stepW:w7:meas-union | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:meas-union@L558-L559 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |


All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

These 15 reopened records are writer-extension consumers of bpW:w7:basic#data, rather than G1 consumers of bpW:w7#data. The extension's full 28 records split as 13 in W-w7a and 15 here; G1's 15 W7 records actually belong to W-w7a. This is a prompt ownership/count clarification, not a packet or blueprint defect.

Every listed SOURCE_HYPOTHESES expressly names bpW:w7:basic#data and the fixed zone-estimate scope at L339-L343. The preparatory steps L467-L503 work with the unperturbed pair on Pi (preamble L466); the iteration steps L518-L543 work with the selected admissible pair on D_nu (preamble L516-L517); measurability and its union step L550-L559 concern the same Borel domains and countable zone families. The package supplies these fixed data and their rho/rho_zeta notation. Each added dependency is therefore direct under the specified package rule, with exactly one DEPS entry, matching EDGE and consumer locator. Existing REVIEWED prep, iter and meas-cont records already have their relevant package edges and are not re-certified.

Across the rendered, non-draft packets, the explicit package-invocation check found no missing direct dependency: literal package IDs in SOURCE_HYPOTHESES and the W3/W5/W7/W8 standing-data phrases all have their named package in DEPS. All 149 new package edges have the correct target, one DEPS entry, a matching EDGE, valid source ranges and exactly the consumer STATEMENT_SOURCE as locator. Their counts are 81 W3-data, 24 W5-data, 15 W7-data, 28 W7-basic-data and 1 W8-data. All 121 G1 EDGE proposals are retained verbatim in the rendered packets. This limited consistency check does not reopen unrelated REVIEWED records or infer new packages from symbols.

## Replacement fragments

None: every in-scope record PASSes.

## Suspected blueprint errata

None newly suspected in this delta. The W7 owner-slice attribution discrepancy above, where applicable, is in the task description, not the mathematical blueprint. Existing pinned-paper errata/source-gap repairs were not independently re-audited. No source deviation is introduced.

## Checks and limits

`sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK. `sha256sum -c docs/graph/W/IMPORTS.sha256`: exit 0; p1-analysis.tex OK.

```text
python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w7b
W-w7b: 41 nodes, 137 edges, 63 coverage items, 0 problems
```

Slice checker: exit 0.

```text
python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable
```

Assembled graph checker: exit 0, no output. These mechanical results validate structure, not mathematical source fidelity, global acceptance or proof completion. The packets remain PROPOSED pending writer application of the verdicts. G2's separate upstream amendment review is outside this task.

Only the seven requested review reports were written. No packets, databases, blueprint sources, frozen files or manifest were edited. No implementation Lean was read; no Lean, Lake, build, axiom probe, source lint or state-changing git command was run.

Final report validation: the seven reports have exactly the 150 requested PROPOSED node verdicts and one PROPOSED coverage verdict, with no duplicate or out-of-scope verdict row; all PASS. No FAIL replacement blocks are required. Review formatting checks passed. SHA-256 comparison of 234 protected packet/source/database/frozen/manifest files found no changes during report writing.
