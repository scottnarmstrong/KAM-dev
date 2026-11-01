# W-w5a: independent delta 9 source review

Reviewer: `sol-delta9-W-W-w5a` (codex-1).

Verdict: **PASS**.

Scope: 24 PROPOSED nodes and 0 PROPOSED coverage items, limited to G1's package edges, the same-rule writer extension, and G3's adaptation/provenance correction as applicable to this slice. Governed by AGENTS.md, PLAN, DECISIONS, SPEC through “2026-10-31, global review 1”, REVIEW-BRIEF rules 1-11 (especially rule 9), and GLOBAL-review findings G1/G3. REVIEWED records were consulted only as touched dependency/consumer context. This is delta acceptance of source topology, not a fresh audit of unchanged fields or Lean proof closure. The reviewer tag is distinct from every earlier tag.

## Node verdicts

| Node | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w5:omega | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:omega@L89-L93 |
| stepW:w5:ombd | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:ombd@L95-L96 |
| stepW:w5:omnd | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnd@L97-L99 |
| stepW:w5:omnorm | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:omnorm@L100-L101 |
| bpW:w5:class | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:class@L105-L119 |
| stepW:w5:g-tail | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-tail@L153-L154 |
| stepW:w5:g-div | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-div@L155-L157 |
| stepW:w5:g-diag | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-diag@L158-L160 |
| stepW:w5:g-rest | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:g-rest@L161-L164 |
| bpW:w5:w4-modified | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:w4-modified@L170-L191 |
| stepW:w5:m-sup | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-sup@L194-L198 |
| stepW:w5:m-other | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-other@L199-L200 |
| stepW:w5:m-lip | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-lip@L201-L204 |
| stepW:w5:m-act | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-act@L205-L226 |
| stepW:w5:m-ass | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-ass@L227-L231 |
| stepW:w5:m-const | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:m-const@L232-L235 |
| bpW:w5:taylor | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:taylor@L265-L285 |
| stepW:w5:t-scale | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-scale@L287-L290 |
| stepW:w5:t-disc | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-disc@L291-L293 |
| stepW:w5:t-poly | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-poly@L294-L298 |
| stepW:w5:t-comp | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-comp@L299-L307 |
| stepW:w5:t-field | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-field@L308-L313 |
| stepW:w5:t-est | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:t-est@L314-L320 |
| bpW:w5:data | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:data@L328-L348 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |


All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

All 24 reopened records explicitly inherit W5 standing data, directly or in their enclosing proof context. The target bpW:w5#data matches the weights paragraph L35-L39: a = p = 1, W4's weight guard, p >= 1/2, and wave weights at Dirichlet label J = j+2. These are the weights used in the symplectic form/norms, smoothing class, W4 adaptations, Taylor scaling and step data at the consumer spans below. A bare lambda in these records is the parameter norm weight; it is not a new use of frozen lam.

Each addition is a direct consumer-to-bpW:w5#data dependency with exactly one DEPS entry and matching EDGE, located at that consumer's own statement or proof step. This consistently extends the already-present package edges, including w4-general and g-pair, without reopening their existing mathematical content. The changed edge does not replace the independent suppliers for divisor, operator, pairing or Taylor estimates. No hypothesis or constant was changed by this delta.

Across the rendered, non-draft packets, the explicit package-invocation check found no missing direct dependency: literal package IDs in SOURCE_HYPOTHESES and the W3/W5/W7/W8 standing-data phrases all have their named package in DEPS. All 149 new package edges have the correct target, one DEPS entry, a matching EDGE, valid source ranges and exactly the consumer STATEMENT_SOURCE as locator. Their counts are 81 W3-data, 24 W5-data, 15 W7-data, 28 W7-basic-data and 1 W8-data. All 121 G1 EDGE proposals are retained verbatim in the rendered packets. This limited consistency check does not reopen unrelated REVIEWED records or infer new packages from symbols.

## Replacement fragments

None: every in-scope record PASSes.

## Suspected blueprint errata

None newly suspected in this delta. The W7 owner-slice attribution discrepancy above, where applicable, is in the task description, not the mathematical blueprint. Existing pinned-paper errata/source-gap repairs were not independently re-audited. No source deviation is introduced.

## Checks and limits

`sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK. `sha256sum -c docs/graph/W/IMPORTS.sha256`: exit 0; p1-analysis.tex OK.

```text
python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w5a
W-w5a: 53 nodes, 206 edges, 77 coverage items, 0 problems
```

Slice checker: exit 0.

```text
python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable
```

Assembled graph checker: exit 0, no output. These mechanical results validate structure, not mathematical source fidelity, global acceptance or proof completion. The packets remain PROPOSED pending writer application of the verdicts. G2's separate upstream amendment review is outside this task.

Only the seven requested review reports were written. No packets, databases, blueprint sources, frozen files or manifest were edited. No implementation Lean was read; no Lean, Lake, build, axiom probe, source lint or state-changing git command was run.

Final report validation: the seven reports have exactly the 150 requested PROPOSED node verdicts and one PROPOSED coverage verdict, with no duplicate or out-of-scope verdict row; all PASS. No FAIL replacement blocks are required. Review formatting checks passed. SHA-256 comparison of 234 protected packet/source/database/frozen/manifest files found no changes during report writing.
