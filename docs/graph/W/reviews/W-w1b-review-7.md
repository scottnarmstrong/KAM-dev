# W-w1b: independent delta 9 source review

Reviewer: `sol-delta9-W-W-w1b` (codex-1).

Verdict: **PASS**.

Scope: 1 PROPOSED nodes and 0 PROPOSED coverage items, limited to G1's package edges, the same-rule writer extension, and G3's adaptation/provenance correction as applicable to this slice. Governed by AGENTS.md, PLAN, DECISIONS, SPEC through “2026-10-31, global review 1”, REVIEW-BRIEF rules 1-11 (especially rule 9), and GLOBAL-review findings G1/G3. REVIEWED records were consulted only as touched dependency/consumer context. This is delta acceptance of source topology, not a fresh audit of unchanged fields or Lean proof closure. The reviewer tag is distinct from every earlier tag.

## Node verdicts

| Node | Verdict | Source spans re-read |
| --- | --- | --- |
| stepW:w1:hacoef | PASS | blueprint-W/parts/w1-sequences.tex#stepW:w1:hacoef@L829-L835 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |


All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

`stepW:w1:hacoef` PASSes G3. W1 L813-L822 permits an arbitrary complex Banach target F; L829-L835 explicitly transfers the Cauchy coefficient argument to complete F. The record owns that adaptation and keeps K's han-cauchy through han-bounds argument solely in NOTE. Its only dependencies are hamargin (r_1 and M_1, L826-L828), ext-onevar (complete-target Cauchy, L89-L98), and ext-integral (complete-target Bochner integration and dominated convergence, L103-L108). Each EDGE is at the corresponding consumer line, L831, L833, L835. K's theorem is neither a dependency nor a hidden finite-dimensional hypothesis. K p1 L24-L32 and L296-L350 were read to distinguish the finite-dimensional theorem from its transferable argument. No mathematical SOURCE_GAP is introduced by this classification.

The three remaining K edges were checked at their actual W uses, without reopening their REVIEWED records. At W1 L1000-L1031, fsum applies Fourier uniqueness to the scalar map h_e = <e,u-v>: it is continuous, periodic and has zero Fourier coefficients; the zero coefficient family is absolutely summable, supplying K fourier-basic(b)'s summability premise. Holomorphy on T_{s'} and vanishing on real points supply strip-identity. The positive smaller strip and n >= 1 come from the enclosing Fourier lemma. The target is C even when the original Hilbert space is infinite-dimensional. At L1038-L1064, fbdual supplies phi o u : T_s -> C, holomorphic, periodic and bounded by M, and commutes phi with the coefficient integral; fbdecay applies K decay for 0 <= s' < s, then takes s' up to s and the dual norm bound. Here too the target C satisfies K's finite-dimensional premise. K statements: p1 L531-L534, L757-L768, L786-L789, with conventions L24-L47. No Banach-target K theorem application remains. The older shift record uses W's own fourier-shift, not a K import.

Across the rendered, non-draft packets, the explicit package-invocation check found no missing direct dependency: literal package IDs in SOURCE_HYPOTHESES and the W3/W5/W7/W8 standing-data phrases all have their named package in DEPS. All 149 new package edges have the correct target, one DEPS entry, a matching EDGE, valid source ranges and exactly the consumer STATEMENT_SOURCE as locator. Their counts are 81 W3-data, 24 W5-data, 15 W7-data, 28 W7-basic-data and 1 W8-data. All 121 G1 EDGE proposals are retained verbatim in the rendered packets. This limited consistency check does not reopen unrelated REVIEWED records or infer new packages from symbols.

## Replacement fragments

None: every in-scope record PASSes.

## Suspected blueprint errata

None newly suspected in this delta. The W7 owner-slice attribution discrepancy above, where applicable, is in the task description, not the mathematical blueprint. Existing pinned-paper errata/source-gap repairs were not independently re-audited. No source deviation is introduced.

## Checks and limits

`sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK. `sha256sum -c docs/graph/W/IMPORTS.sha256`: exit 0; p1-analysis.tex OK.

```text
python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w1b
W-w1b: 67 nodes, 175 edges, 96 coverage items, 0 problems
```

Slice checker: exit 0.

```text
python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable
```

Assembled graph checker: exit 0, no output. These mechanical results validate structure, not mathematical source fidelity, global acceptance or proof completion. The packets remain PROPOSED pending writer application of the verdicts. G2's separate upstream amendment review is outside this task.

Only the seven requested review reports were written. No packets, databases, blueprint sources, frozen files or manifest were edited. No implementation Lean was read; no Lean, Lake, build, axiom probe, source lint or state-changing git command was run.

Final report validation: the seven reports have exactly the 150 requested PROPOSED node verdicts and one PROPOSED coverage verdict, with no duplicate or out-of-scope verdict row; all PASS. No FAIL replacement blocks are required. Review formatting checks passed. SHA-256 comparison of 234 protected packet/source/database/frozen/manifest files found no changes during report writing.
