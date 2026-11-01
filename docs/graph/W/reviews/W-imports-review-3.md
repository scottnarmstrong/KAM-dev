# W-imports: independent delta 9 source review

Reviewer: `sol-delta9-W-W-imports` (codex-1).

Verdict: **PASS**.

Scope: 0 PROPOSED nodes and 1 PROPOSED coverage items, limited to G1's package edges, the same-rule writer extension, and G3's adaptation/provenance correction as applicable to this slice. Governed by AGENTS.md, PLAN, DECISIONS, SPEC through “2026-10-31, global review 1”, REVIEW-BRIEF rules 1-11 (especially rule 9), and GLOBAL-review findings G1/G3. REVIEWED records were consulted only as touched dependency/consumer context. This is delta acceptance of source topology, not a fresh audit of unchanged fields or Lean proof closure. The reviewer tag is distinct from every earlier tag.

## Node verdicts

| Node | Verdict | Source spans re-read |
| --- | --- | --- |


No PROPOSED node record in this slice; the three remaining REVIEWED imports are contextual inputs only.

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |
| K:bp:p1:holomorphic-analytic | PASS | blueprint/parts/p1-analysis.tex#bp:p1:holomorphic-analytic@L296-L312; blueprint-W/parts/w1-sequences.tex L813-L835 |

All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

The sole reopened coverage item K:bp:p1:holomorphic-analytic PASSes as EXCLUDED proof provenance. K p1 L24-L32 and L296-L312 has a finite-dimensional target W; W1 L813-L835 instead states the complete Banach-target result and identifies the Cauchy/integration argument that transfers. The hacoef NOTE retains that provenance, its K import edge is absent, the imported node is absent from the rendered packet, and no other W node depends on that K theorem. Deletion leaves three actual imports, with no artificial unused external.

The actual remaining applications were checked, rather than inferring applicability from their imported fields. W1 fsum L1026-L1031 uses K fourier-basic(b) and strip-identity on h_e = <e,u-v> : T_{s'} -> C. It is continuous and periodic, with all coefficients zero (hence a summable coefficient family); it is holomorphic on a positive smaller strip and vanishes on real points. W1 fbdual L1057-L1060 makes phi o u scalar, holomorphic, periodic and bounded by M, and identifies its coefficients; fbdecay L1061-L1064 applies K decay for 0 <= s' < s and passes to s. Both targets are C, finite-dimensional over C, and n >= 1 is supplied by their enclosing W lemmas. K p1 conventions L24-L47 and statements L531-L534, L757-L768, L786-L789 were read, and all three IDs were found in docs/graph/K/DEPGRAPH.md. W's shift uses its local fourier-shift argument and has no K edge.

The three imported node records remain REVIEWED and out of scope for recertification. In particular this PASS does not adjudicate G2 or approve the pending K-owner amendments; it certifies the G3 exclusion and the requested scalar-consumer premise check only.

Across the rendered, non-draft packets, the explicit package-invocation check found no missing direct dependency: literal package IDs in SOURCE_HYPOTHESES and the W3/W5/W7/W8 standing-data phrases all have their named package in DEPS. All 149 new package edges have the correct target, one DEPS entry, a matching EDGE, valid source ranges and exactly the consumer STATEMENT_SOURCE as locator. Their counts are 81 W3-data, 24 W5-data, 15 W7-data, 28 W7-basic-data and 1 W8-data. All 121 G1 EDGE proposals are retained verbatim in the rendered packets. This limited consistency check does not reopen unrelated REVIEWED records or infer new packages from symbols.

## Replacement fragments

None: every in-scope record PASSes.

## Suspected blueprint errata

None newly suspected in this delta. The W7 owner-slice attribution discrepancy above, where applicable, is in the task description, not the mathematical blueprint. Existing pinned-paper errata/source-gap repairs were not independently re-audited. No source deviation is introduced.

## Checks and limits

`sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK. `sha256sum -c docs/graph/W/IMPORTS.sha256`: exit 0; p1-analysis.tex OK.

```text
python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-imports
W-imports: 3 nodes, 0 edges, 4 coverage items, 0 problems
```

Slice checker: exit 0.

```text
python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable
```

Assembled graph checker: exit 0, no output. These mechanical results validate structure, not mathematical source fidelity, global acceptance or proof completion. The packets remain PROPOSED pending writer application of the verdicts. G2's separate upstream amendment review is outside this task.

Only the seven requested review reports were written. No packets, databases, blueprint sources, frozen files or manifest were edited. No implementation Lean was read; no Lean, Lake, build, axiom probe, source lint or state-changing git command was run.

Final report validation: the seven reports have exactly the 150 requested PROPOSED node verdicts and one PROPOSED coverage verdict, with no duplicate or out-of-scope verdict row; all PASS. No FAIL replacement blocks are required. Review formatting checks passed. SHA-256 comparison of 234 protected packet/source/database/frozen/manifest files found no changes during report writing.
