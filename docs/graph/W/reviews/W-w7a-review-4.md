# W-w7a: independent delta 9 source review

Reviewer: `sol-delta9-W-W-w7a` (codex-1).

Verdict: **PASS**.

Scope: 28 PROPOSED nodes and 0 PROPOSED coverage items, limited to G1's package edges, the same-rule writer extension, and G3's adaptation/provenance correction as applicable to this slice. Governed by AGENTS.md, PLAN, DECISIONS, SPEC through “2026-10-31, global review 1”, REVIEW-BRIEF rules 1-11 (especially rule 9), and GLOBAL-review findings G1/G3. REVIEWED records were consulted only as touched dependency/consumer context. This is delta acceptance of source topology, not a fresh audit of unchanged fields or Lean proof closure. The reviewer tag is distinct from every earlier tag.

## Node verdicts

| Node | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w7:omega0 | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:omega0@L127-L131 |
| bpW:w7:freqcoords | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:freqcoords@L135-L150 |
| stepW:w7:inverse | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:inverse@L152-L157 |
| stepW:w7:norms | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:norms@L158-L162 |
| stepW:w7:Omegazeta | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:Omegazeta@L163-L165 |
| stepW:w7:measure-affine | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:measure-affine@L166-L167 |
| bpW:w7:unpert-bounds | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:unpert-bounds@L172-L181 |
| stepW:w7:ssize | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:ssize@L183-L185 |
| stepW:w7:plus | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:plus@L186-L189 |
| stepW:w7:minus | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:minus@L190-L194 |
| stepW:w7:kappa | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:kappa@L195-L200 |
| stepW:w7:liplOmega | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:liplOmega@L201-L203 |
| bpW:w7:constdef | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L211-L231 |
| stepW:w7:sep-drift | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-drift@L350-L352 |
| stepW:w7:sep-concl | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:sep-concl@L353-L355 |
| stepW:w7:largek-tan | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-tan@L365-L367 |
| stepW:w7:largek-cmp | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:largek-cmp@L368-L370 |
| stepW:w7:zone-lower | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-lower@L382-L386 |
| stepW:w7:zone-slab | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-slab@L387-L389 |
| stepW:w7:zone-psi | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:zone-psi@L390-L393 |
| bpW:w7:Xdef | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:Xdef@L398-L401 |
| stepW:w7:Xfinite | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:Xfinite@L408-L410 |
| stepW:w7:dich-large | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-large@L411-L413 |
| stepW:w7:dich-small | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:dich-small@L414-L416 |
| stepW:w7:X-A3 | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:X-A3@L431-L435 |
| stepW:w7:X-const | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:X-const@L436-L438 |
| stepW:w7:X-slope | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:X-slope@L439-L443 |
| bpW:w7:constdef#base | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:constdef@L214-L217 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |


All other coverage items PASS within the requested delta scope; previously REVIEWED items are not re-certified.

## Source and dependency findings

The actual owner distribution is 28 reopened records here: 15 G1 additions to bpW:w7#data and 13 writer-extension additions to bpW:w7:basic#data. The other 15 writer-extension records belong to W-w7b. Thus the prompt's attribution of the 15 G1 records to W-w7b and all 28 extension records to W-w7a is reversed at the ownership level; the total requested 150 nodes is correct. Verdicts follow the rendered packets and actual source spans.

For the 15 G1 records, SOURCE_HYPOTHESES expressly inherits W7 standing data, including constdef#base's shorter “W7 standing data”. The target opening L33-L41 fixes positive mass, corrected A/B, lambda, max norms, Lebesgue measure, integer l1 norm and mode conventions. Unperturbed frequencies, inverse/norm/affine calculations, separation/asymptotics, constants and X use that scope at the listed consumer sites.

For the 13 extension steps, SOURCE_HYPOTHESES expressly names the fixed data of L339-L343 and bpW:w7:basic#data. That paragraph fixes Pi, alpha, an admissible family, rho/rho_zeta, the unperturbed or iterated frequency pair on a Borel domain, and phi_kl in zeta coordinates. The separation, large-k, zone and exceptional-set proof steps are in this scope. Each new edge goes to the named package, exactly once, and its locator is the consumer's own step. Existing REVIEWED enclosing lemmas already have their package dependencies; they are context, not newly certified records. The same rule is applied to theorem-level and step-level invocation even where a transitive path already exists.

Across the rendered, non-draft packets, the explicit package-invocation check found no missing direct dependency: literal package IDs in SOURCE_HYPOTHESES and the W3/W5/W7/W8 standing-data phrases all have their named package in DEPS. All 149 new package edges have the correct target, one DEPS entry, a matching EDGE, valid source ranges and exactly the consumer STATEMENT_SOURCE as locator. Their counts are 81 W3-data, 24 W5-data, 15 W7-data, 28 W7-basic-data and 1 W8-data. All 121 G1 EDGE proposals are retained verbatim in the rendered packets. This limited consistency check does not reopen unrelated REVIEWED records or infer new packages from symbols.

## Replacement fragments

None: every in-scope record PASSes.

## Suspected blueprint errata

None newly suspected in this delta. The W7 owner-slice attribution discrepancy above, where applicable, is in the task description, not the mathematical blueprint. Existing pinned-paper errata/source-gap repairs were not independently re-audited. No source deviation is introduced.

## Checks and limits

`sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK. `sha256sum -c docs/graph/W/IMPORTS.sha256`: exit 0; p1-analysis.tex OK.

```text
python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w7a
W-w7a: 51 nodes, 182 edges, 79 coverage items, 0 problems
```

Slice checker: exit 0.

```text
python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable
```

Assembled graph checker: exit 0, no output. These mechanical results validate structure, not mathematical source fidelity, global acceptance or proof completion. The packets remain PROPOSED pending writer application of the verdicts. G2's separate upstream amendment review is outside this task.

Only the seven requested review reports were written. No packets, databases, blueprint sources, frozen files or manifest were edited. No implementation Lean was read; no Lean, Lake, build, axiom probe, source lint or state-changing git command was run.

Final report validation: the seven reports have exactly the 150 requested PROPOSED node verdicts and one PROPOSED coverage verdict, with no duplicate or out-of-scope verdict row; all PASS. No FAIL replacement blocks are required. Review formatting checks passed. SHA-256 comparison of 234 protected packet/source/database/frozen/manifest files found no changes during report writing.
