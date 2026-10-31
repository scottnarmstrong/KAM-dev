# W-w7b: delta 6 independent source review

Reviewer: `sol-delta6-W-W-w7b` (codex-1).
Verdict: **PASS**.

Scope: 12 PROPOSED nodes and 0 PROPOSED coverage items in this slice. REVIEWED records were read only as dependency context. This report evaluates the current pinned corpus, not concurrent repairs. No packet, corpus, frozen file, manifest, or Lean implementation was edited or interpreted.

The SPEC wave-2 extraction and wave-2 review-1/delta-5 rulings and REVIEW-BRIEF rules 1-11 govern this review. Re-read source statements, proof contexts, consumer use sites and the cross-part prerequisite statements. No gap was made an assumption; ordinary Lean fields remain initialized.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| stepW:w7:prep-minus-group | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-minus-group@L474-L481 |
| stepW:w7:prep-sum | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:prep-sum@L500-L503 |
| stepW:w7:it-group | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-group@L521-L526 |
| stepW:w7:it-j0 | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-j0@L527-L532 |
| stepW:w7:it-sum | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-sum@L537-L540 |
| stepW:w7:it-X | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:it-X@L541-L543 |
| stepW:w7:meas-cont | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:meas-cont@L555-L557 |
| stepW:w7:layer | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:layer@L625-L629 |
| stepW:w7:upper | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:upper@L646-L647 |
| stepW:w7:lower | PASS | blueprint-W/parts/w7-measure.tex#stepW:w7:lower@L648-L653 |
| bpW:w7:exponents | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:exponents@L676-L691 |
| bpW:w7:dioph-use | PASS | blueprint-W/parts/w7-measure.tex#bpW:w7:dioph-use@L713-L718 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |

No PROPOSED coverage items in this slice.

All other coverage items PASS within the delta scope; previously REVIEWED items are not re-certified.

## Replacement fragments

None.

## Suspected blueprint defects

No additional suspected blueprint defect found in the reviewed records.

These observations concern the blueprint as pinned here. No claim is made that parallel source repairs have landed.

## Checks

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w7b`: exit 0; `W-w7b: 42 nodes, 125 edges, 63 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This checks the existing graph; the proposed report replacements have not been applied.
- Report validation: all 133 requested node rows and 68 coverage rows occur exactly once across the ten reports; the 15 FAIL rows have 15 complete replacement blocks with all fields, valid locators and matching DEPS/EDGE targets. An in-memory overlay of these replacements is acyclic and retains all 693 packet nodes in the root closure, including alternative routes. Packets were not modified.
- Final corpus recheck: all eleven hashes still OK. Review whitespace check passed.
- No Lean, lake, build, proof-body, axiom, or state-changing git checks: this is the explicitly requested source-only review.

Uncertainty: the named SOURCE_GAP obligations remain unpaid in this corpus; structural validation cannot resolve them. No mathematical repair or source deviation is introduced by this report.

READY sol-delta6-W-W-w7b
