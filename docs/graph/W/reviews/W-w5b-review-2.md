# W-w5b: delta 6 independent source review

Reviewer: `sol-delta6-W-W-w5b` (codex-1).
Verdict: **PASS**.

Scope: 11 PROPOSED nodes and 11 PROPOSED coverage items in this slice. REVIEWED records were read only as dependency context. This report evaluates the current pinned corpus, not concurrent repairs. No packet, corpus, frozen file, manifest, or Lean implementation was edited or interpreted.

The SPEC wave-2 extraction and wave-2 review-1/delta-5 rulings and REVIEW-BRIEF rules 1-11 govern this review. Re-read source statements, proof contexts, consumer use sites and the cross-part prerequisite statements. No gap was made an assumption; ordinary Lean fields remain initialized.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| bpW:w5:new-ham | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L457-L472; blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L473-L493 |
| stepW:w5:n-exp | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L474-L480 |
| bpW:w5:pullback | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L502-L506; blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L507-L522 |
| stepW:w5:p-inv | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L508-L513 |
| stepW:w5:p-ass | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L517-L521 |
| bpW:w5:step | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L543-L566; blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L567-L580 |
| stepW:w5:st-con | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L570 |
| stepW:w5:st-div | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L577-L579 |
| stepW:w5:a-hol | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L640-L643 |
| stepW:w5:a-field | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L655-L660 |
| bpW:w5:initial | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L673-L682; blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L683-L703 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |
| bpW:w5:new-ham | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:new-ham@L457-L472 |
| stepW:w5:n-exp | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:n-exp@L474-L480 |
| bpW:w5:pullback | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:pullback@L502-L506 |
| stepW:w5:p-inv | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-inv@L508-L513 |
| stepW:w5:p-ass | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:p-ass@L517-L521 |
| bpW:w5:step | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:step@L543-L566 |
| stepW:w5:st-con | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-con@L568-L570 |
| stepW:w5:st-div | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:st-div@L577-L579 |
| stepW:w5:a-hol | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-hol@L640-L643 |
| stepW:w5:a-field | PASS | blueprint-W/parts/w5-kamstep.tex#stepW:w5:a-field@L655-L660 |
| bpW:w5:initial | PASS | blueprint-W/parts/w5-kamstep.tex#bpW:w5:initial@L673-L682 |

All other coverage items PASS within the delta scope; previously REVIEWED items are not re-certified.

## Replacement fragments

None.

## Source-gap disposition

The following records faithfully expose the pinned source obligations and do not add them to SOURCE_HYPOTHESES: `stepW:w5:n-exp`, `stepW:w5:p-inv`, `stepW:w5:a-hol`. All retain `LEAN_NOTE: -`. A topology PASS does not certify their mathematics. The schurrep replacement, if present, changes only a defining dependency.

## Suspected blueprint defects

- `blueprint-W/parts/w5-kamstep.tex:477-478`: "exchanging the order of integration over 0 <= tau <= t <= 1". The stated box-Fubini external does not literally supply this triangle identity; n-exp keeps the bridge open.
- `blueprint-W/parts/w5-kamstep.tex:512-513`: "lambda |Delta(D phi^t)^(-1)| <= 2 . 1 . 2 = 4". The displayed parameter differences omit the parameter distance or its quotient; the asserted lambda-norm estimate requires it. p-inv retains the literal claim and flags the omission.
- `blueprint-W/parts/w5-kamstep.tex:640`: "sqrt is holomorphic on Re > 0". The principal complex square-root branch is invoked without a listed external or proof; a-hol preserves that obligation.

These observations concern the blueprint as pinned here. No claim is made that parallel source repairs have landed.

## Checks

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w5b`: exit 0; `W-w5b: 32 nodes, 119 edges, 48 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This checks the existing graph; the proposed report replacements have not been applied.
- Report validation: all 133 requested node rows and 68 coverage rows occur exactly once across the ten reports; the 15 FAIL rows have 15 complete replacement blocks with all fields, valid locators and matching DEPS/EDGE targets. An in-memory overlay of these replacements is acyclic and retains all 693 packet nodes in the root closure, including alternative routes. Packets were not modified.
- Final corpus recheck: all eleven hashes still OK. Review whitespace check passed.
- No Lean, lake, build, proof-body, axiom, or state-changing git checks: this is the explicitly requested source-only review.

Uncertainty: the named SOURCE_GAP obligations remain unpaid in this corpus; structural validation cannot resolve them. No mathematical repair or source deviation is introduced by this report.

READY sol-delta6-W-W-w5b
