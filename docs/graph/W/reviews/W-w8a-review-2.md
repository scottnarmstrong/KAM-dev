# W-w8a: delta 6 independent source review

Reviewer: `sol-delta6-W-W-w8a` (codex-1).
Verdict: **FAIL**.

Scope: 15 PROPOSED nodes and 0 PROPOSED coverage items in this slice. REVIEWED records were read only as dependency context. This report evaluates the current pinned corpus, not concurrent repairs. No packet, corpus, frozen file, manifest, or Lean implementation was edited or interpreted.

The SPEC wave-2 extraction and wave-2 review-1/delta-5 rulings and REVIEW-BRIEF rules 1-11 govern this review. Re-read source statements, proof contexts, consumer use sites and the cross-part prerequisite statements. No gap was made an assumption; ordinary Lean fields remain initialized.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| stepW:w8:sd-prep | FAIL | The Borel-domain premise at L168 consumes sd-trim directly. Also the to-w8 EDGE at L146 lies in the parent statement; relocate it to the checking step L168-L171, which concludes (iv). |
| stepW:w8:g-app | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:g-app@L219-L221 |
| stepW:w8:e-tor | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-tor@L236-L239 |
| stepW:w8:e-om | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:e-om@L240-L243 |
| stepW:w8:ts-real | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-real@L294-L299 |
| stepW:w8:ts-per | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:ts-per@L300-L302 |
| stepW:w8:se-an | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-an@L329-L330 |
| stepW:w8:se-inj | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-inj@L331-L337 |
| stepW:w8:se-der | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:se-der@L338-L349 |
| stepW:w8:sc-gamma | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-gamma@L370-L372 |
| stepW:w8:sc-close | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-close@L373-L375 |
| stepW:w8:sc-size | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:sc-size@L376-L377 |
| stepW:w8:si-frozen | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-frozen@L400-L403 |
| stepW:w8:si-cont | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:si-cont@L404-L406 |
| bpW:w8#data | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8@L36-L53 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |

No PROPOSED coverage items in this slice.

All other coverage items PASS within the delta scope; previously REVIEWED items are not re-certified.

## Replacement fragments

### stepW:w8:sd-prep (owner: W-w8a)

The Borel-domain premise at L168 consumes sd-trim directly. Also the to-w8 EDGE at L146 lies in the parent statement; relocate it to the checking step L168-L171, which concludes (iv).

```text
NODE: stepW:w8:sd-prep
KIND: step
TITLE: Lemma~\ref{bpW:w6:prep-step}
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L171
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L171
CONTRACT_ID: stepW:w8:sd-prep
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:shell-data: Definitions bpW:w8:const and bpW:w8:shells
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:shell-data (for every n >= 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:prep-step, bpW:w5:initial, stepW:w8:sd-init, bpW:w6:to-w8, stepW:w8:sd-size, stepW:w8:sd-trim
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:prep-step | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L168 | its hypotheses
EDGE: bpW:w5:initial | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L170-L170 | P real periodic in S_{p+1}
EDGE: stepW:w8:sd-init | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L171-L171 | (iii)
EDGE: bpW:w6:to-w8 | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L171 | the checks conclude clause (iv), including the conditions of the W6 interface remark
EDGE: stepW:w8:sd-size | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L171-L171 | (i) supplies eps^sharp_n <= gamma alpha_n
EDGE: stepW:w8:sd-trim | blueprint-W/parts/w8-assembly.tex#stepW:w8:sd-prep@L168-L168 | the trimmed shell is Borel and lies in the required half-unit box
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8a+sol-delta6-W-W-w8a
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

## Suspected blueprint defects

No additional suspected blueprint defect found in the reviewed records.

These observations concern the blueprint as pinned here. No claim is made that parallel source repairs have landed.

## Checks

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w8a`: exit 0; `W-w8a: 56 nodes, 207 edges, 79 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This checks the existing graph; the proposed report replacements have not been applied.
- Report validation: all 133 requested node rows and 68 coverage rows occur exactly once across the ten reports; the 15 FAIL rows have 15 complete replacement blocks with all fields, valid locators and matching DEPS/EDGE targets. An in-memory overlay of these replacements is acyclic and retains all 693 packet nodes in the root closure, including alternative routes. Packets were not modified.
- Final corpus recheck: all eleven hashes still OK. Review whitespace check passed.
- No Lean, lake, build, proof-body, axiom, or state-changing git checks: this is the explicitly requested source-only review.

Uncertainty: the named SOURCE_GAP obligations remain unpaid in this corpus; structural validation cannot resolve them. No mathematical repair or source deviation is introduced by this report.

READY sol-delta6-W-W-w8a
