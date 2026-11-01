# W-w6: delta 6 independent source review

Reviewer: `sol-delta6-W-W-w6` (codex-1).
Verdict: **FAIL**.

Scope: 16 PROPOSED nodes and 14 PROPOSED coverage items in this slice. REVIEWED records were read only as dependency context. This report evaluates the current pinned corpus, not concurrent repairs. No packet, corpus, frozen file, manifest, or Lean implementation was edited or interpreted.

The SPEC wave-2 extraction and wave-2 review-1/delta-5 rulings and REVIEW-BRIEF rules 1-11 govern this review. Re-read source statements, proof contexts, consumer use sites and the cross-part prerequisite statements. No gap was made an assumption; ordinary Lean fields remain initialized.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| stepW:w6:il-small | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-small@L69-L71 |
| stepW:w6:c-cauchy | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cauchy@L151-L153 |
| stepW:w6:c-cont | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cont@L158-L160 |
| bpW:w6:prep-step | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L220-L245; blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L246-L267 |
| stepW:w6:p-div | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L250-L252 |
| stepW:w6:p-lipp | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L258-L259 |
| stepW:w6:p-gap | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L264-L266 |
| bpW:w6:applicable | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L284-L286; blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L287-L293 |
| bpW:w6:freq-lip | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L296-L304; blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L305-L314 |
| stepW:w6:fl-borel | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L313-L313 |
| bpW:w6:exclusion | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L318-L321; blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L322-L326 |
| stepW:w6:t-hol | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L363-L365 |
| stepW:w6:t-cont | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L366-L367 |
| stepW:w6:t-an | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-an@L374-L376 |
| bpW:w6:to-w8 | FAIL | L395-L398 explicitly invokes applicability for every allowed starting size, but DEPS omits bpW:w6:applicable. Add the direct supplier without changing the starting-size interval. |
| bpW:w6#data | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6@L22-L27 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |
| stepW:w6:il-small | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:il-small@L69-L71 |
| stepW:w6:c-cauchy | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cauchy@L151-L153 |
| stepW:w6:c-cont | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:c-cont@L158-L160 |
| bpW:w6:prep-step | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:prep-step@L220-L245 |
| stepW:w6:p-div | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-div@L250-L252 |
| stepW:w6:p-lipp | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-lipp@L258-L259 |
| stepW:w6:p-gap | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:p-gap@L264-L266 |
| bpW:w6:applicable | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:applicable@L284-L286 |
| bpW:w6:freq-lip | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:freq-lip@L296-L304 |
| stepW:w6:fl-borel | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:fl-borel@L313-L313 |
| bpW:w6:exclusion | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:exclusion@L318-L321 |
| stepW:w6:t-hol | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-hol@L363-L365 |
| stepW:w6:t-cont | PASS | blueprint-W/parts/w6-iteration.tex#stepW:w6:t-cont@L366-L367 |
| bpW:w6:to-w8 | PASS | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L383-L413 |

All other coverage items PASS within the delta scope; previously REVIEWED items are not re-certified.

## Replacement fragments

### bpW:w6:to-w8 (owner: W-w6)

L395-L398 explicitly invokes applicability for every allowed starting size, but DEPS omits bpW:w6:applicable. Add the direct supplier without changing the starting-size interval.

```text
NODE: bpW:w6:to-w8
KIND: claim
TITLE: What W8 consumes from W6
STATEMENT_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L383-L413
PROOF_SOURCE: blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L383-L413
CONTRACT_ID: bpW:w6:to-w8
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: for each shell, W8's choices r, t, rho_xi, Pi, alpha subject to Proposition bpW:w5:initial, eps_in(1 + 4 lambda/rho_xi) <= gamma alpha with lambda = alpha/M, c_A(t + r^2) < rho_1^2, Pi subset {¦xi¦_infty <= 1/2} Borel, alpha <= alpha_0
SOURCE_QUANTIFIERS: for every value of the parameter eps_0 in [eps^flat_0, gamma_1 check alpha]
SOURCE_CONCLUSION: (a)-(c) of Theorem bpW:w6:tori and Lemmas bpW:w6:exclusion, bpW:w6:final-freq hold for every eps_0 in [eps^flat_0, gamma_1 check alpha]; with eps_0 = eps^flat_0: eps^flat_0/check alpha = 2 C^natural_2 sigma_P^{-t^natural/3}(eps/alpha)^{4/3}, M_{F,P} = c^natural_F sigma_P^{1-t^natural} alpha^{3/47} eps/alpha and the displayed bound on e_tor; Theorem bpW:w6:tori(i),(iii) on R^2 is the hypothesis of Corollary bpW:w3:transport-tori-weak
CONSTANT_SCOPE: as displayed
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w6:tori, bpW:w6:exclusion, bpW:w6:final-freq, bpW:w6:prep-step, bpW:w3:transport-tori-weak, bpW:w0:periodone#linearTorus, bpW:w6:wave-iteration, bpW:w6:freq-lip, bpW:w7:measure, bpW:w7:shell-est, bpW:w7:dioph, bpW:w7:limit, bpW:w1:coordinatewise, bpW:w6:applicable
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w6:tori | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L391-L391 | (i)-(v)
EDGE: bpW:w6:exclusion | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L387-L387 | (a)
EDGE: bpW:w6:final-freq | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L390-L390 | (b)
EDGE: bpW:w6:prep-step | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L398-L398 | (v)
EDGE: bpW:w3:transport-tori-weak | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L405-L405 | the return to Cartesian coordinates
EDGE: bpW:w0:periodone#linearTorus | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L393-L393 | the linear torus K^0_I occurs directly here (frozen linearTorus)
EDGE: bpW:w6:wave-iteration | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L396-L396 | the starting size epsilon_0 remains a free parameter of the wave iteration
EDGE: bpW:w6:freq-lip | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L388-L388 | the admissible family required for applying W7 measure and shell estimates
EDGE: bpW:w7:measure | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L387-L387 | the measure result applied to the admissible family
EDGE: bpW:w7:shell-est | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L388-L388 | the shell estimate applied to the same admissible family
EDGE: bpW:w7:dioph | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L390-L390 | conversion of the final frequency bound to the stated Diophantine property
EDGE: bpW:w7:limit | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L390-L390 | the limiting-frequency properties cited in the retained interface claim
EDGE: bpW:w1:coordinatewise | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L407-L407 | conversion of the Cartesian coefficient equations to clause (4)
EDGE: bpW:w6:applicable | blueprint-W/parts/w6-iteration.tex#bpW:w6:to-w8@L395-L398 | the applicability result is explicitly used for every epsilon_0 in the stated interval
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-W-w6+sol-delta6-W-W-w6
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: Remark kept as a node: its starting-size computation (e_tor bound) and the return-trip statement are facts W8 may consume; its 'what W8 must still supply' list is administrative.
```

## Source-gap disposition

The following records faithfully expose the pinned source obligations and do not add them to SOURCE_HYPOTHESES: `bpW:w6:prep-step`, `stepW:w6:p-lipp`, `bpW:w6:freq-lip`, `stepW:w6:fl-borel`. All retain `LEAN_NOTE: -`. A topology PASS does not certify their mathematics. The schurrep replacement, if present, changes only a defining dependency.

## Suspected blueprint defects

- `blueprint-W/parts/w6-iteration.tex:233; blueprint-W/parts/w7-measure.tex:585-586`: "Corollary bpW:w7:melnikov(i); In the setting of Theorem bpW:w7:measure". The cited corollary carries an admissible-family premise before that family has been supplied. The local p-div argument is retained separately; no new premise is authorized.
- `blueprint-W/parts/w6-iteration.tex:258-259; blueprint-W/parts/w5-kamstep.tex:563-564`: "(iii) is Theorem bpW:w5:step(v) (sup part)". The cited bound is 2 M_F, while prep-step(iii) claims M_F. The sharper f-flow estimate is not invoked here; p-lipp keeps the missing factor-two justification visible.
- `blueprint-W/parts/w6-iteration.tex:301-303`: "all <= alpha". Read literally this includes theta, although the proof only gives theta <= theta_0. The intended reference to the three epsilons needs clarification; freq-lip preserves the ambiguity.
- `blueprint-W/parts/w6-iteration.tex:313; blueprint-W/parts/w7-measure.tex:339,550-553`: "Pi minus Xi is Borel (Lemma bpW:w7:measurable)". The cited lemma is in an admissible-family setting while admissibility is being established. An independent preparatory measurability fragment has not been separated; fl-borel exposes this scope gap.

These observations concern the blueprint as pinned here. No claim is made that parallel source repairs have landed.

## Checks

- `sha256sum -c docs/graph/W/CORPUS.sha256`: exit 0; all eleven files OK.
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w6`: exit 0; `W-w6: 47 nodes, 169 edges, 70 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This checks the existing graph; the proposed report replacements have not been applied.
- Report validation: all 133 requested node rows and 68 coverage rows occur exactly once across the ten reports; the 15 FAIL rows have 15 complete replacement blocks with all fields, valid locators and matching DEPS/EDGE targets. An in-memory overlay of these replacements is acyclic and retains all 693 packet nodes in the root closure, including alternative routes. Packets were not modified.
- Final corpus recheck: all eleven hashes still OK. Review whitespace check passed.
- No Lean, lake, build, proof-body, axiom, or state-changing git checks: this is the explicitly requested source-only review.

Uncertainty: the named SOURCE_GAP obligations remain unpaid in this corpus; structural validation cannot resolve them. No mathematical repair or source deviation is introduced by this report.

READY sol-delta6-W-W-w6
