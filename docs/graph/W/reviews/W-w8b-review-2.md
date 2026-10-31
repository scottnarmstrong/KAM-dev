# W-w8b: delta 6 independent source review

Reviewer: `sol-delta6-W-W-w8b` (codex-1).
Verdict: **FAIL**.

Scope: 15 PROPOSED nodes and 0 PROPOSED coverage items in this slice. REVIEWED records were read only as dependency context. This report evaluates the current pinned corpus, not concurrent repairs. No packet, corpus, frozen file, manifest, or Lean implementation was edited or interpreted.

The SPEC wave-2 extraction and wave-2 review-1/delta-5 rulings and REVIEW-BRIEF rules 1-11 govern this review. Re-read source statements, proof contexts, consumer use sites and the cross-part prerequisite statements. No gap was made an assumption; ordinary Lean fields remain initialized.

## Node verdicts

| Node | Verdict | Source spans re-read or failure reason |
| --- | --- | --- |
| stepW:w8:ni-same | FAIL | The shell-frequency comparison uses 2 pi nu(I) = omega_*^(n)(I) and its primed version from patch-local (proof preamble L507). These are derived facts, not implication premises; add their direct supplier. |
| stepW:w8:ni-diff | FAIL | The shell-frequency comparison uses 2 pi nu(I) = omega_*^(n)(I) and its primed version from patch-local (proof preamble L507). These are derived facts, not implication premises; add their direct supplier. |
| stepW:w8:in-orbit | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-orbit@L524-L527 |
| stepW:w8:in-birk | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-birk@L528-L530 |
| stepW:w8:in-freq | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-freq@L531-L534 |
| stepW:w8:in-act | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-act@L535-L535 |
| stepW:w8:in-ang | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:in-ang@L536-L537 |
| bpW:w8:nlw2-proof | PASS | blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L547-L551; blueprint-W/parts/w8-assembly.tex#bpW:w8:nlw2-proof@L552-L599 |
| stepW:w8:p-meas | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-meas@L560-L560 |
| stepW:w8:p-incl | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-incl@L561-L562 |
| stepW:w8:p-nucont | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-nucont@L563-L563 |
| stepW:w8:p-Kcont | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-Kcont@L564-L565 |
| stepW:w8:p-dioph | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-dioph@L575-L578 |
| stepW:w8:p-lim | FAIL | The use at L581 is explicitly freq-shell(iii), which already supplies epsilon_omega^(n) <= alpha_n; the separate etor edge is merely transitive through freq-shell. Remove that edge and retain the direct shell bound and shells limit. |
| stepW:w8:p-size | PASS | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-size@L589-L590 |

## Coverage verdicts

| Item | Verdict | Source spans re-read |
| --- | --- | --- |

No PROPOSED coverage items in this slice.

All other coverage items PASS within the delta scope; previously REVIEWED items are not re-certified.

## Replacement fragments

### stepW:w8:ni-same (owner: W-w8b)

The shell-frequency comparison uses 2 pi nu(I) = omega_*^(n)(I) and its primed version from patch-local (proof preamble L507). These are derived facts, not implication premises; add their direct supplier.

```text
NODE: stepW:w8:ni-same
KIND: step
TITLE: Same shell
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508
CONTRACT_ID: stepW:w8:ni-same
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nu-injective: the patched family; the enclosing implication premise nu(I) = nu(I'); local choices I in Gamma_n, I' in Gamma_{n'}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nu-injective (I, I' in Gamma); within the step: n = n'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: I = I'
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:freq-shell, bpW:w8:patch-local
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-same@L508-L508 | (ii)
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L507-L508 | the proof preamble identifies the patched frequencies with the two shell frequencies used in this case
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b+sol-delta6-W-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

### stepW:w8:ni-diff (owner: W-w8b)

The shell-frequency comparison uses 2 pi nu(I) = omega_*^(n)(I) and its primed version from patch-local (proof preamble L507). These are derived facts, not implication premises; add their direct supplier.

```text
NODE: stepW:w8:ni-diff
KIND: step
TITLE: Different shells
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L509-L513
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L509-L513
CONTRACT_ID: stepW:w8:ni-diff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nu-injective: the patched family; the enclosing implication premise nu(I) = nu(I'); local choices I in Gamma_n, I' in Gamma_{n'}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nu-injective (I, I' in Gamma); within the step: n != n'; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: omega^(n)_*(I) != omega^(n')_*(I')
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w8:shell-data, bpW:w7:freqcoords, bpW:w8:freq-shell, bpW:w8:patch-local
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w8:shell-data | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L510-L510 | (ii) separation
EDGE: bpW:w7:freqcoords | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L510-L510 | (iv)
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:ni-diff@L511-L511 | (iii)
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#bpW:w8:nu-injective@L507-L513 | the proof preamble identifies the patched frequencies with the two shell frequencies used in this case
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b+sol-delta6-W-W-w8b
REVIEWER: -
LEAN_STATUS: NOT_STARTED
LEAN_REF: -
LEAN_NOTE: -
NOTE: -
```

### stepW:w8:p-lim (owner: W-w8b)

The use at L581 is explicitly freq-shell(iii), which already supplies epsilon_omega^(n) <= alpha_n; the separate etor edge is merely transitive through freq-shell. Remove that edge and retain the direct shell bound and shells limit.

```text
NODE: stepW:w8:p-lim
KIND: step
TITLE: Clause (2), frequency limit
STATEMENT_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L582
PROOF_SOURCE: blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L582
CONTRACT_ID: stepW:w8:p-lim
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w8:nlw2-proof: m > 0 (the standing assumption bpW:w0:mass)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w8:nlw2-proof (for every m > 0); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: clause (2): Tendsto nu (nhdsWithin 0 Gamma) (nhds fun i => lam m hm (i : Nat).succPNat / (2 * pi))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w7:limit, bpW:w8:patch-local, bpW:w8:freq-shell, bpW:w0:basis#lam, bpW:w8:shells
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w7:limit | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L579-L579 | frequency limit
EDGE: bpW:w8:patch-local | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L580-L580 | omega_* = omega^(n)_* on Gamma_n
EDGE: bpW:w8:freq-shell | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L581-L581 | (iii) e_n <= alpha_n
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L582-L582 | lam m hm (i : Nat).succPNat occurs directly
EDGE: bpW:w8:shells | blueprint-W/parts/w8-assembly.tex#stepW:w8:p-lim@L581-L581 | alpha_n = (2^{-n} t_0)^{95/64} tends to zero
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: claude-suborch-W+sol-review-W-w8b+sol-delta6-W-W-w8b
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
- `python3 -I scripts/depgraph_slice_check.py docs/graph/W/packets W-w8b`: exit 0; `W-w8b: 46 nodes, 199 edges, 61 coverage items, 0 problems`.
- `python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable`: exit 0, no output. This checks the existing graph; the proposed report replacements have not been applied.
- Report validation: all 133 requested node rows and 68 coverage rows occur exactly once across the ten reports; the 15 FAIL rows have 15 complete replacement blocks with all fields, valid locators and matching DEPS/EDGE targets. An in-memory overlay of these replacements is acyclic and retains all 693 packet nodes in the root closure, including alternative routes. Packets were not modified.
- Final corpus recheck: all eleven hashes still OK. Review whitespace check passed.
- No Lean, lake, build, proof-body, axiom, or state-changing git checks: this is the explicitly requested source-only review.

Uncertainty: the named SOURCE_GAP obligations remain unpaid in this corpus; structural validation cannot resolve them. No mathematical repair or source deviation is introduced by this report.

READY sol-delta6-W-W-w8b
