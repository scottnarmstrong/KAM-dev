# Handoff LP-GRAPH-W2: LP source dependency graph, waves 2 and 3 (streamlined under D65)

2026-11-01, branch `inp-lp-graph` (worktree `/root/code/KAM-inp-lp-graph`), writer and extractor tag `kam-lp`.
Docs only: every change is under `docs/graph/LP/` plus this file. Nothing under `KAM/` or `manifest/` was edited.
Lean bodies were not read: only frozen declaration files were read (imports, docstrings, statements up to `:=`).
No Lean or Lake run. No agents were spawned.

**Scope change mid-package (owner ruling D65, relayed by the orchestrator at about 14:30 UTC).**
- No per-slice reviews and no delta reviews, so **no R2 review packets were written**.
- Waves 2, 3 (and 4 if available) were extracted in one pass.
- LEAN_STATUS is set mechanically from LEAN_REFs that resolve on main.
- The gate is the structural lint without `--require-reviewed`, and the header is labelled.
- The package stops at the assembled, linted graph with LEAN_STATUS applied. The orchestrator then launches ONE
  global review (codex-2).

## R1 consistency check (D65 item 1)

- `inp_depgraph_slice_check.py` gives 0 problems for each of LP-ext, LP-amend, LP-m78, LP-adef-pl, LP-athm, LP-m1,
  LP-m2a and LP-m2b, as found after commits 93bdb95a and c991a513.
- The LP-amend FAIL for `lpA:N2` was already applied:
  - `lpM:L6` and `lpM:L6#shared-U` in `LP-m2b.nodes.md` carry the shared 4r_g tube, r ≤ r_g and Ω_B(4r_g) ≤ δ/16 in
    their four source fields;
  - `lpA:N2`'s REASON is the review's replacement.
  - No further change was needed.

## Files

| File | Content |
|---|---|
| `specs/LP-m3.py`, `LP-m4a.py`, `LP-m4b.py`, `LP-m5.py`, `LP-m6.py` | MAIN Lemmas 7–19 (hand-written compact specs) |
| `specs/LP-imports.py` | `N:bpN:p11:nonresonant` (source fields copied from `docs/graph/N/DEPGRAPH.md`) |
| `specs/LP-ext-w2.py` | the five remaining externals of the closed list |
| `specs/LP-athm-w2.py`, `LP-athm-w3.py` | LP1, LP1-H, the 4 planar osculating characterizations; LP2, LP2-H, the 20 spatial characterizations |
| `specs/LP-adef-pl-w2.py`, `LP-adef-sp.py`, `_lp_anchor_util.py` | 7 reused definitions (wave 2); 53 spatial definitions + `IsHamiltonianSolutionOn`, bound mechanically |
| `specs/LP-m1-w2.py`, `LP-amend-w2.py` | the 13 formerly deferred coverage items |
| `packets/*.{nodes,coverage}.md` (the slices above; skeletons `*.draft-*.md`) | rendered packets |
| `packets/slices-assembled.txt`, `packets/slices.json` | assembly order (21 packets); counts and status |
| `header.txt`, `DEPGRAPH.md`, `DEPGRAPH_COVERAGE.md` | assembled waves 1–3, dashboard current |
| `LEAN_STATUS.md`, `tools/lp_depgraph_lean_sync.py` | mechanical LEAN_STATUS (applied) and its tool |
| `tools/lp_depgraph_fill.py`, `tools/lp_depgraph_header.py` | complete locators for imports, SOURCES for excluded anchor items; the D65 header label and the unconsumed-anchor filter |
| `reports/W2-dryrun.txt`, `reports/W2-lint.txt` | dry run and final lint |
| `SPEC.md` (change log), `README.md` | the record of this package |

Wave-1 packets edited, as writer under D65:
- `LP-adef-pl.{nodes,coverage}.md`: two unconsumed anchors removed and their items EXCLUDED (see "Modelling
  decisions");
- LEAN fields of the anchor packets, set by the sync.

## Approach and modelling decisions

1. **Packets.** The wave additions to the reviewed wave-1 slices are separate packets: `LP-athm-w2`, `-w3`,
   `LP-adef-pl-w2`, `LP-ext-w2`, `LP-m1-w2` and `LP-amend-w2`.
   - The `*.deferred-coverage.md` files are superseded and not assembled.
   - After the LEAN_STATUS apply, the packets (not the specs) are the source of truth. Re-rendering a spec would reset
     the Lean fields, so re-run the sync after any re-render.
2. **Routes (N7).**
   - `lpM:L14#route-L12` (Lemma 12: r = √μ, improvement r/4) and `lpM:L14#route-L13` (Lemma 13, the Lean route:
     r = D_0√μ, improvement r/2, N6) are owned by `lpM:L14#improvement`, the step that consumes the drift (L487/L500).
   - Lemma 14 is d-generic and conditional on the chart and domain premises.
   - `lpM:T15#apply-L14` (Lemmas 7–8, m = n) and `lpM:T19#apply-L14` (Lemmas 17–18, m = 2n) discharge those premises.
   - The L8-type premise of Lemmas 12–13 is Lemma 14's hypothesis.
3. **Headline anchors.**
   - LP1 → `lpM:T15`, `#reconstruction`, `#osculating`, `lpM:L16#mu0-choice` (N10), three osculating
     characterizations, and its 31 statement symbols.
   - LP1-H → LP1 + `lpM:s1:half-integer`. LP2 and LP2-H follow the same pattern.
   - A_elem is the constant A of (43); MAIN's §1 constant list omits it.
4. **Q5 applied.** (35), its proof region and `lpA:N4` are EXCLUDED.
   - The second restriction of (36) only serves (35); this is noted on `lpM:L12#kappa-choice`.
   - The Cauchy bounds on DΦ (L379) are EXCLUDED as unconsumed.
5. **Wave-3 binding is mechanical (D65), in `_lp_anchor_util.py`.**
   - A definition's DEPS, and a theorem's statement-symbol edges, are the bound frozen definitions that its file
     both imports and names in its declaration.
   - The conclusion is the declaration's docstring.
   - Locators come from the binding source range, with four overrides.
   - The source steps of the 22 theorem anchors were chosen by hand.
6. **Unconsumed anchors.** `sourceOscVelocity`, `sourceOscParam` (wave 1) and `spatialSourceOscVelocity` (wave 3)
   occur in no root statement and no source proof.
   - They are not graph nodes. Their items are EXCLUDED as "outside every root closure", and the header tool drops
     them from FROZEN_ANCHORS (145 of the 148 bound anchors remain).
   - `lpM:L3` (the Q3 conjunction) is consumed whole by `lpM:L18#alignment`.
   - `lpM:L9` is cited by name from Lemmas 12 and 13.
   - `lpM:L11#induction` now uses `lpM:L9#projections-tail` (the mean projection).
7. **Imports.** Only `N:bpN:p11:nonresonant` is imported, for Lemma 13.
   - The `nnf_disp_radius` remark at L464 is treated as a check, not a premise.
   - `N:bpN:p0:partial` and the P imports serve LP3 only. IMPORTS.sha256 is unchanged.
8. **LP3 (wave 4) is pending.** At 14:37 UTC main's manifest still has 307 entries and no D64 anchor. LP3-a and
   LP3-b are marked pending in `slices.json`.

## Counts

- 292 nodes (145 anchors, 11 externals: 10 from the closed list and 1 import), 1040 edges, 39 roots.
- Every node lies in a root closure.
- 31 dependency leaves, 2 routes.
- 4 SOURCE_GAP steps:
  - `lpM:L3#deficit-zero-L` (wave 1);
  - `lpM:L10#lie-flow-identification` and `lpM:L10#flow-existence` (N5, route L12 only);
  - `lpM:L14#maximal-solution` (the unique maximal solution and the agreement with every local solution, on top of
    Lemma 6's local existence; §1 L78).
- 394 coverage items (40 excluded).
- Topology status: 72 REVIEWED (from R1); 220 PROPOSED, waiting for the one global review.

| Packet | Nodes | Coverage | | Packet | Nodes | Coverage |
|---|---|---|---|---|---|---|
| LP-m3 | 16 | 27 | | LP-athm-w2 | 6 | 6 |
| LP-m4a | 20 | 35 | | LP-adef-pl-w2 | 7 | 7 |
| LP-m4b | 12 | 21 | | LP-m1-w2 / LP-amend-w2 | 0 | 6 / 7 |
| LP-m5 | 26 | 32 | | LP-adef-sp | 53 | 54 |
| LP-imports | 1 | 1 | | LP-m6 | 17 | 23 |
| LP-ext-w2 | 5 | 0 | | LP-athm-w3 | 22 | 22 |

## Checks and output

- **`inp_depgraph_slice_check.py`, all 21 packets:**
  - before the LEAN_STATUS apply: 0 problems each;
  - after it: the only reported problems are "Lean fields must be initial" on the 145 anchors, which is expected
    under D65 (`reports/W2-lint.txt`).
- **Skill linter.** `proof_depgraph.py --db docs/graph/LP/DEPGRAPH.md --manifest docs/graph/LP/DEPGRAPH_COVERAGE.md
  --source-root . --require-complete-coverage --require-all-reachable`:
  - with `--write-dashboard`: rc 0;
  - with `--check`: rc 0;
  - before the apply, also with `--require-initial-lean-status`: rc 0.
  - The frozen bindings are checked against the manifest hash in the header.
- **LEAN_STATUS.** `lp_depgraph_lean_sync.py --apply --force` gives PROVED 145, EXTERNAL 11, NOT_STARTED 136.
  - PROVED only where all three hold on main: the frozen file declares the export, the manifest state is SEALED, and
    for a theorem the provider module file exists.
  - The ordinary nodes keep NOT_STARTED. No LEAN_REF is inferred for them; they are BYPASS candidates for the
    orchestrator.
- **Docs-only diff.** `git diff --name-only 3ee7b448..HEAD` lists only `docs/graph/LP/`, this handoff and the
  orchestrator's own `docs/tracks/LP/packages/LP-GRAPH-R1APPLY.md`.
- **`scripts/lint_sources.sh`:** exit 0 (`check_lean_modules: PASS (4231 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (305 frozen declarations of KAM; checked by file hash only)`).
- **Build and axioms.** No Lean module was written, so there is no build and no `#print axioms`.

## Uncertainties (for the global review)

1. **Route ownership** at `lpM:L14#improvement` rather than at `lpM:L14`.
   - `lpM:L14#choices` uses the route's radius r and threshold μ_1. This is recorded as local data, not as an edge.
2. **The gap step `lpM:L14#maximal-solution`.** It also supplies §1 L78's "initial pair collisions are excluded"
   through Lemma 5 with m = δ.
3. **Lemma 13 uses Lemma 9's contour estimate** (`lpM:L13#numeric-hypotheses` → `lpM:L9`). The pre-freeze inventory
   had placed L9 on route L12 only.
4. **Mechanical wave-3 bindings** (imports named in the declaration) may miss a use through a local notation, or keep
   a name used only in a comment inside the declaration. The wave-3 definition records were not hand-checked.
5. **The wave-1 coverage reasons** of `lpA:N2` and `lpA:N8` say that their Lemma 8, Lemma 14 and T15 targets "join in
   wave 2".
   - Those nodes now exist (`lpM:L8#shared-tube`, `lpM:L14#choices`, `lpM:T15#orientation`), but the items'
     dispositions were not extended.
   - Coverage is complete either way.
6. **Unconsumed frozen carrier definitions.** Excluding them, rather than keeping orphan anchors, is a modelling
   choice for D65's reachability rule.

## Suspected errata and deviations

- **No new source defect found** in MAIN L190–L603 or AMENDMENTS.
  - Q5/N4 holds: the second κ condition of (36) serves only (35).
- **Deviation:** the three unconsumed frozen definitions are left out of the graph (decision 6).
- **Deviation:** the review gate is replaced by D65's single global review. Per-slice R2/R3 batches were not run.

## Final step D: global review incorporated, landing scope (2026-11-01)

Steps A, B and C (the mechanical LEAN_REF map, the d-generic pair rule and D27 BYPASS, and wave 4 for LP3 after D64)
are recorded in `docs/graph/LP/reports/lean-ref-map.txt` and the SPEC change log.

The ONE global review is `maud-lp-gglob-1`, in `docs/graph/LP/reviews/GLOBAL-review-1.md`, audited at ef3c63d0.
- Verdict: PASS WITH NOTES. It confirms the D27 BYPASS of all 136 nodes.

**Changes made in this step:**
1. **The 11 exact evidence-record refinements** (report lines 161–189) were applied to the packets as EDGE locator
   replacements only. Each target edge was matched exactly once. No DEPS, ROUTES, status or identity field changed.
   - LP1: 4 edges.
   - LP2-H: 1 edge.
   - LP3-1: 2 edges.
   - LP3-2: 2 edges.
   - `lpM:L2#spatialSourceKeplerApo_ge_length` and `lpM:L2#spatialSourceKeplerPeri_le_length`: 1 edge each.
2. **Header.**
   - `GLOBAL_REVIEWER: maud-lp-gglob-1`.
   - `GLOBAL_REVIEW_REF: docs/graph/LP/reviews/GLOBAL-review-1.md`.
   - The D65 label now names the review.
   - TOPOLOGY_STATUS stays PROPOSED outside the 72 R1-reviewed wave-1 records. W's REVIEWED markers came from its
     slice reviews, which D65 replaces by this global review; the structural gate runs without `--require-reviewed`.
3. **Checks.**
   - Re-assembled. `proof_depgraph.py --require-complete-coverage --require-all-reachable` gives rc 0 with
     `--write-dashboard` and rc 0 with `--check`.
   - LEAN_STATUS sync check: `lp_depgraph_lean_sync.py --apply`, now without `--force` because GLOBAL_REVIEWER is set,
     gives PROVED 153, BYPASSED 136, EXTERNAL 12, 0 blocked. It changed no packet byte.
4. **Retained SOURCE_GAP steps,** as the review asks:
   - `lpM:L3#deficit-zero-L`;
   - `lpM:L10#flow-existence`;
   - `lpM:L10#lie-flow-identification`;
   - `lpM:L14#maximal-solution`.
5. **Documentation notes.** The reviewer's notes on the historical SPEC and LEAN_STATUS setup paragraphs, and on
   `reports/W2-lint.txt` as a wave-2/3 snapshot, are clarity notes. The final records are current.

**Final graph:**
- 301 nodes, 1161 edges, 41 roots, 149 anchors.
- 12 externals: 10 on the closed list and 2 imports from track N.
- 2 routes, 4 SOURCE_GAP steps.
- 438 coverage items, 47 of them excluded.
- LEAN_STATUS: PROVED 153, BYPASSED 136, EXTERNAL 12, NOT_STARTED 0.

**Landing scope.** `git diff --name-only inp...HEAD` lists only `docs/graph/LP/` (the graph, its packets, specs,
tools, reports and reviews, including `reviews/GLOBAL-review-1.md`) and `docs/tracks/LP/`:
- `docs/tracks/LP/audits/LP-GRAPH-W1-handoff.md`;
- `docs/tracks/LP/audits/LP-GRAPH-W2-handoff.md`;
- `docs/tracks/LP/packages/LP-GRAPH-R1APPLY.md`;
- `docs/tracks/LP/packages/LP-GRAPH-W2.md`.

Nothing outside these two directories is touched: no `KAM/`, no `manifest/`, no generated roots. The exact list is
in the commit that adds this section (`git diff --name-only inp...HEAD`).
