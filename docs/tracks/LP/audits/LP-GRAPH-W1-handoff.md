# Handoff LP-GRAPH-W1: LP source dependency graph, post-freeze setup and wave 1 (the LP0 closure)

2026-11-01, branch `inp-lp-graph` (worktree `/root/code/KAM-inp-lp-graph`, off inp with the D62 freeze f46b94fb),
writer and extractor tag `kam-lp`. Docs only: every change is under `docs/graph/LP/` plus this file; nothing under
`KAM/` or `manifest/` was edited, no Lean body was read, no Lean or Lake was run (the `lp_lean.sh` wrapper was not
needed). Stopped at the review gate: **nothing is marked REVIEWED** and no self-review was done.

## Files

| File | Content |
|---|---|
| `docs/graph/LP/packets/anchor-map.tsv` | README step 2: the 128 D62 manifest entries (identity fields) |
| `docs/graph/LP/packets/anchor-binding.tsv`, `tools/lp_depgraph_bind.py` | the binding of 148 anchors (128 D62 entries + 20 reused definitions) to node, slice, wave |
| `docs/graph/LP/tools/lp_depgraph_preextract.py` | Q7: Markdown pre-extractor (draft inventory + binding → skeleton slice packets) |
| `docs/graph/LP/tools/lp_depgraph_fill.py`, `specs/*.py` | the writer's compact specs and their renderer |
| `docs/graph/LP/tools/lp_depgraph_header.py`, `header.txt` | header for the waves assembled (wave 1) |
| `docs/graph/LP/packets/<slice>.{nodes,coverage}.md` | the 8 wave-1 packets (source of truth); `*.draft-*.md` skeletons; `LP-m1`/`LP-amend` `.deferred-coverage.md` |
| `docs/graph/LP/DEPGRAPH.md`, `DEPGRAPH_COVERAGE.md` | assembled wave-1 database and coverage manifest, dashboard current |
| `docs/graph/LP/SPEC.md` | §1, §5, §7, §8, §9, §10 settled; change log |
| `docs/graph/LP/LEAN_STATUS-W1.md`, `tools/lp_depgraph_lean_sync.py` | wave-1 LEAN_STATUS against the sealed anchors and its sync command |
| `docs/graph/LP/REVIEW-BRIEF.md`, `reviews/R1-packets.md` | review packets for batch R1 (8 slices, codex-2) |
| `docs/graph/LP/reports/W1-dryrun.txt`, `W1-lint.txt` | dry run and lint outputs |
| `docs/graph/LP/README.md`, `packets/slices.json` | post-freeze status; waves and wave-1 counts |

Commits: 831beafd (anchor map, binding), 56ad9d41 (tools, specs, packets, assembly), 0e521a5e (SPEC), f3d9f45e
(LEAN_STATUS), 98bccfca (review packets, README), and the handoff commit.

## Setup decisions

1. **Pins** re-checked (`sha256sum -c docs/graph/LP/CORPUS.sha256 docs/graph/LP/IMPORTS.sha256`): all six OK, no
   re-pin. `manifest/frozen-anchors.json` equals main's (sha256 `cee8ce34…5cded8`).
2. **Anchor map:** 128 entries (89 definitions, 39 theorems), reconciled with FREEZE.md (the pre-freeze SPEC said
   "88 definitions": the frozen count is 89).
3. **Q1–Q8 recorded as ruled (root-b8, all defaults):** Q1 LP3 source note first (LP3 stays out); Q2 the 34
   characterizations are anchors and roots; Q3/Q4 splits applied in wave 1, Q5 recorded for wave 2; Q6 reused
   definitions bound as LP anchors (exactly the 20 imported directly by LP frozen files: 12 wave 1, 7 wave 2, 1 wave 3);
   Q7 tools written; Q8 writer `kam-lp`, reviews on codex-2 in parallel batches.
4. **Anchor node IDs** are uniformly `<owner>#<LeanName>`, theorem anchors included. **Deviation from the pre-freeze
   proposal:** LP0 is `lpM:L5#planar_strongAMD_barrier`, a separate anchor over the ordinary d-generic node `lpM:L5`
   (MAIN's Lemma 5 is stated for d ∈ {2,3} and is consumed by Lemmas 6 and 16 in both dimensions; the spatial chain
   must not depend on a planar declaration). LP1/LP2 follow the same pattern in waves 2–3.
5. **Dimension rule (SPEC §5):** MAIN nodes are d-generic and depend on the d-generic definition nodes
   `lpM:s1:{data,model,elements}`; dimension-specific frozen definitions attach at the anchors whose statements use
   them. The symbol rule applies to the dimension-free frozen objects (𝒬, a_i(I), D, feasible set, objective, B_ij,
   B_cross, B). Result: LP0's closure contains the planar carriers only, and, through Q3, does not reach Lemma 1.
6. **Q3:** `lpM:L3` = `lpM:L3#static` ∧ `lpM:L3#dynamic` ∧ `lpM:L3#planar-orientation`; Lemma 5 consumes only the
   static part. **Q4:** `lpM:L4`'s fields omit the L143 contact/Laskar–Petit and L147 sharpness clauses; new items
   `lpM:L4#stmt-contact-lp`, `lpM:L4#stmt-sharpness` EXCLUDED. **(10)** became the display node `lpM:L1#velocity`.
7. **Waves:** coverage items whose targets are later-wave nodes are held in `<slice>.deferred-coverage.md` (13:
   six §1 conclusion items → T15/T19 anchors; N1, N3–N7, N10). `--require-all-reachable` joins the gate when the
   served roots exist (W precedent); wave 1 keeps 37 nodes that serve LP1/LP2.
8. **Extraction mode:** the brief makes this agent the extractor under the writer, so the W low-cost precedent
   (option B, writer-tag extraction from compact specs) was used; every record has `EXTRACTOR: kam-lp`.

## Wave-1 counts

| Slice | Nodes | Edges | Coverage | Deferred |
|---|---|---|---|---|
| LP-adef-pl | 48 (36 D62 definitions + 12 reused) | 103 | 48 | – |
| LP-athm | 11 (LP0 + 10 characterizations) | 65 | 11 | – |
| LP-ext | 5 externals | 0 | 0 (items in MAIN slices) | – |
| LP-m1 | 6 | 8 | 19 | 6 |
| LP-m2a | 24 | 77 | 36 | – |
| LP-m2b | 15 | 64 | 20 | – |
| LP-amend | 0 | 0 | 7 | 7 |
| LP-m78 | 0 | 0 | 12 | – |
| **total** | **109** (59 anchors, 5 externals, 0 assumptions) | **317** | **153** (26 excluded) | 13 |

Roots 11, root closure 72 nodes, dependency leaves in the closure 11, external leaves 2 in the closure (5 in all),
**route nodes 0** (the only alternatives in MAIN, L12/L13, are wave 2), explicit SOURCE_GAP 1
(`lpM:L3#deficit-zero-L`), review queue 109.

## Linter output (`docs/graph/LP/reports/W1-lint.txt`)

- `inp_depgraph_slice_check.py` on each of the 8 slices: 0 problems each.
- `proof_depgraph.py --db docs/graph/LP/DEPGRAPH.md --manifest docs/graph/LP/DEPGRAPH_COVERAGE.md --source-root .
  --require-complete-coverage --require-initial-lean-status --write-dashboard` then `--check`: **exit 0** (also with
  the repository copy `scripts/proof_depgraph.py`). The frozen bindings are checked against the manifest (sha256 in the
  header).
- With `--require-all-reachable`: exit 1, exactly the 37 nodes that serve the wave-2/3 roots (expected; SPEC §7).
- `--require-reviewed` is not run: nothing is reviewed yet (gate).
- `scripts/lint_sources.sh`: exit 0 (see "Checks").

## LEAN_STATUS of wave 1 (`docs/graph/LP/LEAN_STATUS-W1.md`)

Against the sealed anchors on main (all 128 D62 entries SEALED): 59 anchor nodes PROVED (LEAN_REF `<export>
(<frozen file>)`; LEAN_NOTE "sealed frozen definition (manifest SEALED); formalized, nothing to prove" or "sealed
frozen theorem (manifest SEALED, D62); proof by exact <provider>"), 5 EXTERNAL, 45 ordinary nodes left NOT_STARTED
(their status needs a Lean reference that a source-level sync must not infer; after the seal they are D27 BYPASS
candidates or get PROVED from LP audits, the orchestrator's decision). 64/109 resolved in the HQ sense. **Not applied
to the packets** (the review and publish gates require the initial Lean fields). Sync command, right after
publication:
```
python3 -I docs/graph/LP/tools/lp_depgraph_lean_sync.py --apply
```
then re-assemble and lint (commands in LEAN_STATUS-W1.md). The apply path was tested on a scratch assembly (lint
exit 0, 59 PROVED) and reverted.

## Review packets (the gate)

`docs/graph/LP/REVIEW-BRIEF.md` (refute-first brief from the W template with LP's rules) and
`docs/graph/LP/reviews/R1-packets.md` (eight packets: LP-adef-pl, LP-athm, LP-ext, LP-m1, LP-m2a, LP-m2b, LP-amend,
LP-m78; tags `sol-review-LP-<slice>`; codex-2, one fresh session each, in a parallel batch; the apply/mark commands
for the writer afterwards). Reviewers are asked for one row per coverage item, so `inp_depgraph_mark_reviewed.py`
marks them without the W "rest" tool.

## Checks

- Docs-only diff: `git diff --name-only f571532c..HEAD` lists only `docs/graph/LP/` (and this file).
- `scripts/lint_sources.sh`: exit 0 (`check_lean_modules: PASS (4231 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (305 frozen declarations of KAM; checked by file hash only, ...)`).
- No Lean module was written, so there is no build and no `#print axioms`.

## Open issues and uncertainties

1. **SOURCE_GAP `lpM:L3#deficit-zero-L`.** The frozen characterization
   `sum_action_mul_eccDeficit_le_sourceStrongAMD` states Σ Λ_i D(e_i) ≤ C on every source canonical phase; MAIN proves
   the inequality of (13) only on orbits with C < B_⋆ (via H_i, which needs L ≠ 0). The step `lpM:L3#deficit` records
   the argument as valid whenever L ≠ 0 (what the proof uses); the L = 0 case is the gap (immediate: C = Σ I_i and
   D ≤ 1 on [0,1]). For the reviewers to confirm.
2. **LP0's distance clauses.** LP0 asserts ¦q_i¦ ≥ d_⋆ and ¦q_i − q_j¦ ≥ d_pair; MAIN's Lemma 5 statement does not,
   its proof does (L175, also §1 L91). Modelled as LP0 → `lpM:L5#pair-distances`. Reviewers should confirm.
3. **L4 characterizations without a positive-mass premise.** Lemma 4 says "for all positive masses"; the frozen
   `orderedPairThreshold_isLeast` etc. rest on the chamber carrier only (which forces 0 ≤ a_i(I) < a_j(I)). Noted in
   the anchor NOTE; not a defect.
4. **`orderedCrossThreshold_isLeast` proof locus.** Attainment of the finite minimum over the adjacent pairs is not
   spelled out in MAIN (L55 points to Lemma 4; L156 "finite minima preserve continuity and positivity"); recorded with
   proof locator L156 and an edge to `lpM:s1:data` (n ≥ 2 makes the family nonempty), not as a gap (elementary).
5. **N2's shared U** is recorded at Lemma 6 in wave 1; its requirements (4r_g tube, r ≤ r_g) are consumed by Lemmas 8
   and 14 (wave 2), where the deferred parts of `lpA:N2` join.
6. **HQ:** `scripts/hq-status.py` has no `LP` key in `ANCHOR_PREFIX` (LP's manifest IDs share the `planetary.` prefix
   with track P), and `graph_sync_lag` is not on this branch; the progress meter for LP needs an orchestrator change
   (not docs/graph, out of scope).
7. **Wave 2 inherits:** the Q5 split of (35); the 13 deferred items; the 7 wave-2 reused definitions; LP1/LP1-H
   anchors and the 4 osculating characterizations; the five wave-2 externals; LP-imports (N/P imports).

## Suspected errata and deviations

- **No defect found in MAIN.md or AMENDMENTS.md lines 1–189, 604–679.** (L1's inverse map checked: ẋ_i = ẋ_0 + q̇_i
  = p_i/ν_i with (10); L4's B = min(B_cross, I_1) follows from B_{i,i+1} < I_{i+1}.)
- **Deviation 1 (frozen surface vs source, for the ledger as a deviation, not a source erratum):** the deficit
  characterization covers L = 0 (item 1 above); bridged by a SOURCE_GAP step.
- **Deviation 2 (graph modelling vs the pre-freeze SPEC proposal):** LP0's node is `lpM:L5#planar_strongAMD_barrier`,
  not `lpM:L5` (setup decision 4).
- **Deviation 3 (pre-freeze count):** the SPEC's "88 new definitions" was the draft-7 estimate; the frozen count is 89.
