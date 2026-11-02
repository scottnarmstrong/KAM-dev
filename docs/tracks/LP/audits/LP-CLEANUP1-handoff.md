# LP-CLEANUP1 handoff (tier-1 clean-up and errata merge, D69)

Branch `lp-cleanup`. Commits: errata merge; tier-1 clean-up; spatial budget-lemma dedup; comment reflow.

## Part 2: errata (done)
- 29 entries of `docs/tracks/LP/errata-proposed.json` (8 errata, 21 deviations) appended to `docs/errata/ledger.json`
  unchanged (6 CANDIDATE stay CANDIDATE); no id collisions; insertions only.
- `LPMAIN` was already in `docs/sources.json` with the correct sha256 (68e9167f...48c1b); nothing to add.
- `scripts/render_errata.py` run; `working-record.md` regenerated; `--check` OK.

## Part 1: Lean (tier 1)
Net `KAM/` diff vs main: +544 / -1237 lines, 183 files (141 LP implementation, 41 providers, 1 touched constants file overlap).
| Category | Change |
|---|---|
| Stale comments | `FREEZE-PROPOSAL.md` sentence removed from all LP implementation and provider files; package labels (`Package LP-…`, `LP3-…`, `LP-SP-…`) replaced by "Source:" / role names; "draft" wording and audit-note refs rewritten; 10 `L15` -> `T15`. Provider edits are comments only (quarantine wording now "This module is quarantined"). About 130 lines re-wrapped to the 100-column limit. |
| Dead code | 96 of the 114 audited declarations deleted. Kept: 5 of the audit's transitive ("*") entries that are in fact used (`fSpatial_spatialPoincareProd_shift`, `mem_ball_shiftNM`, `spatialNekCell_slowGap_pos`, `exists_spatialNek_rpow_lt`, `nekCell_slowGap_pos`). The 13 `@[simp]`/`~` entries (implicit `simp` uses) are all kept (`lp_append_addNat`, `lpRescale_lpUnrescale`, `lpRescaleNM_lpUnrescaleNM`, `planarEmbed_smul/sub`, `reflectPhase_fst`, `reflectPlane_reflectPlane`, `reflectVec_zero`, `spaceDot_add_right`, `spaceSq_sub`, `spaceDot_cross_self_left/right`, `incRotation_e₃_two_pos`). (114 - 5 - 13 = 96.) No deleted name occurs in any graph LEAN_REF or `papers/LP`. |
| Duplicates | Cluster 1 done: `exists_spatialBudget_radius` removed, spatial `SpatialSafety/Constants.lean` imports planar `PlanarSafety.Constants`, `Aligned.lean` uses `exists_budget_radius`. |

## Not done (reported)
- Duplicate clusters 2–8 and retirement of `Spatial/SpatialSafety/Bridge.lean` (each needs re-pointing of definitions across modules; left for a
  follow-up, low value versus risk). Superseded helpers (Diophantine chain, Nek predicate unification): left alone as instructed.
- `Bridge.lean` therefore stays.

## Checks
- `lp_build_fast.sh` on all 141 LP modules, the 41 providers and the 41 LP frozen theorem anchors: `Build completed successfully (9635 jobs)`, rc 0.
- `#print axioms` of the 41 LP theorem anchors (`.drafts/ax.lean`, via `lp_lean.sh`): all 41 exactly `[propext, Classical.choice, Quot.sound]`.
- `lp_lint.sh`: width check, unit tests and the FROZEN-ANCHOR GUARD pass; the script still exits 1 on its ABI step, because the
  worktree's build has no `KAM.Frozen.Magnetic.*` oleans (`MagAlpha.olean does not exist`), an environment issue of the MAG merge, not LP.
- `proof_depgraph.py … --check` on `docs/graph/LP`: reports `FROZEN_MANIFEST sha256 does not match manifest/frozen-anchors.json`
  (DEPGRAPH.md:10). Identical on current `main` (manifest changed by the MAG freeze after the graph); no graph file touched, no LEAN_REF moved.
- Frozen files, `manifest/`, provider statements and the 15 headline names untouched.

## Uncertainties / errata
No new source errata. Deviations: none beyond the above.

## Follow-up (LP-CLEANUP1-FIX)
1. Built the 7 `KAM.Frozen.Magnetic.*` modules with `lp_build.sh` (frozen modules only; `Build completed successfully`, rc 0; the
   only warning is the intended `sorry` of the DRAFT_SORRY `MagneticBarrier` anchor). `lp_lint.sh` then exits 0; tail:
   `check_lean_modules: PASS (4483 Lean files, 0 comparator configurations)`, `Ran 25 tests ... OK`, `FROZEN-ANCHOR GUARD OK`,
   `ABI HASHES OK (314 frozen declarations of KAM; ...)`, `rc=0`. (This supersedes the lint caveat above.)
2. Graph re-pin: `docs/graph/LP/DEPGRAPH.md` line 10 `FROZEN_MANIFEST` sha256 changed from `e5186622...a48375` to the current
   `80b8a24a...c4308f6` (header tool not needed: only the hash differed; kind/path/export/abi_sha256 of all 128 anchor-map rows
   verified equal to the current manifest). SPEC change-log line added. `proof_depgraph.py --db docs/graph/LP/DEPGRAPH.md --manifest
   docs/graph/LP/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-all-reachable --check`: rc 0.
   Note: `header.txt` carries `sha256:auto`, so it needs no change; the hash is stamped at assembly.
