# Handoff LP-FREEZE8-EXEC: draft 8 (LP3) frozen and sealed in one pass (D64)

Branch `inp-lp-freeze8x` (worktree `/root/code/KAM-inp-lp-freeze8x`), cut at the approval commit `6c168945`
(+ brief `bed0f8ef`). Procedure: FREEZE-PROPOSAL-DRAFT8 §6 with D62's scripts. Nothing pushed or landed.

## Commits

| Commit | Content |
|---|---|
| 4e48d05d | A: the 2 anchors installed sealed; manifest +2 SEALED (ABI zero placeholders); roots (+2 Frozen, +2 Provider); 2 MANIFEST-CHANGES rows (D64); `approval-D64.json`; `identity-check-d64.txt`; `lp_manifest_changes_rows_d64.py`; N3 docstring fix; FREEZE.md D64 section. `.drafts/READY-LP-FREEZE8-EDITS` touched here, before the build (14:26 UTC). |
| (this commit) | B: ABI hashes of the 2 entries; FREEZE.md checks; `abi-check-d64.txt`, `seal-probe-verify-d64.txt`, `replay-modules-d64.txt`, `replay-prelanding-d64.txt`; this handoff. |

## Files

- New frozen anchors (approved text + 2 placeholders + sealed body only):
  - `KAM/Frozen/Planetary/StrongAMD/Theorems/PlanarStrongAMDExponentialSafetyNoArith.lean` (149 lines):
    `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith`, body
    `by exact KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith hn ν hν hνmax hνle A hA hAord δ hδ`.
  - `KAM/Frozen/Planetary/Spatial/Theorems/SpatialStrongAMDExponentialSafetyNoArith.lean` (155 lines):
    `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith`, body
    `by exact KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith hn ν hν hνmax hνle A hA hAord δ hδ`.
  The full statements are the approved draft-8 texts (FREEZE-PROPOSAL-DRAFT8 §3), byte-identical modulo the above.
- Providers: unchanged staged files (sha256 956c7e76… planar, 34e337b7… spatial, as in `providers-staging-draft8.txt`),
  now in `KAM/Root/Provider.lean` via `gen_root_imports.py`.
- `manifest/frozen-anchors.json`: +2 entries `planetary.d59.{planar,spatial}_strongAMD_exponentialSafety_noArith.v1`,
  state SEALED, `author_approval`/`ruling_ref` from `approval-D64.json` (D59, D64); closures 79 and 96 files
  (cross-checked against the import closure); ABI b29ff03f… (planar), 387059c6… (spatial). 307 existing entries JSON-equal.
- `KAM/Root/Frozen.lean`, `KAM/Root/Provider.lean` (generated, +2 lines each); `docs/MANIFEST-CHANGES.md` (+2 rows);
  `docs/tracks/LP/FREEZE.md` (D64 section).
- N3: `KAM/Planetary/StrongAMD/Nek/PlanarSafety/Source.lean` lines 15 and 36, `LP:MAIN L15 (502–506)` → `LP:MAIN T15 (502–506)` (docstrings only).
- `docs/tracks/LP/freeze/`: `approval-D64.json`, `lp_manifest_changes_rows_d64.py`, `identity-check-d64.txt`,
  `abi-check-d64.txt`, `seal-probe-verify-d64.txt`, `replay-modules-d64.txt`, `replay-prelanding-d64.txt`.

## Checks (exact)

1. `lp_freeze_install.py --root . --approved 6c168945:docs/tracks/LP/freeze/draft8 --date 2026-11-01 --decision D64 --kind theorem --sealed`
   (dry run into a scratch tree first; real files `cmp`-identical to the dry run) → "installed 2 theorem files (sealed bodies)".
2. `lp_identity_check.py … --pin --show-diff` → 2 files checked, **ALL IDENTICAL**; the only diff lines are the
   placeholder line (`<APPROVAL-DATE>`→`2026-11-01`, `<DECISION>`→`D64`) and `by sorry` → the 2-line sealed body.
   Pins: 77c6bb5e… (planar .txt), ba6087a8… (spatial .txt), 9b8e3ffc… (manifest-entries.json).
3. `lp_manifest_add.py --approval approval-D64.json` → "2 LP entries (0 definitions, 2 theorems; state SEALED; ABI zero
   placeholders); 307 existing entries unchanged; manifest now 309"; then ABI twice (cmp identical) and `--abi` →
   "… ABI filled …". Independent JSON check: first 307 entries and all top-level keys equal to the pre-install manifest.
4. Build: `lp_build_fast.sh /root/code/KAM-inp-lp-freeze8x <21 Nek modules> <2 providers> <2 anchors> KAM.Root.Planetary KAM.Root.Provider KAM.Root.Frozen`
   → "Build completed successfully (11094 jobs)", rc 0 (14:26:55 UTC). Built: the 2 anchors, `PlanarSafety.Source`,
   the two roots; no warning in any new or changed file (the log's warnings are replayed pre-existing ones elsewhere).
5. `check_frozen_anchors.py` → FROZEN-ANCHOR GUARD OK. `abi_hashes.py . manifest/frozen-anchors.json --check` →
   ABI HASHES OK (307 frozen declarations of KAM; KAMLunarBand by file hash only). `gen_root_imports.py --check` exit 0.
6. `lp_lint.sh` → **exit 0**: check_lean_modules PASS (4235 Lean files); FROZEN-ANCHOR GUARD OK; ABI HASHES OK (307).
7. Probe (`lp_axioms.py --probe` on a manifest of the 2 D64 entries, `lp_lean.sh` rc 0, `--verify`) → ALL OK:
   `example : type_of% @X := @Pv` elaborates and the types are TYPE_EQV for both pairs.
8. `#print axioms`: all four of
   `KAM.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith`, `KAM.Provider.Planetary.StrongAMD.planar_strongAMD_exponentialSafety_noArith`,
   `KAM.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith`, `KAM.Provider.Planetary.Spatial.spatial_strongAMD_exponentialSafety_noArith`
   → exactly `[propext, Classical.choice, Quot.sound]`.
9. Kernel replay (leanchecker, 4 GB scope, 1 thread) of the 5 modules of `replay-modules-d64.txt` (Source, 2 providers,
   2 anchors): all rc 0, ~15 s each.

## AUDIT FOCUS

- The sealed bodies: explicit binder order `hn ν hν hνmax hνle A hA hAord δ hδ` (from `Guard.explicit_binders`), equal
  to the docstring sealing string (asserted by the installer).
- `replay-modules-d64.txt` lists 5 modules; the roots `KAM.Root.Frozen`/`KAM.Root.Provider` were rebuilt too but hold
  only imports (excluded, as in D62's list). The providers were not rebuilt by this build (already built at staging);
  they are listed because they enter the core library here.
- The spatial anchor's closure (96 files) and planar (79) as drafted; recomputed by `lp_manifest_add.py`.

## Deviations, errata, design signals

- New script `lp_manifest_changes_rows_d64.py` (D62's row script hard-codes D62's decision/evidence text, filters on
  `planetary.d59.` and refuses if any LP row exists, so it cannot add only the D64 rows). Same row format.
- ABI hashes filled after the build (they need built modules), so commit A carries zero ABI placeholders, as D62's commit B.
- The provider docstrings still say they are quarantined "while the frozen anchor is DRAFT_SORRY (or not yet created)";
  historical now (same note as D62).
- No suspected errata in MAIN. No frozen text changed beyond the two placeholders and the body.
- Hard rules: no heartbeat override; largest touched file 205 lines; no sorry/axiom/admit/unsafe.
