# SO-FREEZE3 audit request: identity audit of the SO freeze (Phase A texts)

Branch `inp-sofreeze3` (off `inp` 9517d71e). Full record: [`../FREEZE.md`](../FREEZE.md).

**Status.** Phase A is **incomplete**: the Q11 switch of the landed code to the frozen definitions is not done,
because it forces a kernel rebuild of all 1645 SO-DATA3 data modules (about 7.5 h, into the shared build overlay).
The brief requires a stop and an orchestrator decision first (FREEZE.md, "Q11 and the heavy rebuild"). The frozen
texts, provider stubs, manifest entries and ABI hashes are final unless the approval date changes (see item 5).
The **identity audit** does not depend on Q11, so it can run now. There is no `.drafts/READY-SO-FREEZE3-A` marker
yet, and no Phase B.

## What to audit (IDENTITY)

Each frozen declaration against FREEZE-PROPOSAL-2 §1 (definition texts: FREEZE-PROPOSAL §1.1–§1.8), with only
the D47/D49 literal substitutions, byte for byte:

1. The 13 files `KAM/Frozen/SpinOrbit/Defs/{SoEcc,SoEps,SoCoeffPoly,SoA,SoModes,SoV,SoField,SoBarrier,LunarPLo,LunarPHi}.lean`
   and `KAM/Frozen/SpinOrbit/Theorems/{LunarBarriers,LunarSpinConfinement,LunarWindow}.lean`.
2. The substitutions (FREEZE.md table): window `9934 / 10000`, `10066 / 10000` (with the interim comments dropped,
   as §1.2 says); band `SoBarrier (97245 / 100000) (102755 / 100000)` twice; bound `≤ 2755 / 100000`; docstrings
   `[0.97245, 1.02755]`, `2755/100000` (2.755 %). Nothing else in the declaration texts changes.
3. Added header lines: copyright, module docstring with the approval paragraph (and the sealing rule in theorem
   files), the `FROZEN_ANCHOR_*` markers. The B and window files use A's wrapper.
4. Deviations:
   - **D-SOF-5:** four one-space-to-newline docstring splits for the 100-column lint. All four lines were already
     too long in the approved text.
   - **D-SOF-6:** the DRAFT body is `by sorry` (guard rule) instead of §1.3's bare `sorry`.
   - **D-SOF-7:** one `source_group` per declaration (guard rule) instead of the shared `spinorbit.lunar`.
5. The approval date 2026-10-31: `docs/DECISIONS.md` on `main` records D47 (2026-10-31, 07:00 UTC, band literal)
   and D49 (2026-10-31, 07:10 UTC, freeze approvals). This closes audit 1 F1.
6. The manifest: 13 new entries, the other 158 unchanged. Theorem closures: B = model + window (no `SoBarrier`),
   A = B's + `SoBarrier`, window = `LunarPLo`, `LunarPHi`. Theorems DRAFT_SORRY, definitions SEALED.
   Implementation `KAM.Provider.SpinOrbit.<Stem>` / `KAM.Provider.SpinOrbit.<name>`.
7. The provider stubs `KAM/Provider/SpinOrbit/*.lean` (empty, quarantined).

Tools: `python3 docs/tracks/SO/freeze/check_identity.py` (prints `ALL IDENTICAL`); `docs/tracks/SO/freeze/gen_frozen.py`
regenerates the files from the snippets; `freeze/cfg.json`, `freeze/freeze.json` are the manifest-tool inputs.

## Metadata change after audit 1 (for the identity auditor): decision references only

On `main` the two 2026-10-31 decisions were renumbered (b17bf0c0) because the first one clashed with the D46 of
2026-10-30: band literal D46 → **D47**, freeze approvals D48 → **D49**. This commit changes **only** decision
references:

- in the 13 frozen files, the docstring approval paragraph `literals D46 and` / `D48). This file is frozen` now
  reads `literals D47 and` / `D49). This file is frozen` (same length, no rewrap);
- in the 13 manifest entries, `approval_ref`, `source.range` and `split_policy.ruling_ref` (`D46` → `D47`,
  `D48` → `D49`), plus the recomputed full-file, prefix/suffix and closure hashes;
- the generator, its config and this record.

**No declaration changed.** Every ABI hash is unchanged (`ABI HASHES OK (171)`). `check_identity.py` reports all 13
identical, and the other 158 manifest entries are unchanged as JSON. `git diff 1e0e888c -- KAM/Frozen` shows
exactly two changed lines per file. The same commit fixes audit 1 F2: `check_identity.py` now compares B and the
window as complete files (A's wrapper with their §1.3 imports and blocks) and exits 1 on a mismatch. Both of the
auditor's mutations (an appended declaration, `<` → `≤`) are now rejected with exit 1.

## Checks run

- Gate build of the three theorem modules (closure = all 13 frozen files + stubs): success, 2112 jobs, only the
  three anchor `sorry` warnings.
- `check_frozen_anchors.py`: `FROZEN-ANCHOR GUARD OK`.
- `abi_hashes.py --check`: `ABI HASHES OK (171 frozen declarations)`.
- `lint_sources.sh`: fails only on the pre-existing `CsegSupport.lean` over-long lines (SO-DATA3) and the
  out-of-date root, which rule 10 leaves to landing.
- `lake build --no-build KAM.SpinOrbit.LunarFinalR2V2`: `All targets up-to-date (5212 jobs)`. Nothing under
  `KAM/SpinOrbit` was edited.

## Pending (after the orchestrator's decision on the rebuild)

- **Q11:** `Model.lean` imports the frozen `soEcc … soField` and drops its copies. `Barrier.lean` imports the frozen
  `SoBarrier`, drops its structure and adds `SoBarrier.isInvariantSet` for `so_confinement`. The two constructor
  sites in `Graph/Inverse.lean` (lines 258, 361) convert `T.soGraph_invariant` to the written-out field. Then the
  data rebuild, the root regeneration and the READY-A marker.
- **Phase B (SEAL audit):** providers from `lunar_barriers_65_v2`, `lunar_spin_confinement_65_v2` (literals:
  `lunarR2BandLo = 97245/100000`, `lunarR2BandHi = 102755/100000`, `lunarR2PLo = 9934/10000`,
  `lunarR2PHi = 10066/10000`, `lunarR2Delta = 2755/100000`, already equal to the frozen ones) and the window by
  `decide`. Then the frozen bodies become `by exact KAM.Provider.SpinOrbit.<name> …`.
