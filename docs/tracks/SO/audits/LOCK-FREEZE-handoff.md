# LOCK-FREEZE Phase A handoff (identity audit request)

Branch `inp-lockfreeze` (off `inp`, merged `inp` at da762768 = SO-FREEZE3 landed). Authority:
`docs/tracks/SO/design/FREEZE-PROPOSAL-LOCK.md` §1 (rev. 3) with the §2 recommended answers; freeze approval
**D49**, route **D45** (renumbered on main b17bf0c0; D48 is "lock data as is" and is not cited).

## Files (all new)
- `KAM/Frozen/SpinOrbit/Defs/{IsSyncOrbit,LunarSyncOrbit,LibAction,LunarOmega}.lean` (SEALED definitions)
- `KAM/Frozen/SpinOrbit/Theorems/{LunarSyncOrbitSpec,LunarSyncOrbitUnique,LunarSyncOrbitBound,LunarSyncLock}.lean`
  (DRAFT_SORRY, body exactly `by sorry` between the markers)
- `KAM/Provider/SpinOrbit/{LunarSyncOrbitSpec,LunarSyncOrbitUnique,LunarSyncOrbitBound,LunarSyncLock}.lean`
  (empty quarantined stubs, as the track W precedent)
- `manifest/frozen-anchors.json`: 8 entries `spinorbit.lock.<name>.v1` (171 → 179), written by
  `kam_manifest_add_track.py`, approval_ref/ruling_ref cite D45, D49; ABI hashes filled.

## Identity with §1
Declaration text (docstrings, binders, bodies, literals 8/65, 17/1000000, 27/200000, 129/10000, 21/100,
26/1000) is copied character for character from §1.1/§1.2. Namespace `KAM.SpinOrbit` (as FREEZE-PROPOSAL-2).
`IsSyncOrbit` uses the `soField` form (Q2) and imports SO-FREEZE3's frozen `SoField`; nothing is redefined.
Added lines (not in §1): copyright header, `module`, imports, module docstring, `@[expose] public
noncomputable section` (defs) / `@[expose] public section` (theorems), `namespace`/`end`, frozen markers,
the `:=` + `by sorry` body, and **`open Real`** in `LibAction.lean` (so `π` resolves; §1 is shown without it).
Imports: IsSyncOrbit ← `Mathlib.Analysis.Calculus.ContDiff.Deriv`, frozen `SoField`; LunarSyncOrbit ←
frozen `IsSyncOrbit`; LibAction ← `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`,
`Mathlib.Analysis.Calculus.Deriv.Basic`; LunarOmega ← `Mathlib.Data.Rat.Defs`; theorems ← the frozen defs
they mention (+ `SoField` for `lunar_sync_lock`) and their provider.

## Landed equivalents: bridges chosen
LOCK-DATA (`/root/code/KAM-inp-lockdata`) builds against `KAM/SpinOrbit/Lock/{Assembly,PO/Orbit,Confine}`,
so the landed `KAM.SpinOrbit.Lock.{IsSyncOrbit,lunarSyncOrbit,libAction,lunarOmega}` are kept unchanged.
Phase B providers will bridge: `IsSyncOrbit` frozen ↔ landed by `soField_eq` (Iff, then funext/propext),
hence `lunarSyncOrbit` equal; `libAction` and `lunarOmega` are syntactically identical (`rfl`).

## Checks
- Build: this worktree has no `.lake/build` (brief: no new build here). Each of the 12 modules was compiled
  with `lean -R . -o` (capped `systemd-run … MemoryMax=8G`, `nice -n 10`, project leanOptions) into the
  scratchpad against SO-FREEZE3's built oleans (`KAM-inp-sodata3`, frozen tree identical to `inp`).
  Output: only `declaration uses 'sorry'` on the four theorems.
- `scripts/abi_hashes.py --check` (LEAN_PATH overlay): `ABI HASHES OK (179 frozen declarations)`; all 171
  pre-existing hashes reproduced unchanged.
- `scripts/check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json`: `FROZEN-ANCHOR GUARD OK`.
- `scripts/lint_sources.sh`: `check_lean_modules: PASS`, guard OK; **fails** on
  1. `DRAFT_SORRY anchor KAM.SpinOrbit.lunarSyncOrbit_{spec,unique,bound} used outside its frozen file`:
     a short-name match on the landed `KAM.SpinOrbit.Lock.lunarSyncOrbit_*` in `Lock/PO/Orbit.lean`
     (136, 147, 148, 213, 215) and `Lock/Assembly.lean` (325, 327). Different declarations (Lock
     namespace, files do not import the frozen ones). Renaming would touch LOCK-DATA's modules, so not
     done; disappears at seal (PROVED), or rename after LOCK-DATA lands — orchestrator's call.
  2. `KAM.lean is out of date` (generated root; rule 10, not edited — needs `gen_root_imports.py`).
  3. its elaborated-hash step needs a lake build (none here); replaced by the ABI check above.
- `#print axioms`: not applicable in Phase A (bodies are `sorry`).

## Uncertainties / errata / deviations
- No suspected errata in the pinned source. Deviation: only the added `open Real` line.
- The frozen theorems `lunarSyncOrbit_*` share short names with landed Lock theorems (lint item 1).
