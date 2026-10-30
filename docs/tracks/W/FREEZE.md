# Track W freeze (decision D41)

Branch `inp-wfreeze` (off `inp` 3860bc48). Freezes exactly the twelve declarations of
`docs/tracks/W/W-STATEMENTS.md` revision 1 (commit ffcbdb93), from the reviewable drafts
`docs/tracks/W/drafts/KAM/Wave/{Defs,Theorems}/*.lean.txt` at that commit.

## Files

| Declaration | Frozen file | Manifest id | State |
|---|---|---|---|
| `KAM.Wave.lam` | `KAM/Frozen/Wave/Defs/Lam.lean` | `wave.lam.v1` | SEALED (definition) |
| `KAM.Wave.sineMode` | `KAM/Frozen/Wave/Defs/SineMode.lean` | `wave.sineMode.v1` | SEALED |
| `KAM.Wave.ellWeight` | `KAM/Frozen/Wave/Defs/EllWeight.lean` | `wave.ellWeight.v1` | SEALED |
| `KAM.Wave.WaveSpace` | `KAM/Frozen/Wave/Defs/WaveSpace.lean` | `wave.WaveSpace.v1` | SEALED |
| `KAM.Wave.coeff` | `KAM/Frozen/Wave/Defs/Coeff.lean` | `wave.coeff.v1` | SEALED |
| `KAM.Wave.reconU` | `KAM/Frozen/Wave/Defs/ReconU.lean` | `wave.reconU.v1` | SEALED |
| `KAM.Wave.reconV` | `KAM/Frozen/Wave/Defs/ReconV.lean` | `wave.reconV.v1` | SEALED |
| `KAM.Wave.cubicGrad` | `KAM/Frozen/Wave/Defs/CubicGrad.lean` | `wave.cubicGrad.v1` | SEALED |
| `KAM.Wave.linearTorus` | `KAM/Frozen/Wave/Defs/LinearTorus.lean` | `wave.linearTorus.v1` | SEALED |
| `KAM.Wave.IsAnalyticTorusEmbedding` | `KAM/Frozen/Wave/Defs/IsAnalyticTorusEmbedding.lean` | `wave.IsAnalyticTorusEmbedding.v1` | SEALED |
| `KAM.Wave.IsClassicalSolution` | `KAM/Frozen/Wave/Defs/IsClassicalSolution.lean` | `wave.IsClassicalSolution.v1` | SEALED |
| `KAM.Wave.nlw2` | `KAM/Frozen/Wave/Theorems/Nlw2.lean` | `wave.nlw2.v1` | DRAFT_SORRY |

Provider stub: `KAM/Provider/Wave/Nlw2.lean` (empty module, quarantined; will define `KAM.Provider.Wave.nlw2`).
Sealing body: `by exact KAM.Provider.Wave.nlw2 hm`.

## Method

`docs/tracks/W/freeze/freeze_w.py` (reads the drafts from `git show ffcbdb93:...`), then
`docs/tracks/W/freeze/add_track.py` (= orchestrator-tools `kam_manifest_add_track.py` with the closure regex
fixed so that `KAM.Frozen.Defs.*` imports, here `IsDiophantine`, enter `definition_closure`) with `cfg.json`,
then `scripts/abi_hashes.py` on the twelve entries, and `scripts/gen_root_imports.py` (KAM.lean: +11 definition
modules; the DRAFT_SORRY anchor and its provider are skipped).

## What changed relative to the drafts (header only)

The drafts are complete module files. For every file:
* the line `-- DRAFT (W-STMT rev1), not frozen. Proposed final path: ...` is dropped;
* `public import KAM.Wave.Defs.X` becomes `public import KAM.Frozen.Wave.Defs.X` (same module, final path);
* the module docstring title becomes ``# Frozen definition `KAM.Wave.<name>` `` (theorem: ``# Frozen theorem
  `KAM.Wave.nlw2` (W-NLW2)``), its body paragraph is kept verbatim, and an approval paragraph is appended
  ("Owner-approved on 2026-10-30 (decision D41; ...). This file is frozen ..."). For `nlw2` the draft sentence
  "The proof body is `sorry` in this draft only." is replaced by the sealing rule.

All other header lines (copyright, `module`, Mathlib/`KAM.Frozen.Defs.IsDiophantine` imports,
`@[expose] public noncomputable section` / `@[expose] public section`, `open MeasureTheory Filter Topology`)
are the drafts' own, unchanged. `Nlw2.lean` additionally gets `-- FROZEN_ANCHOR_PREFIX_BEGIN` after the
copyright, the private `import KAM.Provider.Wave.Nlw2`, and the proof-region markers: the approved
`... := by\n  sorry` becomes `... :=\n  -- FROZEN_ANCHOR_PROOF_BEGIN\n  by sorry\n  -- FROZEN_ANCHOR_PROOF_END`
followed by the marked suffix (the shape of every frozen theorem in the repository).

## Deviation D-WF1 (lint)

`scripts/lint_sources.sh` rejects Lean lines over 100 characters. Three approved declaration docstrings had one
such line; in each, exactly one space is replaced by a newline (no character added, removed or changed
otherwise; precedent: the frozen AmdConfinement docstring rewrap, OVERNIGHT 2026-10-29 20:00):
* `linearTorus`: `... W-ST1),` / `period-one angle ...`
* `reconU`, `reconV`: `... φ_j(x)\`, where` / `` `q = coeff y` (P96-W p. 277). -/``
Docstrings are not part of the ABI (`#print`/`#check` with `pp.all`); the ABI hashes were computed before the
rewrap and re-checked after it: identical.

Every other byte from `namespace KAM.Wave` to the end of each definition file, and to the `:=` of `nlw2`, is
identical to the draft.

## Checks (2026-10-30)

* `inp_lake_build.sh ... KAM.Frozen.Wave.Theorems.Nlw2`: success, 2764 jobs; only message
  `warning: KAM/Frozen/Wave/Theorems/Nlw2.lean:43:8: declaration uses 'sorry'`.
* `check_frozen_anchors.py --root . --manifest manifest/frozen-anchors.json`: `FROZEN-ANCHOR GUARD OK`.
* `abi_hashes.py . manifest/frozen-anchors.json --check` (with inp's oleans for the other 146 anchors via a
  symlink overlay on `LEAN_PATH`, since this slim worktree builds only the W modules):
  `ABI HASHES OK (158 frozen declarations)`.
* `scripts/lint_sources.sh` (same overlay): exit 0; `check_lean_modules: PASS (1464 Lean files ...)`.
* `#print axioms`: `nlw2` `[propext, sorryAx, Classical.choice, Quot.sound]`; the eleven definitions
  `[propext, Classical.choice, Quot.sound]`.

## Notes for errata / later successors (not changed: frozen text)

* N1. `reconV` docstring: "`V_m(p)(x) = Σ √λ_j p_j φ_j(x)`, where `q = coeff y`" should read `p = coeff y`
  (docstring only; the body is right).
* N2. The `nlw2` declaration docstring still opens "**W-NLW2 (proposed).**" (approved text, kept).
