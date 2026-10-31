# Track SO freeze (decisions D40, D47, D49): package SO-FREEZE3

Branch `inp-sofreeze3` (off `inp` 9517d71e). Freezes exactly the thirteen declarations of
[`FREEZE-PROPOSAL-2.md`](FREEZE-PROPOSAL-2.md) §1 (definition texts: [`FREEZE-PROPOSAL.md`](FREEZE-PROPOSAL.md)
§1.1–§1.8, unchanged per proposal 2 §1.1), with the final literals of D47/D49.

**Status: Phase A and Phase B complete (sealed, D50).** The 13 declarations are frozen with the D47/D49
literals (identity audit 1: PASS WITH NOTES; the notes are resolved below). The landed code uses the frozen
definitions (Q11, below), and all SO data modules were rebuilt on top. The three theorems are sealed by
`by exact KAM.Provider.SpinOrbit.<name> …`; their axioms are `propext`, `Classical.choice` and `Quot.sound`. The
SEAL audit request is [`audits/SO-FREEZE3-handoff.md`](audits/SO-FREEZE3-handoff.md); the report goes to
`audits/SO-FREEZE3-seal-audit.md`.

## Files

| Declaration | Frozen file | Manifest id | State |
|---|---|---|---|
| `KAM.SpinOrbit.soEcc` | `KAM/Frozen/SpinOrbit/Defs/SoEcc.lean` | `spinorbit.d40.soEcc.v1` | SEALED (definition) |
| `KAM.SpinOrbit.soEps` | `KAM/Frozen/SpinOrbit/Defs/SoEps.lean` | `spinorbit.d40.soEps.v1` | SEALED |
| `KAM.SpinOrbit.soCoeffPoly` | `KAM/Frozen/SpinOrbit/Defs/SoCoeffPoly.lean` | `spinorbit.d40.soCoeffPoly.v1` | SEALED |
| `KAM.SpinOrbit.soA` | `KAM/Frozen/SpinOrbit/Defs/SoA.lean` | `spinorbit.d40.soA.v1` | SEALED |
| `KAM.SpinOrbit.soModes` | `KAM/Frozen/SpinOrbit/Defs/SoModes.lean` | `spinorbit.d40.soModes.v1` | SEALED |
| `KAM.SpinOrbit.soV` | `KAM/Frozen/SpinOrbit/Defs/SoV.lean` | `spinorbit.d40.soV.v1` | SEALED |
| `KAM.SpinOrbit.soField` | `KAM/Frozen/SpinOrbit/Defs/SoField.lean` | `spinorbit.d40.soField.v1` | SEALED |
| `KAM.SpinOrbit.SoBarrier` | `KAM/Frozen/SpinOrbit/Defs/SoBarrier.lean` | `spinorbit.d40.SoBarrier.v1` | SEALED |
| `KAM.SpinOrbit.lunarPLo` | `KAM/Frozen/SpinOrbit/Defs/LunarPLo.lean` | `spinorbit.d40.lunarPLo.v1` | SEALED |
| `KAM.SpinOrbit.lunarPHi` | `KAM/Frozen/SpinOrbit/Defs/LunarPHi.lean` | `spinorbit.d40.lunarPHi.v1` | SEALED |
| `KAM.SpinOrbit.lunar_barriers` | `KAM/Frozen/SpinOrbit/Theorems/LunarBarriers.lean` | `spinorbit.d40.lunar_barriers.v1` | SEALED (theorem) |
| `KAM.SpinOrbit.lunar_spin_confinement` | `KAM/Frozen/SpinOrbit/Theorems/LunarSpinConfinement.lean` | `spinorbit.d40.lunar_spin_confinement.v1` | SEALED (theorem) |
| `KAM.SpinOrbit.lunarPLo_lt_lunarPHi` | `KAM/Frozen/SpinOrbit/Theorems/LunarWindow.lean` | `spinorbit.d40.lunarPLo_lt_lunarPHi.v1` | SEALED (theorem) |

Providers (quarantined): `KAM/Provider/SpinOrbit/{LunarBarriers,LunarSpinConfinement,LunarWindow}.lean`, from the
landed `lunar_barriers_65_v2`, `lunar_spin_confinement_65_v2` and `decide +kernel`. Sealing bodies:
`by exact KAM.Provider.SpinOrbit.<name> …`.

## Literal substitutions (D47/D49), and nothing else

| Place | Proposal 2 (interim) | Frozen |
|---|---|---|
| `lunarPLo` | `9933 / 10000      -- interim candidate; …` | `9934 / 10000` |
| `lunarPHi` | `10067 / 10000     -- interim candidate; …` | `10066 / 10000` |
| `lunar_barriers` band (twice) | `SoBarrier (97286 / 100000) (102714 / 100000)` | `SoBarrier (97245 / 100000) (102755 / 100000)` |
| `lunar_barriers` docstring | `[0.97286, 1.02714]` | `[0.97245, 1.02755]` |
| `lunar_spin_confinement` bound | `≤ 2714 / 100000` | `≤ 2755 / 100000` |
| `lunar_spin_confinement` docstring | `2714/100000` (2.714 %) | `2755/100000` (2.755 %) |

(Proposal 2 §1.2 says the window comments mark the proposal status and the frozen files carry none.)

## Method

`docs/tracks/SO/freeze/gen_frozen.py` writes the thirteen files and the three stubs from the §1 snippets with the
substitutions above. Then:
* orchestrator-tools `kam_manifest_add_track.py` with `freeze/freeze.json` and `freeze/cfg.json` (+13 entries,
  171 in all);
* `contract.id` set to `spinorbit.<name>` (the proposal 1 §4 shape);
* `scripts/abi_hashes.py` for the 13 hashes (the other 158 were recomputed and are unchanged).

`docs/tracks/SO/freeze/check_identity.py` re-checks every file against the approved text mechanically.

## Header lines added at freeze time (not part of the approved declaration texts)

For every file:
* the copyright block (proposal 1 §1 precedent);
* a module docstring `# Frozen definition|structure|theorem `KAM.SpinOrbit.<name>`` with the approval paragraph
  "Owner-approved on 2026-10-31 (decision D40, docs/tracks/SO/FREEZE-PROPOSAL-2.md; literals D47 and D49). This file
  is frozen: …". The theorem files add the sealing rule (precedent: track W). This docstring replaces the
  placeholder `/-! # Frozen theorem … (docstring as in the precedent) -/` of proposal 2 §1.3.

The theorem files also get `-- FROZEN_ANCHOR_PREFIX_BEGIN` after the copyright block, as shown in §1.3. For
`LunarSpinConfinement` and `LunarWindow` ("same wrapper as A"), §1.3 lists the imports and the A wrapper: the
module line, the frozen imports in the listed order, the private provider import, `@[expose] public section`,
`namespace KAM.SpinOrbit` and the marked suffix.

## Deviations

* **D-SOF-5 (lint, precedent D-WF1).** `scripts/lint_sources.sh` rejects Lean lines over 100 characters. In four
  approved docstring lines exactly one space, the last one at or before column 100 outside a code span, is replaced
  by a newline. No other character changes.
  * `soCoeffPoly`: `… (zero outside `1 ≤ m ≤ 7`);` / `` `A_m = W(m/2, e)/2` ``
  * `lunar_barriers`: `… there are two` / `invariant`; `… the lower one strictly below` / `the`
  * `lunar_spin_confinement`: `… unique among global solutions, and` / `its`

  All four lines were already over 100 characters in the approved text: none contains a substituted literal, except
  the band line, where the substitution keeps the length. Docstrings are not part of the ABI.
* **D-SOF-6 (frozen guard).** Proposal 2 §1.3 shows the DRAFT body as a bare `sorry`.
  `scripts/check_frozen_anchors.py` requires the DRAFT_SORRY body to be exactly `by sorry`, the shape of every
  frozen theorem in the repository. The body is written `by sorry`. It lies inside the proof region, outside the
  prefix and suffix hashes, and sealing replaces it.
* **D-SOF-7 (frozen guard).** The proposal 1 §4 shape has a common `split_policy.source_group: "spinorbit.lunar"`.
  The guard rejects a shared NOT_SPLIT group without one joint anchor ("NOT_SPLIT requires one joint constitutional
  anchor"). Each entry uses its own group `spinorbit.<name>`, as track W does.
* **Approval date (closes audit 1 F1).** `approved_at` and the docstrings say 2026-10-31. `docs/DECISIONS.md` on
  `main` (renumbering commit b17bf0c0; read at 74a963d3) records **D47 (2026-10-31, 07:00 UTC)**, the 2.755 % band
  literal with rule B's tightness clause relaxed (line 385), and **D49 (2026-10-31, 07:10 UTC)**, the freeze
  approvals for band and lock (line 396).
* **Metadata change: decision renumbering (D46 → D47, D48 → D49).** These two decisions were first numbered D46 and
  D48 on `main`; D46 clashed with the earlier D46 of 2026-10-30 (Route B), and the orchestrator renumbered them.
  The approval paragraph of the 13 frozen module docstrings and the manifest fields `approval_ref`,
  `source.range` and `split_policy.ruling_ref` were updated by a same-length substitution, with no rewrap. No
  declaration text changed: `check_identity.py` still reports all 13 identical, and every ABI hash is unchanged.
  The full-file, prefix/suffix and closure hashes of the 13 entries were recomputed with the guard's own region
  rule; the other 158 entries are unchanged as JSON.

## Q11 and the data rebuild

Q11 (proposal 2 §7) makes the landed code use the frozen definitions, with no duplicates (commit 0ed69133):
- `Model.lean` imports the frozen `soEcc … soField` and deletes its own copies;
- `Barrier.lean` imports the frozen `SoBarrier`, with the adapters `SoBarrier.isInvariantSet` and
  `SoBarrier.invariant_of_isInvariantSet`;
- the constructor sites in `Graph/Inverse.lean` and `Graph/Rot.lean` pass the written-out invariance;
- `CsegSupport.lean` gets the 100-column fix in the same change.

Every SO data module reaches `Model` and `Barrier` through public imports, so Q11 forces a rebuild of all of them.
The orchestrator accepted the one-time rebuild. It ran into a copy of the overlay, `kam-data/so-freeze3/build-overlay`,
relinked in this worktree only, with SO-DATA3's capped two-lane driver: 1071 modules built, peak 9.45 GB, both
lanes DONE at 13:34 UTC. One lower module was stopped by earlyoom during system-wide low memory, not by a Lean
error; the lower lane was restarted. Details and logs are in the audit request.

## Checks (2026-10-31, after the seal)

See [`audits/SO-FREEZE3-handoff.md`](audits/SO-FREEZE3-handoff.md), "Checks run":
- builds; `#print axioms` (standard three, for the three exports and their providers);
- `leanchecker` replay of the 13 frozen modules and the 3 providers;
- guard, ABI, `check_identity.py` and lint (only the generated root is out of date, left to landing).
